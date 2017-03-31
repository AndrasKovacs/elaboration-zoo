
{-# language
  PatternSynonyms, BangPatterns, MagicHash, PatternGuards,
  DataKinds, LambdaCase, ViewPatterns, TupleSections, Strict,
  TypeFamilies, GADTs, EmptyCase, OverloadedStrings #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

module MetavarLet where

import Prelude hiding (pi)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM

import Data.List
import Data.String
import Data.Maybe
import System.IO.Unsafe
import Data.IORef

-- Syntax
--------------------------------------------------------------------------------

type Name   = String
type Meta   = Int
type Gen    = Int
type Ty     = Val
type Sub a  = [(Name, a)]
type Env    = Sub (Maybe Val)        -- Nothing: bound, Just: defined
type Cxt    = Sub (Either Ty Ty)     -- Left: bound, Right: defined
type Ren    = HashMap (Either Name Gen) Name
type MCxt   = IntMap Val
type Spine  = Sub (Val, Icit)
data Icit   = Expl | Impl deriving (Eq, Show)

data Raw
  = RVar Name
  | RLet Name Raw Raw Raw
  | RApp Raw Raw Icit
  | RLam Name Icit Raw
  | RPi Name Icit Raw Raw
  | RStar
  | RNoInsert
  | RHole
  deriving Show

data Head
  = VMeta Meta
  | VVar Name
  | VGen Gen

data Val
  = Head :$ Spine
  | VLam Name Icit (Val -> Val)
  | VPi Name Icit Val (Val -> Val)
  | VStar
infix 3 :$

data Tm
  = Var Name
  | Gen Gen    
  | Let Name Tm Tm Tm
  | App Tm Tm Name Icit
  | Lam Name Icit Tm
  | Pi Name Icit Tm Tm
  | Star
  | Meta Meta
  deriving Show

-- Our nice global state, reset before use please
--------------------------------------------------------------------------------

{-# noinline mcxt #-}
mcxt :: IORef MCxt
mcxt = unsafeDupablePerformIO (newIORef mempty)

{-# noinline freshMeta #-}
freshMeta :: IORef Int
freshMeta = unsafeDupablePerformIO (newIORef 0)

reset :: IO ()
reset = do
  writeIORef mcxt mempty
  writeIORef freshMeta 0

inst :: Meta -> Maybe Val
inst m = unsafeDupablePerformIO $ (IM.lookup m <$> readIORef mcxt)

-- Evaluation (modulo global mcxt)
--------------------------------------------------------------------------------

vapp :: Val -> Val -> Name -> Icit -> Val
vapp t ~a x i = case t of
  VLam x i t -> t a 
  h :$ sp    -> h :$ ((x, (a, i)) : sp)
  _          -> error "vapp: impossible" 

eval :: Env -> Tm -> Val
eval vs = \case
  Var x         -> maybe (VVar x :$ []) refresh (fromJust $ lookup x vs)
  Let x e' ty e -> eval ((x, Just (eval vs e')):vs) e
  App f a x i   -> vapp (eval vs f) (eval vs a) x i
  Lam x i t     -> VLam x i $ \a -> eval ((x, Just a):vs) t
  Pi x i a b    -> VPi x i (eval vs a) $ \a -> eval ((x, Just a):vs) b
  Star          -> VStar
  Meta i        -> maybe (VMeta i :$ []) refresh (inst i)                   
  Gen{}         -> error "eval: impossible"

refresh :: Val -> Val
refresh = \case
  VMeta i :$ sp | Just t <- inst i ->
                  refresh (foldr (\(x, (a, i)) t -> vapp t a x i) t sp)
  t -> t

quote :: Val -> Tm
quote = go where
  goHead = \case
    VMeta m -> Meta m
    VVar x  -> Var x
    VGen g  -> Gen g
  go t = case refresh t of
    h :$ sp     -> foldr (\(x, (a, i)) t -> App t (go a) x i) (goHead h) sp    
    VLam x i t  -> Lam x i (go (t (VVar x :$ [])))
    VPi x i a b -> Pi x i (go a) (go (b (VVar x :$ [])))
    VStar       -> Star

-- Unification
--------------------------------------------------------------------------------

lams :: Spine -> Tm -> Tm
lams sp t = foldl' (\t (x, (a, i)) -> Lam x i t) t sp

invert :: Spine -> Ren
invert = foldl' go HM.empty where
  go r (x, (a, _)) =
    let var = case a of
          VVar x' :$ [] -> Left x'
          VGen i  :$ [] -> Right i
          _             -> error "Meta substitution is not a renaming"
    in HM.alter (maybe (Just x) (\_ -> Nothing)) var r

rename :: Meta -> Ren -> Tm -> Tm
rename occur = go where
  go r = \case
    Var x         -> maybe (error "scope") Var (HM.lookup (Left x) r)
    Gen g         -> maybe (error "scope") Var (HM.lookup (Right g) r)
    Let x e' ty e -> Let x (go r e') (go r ty) (go r e)
    App f a x i   -> App  (go r f) (go r a) x i
    Lam x i t     -> Lam x i (go (HM.insert (Left x) x r) t)
    Pi x i a b    -> Pi x i (go r a) (go (HM.insert (Left x) x r) b)
    Star          -> Star
    Meta i | i == occur -> error "occurs"
           | otherwise  -> Meta i  

solve :: Meta -> Spine -> Val -> IO ()
solve m sp t = do
  let t' = lams sp (rename m (invert sp) (quote t))
  modifyIORef' mcxt $ IM.insert m (eval [] t')

gen :: Gen -> Val
gen g = VGen g :$ []

matchIcit :: Icit -> Icit -> IO ()
matchIcit i i' = if i == i'
  then pure ()
  else error "can't match explicit binder with implicit"

unify :: Val -> Val -> IO ()
unify t t' = go 0 t t' where
  
  go :: Gen -> Val -> Val -> IO ()
  go !g t t' = case (refresh t, refresh t') of
    (VStar, VStar) -> pure ()
    
    (VLam x i t, VLam x' i' t') -> go (g + 1) (t (gen g)) (t' (gen g))
    
    (VLam x i t, t')   -> go (g + 1) (t (gen g)) (vapp t' (gen g) x i)
    (t, VLam x' i' t') -> go (g + 1) (vapp t (gen g) x' i') (t' (gen g))
      
    (VPi x i a b, VPi x' i' a' b') -> do
      matchIcit i i'
      go g a a'
      go (g + 1) (b (gen g)) (b' (gen g))      
    
    (VVar x  :$ sp, VVar x'  :$ sp') | x == x' -> goSpine g sp sp'
    (VGen i  :$ sp, VGen i'  :$ sp') | i == i' -> goSpine g sp sp'
    (VMeta m :$ sp, VMeta m' :$ sp') | m == m' -> goSpine g sp sp'
    (VMeta m :$ sp, t              ) -> solve m sp t
    (t,             VMeta m  :$ sp ) -> solve m sp t
    
    (t, t') ->
      error $ "can't unify\n" ++ show (quote t) ++ "\nwith\n" ++  show (quote t')

  goSpine :: Gen -> Spine -> Spine -> IO ()
  goSpine g sp sp' = case (sp, sp') of
    ((_, (a, _)):as, (_, (b, _)):bs)  -> goSpine g as bs >> go g a b
    ([]            , []            )  -> pure ()
    _                                 -> error "unify spine: impossible"  


-- Elaboration
--------------------------------------------------------------------------------

newMeta :: Cxt -> IO Tm
newMeta cxt = do  
  m <- readIORef freshMeta
  writeIORef freshMeta (m + 1)
  let bvars = HS.toList $ HS.fromList [x | (x, Left{}) <- cxt]
  pure $ foldr (\x t -> App t (Var x) x Expl) (Meta m) bvars
  
check :: Cxt -> Env -> Raw -> Ty -> IO Tm
check cxt vs t want = case (t, want) of  
  (RHole, _) ->
    newMeta cxt
    
  (RLam x i t, VPi _ i' a b) | i == i' -> 
    Lam x i <$> check ((x, Left a): cxt) ((x, Nothing):vs) t (b (VVar x :$ []))
    
  (t, VPi x Impl a b) -> 
    Lam x Impl <$> check ((x, Left a): cxt) ((x, Nothing):vs) t (b (VVar x :$ []))
    
  (t, _) -> do
    (t, has) <- infer cxt vs t
    t <$ unify has want

insertMetas :: Cxt -> Env -> (Tm, Ty) -> IO (Tm, Ty)
insertMetas cxt vs (t, ty) = case ty of
  VPi x Impl a b -> do
    m <- newMeta cxt
    insertMetas cxt vs (App t m x Impl, (b (eval vs m)))
  _ -> pure (t, ty)      

infer :: Cxt -> Env -> Raw -> IO (Tm, Ty)
infer cxt vs = \case
  RApp f RNoInsert i -> do
    matchIcit i Expl
    infer' cxt vs f
  t -> infer' cxt vs t >>= insertMetas cxt vs

infer' :: Cxt -> Env -> Raw -> IO (Tm, Ty)
infer' cxt vs = \case
  RStar ->
    pure (Star, VStar)
    
  RNoInsert ->
    error "unexpected NoInsert"
    
  RVar x -> maybe
    (error $ "Variable: " ++ x ++ " not in scope")
    (\ty -> pure (Var x, either id id ty))
    (lookup x cxt)
    
  RApp f RNoInsert i -> do
    matchIcit i Expl
    infer cxt vs f
    
  RApp f a i -> do
    (f, ty) <- infer' cxt vs f
    case ty of
      VPi x i' ta tb -> do
        a' <- case (i', i) of
          (Expl, i)    -> matchIcit i Expl >> check cxt vs a ta
          (Impl, Impl) -> check cxt vs a ta
          (Impl, Expl) -> newMeta cxt
        pure (App f a' x i', tb (eval vs a'))
      _ -> error "can only apply to function"
      
  RPi x i a b -> do
    a <- check cxt vs a VStar
    let ~a' = eval vs a
    b <- check ((x, Left a'): cxt) vs b VStar
    pure (Pi x i a b, VStar)
    
  RLet x e1 t e2 -> do
    t <- check cxt vs t VStar
    let ~t' = eval vs t
    e1 <- check cxt vs e1 t'
    let ~e1' = eval vs e1
    (e2, ~te2) <- infer ((x, Right t'): cxt) ((x, Just e1'):vs) e2
    pure (Let x e1 t e2, te2)

  RLam x i t -> do
    ~ma <- eval vs <$> newMeta cxt
    (t, ty) <- infer ((x, Left ma):cxt) ((x, Nothing):vs) t
    pure (Lam x i t, VPi x i ma (\a -> eval ((x, Just a):vs) (quote ty)))   
    
  RHole -> do
    m1 <- newMeta cxt
    m2 <- newMeta cxt
    pure (m1, eval vs m2)

tmSpine :: Tm -> (Tm, Sub (Tm, Icit))
tmSpine t = go t [] where
  go (App f a x i) sp = go f ((x, (a, i)):sp)
  go t             sp = (t, sp)    

-- zonk :: Spine -> Tm -> Tm
-- zonk env = \case
--   Var x        -> Var x
--   Meta m       -> maybe (Meta m) quote (inst m)  
--   Star         -> Star
--   Pi x i a b   -> Pi x i (zonk env a) (zonk env b)
--   App f a x i  -> _

--   Lam x i t    -> Lam x i (zonk env t)
--   Let x e t e' -> _
--   _            -> error "zonk: impossible Gen"

--------------------------------------------------------------------------------

infer0 :: Raw -> IO Tm
infer0 r = quote . snd <$> (reset *> infer [] [] r)

elab0 :: Raw -> IO Tm
elab0 r = fst <$> (reset *> infer [] [] r)

-- zonk0 :: Raw -> IO Tm
-- zonk0 r = zonk [] . fst <$> (reset *> infer [] [] r)

nf0 :: Raw -> IO Tm
nf0 r = quote . eval [] . fst <$> (reset *> infer [] [] r)

{-
-- Printing
--------------------------------------------------------------------------------

-- prettyTm :: Int -> Tm -> ShowS
-- prettyTm prec = go (prec /= 0) where

--   unwords' :: [ShowS] -> ShowS
--   unwords' = foldr1 (\x acc -> x . (' ':) . acc)

--   spine :: Tm -> Tm -> [Tm]
--   spine f x = go f [x] where
--     go (App f y _) args = go f (y : args)
--     go t           args = t:args

--   lams :: String -> Tm -> ([String], Tm)
--   lams v t = go [v] t where
--     go vs (Lam v t) = go (v:vs) t
--     go vs t         = (vs, t)

--   go :: Bool -> Tm -> ShowS
--   go p (Var v)        = (v++)
--   go p (Let v e t e') =
--     (v++) . (" : "++) . go False t . ("\n"++) .
--     (v++) . (" = "++) . go False e . ("\n\n"++) .
--     go False e'
--   go p (Meta v)       = (("?"++).(show v++))
--   go p (App f x _)    = showParen p (unwords' $ map (go True) (spine f x))
--   go p (Lam v t)      = case lams v t of
--     (vs, t) -> showParen p (("\\"++) . (unwords (reverse vs)++) . (". "++) . go False t)
--   go p (Pi v a b) = showParen p (arg . (" -> "++) . go False b)
--     where arg = if v /= "_" then showParen True ((v++) . (" : "++) . go False a)
--                               else go True a
--   go p Star    = ('*':)
--   go p (Gen g) = ("~"++).(show g++)

-- instance Show Tm where
--   showsPrec = prettyTm

-- instance IsString Tm where
--   fromString = Var

-- -- --------------------------------------------------------------------------------

-- prettyRaw :: Int -> Raw -> ShowS
-- prettyRaw prec = go (prec /= 0) where

--   unwords' :: [ShowS] -> ShowS
--   unwords' = foldr1 (\x acc -> x . (' ':) . acc)

--   spine :: Raw -> Raw -> [Raw]
--   spine f x = go f [x] where
--     go (RApp f y) args = go f (y : args)
--     go t          args = t:args

--   lams :: String -> Raw -> ([String], Raw)
--   lams v t = go [v] t where
--     go vs (RLam v t) = go (v:vs) t
--     go vs t          = (vs, t)

--   go :: Bool -> Raw -> ShowS
--   go p (RVar v)        = (v++)
--   go p (RLet v e t e') =
--     (v++) . (" : "++) . go False t . ("\n"++) .
--     (v++) . (" = "++) . go False e . ("\n\n"++) .
--     go False e'
--   go p RHole           = ('_':)
--   go p (RApp f x)      = showParen p (unwords' $ map (go True) (spine f x))
--   go p (RLam v t)      = case lams v t of
--     (vs, t) -> showParen p (("\\"++) . (unwords (reverse vs)++) . (". "++) . go False t)
--   go p (RPi v a b) = showParen p (arg . (" -> "++) . go False b)
--     where arg = if v /= "_" then showParen True ((v++) . (" : "++) . go False a)
--                               else go True a
--   go p RStar = ('*':)

-- instance Show Raw where
--   showsPrec = prettyRaw

-- instance IsString Raw where
--   fromString = RVar

-- --------------------------------------------------------------------------------

-- pi            = RPi
-- lam           = RLam
-- star          = RStar
-- tlam a b      = pi a star b
-- ($$)          = RApp
-- h             = RHole
-- make v t e e' = RLet v e t e'

-- infixl 9 $$

-- (==>) a b = pi "_" a b
-- infixr 8 ==>

-- test =
--   make "id" (pi "a" star $ "a" ==> "a")
--   (lam "a" $ lam "x" "x") $

--   make "const" (pi "a" h $ pi "b" h $ "a" ==> "b" ==> "a")
--   (lam "a" $ lam "b" $ lam "x" $ lam "y" $ "x") $

--   make "Nat" star
--   (pi "n" h $ ("n" ==> "n") ==> "n" ==> "n") $

--   make "z" "Nat"
--   (lam "n" $ lam "s" $ lam "z" "z") $

--   make "s" ("Nat" ==> "Nat")
--   (lam "a" $ lam "n" $ lam "s" $ lam "z" $ "s" $$ ("a" $$ "n" $$ "s" $$ "z")) $

--   make "add" ("Nat" ==> "Nat" ==> "Nat")
--   (lam "a" $ lam "b" $ lam "n" $ lam "s" $ lam "z" $
--    "a" $$ "n" $$ "s" $$ ("b" $$ "n" $$ "s" $$ "z")) $

--   make "mul" ("Nat" ==> "Nat" ==> "Nat")
--   (lam "a" $ lam "b" $ lam "n" $ lam "s" $ lam "z" $
--    "a" $$ "n" $$ ("b" $$ "n" $$ "s") $$ "z") $
  
--   make "one"     "Nat" ("s" $$ "z") $
--   make "two"     "Nat" ("s" $$ "one") $
--   make "five"    "Nat" ("s" $$ ("add" $$ "two" $$ "two")) $
--   make "ten"     "Nat" ("add" $$ "five" $$ "five") $
--   make "hundred" "Nat" ("mul" $$ "ten" $$ "ten") $

--   make "comp"
--        (pi "a" h $ pi "b" h $ pi "c" h $
--        ("b" ==> "c") ==> ("a" ==> "b") ==> "a" ==> "c")
--   (lam "a" $ lam "b" $ lam "c" $ lam "f" $ lam "g" $ lam "x" $
--     "f" $$ ("g" $$ "x")) $

--   make "ap"
--     (pi "a" h $
--      pi "b" ("a" ==> star) $
--      pi "f" (pi "x" h $ "b" $$ "x") $
--      pi "x" h $ "b" $$ "x")
--   (lam "a" $ lam "b" $ lam "f" $ lam "x" $ "f" $$ "x") $

--   make "dcomp"
--     (pi "A" h $
--      pi "B" ("A" ==> h) $
--      pi "C" (pi "a" h $ "B" $$ "a" ==> star) $
--      pi "f" (pi "a" h $ pi "b" h $ "C" $$ "a" $$ "b") $
--      pi "g" (pi "a" h $ "B" $$ "a") $
--      pi "a" h $
--      "C" $$ h $$ ("g" $$ "a"))
--     (lam "A" $ lam "B" $ lam "C" $
--      lam "f" $ lam "g" $ lam "a" $ "f" $$ h $$ ("g" $$ "a")) $

--   make "Eq" (pi "A" star $ "A" ==> "A" ==> star)
--   (lam "A" $ lam "x" $ lam "y" $ pi "P" ("A" ==> star) $ ("P" $$ "x") ==> ("P" $$ "y")) $

--   make "refl" (pi "A" star $ pi "x" "A" $ "Eq" $$ "A" $$ "x" $$ "x")
--   (lam "A" $ lam "x" $ lam "P" $ lam "px" "px") $

--   make "Bool" star
--   (pi "B" h $ "B" ==> "B" ==> "B") $

--   make "true" "Bool"
--   (lam "B" $ lam "t" $ lam "f" "t") $

--   make "false" "Bool"
--   (lam "B" $ lam "t" $ lam "f" "f") $

--   make "foo" ("Eq" $$ h $$ "true" $$ "true")
--   ("refl" $$ h $$ h) $

--   "mul" $$ "hundred" $$ "hundred"

-- test2 =

--   make "id" (pi "a" star $ "a" ==> "a")
--   (lam "a" $ lam "x" "x") $

--   make "id2" (pi "a" star $ "a" ==> "a")
--   (lam "a" $
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$
--     ("id" $$ h) $$    
--     ("id" $$ h)    
--   ) $ 
--   "id"

-}
