
{-# language
  PatternSynonyms, BangPatterns, MagicHash, PatternGuards,
  DataKinds, LambdaCase, ViewPatterns, TupleSections,
  TypeFamilies, GADTs, EmptyCase, OverloadedStrings #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

module MetavarLet where

import Prelude hiding (pi)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM

import Control.Arrow
import Control.Exception
import Data.Function
import Data.List
import Data.String

import Control.Monad
import Control.Monad.Primitive
import Data.IORef

import Debug.Trace

{- Concept:
  Based onMetavarNoEta3, but we have Let. This requires a value env for
  type checking. 

  Metavars don't have substitution or context type, they simply have
  closed (iterated Pi) types.

  Type errors simply throw IO exceptions. In the future we will have even erroneous
  terms fully elaborated, except that ill-typed terms are converted into guarded
  constants. This way we can neatly gather all type errors for reporting, and
  can also support deferred type errors.

-}

{-

  OPEN questions:

  - fastest and simplest elimination is something like LambdaCase, similarly to
    Agda and miniTT.

  - should we have n-ary pattern lambda like Agda? And elaborate patterns into optimized
    case trees? (probably yes).

  - how to do "with pattern" or smart case:

    - translate to separate definition as in Agda/Idris?
      - but try to do it a more performant way than in Agda, maybe with
        slightly more annotation required from programmers?

    - have a smart case primitive?

  - When to unfold fixpoints or reclets

    - Unfolding only terminates when it's applied to all structurally rec. args

      - only unfold fully applied reclets?
        - but we can have meaningful partial application
        - specify decreasing argument

      - always unfold reclets when the topmost \case reduces with an argument
        - but then we have to make

    - One thing's for sure: we never want to unfold a reclet into a neutral
      \case. We only unfold if the \case can be applied to smth and thus disappears.

  - efficient renaming of values
    - Krikpe closures / function space with renaming?

  - best way to glue?
    - can we only store term environments in term closures

  - Sharing-preserving renaming/sub: check if subexpressions unchanged
    with ptrEquality

-}


-- Syntax
--------------------------------------------------------------------------------

type Name   = String
type Meta   = Int
type Gen    = Int
type Sub    = [(Name, Val)]
type Cxt    = Sub
type Ren    = HashMap (Either Name Gen) Name
type Type   = Val
data MEntry = MEntry {_mty :: Type, _solution :: !(Maybe Val)}
type MCxt   = IntMap MEntry
type M      = IO

data Raw
  = RVar !Name
  | RLet !Name !Raw !Raw !Raw
  | RApp !Raw !Raw
  | RLam !Name !Raw
  | RPi !Name !Raw !Raw
  | RStar
  | RHole

data Head
  = VMeta !Meta
  | VVar !Name
  | VGen !Gen

data Val
  = !Head :$ !Sub
  | VLam !Name !(Val -> Val)
  | VPi !Name !Val !(Val -> Val)
  | VStar
infix 3 :$

data Tm
  = Var !Name
  | Let !Name !Tm !Tm !Tm
  | Gen !Gen
  | App !Tm !Tm !Name
  | Lam !Name !Tm
  | Pi !Name !Tm !Tm
  | Star
  | Meta !Meta


-- Our nice global state, reset before use please
--------------------------------------------------------------------------------

{-# noinline mcxt #-}
mcxt :: IORef MCxt
mcxt = unsafeInlineIO (newIORef mempty)

{-# noinline freshMeta #-}
freshMeta :: IORef Int
freshMeta = unsafeInlineIO (newIORef 0)

reset :: IO ()
reset = do
  writeIORef mcxt mempty
  writeIORef freshMeta 0

lookupMeta :: Meta -> MEntry
lookupMeta m = unsafeInlineIO $ ((IM.! m) <$> readIORef mcxt)

-- Evaluation (modulo global mcxt)
--------------------------------------------------------------------------------

inst :: Meta -> Maybe Val
inst = _solution . lookupMeta

vapp :: Val -> Val -> Name -> Val
vapp t a v = case t of
  VLam v t -> t a 
  h :$ sp  -> h :$ ((v, a) : sp)
  _        -> error "vapp: impossible"      

eval :: Sub -> Tm -> Val
eval vs = \case
  Var v         -> maybe (VVar v :$ []) refresh (lookup v vs)
  Let v e' ty e -> eval ((v, eval vs e'):vs) e
  App f a v     -> vapp (eval vs f) (eval vs a) v
  Lam v t       -> VLam v $ \a -> eval ((v, a):vs) t
  Pi v a b      -> VPi v (eval vs a) $ \a -> eval ((v, a):vs) b
  Star          -> VStar
  Meta i        -> maybe (VMeta i :$ []) refresh (inst i)                   
  Gen{}         -> error "eval: impossible"

refresh :: Val -> Val
refresh = \case
  VMeta i :$ sp | Just t <- inst i -> refresh (foldr (\(v, a) t -> vapp t a v) t sp)
  t -> t

quote :: Val -> Tm
quote = go where
  goHead = \case
    VMeta i -> Meta i
    VVar v  -> Var v
    VGen i  -> Gen i
  go t = case refresh t of
    h :$ sp   -> foldr (\(v, a) t -> App t (go a) v) (goHead h) sp    
    VLam v t  -> Lam v (go (t (VVar v :$ [])))
    VPi v a b -> Pi v (go a) (go (b (VVar v :$ [])))
    VStar     -> Star  

-- Unification
--------------------------------------------------------------------------------

invert :: Sub -> M Ren
invert = foldM go HM.empty where
  go r (v, t) = case t of
    VVar v' :$ [] | HM.member (Left v') r -> pure $ HM.delete (Left v') r
                  | otherwise             -> pure $ HM.insert (Left v') v r
    VGen i  :$ [] | HM.member (Right i) r -> pure $ HM.delete (Right i) r
                  | otherwise             -> pure $ HM.insert (Right i) v r
    _ -> error "inversion"

renameRhs :: Meta -> Ren -> Tm -> M Tm
renameRhs occur r = go r where
  go :: Ren -> Tm -> M Tm
  go r = \case
    Var v         -> maybe (error "scope") (pure . Var) (HM.lookup (Left v) r)
    Gen i         -> maybe (error "scope") (pure . Var) (HM.lookup (Right i) r)
    Let v e' ty e -> Let v <$> go r e' <*> go r ty <*> go r e
    App f a v     -> App <$> go r f <*> go r a <*> pure v
    Lam v t       -> Lam v <$> go (HM.insert (Left v) v r) t
    Pi v a b      -> Pi v <$> go r a <*> go (HM.insert (Left v) v r) b
    Star          -> pure Star
    Meta i | i == occur -> error "occurs"
           | otherwise  -> pure $ Meta i

addLams :: Sub -> Tm -> Tm
addLams sp t = foldl (\t (v, _) -> Lam v t) t sp

solveMeta :: Meta -> Sub -> Val -> M ()
solveMeta m sp t = do
  ren <- invert sp
  t   <- addLams sp <$> renameRhs m ren (quote t)
  modifyIORef' mcxt $ IM.adjust (\e -> e {_solution = Just $ eval [] t}) m

unify :: Val -> Val -> M ()
unify t t' = go 0 t t' where

  go :: Int -> Val -> Val -> M ()
  go !g t t' = case (refresh t, refresh t') of
    (VStar, VStar) -> pure ()
    
    (VLam v t, VLam v' t') -> do
      let gen = VGen g :$ []
      go (g + 1) (t gen) (t' gen)
      
    (VPi v a b, VPi v' a' b') -> do
      go g a a'
      let gen = VGen g :$ []
      go (g + 1) (b gen) (b' gen)      
    
    (VVar v  :$ sp, VVar v'  :$ sp') | v == v' -> goSub g sp sp'
    (VGen i  :$ sp, VGen i'  :$ sp') | i == i' -> goSub g sp sp'
    (VMeta i :$ sp, VMeta i' :$ sp') | i == i' -> goSub g sp sp'
    (VMeta i :$ sp, t              ) -> solveMeta i sp t
    (t,             VMeta i  :$ sp ) -> solveMeta i sp t
    
    (t, t') ->
      error $ "can't unify\n" ++ show (quote t) ++ "\nwith\n" ++  show (quote t')

  goSub :: Int -> Sub -> Sub -> M ()
  goSub g ((_, a):as) ((_, b):bs) = goSub g as bs >> go g a b
  goSub g []          []          = pure ()
  goSub _ _           _           = error "unify Sp: impossible"

-- Elaboration
--------------------------------------------------------------------------------

ext :: (Name, Type) -> Cxt -> Cxt
ext x cxt = x : deleteBy ((==) `on` fst) x cxt

addPis :: Sub -> Tm -> Tm
addPis sp t = foldl (\t (v, a) -> Pi v (quote a) t) t sp

newMeta :: Cxt -> Type -> M Tm
newMeta cxt ty = do  
  m <- readIORef freshMeta
  writeIORef freshMeta (m + 1)
  
  let ty' = eval [] $ addPis cxt (quote ty)
      t   = foldr (\(v, _) t -> App t (Var v) v) (Meta m) cxt
      
  modifyIORef' mcxt $ IM.insert m (MEntry ty' Nothing)
  pure t

check :: Cxt -> Sub -> Raw -> Type -> M Tm
check cxt vs t want = case (t, want) of
  (RLam v t, VPi _ a b) -> do
    Lam v <$> check (ext (v, a) cxt) vs t (b (VVar v :$ []))
  (RHole, _) ->
    newMeta cxt want
  (t, _) -> do
    (t, has) <- infer cxt vs t
    t <$ unify has want

infer :: Cxt -> Sub -> Raw -> M (Tm, Type)
infer cxt vs = \case
  RVar v ->
    maybe (error $ "Variable: " ++ v ++ " not in scope")
          (\ty -> pure (Var v, ty))
          (lookup v cxt)
  RStar     -> pure (Star, VStar)
  RPi v a b -> do
    a <- check cxt vs a VStar
    let a' = eval vs a
    b <- check (ext (v, a') cxt) vs b VStar
    pure (Pi v a b, VStar)
  RApp f a -> do
    (f, tf) <- infer cxt vs f
    case tf of
      VPi v ta tb -> do
        a <- check cxt vs a ta
        pure (App f a v, tb (eval vs a))
      _ -> error "can't apply non-function"
  RLet v e1 t e2 -> do
    t <- check cxt vs t VStar
    let t' = eval vs t
    e1 <- check cxt vs e1 t'
    let e1' = eval vs e1
    (e2, te2) <- infer (ext (v, t') cxt) ((v, e1'):vs) e2
    pure (Let v e1 t e2, te2)
  RLam v t -> do
    error $ "can't infer type for lambda: " ++ show (RLam v t)
  RHole -> error "can't infer type for hole"

zonk :: Sub -> Tm -> Tm
zonk vs = \case
  Var v        -> Var v
  Meta v       -> maybe (Meta v) quote (inst v)  
  Star         -> Star
  Pi v a b     -> Pi v (zonk vs a) (zonk vs b)
  App f a v    -> undefined
  Lam v t      -> Lam v (zonk vs t)
  Let v e t e' -> Let v (zonk vs e) (zonk vs t) (zonk ((v, eval vs e):vs) e')    
  _            -> error "zonk: impossible Gen"


--------------------------------------------------------------------------------

infer0 :: Raw -> M Tm
infer0 r = quote . snd <$> (reset *> infer [] [] r)

elab0 :: Raw -> M Tm
elab0 r = fst <$> (reset *> infer [] [] r)

zonk0 :: Raw -> M Tm
zonk0 r = zonk [] . fst <$> (reset *> infer [] [] r)

nf0 :: Raw -> M Tm
nf0 r = quote . eval [] . fst <$> (reset *> infer [] [] r)

-- Printing
--------------------------------------------------------------------------------

prettyTm :: Int -> Tm -> ShowS
prettyTm prec = go (prec /= 0) where

  unwords' :: [ShowS] -> ShowS
  unwords' = foldr1 (\x acc -> x . (' ':) . acc)

  spine :: Tm -> Tm -> [Tm]
  spine f x = go f [x] where
    go (App f y _) args = go f (y : args)
    go t           args = t:args

  lams :: String -> Tm -> ([String], Tm)
  lams v t = go [v] t where
    go vs (Lam v t) = go (v:vs) t
    go vs t         = (vs, t)

  go :: Bool -> Tm -> ShowS
  go p (Var v)        = (v++)
  go p (Let v e t e') =
    (v++) . (" : "++) . go False t . ("\n"++) .
    (v++) . (" = "++) . go False e . ("\n\n"++) .
    go False e'
  go p (Meta v)       = showParen p (("?"++).(show v++))
  go p (App f x _)    = showParen p (unwords' $ map (go True) (spine f x))
  go p (Lam v t)      = case lams v t of
    (vs, t) -> showParen p (("\\"++) . (unwords (reverse vs)++) . (". "++) . go False t)
  go p (Pi v a b) = showParen p (arg . (" -> "++) . go False b)
    where arg = if v /= "_" then showParen True ((v++) . (" : "++) . go False a)
                              else go True a
  go p Star = ('*':)
  go _ _    = error "prettyTm"

instance Show Tm where
  showsPrec = prettyTm

instance IsString Tm where
  fromString = Var

-- --------------------------------------------------------------------------------

prettyRaw :: Int -> Raw -> ShowS
prettyRaw prec = go (prec /= 0) where

  unwords' :: [ShowS] -> ShowS
  unwords' = foldr1 (\x acc -> x . (' ':) . acc)

  spine :: Raw -> Raw -> [Raw]
  spine f x = go f [x] where
    go (RApp f y) args = go f (y : args)
    go t          args = t:args

  lams :: String -> Raw -> ([String], Raw)
  lams v t = go [v] t where
    go vs (RLam v t) = go (v:vs) t
    go vs t          = (vs, t)

  go :: Bool -> Raw -> ShowS
  go p (RVar v)        = (v++)
  go p (RLet v e t e') =
    (v++) . (" : "++) . go False t . ("\n"++) .
    (v++) . (" = "++) . go False e . ("\n\n"++) .
    go False e'
  go p RHole           = ('_':)
  go p (RApp f x)      = showParen p (unwords' $ map (go True) (spine f x))
  go p (RLam v t)      = case lams v t of
    (vs, t) -> showParen p (("\\"++) . (unwords (reverse vs)++) . (". "++) . go False t)
  go p (RPi v a b) = showParen p (arg . (" -> "++) . go False b)
    where arg = if v /= "_" then showParen True ((v++) . (" : "++) . go False a)
                              else go True a
  go p RStar = ('*':)

instance Show Raw where
  showsPrec = prettyRaw

instance IsString Raw where
  fromString = RVar

--------------------------------------------------------------------------------

pi            = RPi
lam           = RLam
star          = RStar
tlam a b      = pi a star b
($$)          = RApp
h             = RHole
make v t e e' = RLet v e t e'

infixl 9 $$

(==>) a b = pi "_" a b
infixr 8 ==>

test =
  -- make "id" (pi "a" h $ "a" ==> "a")
  -- (lam "a" $ lam "x" "x") $

  -- make "const" (pi "a" h $ pi "b" h $ "a" ==> "b" ==> "a")
  -- (lam "a" $ lam "b" $ lam "x" $ lam "y" $ "x") $

  -- make "Nat" star
  -- (pi "n" h $ ("n" ==> "n") ==> "n" ==> "n") $

  -- make "z" "Nat"
  -- (lam "n" $ lam "s" $ lam "z" "z") $

  -- make "s" ("Nat" ==> "Nat")
  -- (lam "a" $ lam "n" $ lam "s" $ lam "z" $ "s" $$ ("a" $$ "n" $$ "s" $$ "z")) $

  -- make "add" ("Nat" ==> "Nat" ==> "Nat")
  -- (lam "a" $ lam "b" $ lam "n" $ lam "s" $ lam "z" $
  --  "a" $$ "n" $$ "s" $$ ("b" $$ "n" $$ "s" $$ "z")) $

  -- make "mul" ("Nat" ==> "Nat" ==> "Nat")
  -- (lam "a" $ lam "b" $ lam "n" $ lam "s" $ lam "z" $
  --  "a" $$ "n" $$ ("b" $$ "n" $$ "s") $$ "z") $
  
  -- make "one"     "Nat" ("s" $$ "z") $
  -- make "two"     "Nat" ("s" $$ "one") $
  -- make "five"    "Nat" ("s" $$ ("add" $$ "two" $$ "two")) $
  -- make "ten"     "Nat" ("add" $$ "five" $$ "five") $
  -- make "hundred" "Nat" ("mul" $$ "ten" $$ "ten") $

  make "ap"
    (pi "a" h $
     pi "b" ("a" ==> star) $
     pi "f" (pi "x" h $ "b" $$ "x") $
     pi "x" h $ "b" $$ "x")

  (lam "a" $ lam "b" $ lam "f" $ lam "x" $ "f" $$ "x") $

  "ap"


-- const' =
--   ann (pi "a" star $ pi "b" star $ "a" ==> "b" ==> "a") $
--   lam "a" $ lam "b" $ lam "x" $ lam "y" $ "x"

-- compose =
--   ann (tlam "a" $ tlam "b" $ tlam "c" $
--        ("b" ==> "c") ==> ("a" ==> "b") ==> "a" ==> "c") $
--   lam "a" $ lam "b" $ lam "c" $
--   lam "f" $ lam "g" $ lam "x" $
--   "f" $$ ("g" $$ "x")

-- test =
--   ann
--   -- type declarations
--   (pi "id"    (tlam "a" $ "a" ==> "a") $
--    star
--   )
--   -- program
--   (lam "id" $
--    "id" $$ h $$ star
--   )
--   -- declaration definitions
--   $$ (lam "a" $ lam "x" $ "x")

-- test2 =
--   ann
--   (
--   pi "f" (tlam "a" $ tlam "b" $ "a" ==> "b") $
--   star
--   )(
--   lam "f" $
--   "f" $$ h $$ h $$ "f"
--   )

-- test3 =
--   ann
--   (
--   pi "id" (tlam "a" $ "a" ==> "a") $
--   pi "f" h $
--   h
--   )(
--   lam "id" $
--   lam "f" $
--   "id" $$ h $$ "id"
--   )

--   $$ (lam "a" $ lam "x" "x")

-- -- "Substitution for metavariable is not a renaming" : actually correct error!
-- test4 =
--   ann
--   (
--   pi "x" h $
--   pi "y" h $ -- would have to solve "?1 [*] = *", which isn't pattern!
--   h          -- it would work with explicit non-dependent function space
--   )(         -- can we add that since * : * and we're parametric, ?1 = \_ -> *
--   lam "x" $  -- in other words, types are irrelevant.
--   lam "y" $  -- anyway, we'd need the type-directed unif version for this
--   star
--   )
--   $$ star
--   $$ star

-- test5 =
--   ann
--   (
--   pi "a" star $
--   pi "b" star $
--   pi "f" ("a" ==> "b") $
--   pi "x" "a" $
--   pi "ap" (pi "a" h $ pi "b" ("a" ==> h) $ pi "f" (pi "x" h $ "b" $$ "x") $ pi "x" h $ "b" $$ "x") $
--   h
--   )(
--   lam "a" $
--   lam "b" $
--   lam "f" $
--   lam "x" $
--   lam "ap" $
--   "ap" $$ h $$ h $$ "f" $$ "x"
--   )

-- test6 = (pi "a" h $ pi "b" ("a" ==> h) $ pi "f" (pi "x" h $ "b" $$ "x") $ pi "x" h $ "b" $$ "x")

-- test7 =
--   ann
--   (
--     pi "a" h $
--     pi "f" ("a" ==> "a") $
--     "a"
--   )
--   (
--     lam "a" $
--     lam "f" $
--     (lam "x" $ "f" $$ ("x" $$ "x")) $$ (lam "x" $ "f" $$ ("x" $$ "x"))
--   )

-- test8 =
--   ann
--   (
--   pi "ap" (pi "a" h $ pi "b" ("a" ==> h) $ pi "f" (pi "x" h $ "b" $$ "x") $ pi "x" h $ "b" $$ "x") $
--   pi "a" h $
--   pi "b" ("a" ==> h) $
--   pi "f" (pi "x" h $ "b" $$ "x") $
--   pi "x" "a" $
--   h
--   )(
--   lam "ap" $
--   lam "a" $
--   lam "b" $
--   lam "f" $
--   lam "x" $
--   "ap" $$ h $$ h $$ "f" $$ "x"
--   )

-- test9 =
--   ann
--   (
--   pi "ap" (pi "a" h $ pi "b" ("a" ==> h) $ pi "f" (pi "x" h $ "b" $$ "x") $ pi "x" h $ "b" $$ "x") $
--   pi "a" h $
--   pi "b" ("a" ==> h) $
--   pi "f" (pi "x" h $ "b" $$ "x") $
--   pi "x" "a" $
--   h
--   )(
--   lam "ap" $
--   lam "a" $
--   lam "b" $
--   lam "f" $
--   lam "x" $
--   "ap" $$ h $$ h $$ "f" $$ "x"
--   )

-- test10 =
--   let' "id" (tlam "a" $ "a" ==> "a")
--             (lam "a" $ lam "x" "x") $
--   let' "const" (tlam "a" $ tlam "b" $ "a" ==> "b" ==> "a")
--                (lam "a" $ lam "b" $ lam "x" $ lam "y" "x") $
--   let' "const'" (tlam "a" $ "a" ==> (tlam "b" $ "b" ==> "a"))
--                 (lam "a" $ lam "x" $ lam "b" $ lam "y" "x") $
--   "const'" $$ h $$ "id"

-- -- can't depend on value of nat, need true "let"
-- test11 =
--   let' "Nat" star
--              (tlam "n" $ ("n" ==> "n") ==> "n") $
--   let' "z" "Nat"
--            (lam "n" $ lam "s" $ lam "z" "z") $
--   "Nat"

-- test12 =
--   ann 
--     (pi "A" star $
--      pi "B" ("A" ==> star) $
--      pi "C" (pi "a" h $ "B" $$ "a" ==> star) $
--      pi "f" (pi "a" h $ pi "b" h $ "C" $$ "a" $$ "b") $
--      pi "g" (pi "a" h $ "B" $$ "a") $
--      pi "a" h $
--      "C" $$ h $$ ("g" $$ "a"))
--     (lam "A" $ lam "B" $ lam "C" $
--      lam "f" $ lam "g" $ lam "a" $ "f" $$ h $$ ("g" $$ "a"))

-- -- Raw:
-- -- comp :
-- --     (A : *)
-- --  -> (B : A -> *)
-- --  -> (C : (a : _) -> (B a) -> *)
-- --  -> (f : (a : _) -> (b : _) -> C a b)
-- --  -> (g : (a : _) -> B a)
-- --  -> (a : _) -> C _ (g a)         
-- -- comp = \A B C f g a. f _ (g a)

-- -- Elaborated:
-- -- comp :
-- --     (A : *)
-- --  -> (B : A -> *)
-- --  -> (C : (a : ?0 [B,A]) -> (B a) -> *)
-- --  -> (f : (a : ?1 [C,B,A]) -> (b : ?2 [a,C,B,A]) -> C a b)
-- --  -> (g : (a : ?3 [f,C,B,A]) -> B a)
-- --  -> (a : ?4 [g,f,C,B,A]) -> C (?5 [a,g,f,C,B,A]) (g a)
-- -- comp = \A B C f g a. f (?6 [a,g,f,C,B,A]) (g a)

-- -- Zonked
-- -- comp:
-- --      (A : *)
-- --   -> (B : A -> *)
-- --   -> (C : (a : A) -> (B a) -> *)
-- --   -> (f : (a : A) -> (b : B a) -> C a b)
-- --   -> (g : (a : A) -> B a)
-- --   -> (a : A) -> C a (g a)
-- -- comp = \A B C f g a. f a (g a) 



