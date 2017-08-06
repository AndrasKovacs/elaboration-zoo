
{-# language BangPatterns, MagicHash, LambdaCase, Strict, CPP #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

module MetavarLet where

import Prelude hiding (pi)
import Data.Hashable
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
import Control.Arrow

import Debug.Trace

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
  | RNoInsert Raw
  | RHole

data Tm
  = Var Name
  | Gen Gen
  | Let Name Tm Tm Tm
  | App Tm Tm Name Icit
  | Lam Name Icit Tm
  | Pi Name Icit Tm Tm
  | Star
  | Meta Meta

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
  Var x         -> maybe (VVar x :$ []) refresh (maybe (error x) id $ lookup x vs)
  Let x e' ty e -> eval ((x, Just (eval vs e')):vs) e
  App f a x i   -> vapp (eval vs f) (eval vs a) x i
  Lam x i t     -> VLam x i $ \a -> eval ((x, Just a):vs) t
  Pi x i a b    -> VPi x i (eval vs a) $ \a -> eval ((x, Just a):vs) b
  Gen g         -> VGen g :$ []
  Star          -> VStar
  Meta i        -> maybe (VMeta i :$ []) refresh (inst i)

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
    Var x         -> maybe (error $ show ("scope", x, r)) Var (HM.lookup (Left x) r)
    Let x e' ty e -> Let x (go r e') (go r ty) (go r e)
    App f a x i   -> App  (go r f) (go r a) x i
    Lam x i t     -> Lam x i (go (HM.insert (Left x) x r) t)
    Gen g         -> maybe (error $ show ("scope", g, r)) Var (HM.lookup (Right g) r)
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

hashNub :: (Eq a, Hashable a) => [a] -> [a]
hashNub = snd . foldr go (HS.empty, []) where
  go a (!seen, !as) | HS.member a seen = (seen, as)
  go a (seen, as) = (HS.insert a seen, a:as)

newMeta :: Cxt -> IO Tm
newMeta cxt = do
  m <- readIORef freshMeta
  writeIORef freshMeta (m + 1)
  let bvars = hashNub [x | (x, Left{}) <- cxt]

  pure $ foldr (\x t -> App t (Var x) x Expl) (Meta m) bvars

check :: Cxt -> Env -> Raw -> Ty -> IO Tm
check cxt vs t want = case (t, want) of
  (RLam x i t, VPi _ i' a b) | i == i' ->
    Lam x i <$> check ((x, Left a): cxt) ((x, Nothing):vs) t (b (VVar x :$ []))

  (t, VPi x Impl a b) -> do
    let x' = if freeInRaw x t then x ++ show (length cxt) else x
    t <- check ((x', Left a): cxt) ((x', Nothing):vs) t (b (VVar x' :$ []))
    pure $ Lam x' Impl t

  (RLet x e1 t e2, _) -> do
    t <- check cxt vs t VStar
    let ~t' = eval vs t
    e1 <- check cxt vs e1 t'
    let ~e1' = eval vs e1
    e2 <- check ((x, Right t'): cxt) ((x, Just e1'):vs) e2 want
    pure (Let x e1 t e2)

  (RHole, _) ->
    newMeta cxt

  (t, _) -> do
    (t, has) <- infer cxt vs t
    t <$ unify has want

insertMetas :: Cxt -> Env -> (Tm, Ty) -> IO (Tm, Ty)
insertMetas cxt vs (t, ty) = case ty of
  VPi x Impl a b -> do
    m <- newMeta cxt
    insertMetas cxt vs (App t m x Impl, b (eval vs m))
  _ -> pure (t, ty)

infer :: Cxt -> Env -> Raw -> IO (Tm, Ty)
infer cxt vs = \case
  RNoInsert t -> infer' cxt vs t
  t -> insertMetas cxt vs =<< infer' cxt vs t

infer' :: Cxt -> Env -> Raw -> IO (Tm, Ty)
infer' cxt vs = \case
  RStar ->
    pure (Star, VStar)

  RNoInsert t ->
    infer' cxt vs t

  RVar x -> do
    maybe
      (error $ "Variable: " ++ x ++ " not in scope")
      (\ty -> pure (Var x, either id id ty))
      (lookup x cxt)

  RApp f a i -> do
    (f, ty) <- case i of
      Expl -> infer cxt vs f
      Impl -> infer' cxt vs f
    case ty of
      VPi x i' ta tb -> do
        matchIcit i i'
        a <- check cxt vs a ta
        pure (App f a x i', tb (eval vs a))
      _ -> error "expected a function"

  RPi x i a b -> do
    a <- check cxt vs a VStar
    let ~a' = eval vs a
    b <- check ((x, Left a'): cxt) ((x, Nothing):vs) b VStar
    pure (Pi x i a b, VStar)

  RLet x e1 t e2 -> do
    t <- check cxt vs t VStar
    let ~t' = eval vs t
    e1 <- check cxt vs e1 t'
    let ~e1' = eval vs e1
    (e2, ~te2) <- infer' ((x, Right t'): cxt) ((x, Just e1'):vs) e2
    pure (Let x e1 t e2, te2)

  RLam x i t -> do
    ~ma <- eval vs <$> newMeta cxt
    (t, ty) <- infer ((x, Left ma):cxt) ((x, Nothing):vs) t
    pure (Lam x i t, VPi x i ma (\a -> eval ((x, Just a):vs) (quote ty)))

  RHole -> do
    m1 <- newMeta cxt
    m2 <- newMeta cxt
    pure (m1, eval vs m2)

--------------------------------------------------------------------------------

tmSpine :: Tm -> (Tm, Sub (Tm, Icit))
tmSpine = \case
  App f a x i -> ((x, (a, i)):) <$> tmSpine f
  t           -> (t, [])

zonkSp :: Env -> Val -> Sub (Tm, Icit) -> Tm
zonkSp env v sp = either id quote $
  foldr
    (\(x, (a, i)) -> either
      (\t -> Left (App t a x i))
      (\case VLam _ _ t -> Right (t (eval env a))
             v          -> Left (App (quote v) a x i)))
    (Right v) sp

zonk :: Env -> Tm -> Tm
zonk env t = case t of
  Var x        -> Var x
  Meta m       -> maybe (Meta m) quote (inst m)
  Star         -> Star
  Pi x i a b   -> Pi x i (zonk env a) (zonk ((x, Nothing):env) b)
  App f a x i  -> let (h, sp) = tmSpine (App f a x i)
                  in case h of
                       Meta m | Just v <- inst m ->
                         zonkSp env v sp
                       _ -> foldr (\(x, (t, i)) f -> App f (zonk env t) x i) h sp
  Lam x i t    -> Lam x i (zonk ((x, Nothing): env) t)
  Let x e t e' -> Let x (zonk env e) (zonk env t) (zonk ((x, Just (eval env e)) : env) e')
  Gen _        -> error "Impossible Gen"

--------------------------------------------------------------------------------

traceState :: a -> a
traceState a = unsafePerformIO $ do
  m <- readIORef mcxt
  i <- readIORef freshMeta
  print (quote <$> m, i)
  pure $! a

traceStateM :: Monad m => m ()
traceStateM = seq (traceState ()) (pure ())

infer0 :: Raw -> IO Tm
infer0 r = quote . snd <$> (reset *> infer' [] [] r)

elab0 :: Raw -> IO Tm
elab0 r = fst <$> (reset *> infer' [] [] r)

zonk0 :: Raw -> IO Tm
zonk0 r = zonk [] . fst <$> (reset *> infer' [] [] r)

nf0 :: Raw -> IO Tm
nf0 r = quote . eval [] . fst <$> (reset *> infer' [] [] r)

--------------------------------------------------------------------------------

freeInRaw :: Name -> Raw -> Bool
freeInRaw x = \case
  RVar x'         -> x == x'
  RApp f a i      -> freeInRaw x f || freeInRaw x a
  RLam x' i t     -> if x == x' then False else freeInRaw x t
  RPi x' i a b    -> freeInRaw x a || if x == x' then False else freeInRaw x b
  RLet x' t ty t' -> freeInRaw x t || freeInRaw x ty || if x == x' then False else freeInRaw x t'
  RNoInsert t     -> freeInRaw x t
  RStar           -> False
  RHole           -> False

freeIn :: Name -> Tm -> Bool
freeIn x = \case
  Var x'         -> x == x'
  App f a _ i    -> freeIn x f || freeIn x a
  Lam x' i t     -> if x == x' then False else freeIn x t
  Pi x' i a b    -> freeIn x a || if x == x' then False else freeIn x b
  Let x' t ty t' -> freeIn x t || freeIn x ty || if x == x' then False else freeIn x t'
  Gen _          -> error "Impossible Gen"
  Meta _         -> False
  Star           -> False

prettyTm :: Int -> Tm -> ShowS
prettyTm prec = go (prec /= 0) where

  unwords' :: [ShowS] -> ShowS
  unwords' = foldr1 (\x acc -> x . (' ':) . acc)

  lams :: (Name, Icit) -> Tm -> ([(Name, Icit)], Tm)
  lams xi t = go [xi] t where
    go xs (Lam x i t) = go ((x,i):xs) t
    go xs t           = (xs, t)

  bracket :: ShowS -> ShowS
  bracket s = ('{':).s.('}':)

  icit :: Icit -> a -> a -> a
  icit Impl i e = i
  icit Expl i e = e

  -- Note: printing is kinda slow (make tmSpine return in reverse, optimize App case)
  go :: Bool -> Tm -> ShowS
  go p = \case
    Var x -> (x++)
    t@App{} -> let (h, sp) = tmSpine t
      in showParen p $
         unwords' $
         go True h :
         reverse (map (\(_, (t, i)) -> icit i (bracket (go False t)) (go True t)) sp)

    Lam x i t -> case lams (x, i) t of
      (xis, t) -> showParen p (("λ "++) . params . (". "++) . go False t)
        where params = unwords' $ reverse $ map (\(x, i) -> icit i bracket id (x++)) xis

    Pi x i a b -> showParen p (arg . (" → "++) . go False b)
      where
        arg = if freeIn x b
                then (icit i bracket (showParen True)) ((x++) . (" : "++) . go False a)
                else go True a

    Let x t ty t' ->
      (x++) . (" : "++) . go False ty . ("\n"++) .
      (x++) . (" = "++) . go False t  . ("\n\n"++) .
      go False t'
    Star   -> ('*':)
    Meta m -> (("?"++).(show m++))
    Gen _  -> error "Impossible Gen"

instance IsString Tm where fromString = Var
instance Show Tm where showsPrec = prettyTm
deriving instance Show Raw
instance IsString Raw where fromString = RVar

--------------------------------------------------------------------------------

mkLam :: Name -> (Raw -> Raw) -> Raw
mkLam x f = RLam x Expl (f (RVar x))

mkPi :: Name -> Raw -> (Raw -> Raw) -> Raw
mkPi x a b = RPi x Expl a (b (RVar x))

mkiPi :: Name -> Raw -> (Raw -> Raw) -> Raw
mkiPi x a b = RPi x Impl a (b (RVar x))

mkiLam :: Name -> (Raw -> Raw) -> Raw
mkiLam x f = RLam x Impl (f (RVar x))

mkAll :: Name -> (Raw -> Raw) -> Raw
mkAll x b = RPi x Impl RHole (b (RVar x))

mkLet :: Name -> Raw -> Raw -> (Raw -> Raw) -> Raw
mkLet x t e e' = RLet x e t (e' (RVar x))

{-# inline mkLam #-}
{-# inline mkPi #-}
{-# inline mkiPi #-}
{-# inline mkiLam #-}
{-# inline mkAll #-}
{-# inline mkLet #-}

#define LAM(x) mkLam "x" $ \x ->
#define ILAM(x) mkiLam "x" $ \x ->
#define PI(x, a) mkPi "x" a $ \x ->
#define IPI(x, a) mkiPi "x" a $ \x ->
#define ALL(x) mkAll "x" $ \x ->
#define LET(x, t, e) mkLet "x" t e $ \x ->

star          = RStar
(∙) a b       = RApp a b Expl
(⊗) a b       = RApp a b Impl
h             = RHole
noIns         = RNoInsert
(==>) a b     = RPi "_" Expl a b

infixl 9 ∙
infixl 9 ⊗
infixr 8 ==>

test =
  LET(const, (ALL(a) ALL(b) a ==> b ==> a), (LAM(x) LAM(y) x))
  LET(the, (PI(a, star) a ==> a), (LAM(a) LAM(x) x))
  LET(id, (ALL(a) a ==> a), (LAM(x) x))
  LET(nat, star, (PI(n, star) (n ==> n) ==> n ==> n))
  LET(z, nat, (LAM(n) LAM(s) LAM(z) z))
  LET(five, nat, (LAM(n) LAM(s) LAM(z) s ∙ (s ∙ (s ∙ (s ∙ (s ∙ z))))))

  LET(s, (nat ==> nat), (LAM(a) LAM(n) LAM(s) LAM(z) s ∙ (a ∙ n ∙ s ∙ z)))
  LET(add, (nat ==> nat ==> nat), (LAM(a) LAM(b) LAM(n) LAM(s) LAM(z) a ∙ n ∙ s ∙ (b ∙ n ∙ s ∙ z)))
  LET(mul, (nat ==> nat ==> nat), (LAM(a) LAM(b) LAM(n) LAM(s) a ∙ n ∙ (b ∙ n ∙ s)))
  LET(ten, nat, (add ∙ five ∙ five))
  LET(hundred, nat, (mul ∙ ten ∙ ten))

  LET(eq, (ALL(a) a ==> a ==> star), (ILAM(a) LAM(x) LAM(y) PI(p, (a ==> star)) p ∙ x ==> p ∙ y))
  LET(refl, (ALL(a) PI(x, a) eq ∙ x ∙ x), (LAM(x) LAM(p) LAM(px) px))

  LET(trans,
      (ALL(a) ALL(x) ALL(y) ALL(z) eq ⊗ a ∙ x ∙ y ==> eq ∙ y ∙ z ==> eq ∙ x ∙ z),
      (LAM(xy) LAM(yz) LAM(p) LAM(px) yz ∙ p ∙ (xy ∙ p ∙ px)))

  LET(ap,
      (IPI(a, star) IPI(b, (a ==> star)) (PI(x, a) b ∙ x) ==> (PI(x, a) b ∙ x)),
      (LAM(f) LAM(x) f ∙ x))

  LET(foo,
      (PI(a, star) PI(x, a) (PI(p, (a ==> star)) p ∙ x) ==> (PI(p, (a ==> star)) p ∙ x)),
      (LAM(a) LAM(x) LAM(f) LAM(p) f ∙ p))

  refl ∙ noIns ap

