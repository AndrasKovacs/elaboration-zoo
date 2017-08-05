{-# language BangPatterns, MagicHash, LambdaCase, Strict, CPP #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

{-|

A small dependently typed language.

Features:
  - Inductive type families
  - Dependent pattern matching via splitting \case
    + With Axiom K
    + More flexible than in Gallina, less flexible than in Agda
  - Fixpoints
    + Structurally recursive in a single argument, unfolding as in Gallina
  - Implicit arguments
    + Higher-order unification
    + Controllable metavariable insertion
    + Named implicit arguments, named implicit application
  - Eta conversion check for functions, empty and unit types

Implementation:
  - Bidirectional elaboration
  - Pattern matching, case expression and usual lambdas all expressed with
    case splitting lambdas.
  - Mixed call-by-need/call-by-name environment machine evaluation
    + Purely call-by-need for meta-ground terms
  - Existing metas are frozen before elaborating each inductive data def.

Possible features:
  - Consistency:
    + Predicative universes
    + Termination check
    + Positivity check

Questions:
  - How to prevent metas being solved by later (out-of-scope) declared inductive types.
    + Before elaborating an inductive decl, freeze all existing metas.
      * Works but kind of crude, prevents many valid solutions.
    + Work out a more precise scoping system.

-}

module Inductive where

import Prelude hiding (pi)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM

import Control.Arrow
import Data.IORef
import Data.Hashable
import Data.List
import Data.Maybe
import Data.String
import System.IO.Unsafe

-- Syntax
--------------------------------------------------------------------------------

type Name        = String
type Meta        = Int
type Gen         = Int
type VTy         = Val
type Ty          = Tm

data Icit        = Impl | Expl
data LamBinder   = LBIcit Icit Name | LBNamed Name Name | LBUnused
data SplitInfo   = SIIcit Icit | SINamed Name
data AppType     = ATIcit Icit | ATNamed Name

type PiBinder    = (Name, Icit)
type AppInfo     = (Name, AppType)
data TypeEntry   = TENonTCon ~VTy | TETCon ~VTy
data Pattern     = PDefault Name | PCon Name [Name]

type Sub a       = [(Name, a)]
type Spine       = Sub (Val, AppType)
type Values      = Sub (Maybe Val)
type Types       = Sub TypeEntry
data MetaEntry   = MESolved Val | MEFrozen | MEUnsolved
type Metas       = IntMap MetaEntry

data Raw
  = RSym Name
  | RLet Name Raw Raw Raw
  | RApp Raw Raw AppInfo
  | RLam LamBinder Raw
  | RSplit SplitInfo [(Pattern, Raw)]
  | RFix Int Name Raw
  | RPi PiBinder Raw
  | RArrow
  | RStar
  | RStopInsert Raw
  | RHole

data RawDefinition
  = RDDefine Raw Raw
  | RDInductive Raw (Sub Raw)

type RawProg = Sub RawDefinition

--------------------------------------------------------------------------------

data Tm
  = Var Name
  | DCon Name
  | TCon Name
  | Let Name Ty Tm Tm
  | App Tm Tm AppInfo
  | Lam LamBinder Tm
  | Split SplitInfo [(Pattern, Tm)]
  | Fix Int Name Tm
  | Pi PiBinder Ty Tm
  | Arrow Ty Ty
  | Star
  | Meta Meta

data Definition
  = DDefine Ty Tm
  | DInductive Ty (Sub Ty)

type Prog = Sub Definition

--------------------------------------------------------------------------------

data Head
  = HMeta Meta
  | HVar Name
  | HDCon Name
  | HTCon Name
  | HGen Gen
  | HFix Int Name Values Tm
  | HSplit SplitInfo Values [(Pattern, Tm)]

data Val
  = VNeutral Head Spine
  | VLam LamBinder Values Tm
  | VPi PiBinder ~VTy Values Tm
  | VArrow ~VTy ~VTy
  | VStar

-- data Cases
--   = CDefault Name Tm
--   | CEmpty
--   | CCase Name [Name] Tm Cases

-- Metacontext
--------------------------------------------------------------------------------

{-# noinline mcxt #-}
mcxt ∷ IORef Metas
mcxt = unsafeDupablePerformIO (newIORef mempty)

{-# noinline freshMeta #-}
freshMeta ∷ IORef Meta
freshMeta = unsafeDupablePerformIO (newIORef 0)

reset ∷ IO ()
reset = do
  writeIORef mcxt mempty
  writeIORef freshMeta 0

inst ∷ Meta → Maybe Val
inst m = unsafeDupablePerformIO $ do
  entry ← (IM.! m) <$> readIORef mcxt
  pure $ case entry of
    MESolved t → Just t
    _          → Nothing

-- Evaluation
--------------------------------------------------------------------------------

-- | Invariant: we don't have split lambdas that are equivalent to single lambdas.
--   Those are converted to single lambdas elaboration time.
--   Actually, what we have is a non-empty list of constructor cases terminated by either
--   Nil or a default case. TODO: make this precise in types.

-- Note: only use split lambdas for everything?
evalSplitApp ∷ SplitInfo → Values → [(Pattern, Tm)] → AppInfo → Val → Val
evalSplitApp si vs cases ai@(x, i) u = case u of
  VNeutral (HDCon c) sp → select cases
    where
      addSp (x:xs) ((x', (a, i)):sp) = (x, Just a) : addSp xs sp
      addSp [] [] = vs
      addSp _  _  = error "evalSplit.addSp: impossible underapplied constructor"

      select ((PCon c' xs, t):cases)
        | c == c'   = eval (addSp xs sp) t
        | otherwise = select cases
      select ((PDefault x, t) : []) = eval ((x, Just u):vs) t
      select _ = error "evalSplit: impossible non-exhaustive case split"

  u → VNeutral (HSplit si vs cases) [(x, (u, i))]

vAppSpine ∷ Val → Spine → Val
vAppSpine = foldr (\(x, (a, i)) t → vApp t a (x, i))

vApp ∷ Val → Val → AppInfo → Val
vApp t ~u ai@(x, appType) = case t of
  VLam i vs t' → case i of
    LBIcit  _ x → eval ((x, Just u):vs) t'
    LBNamed _ x → eval ((x, Just u):vs) t'
    LBUnused    → eval vs t'
  VNeutral h@(HFix n x vs t') sp → case (n, u) of
    (0, VNeutral (HDCon _) _) → vAppSpine (eval ((x, Just (VNeutral h [])):vs) t') sp
    _ → VNeutral (HFix (n - 1) x vs t') ((x, (u, appType)) : sp)
  VNeutral (HSplit si vs cases) [] → evalSplitApp si vs cases ai u
  VNeutral h sp → VNeutral h ((x, (u, appType)) : sp)
  _ → error "vApp: impossible non-function argument"

eval ∷ Values → Tm → Val
eval vs = \case
  Var  x        → maybe (VNeutral (HVar x) []) refresh $ fromJust $ lookup x vs
  DCon x        → VNeutral (HDCon x) []
  TCon x        → VNeutral (HTCon x) []
  Split i cases → VNeutral (HSplit i vs cases) []
  Let x a t u   → eval ((x, Just (eval vs u)) : vs) t
  App t u i     → vApp (eval vs t) (eval vs u) i
  Lam i t       → VLam i vs t
  Fix n x t     → VNeutral (HFix n x vs t) []
  Pi i a b      → VPi i (eval vs a) vs b
  Arrow a b     → VArrow (eval vs a) (eval vs b)
  Meta m        → maybe (VNeutral (HMeta m) []) refresh $ inst m
  Star          → VStar

refresh ∷ Val → Val
refresh = \case
  VNeutral (HMeta m) sp | Just t ← inst m → vAppSpine t sp
  t → t

quote ∷ Val → Tm
quote = go . refresh where

  goNeu ∷ Tm → Spine → Tm
  goNeu = foldr (\(x, (u, i)) t → App t (go u) (x, i))

  goPat ∷ Values → (Pattern, Tm) → (Pattern, Tm)
  goPat vs (p, t) = case p of
    PCon x xs → (p, nf (map (,Nothing) xs ++ vs) t)
    PDefault x → (p, nf vs t)

  nf ∷ Values → Tm → Tm
  nf vs t = go (eval vs t)

  go ∷ Val → Tm
  go = \case
    VNeutral h sp → case h of
      HVar x            → goNeu (Var x)  sp
      HMeta m           → goNeu (Meta m) sp
      HDCon c           → goNeu (DCon c) sp
      HTCon c           → goNeu (TCon c) sp
      HFix n x vs t     → Fix n x (nf ((x, Nothing):vs) t)
      HSplit i vs cases → Split i (map (goPat vs) cases)
      HGen _            → error "quote: impossible generic variable"
    VLam i vs t → case i of
      LBIcit  _ x → Lam i (nf ((x, Nothing):vs) t)
      LBNamed _ x → Lam i (nf ((x, Nothing):vs) t)
      LBUnused    → Lam i (nf vs t)
    VPi (x, i) a vs b → Pi (x, i) (go a) (nf ((x, Nothing):vs) b)
    VArrow a b        → Arrow (go a) (go b)
    VStar             → Star

nf ∷ Values → Tm → Tm
nf vs t = quote (eval vs t)

--------------------------------------------------------------------------------



{-

eval :: Env -> Tm -> Val
eval vs = \case
  Var x         -> maybe (VVar x :$ []) refresh (maybe (error x) id $ lookup x vs)
  Let x e' ty e -> eval ((x, Just (eval vs e')):vs) e
  App f a x i   -> vapp (eval vs f) (eval vs a) x i
  Lam x i t     -> VLam x i $ \a -> eval ((x, Just a):vs) t
  Pi x i a b    -> VPi x i (eval vs a) $ \a -> eval ((x, Just a):vs) b
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
    VGen{}  -> error "quote: impossible VGen"
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
    Pi x i a b    -> Pi x i (go r a) (go (HM.insert (Left x) x r) b)
    Star          -> Star
    Meta i | i == occur -> error "occurs"
           | otherwise  -> Meta i

solve :: Meta -> Spine -> Val -> IO ()
solve m sp t = do
  -- print ("solve", m, map (second $ first quote) sp, quote t)
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

  -- print $ ("newMeta", m, map (second $ either quote quote) cxt)
  -- print bvars

  pure $ foldr (\x t -> App t (Var x) x Expl) (Meta m) bvars

check :: Cxt -> Env -> Raw -> Ty -> IO Tm
check cxt vs t want = case (t, want) of
  (RHole, _) ->
    newMeta cxt

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
      -- VMeta m :$ sp -> do
      --   (a, ta) <- infer cxt vs a
      --   let x  = "x" ++ show (length cxt)
      --   tb <- newMeta ((x, Left ta):cxt)
      --   unify (VMeta m :$ sp)
      --         (VPi x i ta (\v -> eval ((x, Just v):vs) tb))
      --   pure (App f a x i, eval ((x, Just (eval vs a)):vs) tb)
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
  -- LET(const, (ALL(a) ALL(b) a ==> b ==> a), (LAM(x) LAM(y) x))
  -- LET(the, (PI(a, star) a ==> a), (LAM(a) LAM(x) x))
  -- LET(id, (ALL(a) a ==> a), (LAM(x) x))
  -- LET(nat, star, (PI(n, star) (n ==> n) ==> n ==> n))
  -- LET(z, nat, (LAM(n) LAM(s) LAM(z) z))
  -- LET(five, nat, (LAM(n) LAM(s) LAM(z) s ∙ (s ∙ (s ∙ (s ∙ (s ∙ z))))))

  -- LET(s, (nat ==> nat), (LAM(a) LAM(n) LAM(s) LAM(z) s ∙ (a ∙ n ∙ s ∙ z)))
  -- LET(add, (nat ==> nat ==> nat), (LAM(a) LAM(b) LAM(n) LAM(s) LAM(z) a ∙ n ∙ s ∙ (b ∙ n ∙ s ∙ z)))
  -- LET(mul, (nat ==> nat ==> nat), (LAM(a) LAM(b) LAM(n) LAM(s) a ∙ n ∙ (b ∙ n ∙ s)))
  -- LET(ten, nat, (add ∙ five ∙ five))
  -- LET(hundred, nat, (mul ∙ ten ∙ ten))

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


    -- (forall "a" $ forall "b" $ "a" ==> "b" ==> "a")
    -- (lam "x" $ lam "y" $ "x") $

--   make "the"
--     (pi "a" h $ "a" ==> "a")
--     (lam "a" $ lam "x" "x") $

--   make "id"
--     (forall "a" $ "a" ==> "a")
--     (lam "x" "x") $

--   makeh "pair"
--    (lam "A" $ lam "B" $ forall "P" $ ("A" ==> "B" ==> "P") ==> "P") $

--   make "ap"
--     (forall "a" $ forall "b" $ ("a" ==> "b") ==> "a" ==> "b")
--     (lam "f" $ lam "x" $ "f" ∙ "x") $

--   -- make "stress"
--   --   (forall "a" $ "a" ==> "a")
--   --   (
--   --    "id" ∙ "id" ∙ "id" ∙ "id" ∙ "id" ∙ "id" ∙ "id" ∙ "id" ∙
--   --    "id" ∙ "id" ∙ "id" ∙ "id" ∙ "id" ∙ "id" ∙ "id" ∙ "id"  ) $

--   makeh "Nat"
--     (pi "n" h $ ("n" ==> "n") ==> "n" ==> "n") $

--   make "z"
--     "Nat"
--     (lam "n" $ lam "s" $ lam "z" "z") $

--   make "s"
--     ("Nat" ==> "Nat")
--     (lam "a" $ lam "n" $ lam "s" $ lam "z" $ "s" ∙ ("a" ∙ "n" ∙ "s" ∙ "z")) $

--   make "add"
--     ("Nat" ==> "Nat" ==> "Nat")
--     (lam "a" $ lam "b" $ lam "n" $ lam "s" $ lam "z" $
--       "a" ∙ "n" ∙ "s" ∙ ("b" ∙ "n" ∙ "s" ∙ "z")) $

--   make "mul"
--     ("Nat" ==> "Nat" ==> "Nat")
--     (lam "a" $ lam "b" $ lam "n" $ lam "s" $ lam "z" $
--        "a" ∙ "n" ∙ ("b" ∙ "n" ∙ "s") ∙ "z") $

--   make "one"     "Nat" ("s" ∙ "z") $
--   make "two"     "Nat" ("s" ∙ "one") $
--   make "five"    "Nat" ("s" ∙ ("add" ∙ "two" ∙ "two")) $
--   make "ten"     "Nat" ("add" ∙ "five" ∙ "five") $
--   make "hundred" "Nat" ("mul" ∙ "ten" ∙ "ten") $

--   "hundred"

-}
