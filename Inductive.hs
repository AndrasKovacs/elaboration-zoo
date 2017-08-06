{-# language BangPatterns, MagicHash, LambdaCase, Strict, CPP, PatternGuards #-}
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

Impl TODOS:
  - API for working with closures
  - Special check case for applying lambda to bound variable
    + (Dependent standalone match expression can be desugared to this)
-}

module Inductive where

import Prelude hiding (pi)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Data.HashSet (HashSet)
import qualified Data.HashSet as HS

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM

import Data.IORef
import Data.Hashable
import Data.List
import Data.Maybe
import Data.String
import System.IO.Unsafe

--------------------------------------------------------------------------------

type Name        = String
type Meta        = Int
type Gen         = Int
type VTy         = Val
type Ty          = Tm
data Icit        = Impl | Expl deriving Eq
type NameOrIcit  = Either Name Icit
data TyEntry     = TETCon ~VTy (Sub VTy) | TEDCon ~VTy Name | TEBound ~VTy | TEDefined ~VTy
data ValEntry    = VEBound | VEDefined ~Val
type Sub a       = [(Name, a)]
type Vals        = Sub ValEntry
type Tys         = Sub TyEntry
type Spine       = Sub (Val, Icit)
type Renaming    = HashMap (Either Name Gen) Name
data MetaEntry   = MESolved Val | MEFrozen | MEUnsolved
type Metas       = IntMap MetaEntry

-- Raw syntax
--------------------------------------------------------------------------------

data RawCases
  = RCDefault Name Raw
  | RCEmpty
  | RCCase Name (Sub (Either Icit Name)) Raw RawCases

data Raw
  = RSym Name
  | RLet Name Raw Raw Raw
  | RApp Raw Raw NameOrIcit
  | RLam NameOrIcit RawCases
  | RFix Int Name Raw
  | RPi Name Icit Raw Raw
  | RArrow Raw Raw
  | RStar
  | RStopMetaInsertion Raw
  | RHole

data RawDefinition
  = RDDefine Raw Raw
  | RDInductive Raw (Sub Raw)

type RawProg = Sub RawDefinition

-- Core terms
--------------------------------------------------------------------------------

data Cases
  = CDefault Name Tm
  | CEmpty
  | CCase Name [Name] Tm Cases

data Tm
  = Var Name
  | Gen Gen
  | DCon Name
  | TCon Name
  | Let Name Ty Tm Tm
  | App Tm Tm Name Icit
  | Lam Icit Cases
  | Fix Int Name Tm
  | Pi Name Icit Ty Tm
  | Arrow Ty Ty
  | Star
  | Meta Meta

data Definition
  = DDefine Ty Tm
  | DInductive Ty (Sub Ty)

type Prog = Sub Definition

-- Core values
--------------------------------------------------------------------------------

data Head
  = HMeta Meta
  | HVar Name
  | HDCon Name
  | HTCon Name
  | HGen Gen
  | HFix Int Name Vals Tm
  | HLam Icit Vals Cases

data Val
  = VApp Head Spine
  | VLam Icit Vals Cases
  | VPi Name Icit ~VTy Vals Ty
  | VArrow ~VTy ~VTy
  | VStar

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

freeze ∷ IO ()
freeze = modifyIORef' mcxt (IM.map (\case MEUnsolved → MEFrozen; e → e))

inst ∷ Meta → MetaEntry
inst m = unsafeDupablePerformIO (readIORef mcxt) IM.! m

-- Evaluation
--------------------------------------------------------------------------------

vAppSpine ∷ Val → Spine → Val
vAppSpine = foldr (\(x, (a, i)) t → vApp t a x i)

inst1 ∷ Vals → Name → Val → Tm → Val
inst1 vs x ~t u = eval ((x, VEDefined t):vs) u

instN ∷ Vals → [Name] → Spine → Tm → Val
instN vs xs sp t = eval (go xs sp) t where
  go (x:xs) ((_, (a, _)):sp) = (x, VEDefined a) : go xs sp
  go [] [] = vs
  go _  _  = error "instN: mismatch between bindings and values"

vApp ∷ Val → Val → Name → Icit → Val
vApp t ~u ux ui = case t of
  VLam ti vs cs → case cs of
    CDefault x' t' → inst1 vs x' u t'
    _              → case u of
      VApp (HDCon c) sp → select cs where
          select (CCase c' xs t' cs)
            | c == c'   = instN vs xs sp t'
            | otherwise = select cs
          select (CDefault x' t') = inst1 vs x' u t'
          select CEmpty           = error "Non-exhaustive case split."
      _ → VApp (HLam ti vs cs) [(ux, (u, ui))]

  VApp h sp → case h of
    HFix n fx vs t' → case (n, u) of
      (0, VApp (HDCon _) _) → vAppSpine (eval ((fx, VEDefined (VApp h [])):vs) t') sp
      _ → VApp (HFix (n - 1) fx vs t') ((ux, (u, ui)) : sp)
    _ → VApp h ((ux, (u, ui)) : sp)

  _ → error "Impossible non-function application."

eval ∷ Vals → Tm → Val
eval vs = \case
  Var  x      → case fromJust (lookup x vs) of
                  VEBound     → VApp (HVar x) []
                  VEDefined t → refresh t
  DCon x      → VApp (HDCon x) []
  TCon x      → VApp (HTCon x) []
  Gen g       → VApp (HGen g)  []
  Let x a t u → inst1 vs x (eval vs t) u
  App t u x i → vApp (eval vs t) (eval vs u) x i
  Lam i cs    → VLam i vs cs
  Fix n x t   → VApp (HFix n x vs t) []
  Pi x i a b  → VPi x i (eval vs a) vs b
  Arrow a b   → VArrow (eval vs a) (eval vs b)
  Meta m      → case inst m of
                  MESolved t → refresh t
                  _          → VApp (HMeta m) []
  Star        → VStar

refresh ∷ Val → Val
refresh = \case
  VApp (HMeta m) sp | MESolved t ← inst m → refresh (vAppSpine t sp)
  t → t

quote ∷ Val → Tm
quote = go . refresh where
  goSpine ∷ Tm → Spine → Tm
  goSpine = foldr (\(x, (u, i)) t → App t (go u) x i)

  goClosure1 ∷ Name → Vals → Tm → Tm
  goClosure1 x vs t = go (eval ((x, VEBound):vs) t)

  goClosureN ∷ [Name] → Vals → Tm → Tm
  goClosureN xs vs t = go (eval (foldr (\x → ((x, VEBound):)) vs xs) t)

  goCases ∷ Vals → Cases → Cases
  goCases vs = \case
    CCase c xs t cs → CCase c xs (goClosureN xs vs t) (goCases vs cs)
    CDefault x t    → CDefault x (goClosure1 x vs t)
    CEmpty          → CEmpty

  go ∷ Val → Tm
  go = \case
    VApp h sp → goSpine t sp where
      t = case h of
        HVar x        → Var x
        HMeta m       → Meta m
        HDCon c       → DCon c
        HTCon c       → TCon c
        HFix n x vs t → Fix n x (goClosure1 x vs t)
        HLam i vs cs  → Lam i (goCases vs cs)
        HGen g        → Gen g
    VLam i vs cs   → Lam i (goCases vs cs)
    VPi x i a vs b → Pi x i (go a) (goClosure1 x vs b)
    VArrow a b     → Arrow (go a) (go b)
    VStar          → Star

nf ∷ Vals → Tm → Tm
nf vs t = quote (eval vs t)

-- Unification
--------------------------------------------------------------------------------

invert ∷ Spine → Renaming
invert = foldl' go HM.empty where
  go r (x, (a, _)) =
    let var = case a of
          VApp (HVar x') [] → Left x'
          VApp (HGen g)  [] → Right g
          _                 → error "Metavariable substitution is not a renaming."
    in HM.alter (maybe (Just x) (\_ → Nothing)) var r

rename ∷ Meta → Renaming → Tm → Tm
rename occur = go where
  goCases ∷ Renaming → Cases → Cases
  goCases r = \case
    CEmpty → CEmpty
    CDefault x t → CDefault x (go (HM.insert (Left x) x r) t)
    CCase c xs t cs →
      CCase c xs (go (foldl' (\r x → HM.insert (Left x) x r) r xs) t) (goCases r cs)

  go ∷ Renaming → Tm → Tm
  go r = \case
    Var x         → maybe (error "Scope check") Var (HM.lookup (Left x) r)
    Gen g         → maybe (error "Scope check") Var (HM.lookup (Right g) r)
    DCon c        → DCon c
    TCon c        → TCon c
    Let x e' ty e → Let x (go r e') (go r ty) (go r e)
    App f a x i   → App (go r f) (go r a) x i
    Lam i cs      → Lam i (goCases r cs)
    Pi x i a b    → Pi x i (go r a) (go (HM.insert (Left x) x r) b)
    Arrow a b     → Arrow (go r a) (go r b)
    Star          → Star
    Fix n x t     → Fix n x (go (HM.insert (Left x) x r) t)
    Meta i | i == occur → error "Occurs check."
           | otherwise  → Meta i

pattern Lam1 ∷ Name → Icit → Tm → Tm
pattern Lam1 x i t = Lam i (CDefault x t)

pattern VLam1 ∷ Name → Icit → Vals → Tm → Val
pattern VLam1 x i vs t = VLam i vs (CDefault x t)

lams ∷ Spine → Tm → Tm
lams sp t = foldl' (\t (x, (_, i)) → Lam1 x i t) t sp

solve ∷ Meta → Spine → Val → IO ()
solve m sp t = do
  modifyIORef' mcxt $ IM.update
    (\case MEFrozen   → error "Can't solve frozen metavariable"
           MESolved _ → error "Impossible: attempted to solve solved metavariable"
           MEUnsolved → Just (MESolved (eval [] (lams sp (rename m (invert sp) (quote t))))))
    m

vGen ∷ Gen → Val
vGen g = VApp (HGen g) []

matchIcit ∷ Icit → Icit → IO ()
matchIcit i i' =
  if i == i' then pure ()
             else error "Implicit-explicit binder mismatch"

unify ∷ Val → Val → IO ()
unify t t' = go 0 t t' where

  goCases ∷ Gen → Vals → Vals → Cases → Cases → IO ()
  goCases g vs vs' (CCase c xs t cs) (CCase c' xs' t' cs') = do
    if c == c' then pure () else error "Can't unify"

    let goCase g vs vs' [] [] = go g (eval vs t) (eval vs' t')
        goCase g vs vs' (x:xs) (x':xs') =
          goCase (g + 1) ((x, VEDefined (vGen g)):vs) ((x', VEDefined (vGen g)):vs') xs xs'
        goCase _ _ _ _ _ = error "Impossible constructor arity mismatch"

    goCase g vs vs' xs xs'

  goCases g vs vs' (CDefault x t) (CDefault x' t') =
    go (g + 1) (inst1 vs x (vGen g) t) (inst1 vs' x' (vGen g) t')
  goCases g _ _ CEmpty CEmpty = pure ()
  goCases g _ _ _      _      = error "Can't unify"

  goSpine ∷ Gen → Spine → Spine → IO ()
  goSpine g sp sp' = case (sp, sp') of
    ((_, (t, _)):sp, (_, (t', _)):sp') → goSpine g sp sp' >> go g t t'
    ([]            , []              ) → pure ()
    _                                  → error "Unify spine: impossible spine length mismatch"

  goHead ∷ Gen → Head → Head → IO ()
  goHead g h h' = case (h, h') of
    (HVar x       , HVar x'          ) | x == x' → pure ()
    (HTCon c      , HTCon c'         ) | c == c' → pure ()
    (HDCon c      , HDCon c'         ) | c == c' → pure ()
    (HGen g       , HGen g'          ) | g == g' → pure ()
    (HMeta m      , HMeta m'         ) | m == m' → pure ()
    (HLam i vs cs , HLam i' vs' cs'  ) | i == i' → goCases g vs vs' cs cs'
    (HFix n x vs t, HFix n' x' vs' t') | n == n' →
      go (g + 1) (inst1 vs x (vGen g) t) (inst1 vs' x' (vGen g) t')
    (h, h') → error "Application head mismatch"

  go ∷ Gen → Val → Val → IO ()
  go g t t' = case (refresh t, refresh t') of
    (VStar, VStar) → pure ()

    (VLam1 x i vs t, VLam1 x' i' vs' t') →
      go (g + 1) (inst1 vs x (vGen g) t) (inst1 vs' x' (vGen g) t')

    (VLam1 x i vs t, t')    → go (g + 1) (inst1 vs x (vGen g) t) (vApp t' (vGen g) x i)
    (t, VLam1 x' i' vs' t') → go (g + 1) (vApp t (vGen g) x' i') (inst1 vs' x' (vGen g) t')

    (VLam _ vs cs, VLam _ vs' cs') → goCases g vs vs' cs cs'

    (VPi x i a vs b, VPi x' i' a' vs' b') | i == i' → do
      go g a a'
      go (g + 1) (inst1 vs x (vGen g) b) (inst1 vs' x' (vGen g) b')

    (VApp h sp, VApp h' sp') → do
      goHead g h h'
      goSpine g sp sp'

    (VArrow a b, VArrow a' b') → do
      go g a a'
      go g b b'

    (VApp (HMeta m) sp, t')  → solve m sp t'
    (t, VApp (HMeta m') sp') → solve m' sp' t

    (t, t') → error "Can't unify"

-- Elaboration
--------------------------------------------------------------------------------

hashNub :: (Eq a, Hashable a) ⇒ [a] → [a]
hashNub = snd . foldr go (HS.empty, []) where
  go a (!seen, !as) | HS.member a seen = (seen, as)
  go a (seen, as) = (HS.insert a seen, a:as)

newMeta ∷ Tys → IO Tm
newMeta as = do
  m ← readIORef freshMeta
  writeIORef freshMeta (m + 1)
  modifyIORef' mcxt (IM.insert m MEUnsolved)
  let bvars = hashNub [x | (x, TEBound{}) ← as]
      mkApp = foldr (\x t → App t (Var x) x Expl) (Meta m)
  pure $ mkApp bvars

data MetaInsertion = MIUntilName Name | MIInsert | MINoInsert

-- | Expects up-to-date type as input.
insertMetas ∷ Tys → Vals → MetaInsertion → IO (Tm, VTy) → IO (Tm, VTy)
insertMetas as vs ins inp = case ins of
  MINoInsert → inp
  MIInsert   → uncurry go =<< inp where
    go t (VPi x Impl a vs' b) = do
      m ← newMeta as
      go (App t m x Impl) (inst1 vs' x (eval vs m) b)
    go t a = pure (t, a)
  MIUntilName x → uncurry go =<< inp where
    go t (VPi x' Impl a vs' b)
      | x == x'   = pure (t, VPi x' Impl a vs' b)
      | otherwise = do
          m ← newMeta as
          go (App t m x Impl) (inst1 vs' x (eval vs m) b)
    go t a = error "Expected named implicit argument"

vVar ∷ Name → Val
vVar x = VApp (HVar x) []

-- | Apply a type constructor to a spine of new metas.
newTConMetaSpine ∷ Tys → Vals → VTy → IO Spine
newTConMetaSpine = go [] where
  go sp as vs (VPi bx i a bvs b) = do
    m ← eval vs <$> newMeta as
    go ((bx, (m, i)):sp) ((bx, TEBound a):as) ((bx, VEBound):vs) (inst1 vs bx m b)
  go sp _ _ VStar = pure sp
  go _  _ _ _     = error "Impossible non-Type return type for type constructor"

getTConInfo ∷ Tys → Name → IO (VTy, Sub VTy)
getTConInfo as tcon = do
  case lookup tcon as of
    Just (TETCon a dcons) → pure (a, dcons)
    _ → error "Impossible missing type constructor info"

-- | Check cases with a known inductive domain type.
checkIndCases ∷ Tys → Vals → RawCases → (Name, Spine, VTy, Sub VTy) → (Name, Vals, Ty) → IO Cases
checkIndCases as vs cs (tcon, sp, a, dcons) (bx, bvs, b) = _

checkCases ∷ Tys → Vals → RawCases → VTy → (Name, Vals, Ty) → IO Cases
checkCases as vs cs a (bx, bvs, b) = case a of
  VApp (HTCon tcon) sp → do
    (tconTy, dcons) ← getTConInfo as tcon
    checkIndCases as vs cs (tcon, sp, tconTy, dcons) (bx, bvs, b)
  VApp (HMeta m) sp → case cs of
    RCEmpty → error "Ambiguous empty case split"
    RCDefault x t →
      CDefault x <$> check ((x, TEBound a):as) ((x, VEBound):vs) t (inst1 bvs bx (vVar x) b)
    RCCase c _ _ _ → do
      case lookup c as of
        Nothing → error "Constructor not in scope"
        Just (TEDCon _ tcon) → do
          (tconTy, dcons) ← getTConInfo as tcon
          sp ← newTConMetaSpine as vs tconTy
          checkIndCases as vs cs (tcon, sp, tconTy, dcons) (bx, bvs, b)
        Just _ → error "Expected constructor in case split"
  a → case cs of
    RCDefault x t →
      CDefault x <$> check ((x, TEBound a):as) ((x, VEBound):vs) t (inst1 bvs bx (vVar x) b)
    _ → error "Cannot split cases on non-inductive type"

check ∷ Tys → Vals → Raw → VTy → IO Tm
check as vs t a = case (t, a) of

  (RLam i cs, VPi x i' a vs' b) | either (==x) (==i') i → do
    Lam i' <$> checkCases as vs cs a (x, vs', b)

  (t, VPi x Impl a vs' b) → do
    let x' = x ++ show (length as)
    t ← check ((x', TEBound a):as) ((x', VEBound):vs) t (inst1 vs' x (vVar x') b)
    pure (Lam1 x' Impl t)

  (RHole, _) →
    newMeta as

  (RLet x a t u, b) → do
    a ← check as vs a VStar
    let ~a' = eval vs a
    t ← check as vs t a'
    let ~t' = eval vs t
    u ← check ((x, TEDefined a'):as) ((x, VEDefined t'):vs) u b
    pure (Let x a t u)

  (t, a) -> do
    (t, a') <- infer as vs MIInsert t
    unify a a'
    pure t

-- | Returns up-to-date types.
infer ∷ Tys → Vals → MetaInsertion → Raw → IO (Tm, VTy)
infer as vs ins = \case
  RStar →
    pure (Star, VStar)

  RStopMetaInsertion t →
    infer as vs MINoInsert t

  RSym x → insertMetas as vs ins $
    case lookup x as of
      Nothing → error "Symbol not in scope"
      Just e  → pure $ case e of
        TETCon a _  → (TCon x, refresh a)
        TEDCon a _  → (DCon x, refresh a)
        TEBound a   → (Var  x, refresh a)
        TEDefined a → (Var  x, refresh a)

  RApp t u i → insertMetas as vs ins $ do
    let ins = case i of
          Left x     → MIUntilName x
          Right Impl → MINoInsert
          Right Expl → MIInsert
    (t, a) ← infer as vs ins t
    case a of
      VPi x i' a vs' b → do
        case i of
          Right i → matchIcit i i'
          _       → pure ()
        u ← check as vs u a
        pure (App t u x i', inst1 vs' x (eval vs u) b)
      _ → error "Expected a function in application"

  RPi x i a b → do
    a ← check as vs a VStar
    b ← check ((x, TEBound (eval vs a)):as) ((x, VEBound):vs) b VStar
    pure (Pi x i a b, VStar)

  RArrow a b → do
    a ← check as vs a VStar
    b ← check as vs b VStar
    pure (Arrow a b, VStar)

  RLet x a t u → do
    a ← check as vs a VStar
    let ~a' = eval vs a
    t ← check as vs t a'
    let ~t' = eval vs t
    infer ((x, TEDefined a'):as) ((x, VEDefined t'):vs) ins u

  RLam i cs → insertMetas as vs ins $ do
    i ← case i of
      Left x → error "Can't use named argument for inferred lambda"
      Right i → pure i
    a ← eval vs <$> newMeta as
    let xa = "x" ++ show (length as)
    b ← newMeta ((xa, TEBound a):as)
    let ty = VPi xa i a vs b
    t ← check as vs (RLam (Right i) cs) ty
    pure (t, ty)

  RFix n x t → insertMetas as vs ins $ do
    a ← eval vs <$> newMeta as
    let xa = "x" ++ show (length as)
    t ← check ((xa, TEBound a):as) ((xa, VEBound):vs) t a
    pure (t, refresh a)

  RHole → do
    m₁ ← newMeta as
    m₂ ← newMeta as
    pure (m₁, eval vs m₂)


{-

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
