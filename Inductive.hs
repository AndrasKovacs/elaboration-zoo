{-# language BangPatterns, Strict, LambdaCase, PatternGuards, OverloadedStrings #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

import qualified Data.Text as T
import Data.Maybe
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Except
import Control.Arrow
import GHC.Prim
import GHC.Types




{-
import qualified Data.Text as T
import Data.Maybe
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Except
import Control.Arrow
import GHC.Prim
import GHC.Types

type Name   = T.Text
type Gen    = Int
type Sub a  = [(Name, a)]
type Vals   = Sub ValEntry
type Ty     = Tm
type VTy    = Val
type RTy    = RTm
type Id     = Int

data ValEntry
  = VEBound        -- ^ Bound variable
  | VERec Id ~Val  -- ^ Recursive definition (relative to some term)
  | VEDef ~Val     -- ^ Non-recursive definition

data RTm
  = RName Name
  | RApp RTm RTm
  | RLam Name RTm
  | RSplit [(Pat, RTm)]
  | RPi Name RTy RTy
  | RLet Name RTm RTy RTm
  | RInd Name RTy (Sub RTy) RTm
  | RU

data Pat
  = PCon Name [Name]
  | PAny Name

data Tm
  = Var Name
  | DCon Name
  | TCon Name
  | App Tm Tm
  | Lam Name Tm
  | Split [(Pat, Tm)]
  | Pi Name Ty Tm
  | Let Id Name Ty Tm Tm
  | Ind Name Ty (Sub Ty) Tm
  | U

data Head
  = HBound Name
  | HRec Id Name
  | HGen Gen
  | HDCon Name
  | HTCon Name
  | HSplit Vals [(Pat, Tm)]

vbound x = VNe (HBound x) []
vgen   g = VNe (HGen g  ) []
vdcon  x = VNe (HDCon x ) []
vtcon  x = VNe (HTCon x ) []
vrec i x = VNe (HRec i x) []

data Val
  = VNe Head [Val]
  | VLam Name Vals Tm
  | VSplit Vals [(Pat, Tm)]
  | VPi Name VTy Vals Tm
  | VU

--------------------------------------------------------------------------------

appSplit :: Bool -> Vals -> [(Pat, Tm)] -> Val -> Val
appSplit urec vs ps a = case a of
  VNe (HDCon x) args -> match x args ps
  _                  -> matchAny a ps
  where
    match :: Name -> [Val] -> [(Pat, Tm)] -> Val
    match x args ((PCon x' xs, t):ps)
      | x == x'   = eval urec (zipWith (\v x -> (x, VEDef v)) args xs ++ vs) t
      | otherwise = match x args ps
    match x args ((PAny x', t):ps) = eval urec ((x', VEDef (VNe (HDCon x) args)):vs) t
    match x args [] = error "inexhaustive pattern"

    matchAny :: Val -> [(Pat, Tm)] -> Val
    matchAny a ((PAny x, t):ps) = eval urec ((x, VEDef a):vs) t
    matchAny a ((_,      _):ps) = matchAny a ps
    matchAny _ []               = VNe (HSplit vs ps) [a]

vapp :: Bool -> Val -> Val -> Val
vapp urec f ~a = case f of
  VLam x e t   -> eval urec ((x, VEDef a):e) t
  VSplit vs ps -> appSplit urec vs ps a
  VNe x vs     -> VNe x (a:vs)
  _            -> error "vapp"

evalVar :: Bool -> Name -> Vals -> Val
evalVar urec x vs = case fromJust $ lookup x vs of
  VEBound   -> vbound x
  VEDef a   -> a
  VERec i a -> if urec then a else vrec i x

eval :: Bool -> Vals -> Tm -> Val
eval urec e = \case
  Var x           -> evalVar urec x e
  DCon x          -> vdcon x
  TCon x          -> vtcon x
  App f a         -> vapp urec (eval urec e f) (eval urec e a)
  Lam x t         -> VLam x e t
  Split ps        -> VSplit e ps
  Pi x a b        -> VPi x (eval urec e a) e b
  Let i x ty t t' -> let ~vt = eval urec ((x, VERec i vt):e) t
                     in eval urec ((x, VEDef vt):e) t'
  Ind x t cs t'   -> eval urec e t'
  U               -> VU

--------------------------------------------------------------------------------

data TyEntry
  = EInd VTy (Sub VTy)
  | EVar ~VTy
  | ECon VTy

type Types = Sub TyEntry
type M = StateT Int (Either T.Text)

ptrEq :: a -> a -> Bool
ptrEq !a !b = isTrue# (reallyUnsafePtrEquality# a b)

conv :: Bool -> Val -> Val -> Bool
conv urec = go 0 where
  go :: Gen -> Val -> Val -> Bool
  go g VU VU = True
  go g (VPi x a vs b) (VPi x' a' vs' b') =
    go g a a' && let gen = vgen g in
    go (g+1) (eval urec ((x, VEDef gen):vs) b) (eval urec ((x', VEDef gen):vs') b')
  go g (VLam x vs t) (VLam x' vs' t') =
    let gen = vgen g in
    go (g+1) (eval urec ((x, VEDef gen):vs) t) (eval urec ((x', VEDef gen):vs') t')
  go g t (VLam x' vs' t') =
    let gen = vgen g in
    go (g+1) (vapp urec t gen) (eval urec ((x', VEDef gen):vs') t')
  go g (VLam x vs t) t' =
    let gen = vgen g in
    go (g+1) (eval urec ((x, VEDef gen):vs) t) (vapp urec t' gen)
  go g (VNe h vs) (VNe h' vs') = goHead g h h' && goSp g vs vs'
  go g t@(VSplit vs ps) t'@(VSplit vs' ps') = ptrEq t t' || goSplit g vs ps vs' ps'
  go g _ _ = False

  goPat :: Gen -> Pat -> Pat -> Maybe (Gen, Vals, Vals)
  goPat g (PAny x) (PAny x') =
    let e = VEDef $ vgen g
    in Just (g + 1, [(x, e)], [(x', e)])
  goPat g (PCon x xs) (PCon x' xs')
    | x == x' =
      let g' = g + length xs
          gs = map (VEDef . vgen) [g+1..g']
      in Just (g', zip xs gs, zip xs' gs)
  goPat _ _ _ = Nothing

  goSplit :: Gen -> Vals -> [(Pat, Tm)] -> Vals -> [(Pat, Tm)] -> Bool
  goSplit g vs ((p, t):ps) vs' ((p', t'):ps') = case goPat g p p' of
    Just (g', gens, gens') ->
      conv False (eval False (gens++vs) t) (eval False (gens'++vs') t')
      &&
      goSplit g vs ps vs' ps'
    Nothing -> False
  goSplit g _ [] _ [] = True
  goSplit _ _ _ _ _ = False

  goHead :: Gen -> Head -> Head -> Bool
  goHead g h h' = case (h, h') of
    (HBound x,     HBound x'     ) -> x == x'
    (HGen g,       HGen g'       ) -> g == g'
    (HDCon x,      HDCon x'      ) -> x == x'
    (HTCon x,      HTCon x'      ) -> x == x'
    (HSplit vs ps, HSplit vs' ps') -> goSplit g vs ps vs' ps'
    (HRec i x,     HRec i' x'    ) -> x == x' && i == i'
    _ -> False

  goSp :: Gen -> [Val] -> [Val] -> Bool
  goSp g vs vs' = case (vs, vs') of
    (v:vs , v':vs') -> go g v v' && goSp g vs vs'
    ([]   , []    ) -> True
    (_    , _     ) -> error "goSp: impossible"


data Perhaps = Yes | No | Dunno

-- | Unify indices and stuff in patterns
unifyPat :: Types -> Val -> Val -> State Vals Perhaps
unifyPat ts t t' = _

check :: Types -> Vals -> RTm -> VTy -> M Tm
check ts vs t ty = case (t, ty) of
  (RLam x t, VPi x' a vs' b) -> do
    t <- check ((x, EVar a):ts) ((x, VEBound):vs) t (eval True ((x', VEBound):vs') b)
    pure (Lam x t)
  (RSplit ps, VPi x' a vs' b) ->
    case a of
      VNe (HTCon ind) ixes -> do
        let EInd ity cty = fromJust $ lookup ind ts
        undefined


      _ -> throwError "cannot split on non-inductive type"
  (t, ty) -> do
    (t, tty) <- infer ts vs t
    unless (conv True tty ty) $
      throwError "type mismatch"
    pure t

inferName :: Types -> Name -> M (Tm, VTy)
inferName ts x = case lookup x ts of
  Nothing    -> throwError "name not in scope"
  Just entry -> case entry of
    EInd ty _ -> pure (TCon x, ty)
    ECon ty   -> pure (DCon x, ty)
    EVar ty   -> pure (Var x, ty)

elabInd :: Types -> Vals -> Name -> RTy -> Sub RTy -> M (Ty, Sub Ty)
elabInd ts vs x ty cs = undefined

infer :: Types -> Vals -> RTm -> M (Tm, VTy)
infer ts vs = \case
  RName x   -> inferName ts x
  RLam x t  -> throwError "can't infer type for lambda"
  RPi x a b -> do
    a <- check ts vs a VU
    b <- check ((x, EVar (eval True vs a)):ts) ((x, VEBound):vs) b VU
    pure (Pi x a b, VU)
  RLet x ty t t' -> do
    i <- get <* modify (+1)
    ty <- check ts vs t VU
    let ~vty = eval True vs ty
    t <- check ((x, EVar vty):ts) ((x, VEBound):vs) t vty
    let ~vt = eval True ((x, VERec i vt):vs) t
    (t', t'ty) <- infer ((x, EVar vty):ts) ((x, VEDef vt):vs) t'
    pure (Let i x ty t t', t'ty)
  RApp f a -> do
    (f, fty) <- infer ts vs f
    case fty of
      VPi x aty vs' b -> do
        a <- check ts vs a aty
        let ~va = eval True vs a
        pure (App f a, eval True ((x, VEDef va):vs) b)
      _ -> throwError "infer: expected function type"
  RU -> pure (U, VU)
  RInd x ty cs t' -> do
    (ty, cs) <- elabInd ts vs x ty cs
    let ~vty = eval True vs ty
    let vcs  = map (second (eval True vs)) cs
    let ts'  = map (second ECon) vcs ++ (x, EInd vty vcs) : ts
    (t', t'ty) <- infer ts' vs t'
    pure (Ind x ty cs t', t'ty)
  RSplit ps -> throwError "cannot infer type for split"

-}
