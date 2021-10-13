
module Evaluation (($$), quote, eval, nf, force, lvl2Ix, vApp, vAppSp, vProj1, vProj2, vProjField) where

import Common
import Metacontext
import Syntax
import Value


infixl 8 $$
($$) :: Closure -> Val -> Val
($$) (Close env t) ~u = eval (env :> u) t
($$) (Fun t)       ~u = t u

vApp :: Val -> Val -> Icit -> Val
vApp t ~u i = case t of
  VLam _ _ t  -> t $$ u
  VFlex  m sp -> VFlex m  (SApp sp u i)
  VRigid x sp -> VRigid x (SApp sp u i)
  t           -> error $ "vApp: " ++ show t

vProj1 :: Val -> Val
vProj1 = \case
  VPair t _   -> t
  VFlex  m sp -> VFlex m  (SProj1 sp)
  VRigid x sp -> VRigid x (SProj1 sp)
  _           -> impossible

vProj2 :: Val -> Val
vProj2 = \case
  VPair _ u   -> u
  VFlex  m sp -> VFlex m  (SProj2 sp)
  VRigid x sp -> VRigid x (SProj2 sp)
  _           -> impossible

vProjField :: Val -> Name -> Int -> Val
vProjField t field n = case t of
  VPair t u   -> case n of 0 -> t
                           n -> vProjField u field (n - 1)
  VFlex  m sp -> VFlex m  (SProjField sp field n)
  VRigid x sp -> VRigid x (SProjField sp field n)
  _           -> impossible

vAppSp :: Val -> Spine -> Val
vAppSp t = \case
  SNil              -> t
  SApp sp u i       -> vApp (vAppSp t sp) u i
  SProj1 sp         -> vProj1 (vAppSp t sp)
  SProj2 sp         -> vProj2 (vAppSp t sp)
  SProjField sp x n -> vProjField (vAppSp t sp) x n

vMeta :: MetaVar -> Val
vMeta m = case lookupMeta m of
  Solved _ v _ -> v
  Unsolved{}   -> VMeta m

vAppPruning :: Env -> Val -> Pruning -> Val
vAppPruning env ~v pr = case (env, pr) of
  ([]       , []           ) -> v
  (env :> t , pr :> Just i ) -> vApp (vAppPruning env v pr) t i
  (env :> t , pr :> Nothing) -> vAppPruning env v pr
  _                          -> impossible

vVar :: Dbg => Env -> Ix -> Val
vVar env x | unIx x < 0          = VVar (coerce x)  -- temporary fresh variable!
vVar env x | unIx x < length env = env !! unIx x
vVar env x = error $ "index out of env: "
                  ++ show ("env len"::String, length env, "ix"::String, x)

eval :: Dbg => Env -> Tm -> Val
eval env = \case
  Var x           -> vVar env x
  App t u i       -> vApp (eval env t) (eval env u) i
  Lam x i t       -> VLam x i (Close env t)
  Pi x i a b      -> VPi x i (eval env a) (Close env b)
  Let _ _ t u     -> eval (env :> eval env t) u
  U               -> VU
  Meta m          -> vMeta m
  AppPruning t pr -> vAppPruning env (eval env t) pr
  Sg x a b        -> VSg x (eval env a) (Close env b)
  Pair t u        -> VPair (eval env t) (eval env u)
  Proj1 t         -> vProj1 (eval env t)
  Proj2 t         -> vProj2 (eval env t)
  ProjField t x n -> vProjField (eval env t) x n

force :: Dbg => Val -> Val
force = \case
  VFlex m sp | Solved _ t _ <- lookupMeta m -> force (vAppSp t sp)
  t -> t

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quoteLvl :: Lvl -> Lvl -> Ix
quoteLvl l x | x < 0 = coerce x
quoteLvl l x = lvl2Ix l x

quoteSp :: Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  SNil              -> t
  SApp sp u i       -> App (quoteSp l t sp) (quote l u) i
  SProj1 sp         -> Proj1 (quoteSp l t sp)
  SProj2 sp         -> Proj2 (quoteSp l t sp)
  SProjField sp x n -> ProjField (quoteSp l t sp) x n

quote :: Lvl -> Val -> Tm
quote l t = case force t of
  VFlex m sp  -> quoteSp l (Meta m) sp
  VRigid x sp -> quoteSp l (Var (quoteLvl l x)) sp
  VLam x i t  -> Lam x i (quote (l + 1) (t $$ VVar l))
  VPi x i a b -> Pi x i (quote l a) (quote (l + 1) (b $$ VVar l))
  VSg x a b   -> Sg x (quote l a) (quote (l + 1) (b $$ VVar l))
  VPair t u   -> Pair (quote l t) (quote l u)
  VU          -> U

nf :: Env -> Tm -> Tm
nf env t = quote (Lvl (length env)) (eval env t)
