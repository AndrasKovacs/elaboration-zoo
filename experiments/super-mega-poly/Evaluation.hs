
module Evaluation (($$), quote, eval, nf, force, lvl2Ix, vApp, vAppSp, vProj1, vProj2) where


import Common
import Metacontext
import Syntax
import Value

infixl 8 $$
($$) :: Closure -> Val -> Val
($$) (Closure env t) ~u = eval (env :> u) t

vApp :: Val -> Val -> Icit -> Val
vApp t ~u i = case t of
  VLam _ _ t  -> t $$ u
  VFlex  m sp -> VFlex m  (SApp sp u i)
  VRigid x sp -> VRigid x (SApp sp u i)
  _           -> impossible

vProj1 :: Val -> Val
vProj1 = \case
  VPair t u   -> t
  VRigid x sp -> VRigid x (SProj1 sp)
  VFlex  m sp -> VFlex m (SProj1 sp)
  _           -> impossible

vProj2 :: Val -> Val
vProj2 = \case
  VPair t u   -> t
  VRigid x sp -> VRigid x (SProj2 sp)
  VFlex  m sp -> VFlex m (SProj2 sp)
  _           -> impossible

vAppSp :: Val -> Spine -> Val
vAppSp t = \case
  SNil        -> t
  SApp sp u i -> vApp (vAppSp t sp) u i
  SProj1 sp   -> vProj1 (vAppSp t sp)
  SProj2 sp   -> vProj2 (vAppSp t sp)

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

vVar :: Env -> Ix -> Val
vVar env x | unIx x < length env = env !! unIx x
vVar env x = error $ "index out of env: "
                  ++ show ("env len"::String, length env, "ix"::String, x)

eval :: Env -> Tm -> Val
eval env = \case
  Var x           -> vVar env x
  App t u i       -> vApp (eval env t) (eval env u) i
  Lam x i t       -> VLam x i (Closure env t)
  Pi x i a b      -> VPi x i (eval env a) (Closure env b)
  Let _ _ t u     -> eval (env :> eval env t) u
  U               -> VU
  Meta m          -> vMeta m
  AppPruning t pr -> vAppPruning env (eval env t) pr
  Ex x a b        -> VEx x (eval env a) (Closure env b)
  Proj1 t         -> vProj1 (eval env t)
  Proj2 t         -> vProj2 (eval env t)
  Pair t u        -> VPair (eval env t) (eval env u)
  Postponed _ t   -> eval env t
  Wk t            -> eval (tail env) t

force :: Val -> Val
force = \case
  VFlex m sp | Solved _ t _ <- lookupMeta m -> force (vAppSp t sp)
  t -> t

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quoteSp :: Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  SNil        -> t
  SApp sp u i -> App (quoteSp l t sp) (quote l u) i
  SProj1 sp   -> Proj1 (quoteSp l t sp)
  SProj2 sp   -> Proj2 (quoteSp l t sp)

quote :: Lvl -> Val -> Tm
quote l t = case force t of
  VFlex m sp  -> quoteSp l (Meta m) sp
  VRigid x sp -> quoteSp l (Var (lvl2Ix l x)) sp
  VLam x i t  -> Lam x i (quote (l + 1) (t $$ VVar l))
  VPi x i a b -> Pi x i (quote l a) (quote (l + 1) (b $$ VVar l))
  VEx x a b   -> Ex x (quote l a) (quote (l + 1) (b $$ VVar l))
  VPair t u   -> Pair (quote l t) (quote l u)
  VU          -> U

nf :: Env -> Tm -> Tm
nf env t = quote (Lvl (length env)) (eval env t)
