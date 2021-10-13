
module Evaluation (($$), quote, eval, nf, force, lvl2Ix, vApp, vAppSp) where

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
  VFlex  m sp -> VFlex m  (sp :> (u, i))
  VRigid x sp -> VRigid x (sp :> (u, i))
  _           -> impossible

vAppSp :: Val -> Spine -> Val
vAppSp t = \case
  []           -> t
  sp :> (u, i) -> vApp (vAppSp t sp) u i

vMeta :: MetaVar -> Val
vMeta m = case lookupMeta m of
  Solved v _ -> v
  Unsolved{} -> VMeta m

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

force :: Val -> Val
force = \case
  VFlex m sp | Solved t _ <- lookupMeta m -> force (vAppSp t sp)
  t -> t

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quoteSp :: Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  []           -> t
  sp :> (u, i) -> App (quoteSp l t sp) (quote l u) i

quote :: Lvl -> Val -> Tm
quote l t = case force t of
  VFlex m sp  -> quoteSp l (Meta m) sp
  VRigid x sp -> quoteSp l (Var (lvl2Ix l x)) sp
  VLam x i t  -> Lam x i (quote (l + 1) (t $$ VVar l))
  VPi x i a b -> Pi x i (quote l a) (quote (l + 1) (b $$ VVar l))
  VU          -> U

nf :: Env -> Tm -> Tm
nf env t = quote (Lvl (length env)) (eval env t)
