{-# LANGUAGE FunctionalDependencies #-}

module Evaluation (($$), quote, eval, nf, force, lvl2Ix, vApp, QuoteContext(..)) where

import Data.Functor.Identity

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
  _           -> error "impossible"

vAppSp :: Val -> Spine -> Val
vAppSp t = \case
  []           -> t
  sp :> (u, i) -> vApp (vAppSp t sp) u i

vMeta :: MetaVar -> Val
vMeta m = case lookupMeta m of
  Solved v -> v
  Unsolved -> VMeta m

vAppBDs :: Env -> Val -> [BD] -> Val
vAppBDs env ~v bds = case (env, bds) of
  ([]       , []            ) -> v
  (env :> t , bds :> Bound  ) -> vApp (vAppBDs env v bds) t Expl
  (env :> t , bds :> Defined) -> vAppBDs env v bds
  _                           -> error "impossible"

eval :: Env -> Tm -> Val
eval env = \case
  Var x              -> env !! unIx x
  App t u i          -> vApp (eval env t) (eval env u) i
  Lam x i t          -> VLam x i (Closure env t)
  Pi x i a b         -> VPi x i (eval env a) (Closure env b)
  Let _ _ t u        -> eval (env :> eval env t) u
  U                  -> VU
  Meta m             -> vMeta m
  InsertedMeta m bds -> vAppBDs env (vMeta m) bds

force :: Val -> Val
force = \case
  VFlex m sp | Solved t <- lookupMeta m -> force (vAppSp t sp)
  t -> t

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

class (Monad m) => QuoteContext cxt m | cxt -> m where
  neutral :: cxt -> Val
  lift :: cxt -> cxt
  quoteMeta :: cxt -> MetaVar -> m Tm
  quoteVar :: cxt -> Lvl -> m Tm

instance QuoteContext Lvl Identity where
  neutral = VVar
  lift l = l + 1
  quoteMeta l m = pure $ Meta m
  quoteVar l x = pure $ Var (lvl2Ix l x)

quoteSp :: (QuoteContext cxt m) => cxt -> Tm -> Spine -> m Tm
quoteSp cxt t = \case
  []           -> pure t
  sp :> (u, i) -> App <$> quoteSp cxt t sp <*> quote cxt u <*> pure i

quote :: (QuoteContext cxt m) => cxt -> Val -> m Tm
quote cxt t = case force t of
  VFlex m sp  -> quoteMeta cxt m >>= \t -> quoteSp cxt t sp
  VRigid m sp -> quoteVar cxt m >>= \t -> quoteSp cxt t sp
  VLam x i t  -> Lam x i <$> quote (lift cxt) (t $$ neutral cxt)
  VPi x i a b -> Pi x i <$> quote cxt a <*> quote (lift cxt) (b $$ neutral cxt)
  VU          -> pure U

nf :: Env -> Tm -> Tm
nf env t = runIdentity $ quote (Lvl (length env)) (eval env t)
