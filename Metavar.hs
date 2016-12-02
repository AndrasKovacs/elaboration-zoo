{-# language
  PatternSynonyms, BangPatterns, MagicHash, PatternGuards,
  DataKinds, LambdaCase, ViewPatterns, TupleSections,
  TypeFamilies, GADTs, EmptyCase, OverloadedStrings #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

module Metavar where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM

import Data.Monoid
import Control.Arrow
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Except

{-
  concept
    - metavariables in contextual modal TT style
    - mixed evaluation: call-by-need generally, but call-by-name
      for meta instantiation
    - no postponing or guards

  evaluation:
    - We evaluate to whnf HOAS.

    - We have a mixed call-by-need/call-by-name evaluation, where
      known non-meta beta redexes evaluate call-by-need (with shared lazy
      computation), but metavariables are instantiated on the fly without
      sharing.

    - The key point is that evaluation takes place modulo the current
      metacontext, therefore values stored in closures may become out-of-date
      when the metacontext changes. We have shared upfront computation from
      non-meta redexes, but computation resulting from meta instantiation
      must be redone each time.

    - We have two functions: "eval" and "refresh".

      - "eval" evaluates a term in an environment of possibly out-of-date
        values. When we look up a value from env, instead of just returning
        it (as in plain call-by-need evaluation), we first apply "refresh".

      - "refresh" takes a Val, and if it's a meta application then it tries
        to eliminate the meta by instantiating the head and evaluating the new redex.
        It proceeds recursively until the topmost expression is not an instantiable
        meta application.

        However, it doesn't recurse into the values in a spine. Fully re-evaluating
        a value modulo a meta-context requires full traversal, so it only makes sense
        if we can somehow distinguish up-to-date and out-of-date values in environments,
        so we don't re-evaluate up-to-date entries on each env lookup.

        It may or may not be a worthwhile optimization to store "timestamp"-s along values
        in environments that indicate the "version" of the metacontext in which the value
        was evaluated, so we know if it's up to date.

        But many metacxt changes affect metavariables that don't occur in a certain value,
        so most re-evaluations would be useless. So it would make sense to make metavar
        occurrences cached or queriable. But this is a heavyweight solution that makes
        me rather uncomfortable.

        My impression is that it's better to simply redo computation arising from meta
        instantiation whenever it's needed, while keeping the administrative overheads
        minimal. Anyway, elaborating a module would proceed one-by-one on top level
        binding groups, and whenever we finish a binding group we can zonk the elaborated
        terms, removing all metas and clearing the metacxt. Therefore, the vast majority
        of computation would involve meta-free terms anyway.

        It's yet another optimization question though when to zonk. In theory, we
        could always zonk before evaluating a freshly elaborated term. On one hand,
        zonking is a waste if few contained metavariables are actually solved, but
        on the other hand, zonking is only performed on terms with source-bounded size,
        so it may be not so bad.

    - We need to "refresh" whenever a value might be out of date:
      - When looking up from env
      - Each value in a spine may be out of date, as a result of past
        refreshing.

    - The biggest advantage:
      - almost no overhead for evaluating/unifying meta-free terms in meta-free environments!
        If the top of the value is not a meta spine, "refresh" does nothing, and top-meta-ness
        can be decided in constant time.

-}

{-
  - implementation ideas: De Bruijn levels + binder metadata plz with lists for sub/env/cxt
    - almost certainly faster for any sensibly large term
  - No types stored in app-s and vars
    - Spine form makes recovery of types relatively nice

  - even simpler impl: no type-directed conv, no eta conversion, no type tagging in Tm
-}

{-
  - General choices:
    - 1. Do as much as possible type-directed
       - 1.1 : Don't tag spines with types, recreate types on the fly. Disadvantage
               is wasted computation.
       - 1.2 : Tag spines with types and binder metadata. Disadvantage: we need renaming
               for metavariable solution, and renaming values in tags is unwieldy, though
               not impossible.
    - 2. Minimize type use. This makes a couple of things simpler, but eta converrsion
         checking becomes incomplete and full of hacks.

  - Ideas:
    - Implement lazy metacontext instantiation with mutable (IO) refs.

    - Don't use error monad. Use metas for type-incorrect expressions, don't
      stop elaboration on errors. Use IO exception for conversion checks.
      Zonking will nicely list all errors and unsolved metas.

    - Backtracking metacxt still possible with lazy metacxt instantiation:
      we just need to switch mode from "destructive" to "persistent".

      On switch to "persistent", we copy metacxt to persistent data structure, and we only
      use persistent cxt with immediate instantiation for eval while we're
      in persistent mode.

      On switch to "destructive", we copy the metacxt back to new mutable array.

      The two copying can be avoided by only having a persistent data structure at
      all times under the IORef. When switching, we just change eval between immediate
      and lazy modes.

  - General invariant to be preserved with glued repr:
    - All stored Tm-s must be the same size (not counting possible Type tags)
      as some Raw term that was present in the source code. 
    - We could violate this by keeping normalized Tm-s around.
    - Metavar fiddling requires operations on Tm-s, but fortunately it seems
      that we get away with mere renamings:
        - When solving metas, we only need renaming on the RHS
        - When pruning and intersecting, we need to strenghten the types
          of metas, but that's also renaming.

  - Questions for someone knowledgeable, e.g. Andreas Abel

    - Ordered metacontext:
      - Pientka says ord. metacxt. makes type occurs check unnecessary
      - Gundry has it in ch. 4 of his thesis, and does lots of shuffling on
        metavar solving to keep the ordering
      - However, Agda doesn't do type occurs check, and doesn't have ordered metacxt either

    - When pruning occurring metas on RHS, Agda assumes that all the types of the pruned metas
      can be strengthened. Why is that?
      - Answer: no Agda *doesn't* assume such thing. It doesn't prune vars that are
        unpruneable because of type dependency.

  - Idea: metavariable operations require only renamaing. Can we switch to Kripke
    closures or semantic functions with minimal overhead, and see if that makes
    renaming faster?

-}

type Name = String

data Raw
  = RVar !Name
  | RApp !Raw !Raw
  | RLam !Name !Raw    
  | RPi !Name !Raw !Raw    
  | RAnn !Raw !Raw
  | RStar
  | RHole

data Head
  = VMeta !Int !Env    -- ^ metavariable
  | VVar !Name Type    -- ^ bound variable
  | VGen !Int Type     -- ^ generic variable for alpha equality checks

data Sp
  = Nil
  | VApp !Sp Val Type

data Val
  = !Head :$ !Sp
  | VLam !Name !(Val -> MCxt -> Val)
  | VPi !Name !Val !(Val -> MCxt -> Val)
  | VStar

data Tm
  = Var !Name Type
  | App !Tm !Tm Type
  | Lam !Name !Tm
  | Pi !Name !Tm !Tm
  | Ann !Tm !Tm
  | Star
  | Meta !Int !Sub

infix  3 :$

type Type   = Val
type Cxt    = HashMap Name Type
type Env    = HashMap Name Val
type Sub    = HashMap Name Tm
data MEntry = MEntry !Cxt Type !(Maybe (Env -> MCxt -> Val))
type MCxt   = IntMap MEntry
type TM     = StateT (MCxt, Int) (Either String)

instance Monoid Sp where
  mempty                    = Nil
  mappend as (VApp bs b ty) = VApp (mappend as bs) b ty
  mappend as Nil            = as

inst :: Int -> Env -> MCxt -> ((Cxt, Type), Maybe Val)
inst v sub mcxt = 
  let MEntry cxt ty mt = mcxt IM.! v
  in ((cxt, ty), (\t -> t sub mcxt) <$> mt)

refresh :: Val -> MCxt -> Val
refresh v !mcxt = go v where
  go (VMeta i sub :$ sp) | Just t <- snd $ inst i sub mcxt = go (appSp t sp mcxt)
  go v = v

appSp :: Val -> Sp -> MCxt -> Val
appSp v !sp !mcxt = go v sp where
  go (VLam v t) (VApp sp a ty) = go (t a mcxt) sp
  go (h :$ sp)  sp'            = h :$ (sp <> sp')
  go _          _              = error "appSp: impossible"

vapp :: Val -> Val -> Type -> MCxt -> Val
vapp (VLam v t) a ty mcxt = t a mcxt
vapp (h :$ sp)  a ty mcxt = h :$ (VApp sp a ty)
vapp _          _ _  mcxt = error "vapp: impossible"

eval :: Env -> Tm -> MCxt -> Val
eval !env !t !mcxt = case t of
  Var v ty   -> maybe (VVar v ty :$ Nil) (flip refresh mcxt) (HM.lookup v env)
  App f a ty -> vapp (eval env f mcxt) (eval env a mcxt) ty mcxt
  Lam v t    -> VLam v $ \a -> eval (HM.insert v a env) t
  Pi v a b   -> VPi v (eval env a mcxt) $ \a -> eval (HM.insert v a env) b
  Ann t ty   -> eval env t mcxt
  Star       -> VStar
  Meta i sub -> let sub' = flip (eval env) mcxt <$> sub in
                maybe (VMeta i sub' :$ Nil) id (snd $ inst i sub' mcxt)

quote :: Val -> Type -> MCxt -> Tm
quote t ty mcxt = go t ty where
  
  go (VMeta i sub :$ sp) ty =
    let ((cxt, _), t) = inst i sub mcxt in case t of
      Just t -> go (appSp t sp mcxt) ty
      _      -> goSp (Meta i (HM.mapWithKey (\v t -> go t (cxt HM.! v)) sub)) sp
      
  go (VVar v ty :$ sp) _  = goSp (Var v ty) sp
  
  go (VLam v t) (VPi _ a b) =
    let var = VVar v a :$ Nil in Lam v (go (t var mcxt) (b var mcxt))

  go VStar _ = Star
  go _ _ = error "quote: impossible"
       
  goSp h = \case    
    VApp sp a ta -> App (goSp h sp) (go a ta) ta
    Nil          -> h

-- Problem: we want to rename meta solutions (with the inverted ren),
-- but we there's no good way to rename type tags, which are values. 
-- Possible solution:
--  1. Rename Tm while ignoring type tags
--  2. Do special eval for Tm which rebuilds type tags

sub :: Sub -> Tm -> MCxt -> Tm
sub s t mcxt = go s t where
  go s = \case
    Var v ty   -> maybe (Var v ty) id (HM.lookup v s)
    App f a ty -> App (go s f) (go s a) ty
    Lam v t    -> Lam v (go (HM.delete v s) t)
    Pi v a b   -> Pi v (go s a) (go (HM.delete v s) b)
    Ann t ty   -> Ann (go s t) (go s ty)
    Star       -> Star
    Meta i s'  -> Meta i (go s <$> s')  

unify :: Val -> Val -> Type -> TM ()
unify = go 0 where
  
  go :: Int -> Val -> Val -> Type -> TM ()
  go !g t t' ty = do
    
    t  <- refresh t  <$> gets fst
    t' <- refresh t' <$> gets fst
    ty <- refresh ty <$> gets fst

    -- could postpone if ty is meta (because we don't know if we should eta expand)
    case ty of
      
     VPi v a b -> do
       mcxt <- gets fst       
       let gen = VGen g a :$ Nil
       go (g + 1) (vapp t gen a mcxt) (vapp t' gen a mcxt) (b gen mcxt)
       
     _ -> case (t, t') of       
       (VStar, VStar) ->
         pure ()
       
       (VPi v a b, VPi v' a' b') -> do         
         go g a a' VStar  -- NOTE : refreshed "a" should be reused here
         mcxt <- gets fst         
         let gen = VGen g a :$ Nil         
         go (g + 1) (b gen mcxt) (b' gen mcxt) VStar

       (VVar v _ :$ sp, VVar v' _ :$ sp') | v == v' -> goSp g sp sp'
       (VGen i _ :$ sp, VGen i' _ :$ sp') | i == i' -> goSp g sp sp'

       (VMeta i sub :$ sp, t) -> solveMeta i sub sp t ty
       (t, VMeta i sub :$ sp) -> solveMeta i sub sp t ty
       
       _ -> throwError "can't unify terms"

  goSp :: Int -> Sp -> Sp -> TM ()
  goSp g (VApp sp a ta) (VApp sp' a' ta') = goSp g sp sp' >> go g a a' ta   
  goSp g Nil            Nil               = pure ()
  goSp _ _              _                 = throwError "can't unify spines"

  addSpToSub :: Env -> Sp -> Type -> MCxt -> Env
  addSpToSub env sp ty mcxt = go env sp ty where
    go env (VApp sp a _) (VPi v _ b) = HM.insert v a (go env sp (b a mcxt))
    go env Nil _ = env

  invertSub :: Env -> TM Sub
  invertSub = foldM go HM.empty . HM.toList where
    go sub (v, VVar v' ty :$ Nil)
      | not (HM.member v' sub) = pure $ HM.insert v' (Var v ty) sub
    go _ _ = throwError "solveMeta: substitution not invertible"

  -- Expensive. Would be better with glued rhs.
  solveMeta :: Int -> Env -> Sp -> Val -> Type -> TM ()
  solveMeta i sub sp t ty = do
    mcxt <- gets fst
    let MEntry cxt retTy Nothing = mcxt IM.! i    

    sub <- invertSub (addSpToSub sub sp ty mcxt)
    undefined
    -- let MEntry cxt ty Nothing = mcxt IM.! i
    -- let t' = quote ty 

  

check :: Cxt -> Raw -> Type -> TM Tm
check cxt t want = get >>= \(mcxt, i) -> case (t, want) of
  -- could postpone if want is meta
  (RLam v t, VPi _ a b) -> 
    check (HM.insert v a cxt) t (b (VVar v a :$ Nil) mcxt)
    
  (RHole, _) -> do
    put (IM.insert i (MEntry cxt want Nothing) mcxt, i + 1)
    pure $ Meta i (HM.mapWithKey (\v _ -> Var v want) cxt)
    
  (t, _) -> do
    (t, has) <- infer cxt t
    t <$ unify has want VStar

infer :: Cxt -> Raw -> TM (Tm, Type)
infer cxt = \case
  RVar v    ->
    maybe (throwError $ "Variable: " ++ v ++ " not in scope")
          (\ty -> pure (Var v ty, ty))
          (HM.lookup v cxt)
  RStar     -> pure (Star, VStar)
  RAnn t ty -> do
    ty  <- check cxt ty VStar
    ty' <- eval mempty ty <$> gets fst
    t   <- check cxt t ty'
    pure (Ann t ty, ty')
  RPi v a b -> do
    a  <- check cxt a VStar
    a' <- eval mempty a <$> gets fst
    b  <- check (HM.insert v a' cxt) b VStar
    pure (Pi v a b, VStar)  
  RApp f a -> do
    (f, tf) <- infer cxt f
    case tf of
      VPi v ta tb -> do
        a   <- check cxt a ta
        a'  <- eval mempty a <$> gets fst
        tb' <- tb a' <$> gets fst
        pure (App f a ta, tb')              
      _ -> throwError "can't apply non-function"
  RHole     -> throwError "can't infer type for hole"
  RLam v t  -> throwError "can't infer type for lambda"        

          
