{-# language
  PatternSynonyms, BangPatterns, MagicHash, PatternGuards,
  DataKinds, LambdaCase, ViewPatterns, TupleSections,
  TypeFamilies, GADTs, EmptyCase, OverloadedStrings #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

module MetavarNoEta where

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HM
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM

import Data.Foldable
import Data.Monoid
import Control.Arrow
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Except

-- | Spine-strict snoc list.
data SList a = Nil | !(SList a) :> a
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Monoid (SList a) where
  mempty               = Nil
  mappend as (bs :> b) = mappend as bs :> b
  mappend as Nil       = as

-- Syntax
--------------------------------------------------------------------------------  

type Name   = String
type Meta   = Int
type Gen    = Int
type Sp     = SList (Name, Val)
type Sub    = HashMap Name Tm

data Raw
  = RVar !Name
  | RApp !Raw !Raw
  | RLam !Name !Raw    
  | RPi !Name !Raw !Raw    
  | RAnn !Raw !Raw
  | RStar
  | RHole

data Head
  = VMeta !Meta !Env
  | VVar !Name         
  | VGen !Gen        -- ^ Bound var only used for unification modulo alpha equality.

data Val
  = !Head :$ !Sp
  | VLam !Name !(Val -> MCxt -> Val)
  | VPi !Name !Val !(Val -> MCxt -> Val)
  | VStar

data Tm
  = Var !Name
  | Gen !Gen -- ^ Only appears briefly in normal terms on the rhs of metavar equations.
  | App !Tm !Tm !Name -- ^ Tagged with Pi binder names.
  | Lam !Name !Tm
  | Pi !Name !Tm !Tm
  | Ann !Tm !Tm
  | Star
  | Meta !Meta !Sub
  deriving Show

infix 3 :$
infixl 5 :>
  
type Type   = Val
type Cxt    = HashMap Name Type
type Env    = HashMap Name Val
data MEntry = MEntry {_cxt :: !Cxt, _ty :: Type, _solution :: !(Maybe (Env -> MCxt -> Val))}
type MCxt   = IntMap MEntry
data S      = S {_mcxt :: !MCxt, _freshMeta :: !Int}
type M      = StateT S (Either String)
type Ren    = HashMap (Either Name Int) Name

-- Evaluation
--------------------------------------------------------------------------------

-- | Try to instantiate a metavariable and apply it to its substitution.
inst :: Meta -> Env -> MCxt -> Maybe Val
inst v sub mcxt = let MEntry _ _ mt = mcxt IM.! v in (\t -> t sub mcxt) <$> mt

-- | Try to instantiate the top-level head meta recursively until
--   we don't have a meta application at top or the top meta is unsolved.
refresh :: Val -> MCxt -> Val
refresh t !mcxt = go t where
  go (VMeta i sub :$ sp)
    | Just t <- inst i sub mcxt = go (foldl' (\t (v, t') -> vapp t t' v mcxt) t sp)
  go t = t

vapp :: Val -> Val -> Name -> MCxt -> Val
vapp t t' v !mcxt = case (t, t') of
  (VLam v t, a) -> t a mcxt
  (h :$ sp , a) -> h :$ (sp :> (v, a))
  _             -> error "vapp: impossible"

-- | Evaluate to weak head normal form in a metacontext.
eval :: Env -> Tm -> MCxt -> Val
eval !env !t !mcxt = go env t where
  go env = \case
    Var v      -> maybe (VVar v :$ Nil) (flip refresh mcxt) (HM.lookup v env)
    App f a v  -> vapp (go env f) (go env a) v mcxt
    Lam v t    -> VLam v $ \a -> eval (HM.insert v a env) t
    Pi v a b   -> VPi v (go env a) $ \a -> eval (HM.insert v a env) b
    Ann t ty   -> go env t
    Star       -> VStar
    Meta i sub -> let sub' = go env <$> sub
                  in maybe (VMeta i sub' :$ Nil) id (inst i sub' mcxt)
    Gen{}      -> error "eval: impossible Gen"                  

-- | Strongly normalize a weak head normal value in a metacontext.
--   It's fine if the input value is out of date, it's updated anyway.
quote :: Val -> MCxt -> Tm
quote t !mcxt = go t where
  go t = case refresh t mcxt of
    VMeta i sub :$ sp -> foldl' (\t (v, t') -> App t (go t') v) (Meta i (go <$> sub)) sp
    VVar v      :$ sp -> foldl' (\t (v, t') -> App t (go t') v) (Var v) sp
    VGen i      :$ sp -> foldl' (\t (v, t') -> App t (go t') v) (Gen i) sp
    VLam v t          -> Lam v (go (t (VVar v :$ Nil) mcxt))
    VPi v a b         -> Pi v (go a) (go (b (VVar v :$ Nil) mcxt))
    VStar             -> Star

-- Conversion
--------------------------------------------------------------------------------

-- | Try to create an inverse partial renaming from a substitution.
--   Only variables are allowed in the input substitution, but it can be non-linear,
--   since we restrict the output renaming to the linear part. 
invert :: Env -> Either String Ren
invert = foldM go HM.empty . HM.toList where
  go r (v, t) = case t of
    VVar v' :$ Nil | HM.member (Left v') r -> pure $ HM.delete (Left v') r
                   | otherwise             -> pure $ HM.insert (Left v') v r
    VGen i  :$ Nil | HM.member (Right i) r -> pure $ HM.delete (Right i) r
                   | otherwise             -> pure $ HM.insert (Right i) v r
    _ -> throwError "meta substitution is not a renaming"    

-- | Rename the right hand side of a metavariable equation while
--   checking for occurrence and scoping. TODO: pruning.
renameRhs :: Meta -> Ren -> Tm -> Either String Tm
renameRhs occur r = go r where
  go :: Ren -> Tm -> Either String Tm
  go r = \case  
    Var v      -> maybe (throwError "scope fail") (pure . Var) (HM.lookup (Left v) r)
    Gen i      -> maybe (throwError "scope fail") (pure . Var) (HM.lookup (Right i) r)    
    App f a v  -> App <$> go r f <*> go r a <*> pure v
    Lam v t    -> Lam v <$> go (HM.delete (Left v) r) t
    Pi v a b   -> Pi v <$> go r a <*> go (HM.delete (Left v) r) b
    Ann t ty   -> Ann <$> go r t <*> go r ty
    Star       -> pure Star
    Meta i sub | i == occur -> throwError "occurs fail"
               | otherwise  -> Meta i <$> traverse (go r) sub

addLams :: Sp -> Tm -> Tm
addLams sp t = foldr (Lam . fst) t sp

extendSub :: Env -> Sp -> Env
extendSub = foldl' (\s (v, t) -> HM.insert v t s)

-- | Solve a meta by applying the inverse of its substitution to the RHS.
--   It uses full normalization on for the RHS, which is costly. Future versions
--   will use "glued" representation which enable various syntactic checks
--   and heuristics.
solveMeta :: Meta -> Env -> Sp -> Val -> M ()
solveMeta m sub sp t = do
  ren <- lift $ invert (extendSub sub sp)
  t   <- quote t <$> gets _mcxt
  !t  <- lift $ addLams sp <$> renameRhs m ren t
  modify $ \s@S{..} ->
    s {_mcxt = IM.adjust (\e -> e {_solution = Just $ \env -> eval env t}) m _mcxt}

unify :: Val -> Val -> M ()
unify = go 0 where
  go :: Gen -> Val -> Val -> M ()
  go !g t t' = do
    t  <- refresh t  <$> gets _mcxt
    t' <- refresh t' <$> gets _mcxt
    case (t, t') of
      (VStar, VStar) -> pure ()
      (VLam _ t, VLam _ t') -> do
        mcxt <- gets _mcxt
        let gen = VGen g :$ Nil
        go (g + 1) (t gen mcxt) (t' gen mcxt)
      (VPi _ a b, VPi _ a' b') -> do
        go g a a'
        mcxt <- gets _mcxt
        let gen = VGen g :$ Nil
        go (g + 1) (b gen mcxt) (b' gen mcxt)
      (VVar v :$ sp, VVar v' :$ sp') | v == v' -> goSp g sp sp'
      (VGen i :$ sp, VGen i' :$ sp') | i == i' -> goSp g sp sp'
      (VMeta i sub :$ sp, VMeta i' sub' :$ sp') | i == i' -> do
        -- order ?                                                    
        zipWithM_ (go g) (HM.elems sub) (HM.elems sub')
        goSp g sp sp'
      (VMeta i sub :$ sp, t) -> solveMeta i sub sp t
      (t, VMeta i sub :$ sp) -> solveMeta i sub sp t
      _ -> throwError "can't unify"
                                                  
  goSp :: Int -> Sp -> Sp -> M ()
  goSp g (as :> (_, a)) (bs :> (_, b)) = goSp g as bs >> go g a b
  goSp g Nil Nil = pure ()
  goSp _ _   _   = error "unify Sp: impossible" 


-- -- unify :: Val -> Val -> M ()
-- -- unify = go 0 where
  
-- --   go :: Int -> Val -> Val -> M ()
-- --   go !g t t' = do
-- --     t  <- refresh t  <$> gets fst
-- --     t' <- refresh t' <$> gets fst
-- --     case (t, t') of
-- --       (VStar, VStar) -> pure ()
-- --       (VLam v t, VLam v' t') -> do
-- --         mcxt <- gets fst
-- --         let gen = VGen g :$ Nil
-- --         go (g + 1) (t gen mcxt) (t' gen mcxt)
-- --       (VPi v a b, VPi v' a' b') -> do
-- --         go g a a'
-- --         let gen = VGen g :$ Nil        
-- --         mcxt <- gets fst
-- --         go (g + 1) (b gen mcxt) (b' gen mcxt)
-- --       (VVar v :$ sp, VVar v' :$ sp') | v == v' -> goSp g sp sp'
-- --       (VGen i :$ sp, VGen i' :$ sp') | i == i' -> goSp g sp sp'
-- --       (VMeta i sub :$ sp, t) -> solveMeta i sub sp t
-- --       (t, VMeta i sub :$ sp) -> solveMeta i sub sp t
-- --       _ -> throwError "can't unify"

-- --   goSp :: Int -> Sp -> Sp -> M ()
-- --   goSp g (as :> a) (bs :> b) = goSp g as bs >> go g a b
-- --   goSp g Nil       Nil       = pure ()
-- --   goSp _ _         _         = error "unify Sp: impossible"


  

-- -- check :: Cxt -> Raw -> Type -> TM Tm
-- -- check cxt t want = get >>= \(mcxt, i) -> case (t, want) of
-- --   -- could postpone if want is meta
-- --   (RLam v t, VPi _ a b) -> 
-- --     check (HM.insert v a cxt) t (b (VVar v a :$ Nil) mcxt)
    
-- --   (RHole, _) -> do
-- --     put (IM.insert i (MEntry cxt want Nothing) mcxt, i + 1)
-- --     pure $ Meta i (HM.mapWithKey (\v _ -> Var v want) cxt)
    
-- --   (t, _) -> do
-- --     (t, has) <- infer cxt t
-- --     t <$ unify has want VStar

-- -- infer :: Cxt -> Raw -> TM (Tm, Type)
-- -- infer cxt = \case
-- --   RVar v    ->
-- --     maybe (throwError $ "Variable: " ++ v ++ " not in scope")
-- --           (\ty -> pure (Var v ty, ty))
-- --           (HM.lookup v cxt)
-- --   RStar     -> pure (Star, VStar)
-- --   RAnn t ty -> do
-- --     ty  <- check cxt ty VStar
-- --     ty' <- eval mempty ty <$> gets fst
-- --     t   <- check cxt t ty'
-- --     pure (Ann t ty, ty')
-- --   RPi v a b -> do
-- --     a  <- check cxt a VStar
-- --     a' <- eval mempty a <$> gets fst
-- --     b  <- check (HM.insert v a' cxt) b VStar
-- --     pure (Pi v a b, VStar)  
-- --   RApp f a -> do
-- --     (f, tf) <- infer cxt f
-- --     case tf of
-- --       VPi v ta tb -> do
-- --         a   <- check cxt a ta
-- --         a'  <- eval mempty a <$> gets fst
-- --         tb' <- tb a' <$> gets fst
-- --         pure (App f a ta, tb')              
-- --       _ -> throwError "can't apply non-function"
-- --   RHole     -> throwError "can't infer type for hole"
-- --   RLam v t  -> throwError "can't infer type for lambda"        

          
