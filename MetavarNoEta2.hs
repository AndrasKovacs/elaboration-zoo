
{-# language
  PatternSynonyms, BangPatterns, MagicHash, PatternGuards,
  DataKinds, LambdaCase, ViewPatterns, TupleSections,
  TypeFamilies, GADTs, EmptyCase, OverloadedStrings #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

module MetavarNoEta2 where

import Prelude hiding (pi)

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM

import Data.Function
import Data.List
import Data.String
import Data.Foldable
import Data.Monoid
import Control.Arrow
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Except

import Debug.Trace

-- Syntax
--------------------------------------------------------------------------------  

type Name   = String
type Meta   = Int
type Gen    = Int

-- Note: context-like things have the *rightmost* element at top, so it's reverse order
-- compared to how we usually print lists.
type VSub   = [(Name, Val)]
type Sub    = [(Name, Tm)]
type Cxt    = [(Name, Type)]

type Ren    = HashMap (Either Name Gen) Name
type Type   = Val
data MEntry = MEntry {_cxt :: !Cxt, _ty :: Type, _solution :: !(Maybe (VSub -> MCxt -> Val))}
type MCxt   = IntMap MEntry
data S      = S {_mcxt :: !MCxt, _freshMeta :: !Meta}
type M      = StateT S (Either String)

data Raw
  = RVar !Name
  | RApp !Raw !Raw
  | RLam !Name !Raw    
  | RPi !Name !Raw !Raw    
  | RAnn !Raw !Raw
  | RStar
  | RHole

data Head
  = VMeta !Meta !VSub
  | VVar !Name         
  | VGen !Gen

data Val
  = !Head :$ !VSub
  | VLam !Name !(Val -> MCxt -> Val)
  | VPi !Name !Val !(Val -> MCxt -> Val)
  | VStar
infix 3 :$  

data Tm
  = Var !Name
  | Gen !Gen -- ^ Only appears briefly in normal terms on the RHS of metavar equations.
  | App !Tm !Tm !Name
  | Lam !Name !Tm
  | Pi !Name !Tm !Tm
  | Ann !Tm !Tm
  | Star
  | Meta !Meta !Sub


-- Evaluation
--------------------------------------------------------------------------------

-- | Try to instantiate a metavariable and apply it to its substitution.
inst :: Meta -> VSub -> MCxt -> Maybe Val
inst v sub mcxt = let MEntry _ _ mt = mcxt IM.! v in (\t -> t sub mcxt) <$> mt

-- | Try to instantiate the top-level head meta recursively until
--   we don't have a meta application at top or the top meta is unsolved.
refresh :: Val -> MCxt -> Val
refresh t !mcxt = go t where
  go (VMeta i sub :$ sp) | Just t <- inst i sub mcxt =
    go (foldr (\(v, a) t -> vapp t a v mcxt) t sp)
  go t = t

vapp :: Val -> Val -> Name -> MCxt -> Val
vapp t t' v !mcxt = case (t, t') of
  (VLam v t, a) -> t a mcxt
  (h :$ sp , a) -> h :$ ((v, a) : sp)
  _             -> error "vapp: impossible"

-- | Evaluate to weak head normal form in a metacontext.
eval :: VSub -> Tm -> MCxt -> Val
eval !vs !t !mcxt = go vs t where
  go vs = \case    
    Var v      -> maybe (VVar v :$ []) (flip refresh mcxt) (lookup v vs)
    App f a v  -> vapp (go vs f) (go vs a) v mcxt
    Lam v t    -> VLam v $ \a -> eval ((v, a):vs) t
    Pi v a b   -> VPi v (go vs a) $ \a -> eval ((v, a):vs) b
    Ann t ty   -> go vs t
    Star       -> VStar
    Meta i sub -> let sub' = (go vs <$>) <$> sub in 
                  maybe (VMeta i sub' :$ []) id (inst i sub' mcxt)
    Gen{}      -> error "eval: impossible Gen"

-- | Fully normalize a weak head normal value in a metacontext.
quote :: Val -> MCxt -> Tm
quote t !mcxt = go t where  
  goHead = \case
    VMeta i sub -> Meta i ((go <$>) <$> sub)
    VVar v      -> Var v
    VGen i      -> Gen i    
  go t = case refresh t mcxt of
    h :$ sp   -> foldr (\(v, a) t -> App t (go a) v) (goHead h) sp
    VLam v t  -> Lam v (go (t (VVar v :$ []) mcxt))
    VPi v a b -> Pi v (go a) (go (b (VVar v :$ []) mcxt))
    VStar     -> Star

nf :: Tm -> MCxt -> Tm
nf t mcxt = quote (eval [] t mcxt) mcxt

-- Unification
--------------------------------------------------------------------------------

-- | Try to create an inverse partial renaming from a substitution.
--   Only variables are allowed in the input substitution, but it can be non-linear,
--   since we restrict the output renaming to the linear part. 
invert :: VSub -> Either String Ren
invert = foldM go HM.empty where
  go r (v, t) = case t of
    VVar v' :$ [] | HM.member (Left v') r -> pure $ HM.delete (Left v') r
                  | otherwise             -> pure $ HM.insert (Left v') v r
    VGen i  :$ [] | HM.member (Right i) r -> pure $ HM.delete (Right i) r
                  | otherwise             -> pure $ HM.insert (Right i) v r
    _ -> throwError "Substitution for metavariable is not a renaming"    

-- | Rename the right hand side of a metavariable equation while
--   checking for occurrence and scoping. TODO: pruning.
renameRhs :: Meta -> Ren -> Tm -> Either String Tm
renameRhs occur r = go r where
  go :: Ren -> Tm -> Either String Tm
  go r = \case  
    Var v      -> maybe (throwError $ "scope fail") (pure . Var) (HM.lookup (Left v) r)
    Gen i      -> maybe (throwError $ "scope fail") (pure . Var) (HM.lookup (Right i) r)    
    App f a v  -> App <$> go r f <*> go r a <*> pure v
    Lam v t    -> Lam v <$> go (HM.insert (Left v) v r) t
    Pi v a b   -> Pi v <$> go r a <*> go (HM.insert (Left v) v r) b
    Ann t ty   -> Ann <$> go r t <*> go r ty
    Star       -> pure Star
    Meta i sub | i == occur -> throwError "occurs fail"
               | otherwise  -> Meta i <$> traverse (traverse (go r)) sub

addLams :: VSub -> Tm -> Tm
addLams sp t = foldr (Lam . fst) t sp

-- | Solve a meta by applying the inverse of its substitution to the RHS.
--   It uses full normalization on the RHS, which is costly. Future versions
--   should use "glued" representation which enables various syntactic checks
--   and heuristics.
solveMeta :: Meta -> VSub -> VSub -> Val -> M ()
solveMeta m sub sp t = do
  ren <- lift $ invert (sp ++ sub)
  t   <- quote t <$> gets _mcxt
  !t  <- lift $ addLams sp <$> renameRhs m ren t
  modify $ \s@S{..} ->
    s {_mcxt = IM.adjust (\e -> e {_solution = Just $ \env -> eval env t}) m _mcxt}

unify :: Val -> Val -> M ()
unify t t' = go 0 t t' where

  go :: Int -> Val -> Val -> M ()
  go !g t t' = do
    t  <- refresh t  <$> gets _mcxt
    t' <- refresh t' <$> gets _mcxt
    case (t, t') of
      (VStar, VStar) -> pure ()
      
      (VLam v t, VLam v' t') -> do
        mcxt <- gets _mcxt
        let gen = VGen g :$ []
        go (g + 1) (t gen mcxt) (t' gen mcxt)        

      (VPi v a b, VPi v' a' b') -> do
        go g a a'
        let gen = VGen g :$ []
        mcxt <- gets _mcxt
        go (g + 1) (b gen mcxt) (b' gen mcxt)
        
      (VVar v :$ sp, VVar v' :$ sp') | v == v' -> goVSub g sp sp'
      (VGen i :$ sp, VGen i' :$ sp') | i == i' -> goVSub g sp sp'

      (VMeta i sub :$ sp, VMeta i' sub' :$ sp') | i == i' ->
        goVSub g (sp ++ sub) (sp' ++ sub')

      (VMeta i sub :$ sp, t) -> solveMeta i sub sp t
      (t, VMeta i sub :$ sp) -> solveMeta i sub sp t

      _ -> throwError "can't unify"

  goVSub :: Int -> VSub -> VSub -> M ()
  goVSub g ((_, a):as) ((_, b):bs) = goVSub g as bs >> go g a b
  goVSub g []          []          = pure ()
  goVSub _ _           _           = error "unify Sp: impossible"


-- Elaboration
--------------------------------------------------------------------------------

-- | Extend a 'Cxt' with an entry. We need to delete shadowed entries,
--   or else substitutions for fresh metas would contain nonsense
--   repeated variables. 
ext :: (Name, Type) -> Cxt -> Cxt
ext x cxt = x : deleteBy ((==) `on` fst) x cxt    

check :: Cxt -> Raw -> Type -> M Tm
check cxt t want = get >>= \(S mcxt i) -> case (t, want) of
  -- could postpone if want is meta
  (RLam v t, VPi _ a b) -> 
    Lam v <$> check (ext (v, a) cxt) t (b (VVar v :$ []) mcxt)
    
  (RHole, _) -> do
    put $ S (IM.insert i (MEntry cxt want Nothing) mcxt) (i + 1)
    pure $ Meta i ((\(v, _) -> (v, Var v)) <$> cxt)
    
  (t, _) -> do
    (t, has) <- infer cxt t
    t <$ unify has want

infer :: Cxt -> Raw -> M (Tm, Type)
infer cxt = \case
  RVar v ->
    maybe (throwError $ "Variable: " ++ v ++ " not in scope")
          (\ty -> pure (Var v, ty))
          (lookup v cxt)
  RStar     -> pure (Star, VStar)
  RAnn t ty -> do
    ty  <- check cxt ty VStar
    ty' <- eval [] ty <$> gets _mcxt
    t   <- check cxt t ty'
    pure (Ann t ty, ty')
  RPi v a b -> do
    a  <- check cxt a VStar
    a' <- eval [] a <$> gets _mcxt
    b  <- check (ext (v, a') cxt) b VStar
    pure (Pi v a b, VStar)  
  RApp f a -> do
    (f, tf) <- infer cxt f
    case tf of
      VPi v ta tb -> do
        a   <- check cxt a ta
        a'  <- eval [] a <$> gets _mcxt
        tb' <- tb a' <$> gets _mcxt
        pure (App f a v, tb')              
      _ -> throwError "can't apply non-function"
  RHole     -> throwError "can't infer type for hole"
  RLam v t  -> throwError "can't infer type for lambda" -- not useful without "let"

-- | Replace all metas with their normal solutions.
zonk :: Tm -> M Tm
zonk = \case
  Var v      -> pure (Var v)
  Star       -> pure Star
  Ann t ty   -> Ann <$> zonk t <*> zonk ty
  Pi v a b   -> Pi v <$> zonk a <*> zonk b
  App f a v  -> App <$> zonk f <*> zonk a <*> pure v
  Meta v sub -> do
    mcxt <- gets _mcxt
    case inst v (((\t -> eval [] t mcxt) <$>) <$> sub) mcxt of
      Just t -> pure (quote t mcxt)
      _      -> Meta v <$> (traverse (traverse zonk) sub)
  Lam v t -> Lam v <$> zonk t
  _ -> error "zonk"

--------------------------------------------------------------------------------  

run0 :: ((Tm, Type) -> M a) -> Raw -> Either String a
run0 act t = evalStateT (infer [] t >>= act) (S mempty 0)

-- | Infer normal type.
infer0 :: Raw -> Either String Tm
infer0 = run0 (\(_, ty) -> quote ty <$> gets _mcxt)

-- | Return elaborated 'Tm'.
elab0 :: Raw -> Either String Tm
elab0 = run0 (pure . fst)

-- | Return elaborated and zonked 'Tm'.
zonk0 :: Raw -> Either String Tm
zonk0 = run0 (zonk . fst)

-- | Return normalized 'Tm'. It's only safe to normalize terms without unsolved metas.
nf0 :: Raw -> Either String Tm
nf0 = run0 (\(t, _) -> nf t <$> gets _mcxt)

-- Printing
--------------------------------------------------------------------------------

-- freeInTm :: Name -> Tm -> Bool
-- freeInTm v = go where
--   go (Var v')     = v' == v
--   go (Meta i sub) = any (freeInTm v . snd) sub
--   go (App f x _)  = go f || go x
--   go (Lam v' t)   = v' /= v && go t
--   go (Pi  v' a b) = go a || (v' /= v && go b)
--   go (Ann t ty)   = go t || go ty
--   go Star         = False
--   go _            = error "freeInTm"

prettyTm :: Int -> Tm -> ShowS
prettyTm prec = go (prec /= 0) where

  unwords' :: [ShowS] -> ShowS
  unwords' = foldr1 (\x acc -> x . (' ':) . acc)

  spine :: Tm -> Tm -> [Tm]
  spine f x = go f [x] where
    go (App f y _) args = go f (y : args)
    go t           args = t:args

  lams :: String -> Tm -> ([String], Tm)
  lams v t = go [v] t where
    go vs (Lam v t) = go (v:vs) t
    go vs t         = (vs, t)

  go :: Bool -> Tm -> ShowS
  go p (Var v)      = (v++)
  go p (Meta v sub) = showParen p (("?"++).(show v++).(" "++).(show (snd <$>sub)++))
  go p (App f x _)  = showParen p (unwords' $ map (go True) (spine f x))
  go p (Ann t ty)   = showParen p (go False t . (" : "++) . go False ty)
  go p (Lam v t)    = case lams v t of
    (vs, t) -> showParen p (("λ "++) . (unwords (reverse vs)++) . (". "++) . go False t)
  go p (Pi v a b) = showParen p (arg . (" -> "++) . go False b)
    where arg = if v /= "" then showParen True ((v++) . (" : "++) . go False a)
                              else go True a
  go p Star = ('*':)
  go _ _    = error "prettyTm"

instance Show Tm where
  showsPrec = prettyTm

instance IsString Tm where
  fromString = Var

--------------------------------------------------------------------------------

-- freeInRaw :: Name -> Raw -> Bool
-- freeInRaw v = go where
--   go (RVar v')     = v' == v
--   go RHole         = False
--   go (RApp f x)    = go f || go x
--   go (RLam v' t)   = v' /= v && go t
--   go (RPi  v' a b) = go a || (v' /= v && go b)
--   go (RAnn t ty)   = go t || go ty
--   go RStar         = False

prettyRaw :: Int -> Raw -> ShowS
prettyRaw prec = go (prec /= 0) where

  unwords' :: [ShowS] -> ShowS
  unwords' = foldr1 (\x acc -> x . (' ':) . acc)

  spine :: Raw -> Raw -> [Raw]
  spine f x = go f [x] where
    go (RApp f y) args = go f (y : args)
    go t          args = t:args

  lams :: String -> Raw -> ([String], Raw)
  lams v t = go [v] t where
    go vs (RLam v t) = go (v:vs) t
    go vs t          = (vs, t)

  go :: Bool -> Raw -> ShowS
  go p (RVar v)      = (v++)
  go p RHole         = ('_':)
  go p (RApp f x)    = showParen p (unwords' $ map (go True) (spine f x))
  go p (RAnn t ty)   = showParen p (go False t . (" : "++) . go False ty)
  go p (RLam v t)    = case lams v t of
    (vs, t) -> showParen p (("λ "++) . (unwords (reverse vs)++) . (". "++) . go False t)
  go p (RPi v a b) = showParen p (arg . (" -> "++) . go False b)
    where arg = if v /= "" then showParen True ((v++) . (" : "++) . go False a)
                              else go True a
  go p RStar = ('*':)

instance Show Raw where
  showsPrec = prettyRaw

instance IsString Raw where
  fromString = RVar  

--------------------------------------------------------------------------------

pi           = RPi
lam          = RLam
star         = RStar
tlam a b     = pi a star b
ann          = flip RAnn
($$)         = RApp
h            = RHole

infixl 9 $$

(==>) a b = pi "" a b
infixr 8 ==>

 
id' =
  ann (pi "a" star $ "a" ==> "a") $
  lam "a" $ lam "x" $ "x"

const' =
  ann (pi "a" star $ pi "b" star $ "a" ==> "b" ==> "a") $
  lam "a" $ lam "b" $ lam "x" $ lam "y" $ "x"

compose =
  ann (tlam "a" $ tlam "b" $ tlam "c" $
       ("b" ==> "c") ==> ("a" ==> "b") ==> "a" ==> "c") $
  lam "a" $ lam "b" $ lam "c" $
  lam "f" $ lam "g" $ lam "x" $
  "f" $$ ("g" $$ "x")


test =
  ann
  -- type declarations
  (pi "id"    (tlam "a" $ "a" ==> "a") $
   star
  )
  -- program
  (lam "id" $
   "id" $$ h $$ star
  )
  -- declaration definitions
  $$ (lam "a" $ lam "x" $ "x")

test2 =
  ann  
  (
  pi "f" (tlam "a" $ tlam "b" $ "a" ==> "b") $
  star
  )(
  lam "f" $
  "f" $$ h $$ h $$ "f"
  )

test3 =
  ann  
  (
  pi "id" (tlam "a" $ "a" ==> "a") $
  pi "f" h $
  h
  )(
  lam "id" $
  lam "f" $
  "id" $$ h $$ "id"
  )
  
  $$ (lam "a" $ lam "x" "x")

-- "Substitution for metavariable is not a renaming" : actually correct error!
test4 =
  ann  
  (
  pi "x" h $
  pi "y" h $ -- would have to solve "?1 [*] = *", which isn't pattern!
  h          -- it would work with explicit non-dependent function space
  )(         -- can we add that since * : * and we're parametric, ?1 = \_ -> *
  lam "x" $  -- in other words, types are irrelevant.
  lam "y" $  -- anyway, we'd need the type-directed unif version for this
  star
  )
  $$ star
  $$ star

test5 =
  ann  
  (
  pi "a" star $
  pi "b" star $
  pi "f" ("a" ==> "b") $
  pi "x" "a" $
  pi "ap" (pi "a" h $ pi "b" ("a" ==> h) $ pi "f" (pi "x" h $ "b" $$ "x") $ pi "x" h $ "b" $$ "x") $
  star          
  )(
  lam "a" $
  lam "b" $
  lam "f" $
  lam "x" $
  lam "ap" $
  star
  )

test6 = (pi "a" h $ pi "b" ("a" ==> h) $ pi "f" (pi "x" h $ "b" $$ "x") $ pi "x" h $ "b" $$ "x")


-- ap : (A : _)(B : A -> _)(f : (a : _) -> B a)(a : _) -> b a

  

-- test =
--   ann

--   -- type declarations
--   (pi "id"    (tlam "a" $ "a" ==> "a") $
--    pi "const" (tlam "a" $ tlam "b" $ "a" ==> "b" ==> "a") $
--    star
--   )

--   -- program
--   (lam "id" $
--    lam "const" $
--    "const" $$ h $$ h $$ star $$ star
--   )

--   -- declaration definitions
--   $$ (lam "a" $ lam "x" $ "x")
--   $$ (lam "a" $ lam "b" $ lam "x" $ lam "y" $ "x")


