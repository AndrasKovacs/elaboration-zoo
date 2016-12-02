

{-# language
  PatternSynonyms, BangPatterns, MagicHash, PatternGuards,
  DataKinds, LambdaCase, ViewPatterns, TupleSections,
  RecordWildCards,
  TypeFamilies, GADTs, EmptyCase, OverloadedStrings #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

module Metavar where

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

type Env    = [(Name, Val)]
type Cxt    = [(Name, Type)]

type Ren    = HashMap (Either Name Gen) Name
type Type   = Val
data MEntry = MEntry {_ty :: Type, _solution :: !(Maybe Val)}
type MCxt   = IntMap MEntry
data S      = S {_mcxt :: !MCxt, _freshMeta :: !Meta}
type M      = StateT S (Either String)

data Raw
  = RVar !Name
  | RApp !Raw !Raw
  | RLam !Name !Raw
  | RLet !Name !Raw !Raw !Raw
  | RPi !Name !Raw !Raw
  | RStar
  | RHole

data Head
  = VMeta !Meta
  | VVar !Name
  | VGen !Gen

data Val
  = !Head :$ !Env
  | VLam !Name !(Val -> MCxt -> Val)
  | VPi !Name !Val !(Val -> MCxt -> Val)
  | VStar
infix 3 :$

data Tm
  = Var !Name
  | Gen !Gen
  | App !Tm !Tm !Name
  | Lam !Name !Tm
  | Let !Name !Tm !Tm !Tm
  | Pi !Name !Tm !Tm
  | Star
  | Meta !Meta


-- Evaluation
--------------------------------------------------------------------------------

-- | Try to instantiate the top-level head meta recursively until
--   we don't have a meta application at top or the top meta is unsolved.
refresh :: Val -> MCxt -> Val
refresh t !mcxt = go t where
  go (VMeta i :$ sp) | Just t <- _solution $ mcxt IM.! i  =
    go (foldr (\(v, a) t -> vapp t a v mcxt) t sp)
  go t = t

vapp :: Val -> Val -> Name -> MCxt -> Val
vapp t t' v !mcxt = case (t, t') of
  (VLam v t, a) -> t a mcxt
  (h :$ sp , a) -> h :$ ((v, a) : sp)
  _             -> error "vapp: impossible"

-- | Evaluate to weak head normal form in a metacontext.
eval :: Env -> Tm -> MCxt -> Val
eval !vs !t !mcxt = go vs t where
  go vs = \case
    Var v        -> maybe (VVar v :$ []) (flip refresh mcxt) (lookup v vs)
    App f a v    -> vapp (go vs f) (go vs a) v mcxt
    Lam v t      -> VLam v $ \a -> eval ((v, a):vs) t
    Let v e t e' -> eval ((v, eval vs e mcxt):vs) e' mcxt
    Pi v a b     -> VPi v (go vs a) $ \a -> eval ((v, a):vs) b
    Star         -> VStar
    Meta i       -> maybe (VMeta i :$ []) id (_solution $ mcxt IM.! i)
    Gen{}        -> error "eval: impossible Gen"

-- | Fully normalize a weak head normal value in a metacontext.
quote :: Val -> MCxt -> Tm
quote t !mcxt = go t where
  goHead = \case
    VMeta i -> Meta i
    VVar v  -> Var v
    VGen i  -> Gen i
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
invert :: Env -> Either String Ren
invert = foldM go HM.empty where
  go r (v, t) = case t of
    VVar v' :$ [] | HM.member (Left v') r -> pure $ HM.delete (Left v') r
                  | otherwise             -> pure $ HM.insert (Left v') v r
    VGen i  :$ [] | HM.member (Right i) r -> pure $ HM.delete (Right i) r
                  | otherwise             -> pure $ HM.insert (Right i) v r
    _ -> throwError "Substitution for metavariable is not a renaming"

-- | Rename the right hand side of a metavariable equation while
--   checking for occurrence and scoping. TODO: pruning. NOTE: we can only
--   prune variables from metas that don't occur in the sub. We can't prune
--   non-linear variables that do occur (see Abel & Pientka)
--   More on pruning: pruning requires strengtheninh the type of the pruned
--   metavar, which may not be possible because of type dependency.

renameRhs :: Meta -> Ren -> Tm -> Either String Tm
renameRhs occur r = go r where
  go :: Ren -> Tm -> Either String Tm
  go r = \case
    Var v        -> maybe (throwError $ "scope fail") (pure . Var) (HM.lookup (Left v) r)
    Gen i        -> maybe (throwError $ "scope fail") (pure . Var) (HM.lookup (Right i) r)
    App f a v    -> App <$> go r f <*> go r a <*> pure v
    Lam v t      -> Lam v <$> go (HM.insert (Left v) v r) t
    Let v e t e' -> error "renameRhs: impossible"
    Pi v a b     -> Pi v <$> go r a <*> go (HM.insert (Left v) v r) b
    Star         -> pure Star
    Meta i | i == occur -> throwError "occurs fail"
           | otherwise  -> pure (Meta i)

addLams :: Env -> Tm -> Tm
addLams sp t = foldr (Lam . fst) t sp           

-- | Solve a meta by applying the inverse of its substitution to the RHS.
--   It uses full normalization on the RHS, which is costly. Future versions
--   should use "glued" representation which enables various syntactic checks
--   and heuristics.
solveMeta :: Meta -> Env -> Val -> M ()
solveMeta m sp t = do
  ren <- lift $ invert sp
  t   <- quote t <$> gets _mcxt
  !t  <- lift $ addLams sp <$> renameRhs m ren t
  modify $ \s@(S _mcxt _) ->
    s {_mcxt = IM.adjust (\e -> e {_solution = Just $ eval [] t _mcxt}) m _mcxt}

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

      (VVar v  :$ sp, VVar v'  :$ sp') | v == v' -> goEnv g sp sp'
      (VGen i  :$ sp, VGen i'  :$ sp') | i == i' -> goEnv g sp sp'
      (VMeta i :$ sp, VMeta i' :$ sp') | i == i' -> goEnv g sp sp'

      (VMeta i :$ sp, t) -> solveMeta i sp t
      (t, VMeta i :$ sp) -> solveMeta i sp t

      _ -> do
        nt  <- quote t <$> gets _mcxt
        nt' <- quote t' <$> gets _mcxt
        throwError $ "can't unify\n" ++ show nt ++ "\nwith\n" ++  show nt'

  goEnv :: Int -> Env -> Env -> M ()
  goEnv g ((_, a):as) ((_, b):bs) = goEnv g as bs >> go g a b
  goEnv g []          []          = pure ()
  goEnv _ _           _           = error "unify Sp: impossible"


-- Elaboration
--------------------------------------------------------------------------------

-- | Extend a 'Cxt' with an entry. We need to delete shadowed entries,
--   or else substitutions for fresh metas would contain nonsense
--   repeated variables.
ext :: (Name, Type) -> Cxt -> Cxt
ext x cxt = x : deleteBy ((==) `on` fst) x cxt

metaType :: Cxt -> Type -> Type
metaType cxt t = foldl (\t (v, a) -> VPi v a $ \_ _ -> t) t cxt

newMeta :: Cxt -> Type -> M Tm
newMeta cxt ty = do
  S mcxt i <- get
  put $ S (IM.insert i (MEntry (metaType cxt ty) Nothing) mcxt) (i + 1)
  pure $ Meta i

check :: Cxt -> Env ->  Raw -> Type -> M Tm
check cxt env t want = case (t, want) of
  (RLam v t, VPi _ a b) -> do
    mcxt <- gets _mcxt
    Lam v <$> check (ext (v, a) cxt) env t (b (VVar v :$ []) mcxt)
  (RHole, _) ->
    newMeta cxt want
  (t, _) -> do
    want' <- quote want <$> gets _mcxt
    (t, has) <- infer cxt env t
    t <$ unify has want

infer :: Cxt -> Env -> Raw -> M (Tm, Type)
infer cxt env = \case
  RVar v ->
    maybe (throwError $ "Variable: " ++ v ++ " not in scope")
          (\ty -> pure (Var v, ty))
          (lookup v cxt)
  RStar     -> pure (Star, VStar)
  RPi v a b -> do
    a  <- check cxt env a VStar
    a' <- eval env a <$> gets _mcxt
    b  <- check (ext (v, a') cxt) env b VStar
    pure (Pi v a b, VStar)
  RLet v e1 t e2 -> do
    t   <- check cxt env t VStar
    t'  <- eval env t <$> gets _mcxt
    e1  <- check cxt env e1 t'
    e1' <- eval env e1 <$> gets _mcxt
    (e2, te) <- infer cxt ((v, e1') : env) e2
    pure (Let v e1 t e2, te)    
  RApp f a -> do
    (f, tf) <- infer cxt env f
    case tf of
      VPi v ta tb -> do
        a   <- check cxt env a ta
        a'  <- eval env a <$> gets _mcxt
        tb' <- tb a' <$> gets _mcxt
        pure (App f a v, tb')

      -- we would need fresh names or dB indices for splitting metas into functions
      _ -> throwError "can't apply non-function"

  -- here as well
  RLam v t -> do
    throwError $ "can't infer type for lambda: " ++ show (RLam v t)
  RHole -> throwError "can't infer type for hole"

-- | Replace all metas with their normal solutions.
zonk :: Tm -> M Tm
zonk = \case
  Var v        -> pure (Var v)
  Star         -> pure Star
  Pi v a b     -> Pi v <$> zonk a <*> zonk b
  App f a v    -> App <$> zonk f <*> zonk a <*> pure v
  Let v e t e' -> Let v <$> zonk e <*> zonk t <*> zonk e'
  Meta v       -> do
    mcxt <- gets _mcxt
    case _solution $ mcxt IM.! v of
      Just t -> pure (quote t mcxt)
      _      -> pure (Meta v)
  Lam v t -> Lam v <$> zonk t
  _ -> error "zonk"



--------------------------------------------------------------------------------

run0 :: ((Tm, Type) -> M a) -> Raw -> Either String a
run0 act t = evalStateT (infer [] [] t >>= act) (S mempty 0)

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
  go p (Var v)        = (v++)
  go p (Let v e t e') =
    showParen p (go False e . (" : "++) . go False t . ("\n"++) . go False e')
  go p (Meta v)       = showParen p (("?"++).(show v++))
  go p (App f x _)    = showParen p (unwords' $ map (go True) (spine f x))
  go p (Lam v t)      = case lams v t of
    (vs, t) -> showParen p (("\\"++) . (unwords (reverse vs)++) . (". "++) . go False t)
  go p (Pi v a b) = showParen p (arg . (" -> "++) . go False b)
    where arg = if v /= "_" then showParen True ((v++) . (" : "++) . go False a)
                              else go True a
  go p Star = ('*':)
  go _ _    = error "prettyTm"

instance Show Tm where
  showsPrec = prettyTm

instance IsString Tm where
  fromString = Var

--------------------------------------------------------------------------------

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
  go p (RVar v)        = (v++)
  go p (RLet v e t e') =
    showParen p (go False e . (" : "++) . go False t . ("\n"++) . go False e')
  go p RHole           = ('_':)
  go p (RApp f x)      = showParen p (unwords' $ map (go True) (spine f x))
  go p (RLam v t)      = case lams v t of
    (vs, t) -> showParen p (("\\"++) . (unwords (reverse vs)++) . (". "++) . go False t)
  go p (RPi v a b) = showParen p (arg . (" -> "++) . go False b)
    where arg = if v /= "_" then showParen True ((v++) . (" : "++) . go False a)
                              else go True a
  go p RStar = ('*':)

instance Show Raw where
  showsPrec = prettyRaw

instance IsString Raw where
  fromString = RVar


{-

--------------------------------------------------------------------------------

pi           = RPi
lam          = RLam
star         = RStar
tlam a b     = pi a star b
ann          = flip RAnn
($$)         = RApp
h            = RHole

infixl 9 $$

(==>) a b = pi "_" a b
infixr 8 ==>

let' :: Name -> Raw -> Raw -> Raw -> Raw
let' x t e e' = (ann (pi x t $ h) (lam x e')) $$ e

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
  h
  )(
  lam "a" $
  lam "b" $
  lam "f" $
  lam "x" $
  lam "ap" $
  "ap" $$ h $$ h $$ "f" $$ "x"
  )

test6 = (pi "a" h $ pi "b" ("a" ==> h) $ pi "f" (pi "x" h $ "b" $$ "x") $ pi "x" h $ "b" $$ "x")

test7 =
  ann
  (
    pi "a" h $
    pi "f" ("a" ==> "a") $
    "a"
  )
  (
    lam "a" $
    lam "f" $
    (lam "x" $ "f" $$ ("x" $$ "x")) $$ (lam "x" $ "f" $$ ("x" $$ "x"))
  )

test8 =
  ann
  (
  pi "ap" (pi "a" h $ pi "b" ("a" ==> h) $ pi "f" (pi "x" h $ "b" $$ "x") $ pi "x" h $ "b" $$ "x") $
  pi "a" h $
  pi "b" ("a" ==> h) $
  pi "f" (pi "x" h $ "b" $$ "x") $
  pi "x" "a" $
  h
  )(
  lam "ap" $
  lam "a" $
  lam "b" $
  lam "f" $
  lam "x" $
  "ap" $$ h $$ h $$ "f" $$ "x"
  )

test9 =
  ann
  (
  pi "ap" (pi "a" h $ pi "b" ("a" ==> h) $ pi "f" (pi "x" h $ "b" $$ "x") $ pi "x" h $ "b" $$ "x") $
  pi "a" h $
  pi "b" ("a" ==> h) $
  pi "f" (pi "x" h $ "b" $$ "x") $
  pi "x" "a" $
  h
  )(
  lam "ap" $
  lam "a" $
  lam "b" $
  lam "f" $
  lam "x" $
  "ap" $$ h $$ h $$ "f" $$ "x"
  )

test10 =
  let' "id" (tlam "a" $ "a" ==> "a")
            (lam "a" $ lam "x" "x") $
  let' "const" (tlam "a" $ tlam "b" $ "a" ==> "b" ==> "a")
               (lam "a" $ lam "b" $ lam "x" $ lam "y" "x") $
  let' "const'" (tlam "a" $ "a" ==> (tlam "b" $ "b" ==> "a"))
                (lam "a" $ lam "x" $ lam "b" $ lam "y" "x") $
  "const'" $$ h $$ "id"

-- can't depend on value of nat, need true "let"
test11 =
  let' "Nat" star
             (tlam "n" $ ("n" ==> "n") ==> "n") $
  let' "z" "Nat"
           (lam "n" $ lam "s" $ lam "z" "z") $
  "Nat"

test12 =
  ann 
    (pi "A" star $
     pi "B" ("A" ==> star) $
     pi "C" (pi "a" h $ "B" $$ "a" ==> star) $
     pi "f" (pi "a" h $ pi "b" h $ "C" $$ "a" $$ "b") $
     pi "g" (pi "a" h $ "B" $$ "a") $
     pi "a" h $
     "C" $$ h $$ ("g" $$ "a"))
    (lam "A" $ lam "B" $ lam "C" $
     lam "f" $ lam "g" $ lam "a" $ "f" $$ h $$ ("g" $$ "a"))

-- Raw:
-- comp :
--     (A : *)
--  -> (B : A -> *)
--  -> (C : (a : _) -> (B a) -> *)
--  -> (f : (a : _) -> (b : _) -> C a b)
--  -> (g : (a : _) -> B a)
--  -> (a : _) -> C _ (g a)         
-- comp = \A B C f g a. f _ (g a)

-- Elaborated:
-- comp :
--     (A : *)
--  -> (B : A -> *)
--  -> (C : (a : ?0 [B,A]) -> (B a) -> *)
--  -> (f : (a : ?1 [C,B,A]) -> (b : ?2 [a,C,B,A]) -> C a b)
--  -> (g : (a : ?3 [f,C,B,A]) -> B a)
--  -> (a : ?4 [g,f,C,B,A]) -> C (?5 [a,g,f,C,B,A]) (g a)
-- comp = \A B C f g a. f (?6 [a,g,f,C,B,A]) (g a)

-- Zonked
-- comp:
--      (A : *)
--   -> (B : A -> *)
--   -> (C : (a : A) -> (B a) -> *)
--   -> (f : (a : A) -> (b : B a) -> C a b)
--   -> (g : (a : A) -> B a)
--   -> (a : A) -> C a (g a)
-- comp = \A B C f g a. f a (g a) 


-}
