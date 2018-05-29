{-# language OverloadedStrings, UnicodeSyntax, LambdaCase,
             TupleSections, StandaloneDeriving, PatternSynonyms,
             ViewPatterns, NoMonomorphismRestriction #-}

{-# options_ghc -fwarn-incomplete-patterns #-}

module DepTCHoles where

import Prelude hiding (all)

import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Foldable hiding (all)
import Data.List hiding (all)
import Data.Maybe
import Data.String
import qualified Data.IntMap.Strict as M
import Debug.Trace

type Name = String
type Ty   = Tm

data Raw
  = RVar Name
  | RLam Name Raw
  | RApp Raw Raw
  | RU
  | RPi Name Raw Raw
  | RLet Name Raw Raw Raw
  | RHole
  deriving Show

type Meta = Int
type MCxt = M.IntMap Val -- megoldatlan meta: nincs benne a környezetben

data Tm
  = Var Name
  | Lam Name Tm
  | App Tm Tm
  | U
  | Pi Name Ty Ty
  | Let Name Ty Tm Tm
  | Meta Meta

data Head = HMeta Meta | HVar Name deriving Eq

data Val
  = VNe Head [Val] -- [Val] : spine in reversed order
  | VLam Name (Val -> M Val)
  | VPi Name Val (Val -> M Val)
  | VU

type Bind a = (Name, a)
type Sub  a = [Bind a]
type Env    = [(Name, Maybe Val)]

pattern VVar :: Name -> Val
pattern VVar x = VNe (HVar x) []

pattern VMeta :: Meta -> Val
pattern VMeta m = VNe (HMeta m) []

vapp :: Val -> Val -> M Val
vapp (VLam _ t) u = t u
vapp (VNe h sp) u = pure (VNe h (u:sp)) -- building spine in reverse order
vapp _          _ = error "impossible"

eval :: Env -> Tm -> M Val
eval env = \case
  Var x    -> maybe (pure $ VVar x) force (fromJust $ lookup x env)
  Meta m   -> force (VMeta m)
  App t u  -> join (vapp <$> eval env t <*> eval env u)
  Lam x t  -> pure (VLam x (\u -> eval ((x, Just u):env) t))
  Pi x a b -> VPi x <$> eval env a <*> pure (\u -> eval ((x, Just u):env) b)
  Let x _ t u -> do
    t' <- eval env t
    eval ((x, Just t'):env) u
  U -> pure VU

quoteHead :: Head -> Tm
quoteHead = \case HMeta m -> Meta m; HVar x -> Var x

quote :: Env -> Val -> M Tm
quote env t = force t >>= \case
  VNe h sp ->
    foldrM (\v acc -> App acc <$> quote env v) (quoteHead h) sp
  VLam (inventName env -> x) t ->
    Lam x <$> (quote ((x, Nothing):env) =<< t (VVar x))
  VPi (inventName env -> x) a b ->
    Pi x <$> quote env a <*> (quote ((x, Nothing):env) =<< b (VVar x))
  VU -> pure U

nf :: Env -> Tm -> M Tm
nf env = quote env <=< eval env

nf₀ :: Tm -> M Tm
nf₀ = nf []

inventName :: Env -> Name -> Name
inventName env "_" = "_"
inventName env x = case lookup x env of
  Just _  -> inventName env (x ++ "'")
  Nothing -> x

type M = StateT (Int, MCxt) (Either String)

instMeta :: Meta -> M (Maybe Val)
instMeta m = gets (M.lookup m . snd)

force :: Val -> M Val
force t@(VNe (HMeta m) sp) = do
  instMeta m >>= \case
    Just t -> force =<< foldrM (flip vapp) t sp
    _      -> pure t
force t = pure t

-- pattern condition
-- α : metavar
-- [σ] : spine
-- α [σ]            (means "VNe (Meta α) σ")
-- α [σ] =? t       (=? means unify)

-- solvable with α := λ σ. t if:
--    1. σ only consists of variables
--    2. ∀ x ∈ FV(t) → x ∈! σ           -- scope & linearity check
--    3. α ∉ MetaVars(t)                -- occurs check

-- Note : we ignore nonlinear spines now

-- examples:
--   valid     : α x y =? x         α := λ x y. x
--   nonlinear : α x x =? x         α := λ x x. x   (but we accept it now)
--   invalid   : α (λ x. x) y =? y

checkSp :: [Val] -> M [Name]
checkSp = mapM $ force >=>
  \case VVar x -> pure x
        _      -> throwError "non-variable value in meta spine"

-- Check the *normal* form of rhs.
-- Since normal forms don't have shadowing, we don't need the environment.
checkRhs :: Meta -> [Name] -> Tm -> M ()
checkRhs m' sp' = go sp' where
  go :: [Name] -> Tm -> M ()
  go sp' = \case
    Var x    -> unless (elem x sp') $ do
      traceShowM ("scope error", m', sp', x)
      throwError "solution scope error"
    App t u  -> go sp' t >> go sp' u
    Lam x t  -> go (x:sp') t
    Pi x a b -> go sp' a >> go (x:sp') b
    U        -> pure ()
    Meta m   -> when (m == m') $ do
      traceShowM (m', m, sp')
      throwError "occurs check"
    Let{}    -> error "impossible"

solve :: Env -> Meta -> [Val] -> Val -> M ()
solve env m sp t = do
  sp <- checkSp sp
  t <- quote env t
  checkRhs m sp t
  rhs <- eval [] (foldl (flip Lam) t sp)
    -- this only converts the outermost
    -- Lam to VLam if we have nonempty
    -- spine
  modify (\(i, mcxt) -> (i, M.insert m rhs mcxt))

newMeta :: Env -> M Tm
newMeta env = do
  let sp = map Var (nub [x | (x, Nothing) <- env])
  -- nub removes shadowed names from spine
  -- spine happens to be in correct order
  -- opaque example:
  -- [z, x, y, z] ~ {z, y, x, z}
  -- α [z, x, y]  ~ α y x z
  (i, mcxt) <- get
  put (i + 1, mcxt)
  pure (foldr (flip App) (Meta i) sp)

-- unify env t u: unify t and u
-- if returns successfully,
-- then it will be the case that t and u are beta-eta convertible in the
-- new metacontext

unify :: Env -> Val -> Val -> M ()
unify env t u = do
  t <- force t
  u <- force u
  case (t, u) of
    (VLam (inventName env -> gx) t, VLam x' t') ->
      join (unify ((gx, Nothing):env) <$> t (VVar gx) <*> t' (VVar gx))
    (VLam (inventName env -> gx) t, u) ->
      join (unify ((gx, Nothing):env) <$> t (VVar gx) <*> vapp u (VVar gx))
    (u, VLam (inventName env -> gx) t) ->
      join (unify ((gx, Nothing):env) <$> vapp u (VVar gx) <*> t (VVar gx))
    (VPi (inventName env -> gx) a b, VPi x' a' b') -> do
      unify env a a'
      join (unify ((gx, Nothing):env) <$> b (VVar gx) <*> b' (VVar gx))
    (VU, VU) -> pure ()
    (VNe (HMeta m) sp, t) -> solve env m sp t
    (t, VNe (HMeta m) sp) -> solve env m sp t
    (VNe h sp, VNe h' sp') -> do
      unless (h == h') $ throwError "heads not equal"
      zipWithM_ (unify env) sp sp'
    _ -> throwError "can't unify"

type VTy = Val
type Cxt = Sub VTy

-- when we elaborate, this becomes: Env -> Cxt -> Raw -> VTy -> M Tm
check :: Env -> Cxt -> Raw -> VTy -> M Tm
check env cxt t a = case (t, a) of
  (RLam x t, VPi (inventName env -> gx) a b) ->
    Lam x <$> (check ((x, Just (VVar gx)):env) ((x, a):cxt) t =<< b (VVar gx))
  (RLet x a' t' u, _) -> do
    a'   <- check env cxt a' VU
    ~a'' <- eval env a'
    t'   <- check env cxt t' a''
    ~t'' <- eval env t'
    u    <- check ((x, Just t''):env) ((x, a''):cxt) u a
    pure $ Let x a' t' u
  _ -> do
    (t, tty) <- infer env cxt t
    unify env tty a
    pure t

infer :: Env -> Cxt -> Raw -> M (Tm, VTy)
infer env cxt = \case
  RVar "_" -> throwError "_ is not a valid name"
  RVar x   -> maybe (throwError ("var not in scope: " ++ x))
                    (\a -> pure (Var x, a))
                    (lookup x cxt)
  RU -> pure (U, VU)

  RApp t u -> do
    (t, tty) <- infer env cxt t
    force tty >>= \case
      VPi _ a b -> do
        u <- check env cxt u a
        ~u' <- eval env u
        ~bu' <- b u'
        pure (App t u, bu')
      _ -> throwError "expected a function type"

  -- only inferable with metas
  RLam x t -> do
    a <- eval env =<< newMeta env
    (t, b) <- infer ((x, Nothing):env) ((x, a):cxt) t
    -- here it's not very efficient because we fully normalize with
    -- quote
    -- in "industrial strength implementation": eval computes two kinds of
    -- Val at the same time: a) regular Val b) values where in-scope definitions
    -- are not unfolded. (Glued evaluator)
    b <- quote ((x, Nothing):env) b
    pure (Lam x t, VPi x a $ \u -> eval ((x, Just u):env) b)

  RPi x a b -> do
    a <- check env cxt a VU
    ~a' <- eval env a
    b <- check ((x, Nothing):env) ((x, a'):cxt) b VU
    pure (Pi x a b, VU)

  RHole -> do
    a <- newMeta env
    b <- eval env =<< newMeta env
    pure (a, b)

  RLet x a t u -> do
    a <- check env cxt a VU
    ~a' <- eval env a
    t <- check env cxt t a'
    ~t' <- eval env t
    (u, uty) <- infer ((x, Just t'):env) ((x, a'):cxt) u
    pure (Let x a t u, uty)

infer0 :: Raw -> IO ()
infer0 t = do
  case evalStateT (do {(_, a) <- infer [] [] t; quote [] a}) (0, mempty) of
    Left e  -> putStrLn e
    Right a -> print a

nf0 :: Raw -> IO ()
nf0 t = do
  case evalStateT (do {(t, _) <- infer [] [] t; nf [] t})
                  (0, mempty) of
    Left e  -> putStrLn e
    Right t -> print t

------------------------------------------------------------

prettyTm ∷ Int → Tm → ShowS
prettyTm prec = go (prec /= 0) where

  bracket ∷ ShowS → ShowS
  bracket s = ('{':).s.('}':)

  goArg ∷ Tm → ShowS
  goArg t = go True t

  goPiBind ∷ Name → Tm → ShowS
  goPiBind x a =
    showParen True ((x++) . (" : "++) . go False a)

  goLamBind ∷ Name → ShowS
  goLamBind x = (x++)

  goLam ∷ Tm → ShowS
  goLam (Lam x t) = (' ':) . goLamBind x . goLam t
  goLam t         = (". "++) . go False t

  goPi ∷ Bool → Tm → ShowS
  goPi p (Pi x a b)
    | x /= "_" = goPiBind x a . goPi True b
    | otherwise =
       (if p then (" → "++) else id) .
       go (case a of App{} → False; _ → True) a .
       (" → "++) . go False b
  goPi p t = (if p then (" → "++) else id) . go False t

  go ∷ Bool → Tm → ShowS
  go p = \case
    Var x → (x++)

    App (App t u) u' →
      showParen p (go False t . (' ':) . goArg u . (' ':) . goArg u')

    App t u  → showParen p (go True t . (' ':) . goArg u)
    Lam x t  → showParen p (("λ "++) . goLamBind x . goLam t)
    Pi x a b → showParen p (goPi False (Pi x a b))

    Let x a t u →
      ("let "++) . (x++) . (" : "++) . go False a . ("\n    = "++)
      . go False t  . ("\nin\n"++) . go False  u
    U      → ('*':)
    Meta m → (("?"++).(show m++))

instance Show Tm where showsPrec = prettyTm
-- deriving instance Show Tm

------------------------------------------------------------

instance IsString Raw where
  fromString = RVar

(∙) = RApp
infixl 6 ∙

(==>) a b = RPi "_" a b
infixr 4 ==>

(↦) ∷ Name → Raw -> Raw
(↦) = RLam
infixr 0 ↦
all x b = RPi x RU b
make = RLet
u = RU
h = RHole

test =
  make "id" (all "a" $ "a" ==> "a")
    ("a" ↦ "x" ↦ "x") $

  make "const" (all "a" $ all "b" $ "a" ==> "b" ==> "a")
    ("a" ↦ "b" ↦ "x" ↦ "y" ↦ "x") $

  make "nat" u
    (all "n" $ ("n" ==> "n") ==> "n" ==> "n") $

  make "zero" "nat"
    ("n" ↦ "s" ↦ "z" ↦ "z") $

  make "suc" ("nat" ==> "nat")
    ("a" ↦ "n" ↦ "s" ↦ "z" ↦ "s" ∙ ("a" ∙ "n" ∙ "s" ∙ "z")) $

  make "four" "nat"
    ("suc" ∙ ("suc" ∙ ("suc" ∙ ("suc" ∙ "zero")))) $

  make "mul" ("nat" ==> "nat" ==> "nat")
    ("a" ↦ "b" ↦ "n" ↦ "s" ↦ "z" ↦
       ("a" ∙ "n" ∙ ("b" ∙ "n" ∙ "s") ∙ "z")) $

  "id" ∙ h ∙ "four"

  -- id : {A : Set} -> A -> A
  -- id t   ~>   id {α} t   ~> id {u} t

  -- Let "prod" (U ==> U ==> U)
  --   ("a" ↦ "b" ↦ Sg "_" "a" "b") $a

  -- Let "bool" U (all "b" $ "b" ==> "b" ==> "b") $

  -- Let "true"  "bool" ("b" ↦ "t" ↦ "f" ↦ "t") $
  -- Let "false" "bool" ("b" ↦ "t" ↦ "f" ↦ "f") $

  -- Let "either" (U ==> U ==> U)
  --   ("a" ↦ "b" ↦ Sg "x" "bool" ("x" ∙ U ∙ "a" ∙ "b")) $

  -- Let "left" (all "a" $ all "b" $ "a" ==> "either" ∙ "a" ∙ "b")
  --   ("a" ↦ "b" ↦ "x" ↦ Pair "true" "x") $

  -- Let "right" (all "a" $ all "b" $ "b" ==> "either" ∙ "a" ∙ "b")
  --   ("a" ↦ "b" ↦ "x" ↦ Pair "false" "x") $
