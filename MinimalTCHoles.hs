{-# language
  OverloadedStrings, UnicodeSyntax, LambdaCase, TupleSections,
  StandaloneDeriving, PatternSynonyms, ViewPatterns,
  NoMonomorphismRestriction, EmptyCase #-}

{-# options_ghc -Wall -Wno-unused-matches -Wno-name-shadowing
                -Wno-missing-signatures #-}

{-| Minimal implementation of an elaborator with holes and pattern unification -}

module MinimalTCHoles where

import Prelude hiding (all)

import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Foldable hiding (all)
import Data.List hiding (all)
import Data.Maybe
import Data.String
import qualified Data.IntMap.Strict as M

type Name = String
type Ty   = Tm

-- | Elaboration input contains holes which are filled in the output.
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

-- | An unsolved meta is just a meta which isn't contained in 'MCxt'.
type MCxt = M.IntMap Val
type M = StateT (Int, MCxt) (Either String)

data Tm
  = Var Name
  | Lam Name Tm
  | App Tm Tm
  | U
  | Pi Name Ty Ty
  | Let Name Ty Tm Tm
  | Meta Meta

data Head = HMeta Meta | HVar Name deriving Eq

-- | We use a spine form for neutral values, because we want to see immediately
--   whether a neutral is headed by a meta.
data Val
  = VNe Head [Val]
  | VLam Name (Val -> Val)
  | VPi Name Val (Val -> Val)
  | VU

type Bind a = (Name, a)
type Sub  a = [Bind a]
type Vals   = [(Name, Maybe Val)]

pattern VVar :: Name -> Val
pattern VVar x = VNe (HVar x) []

pattern VMeta :: Meta -> Val
pattern VMeta m = VNe (HMeta m) []

inventName :: Vals -> Name -> Name
inventName vs "_" = "_"
inventName vs x = case lookup x vs of
  Just _  -> inventName vs (x ++ "'")
  Nothing -> x

force :: MCxt -> Val -> Val
force ms = \case
  VNe (HMeta m) sp | Just t <- M.lookup m ms ->
    force ms (foldr (flip vApp) t sp)
  v -> v

forceM :: Val -> M Val
forceM v = gets (\(_, ms) -> force ms v)

vApp :: Val -> Val -> Val
vApp (VLam _ t) u = t u
vApp (VNe h sp) u = VNe h (u:sp)
vApp _          _ = error "impossible"

eval :: MCxt -> Vals -> Tm -> Val
eval ms = go where
  go vs = \case
    Var x       -> maybe (VVar x) id (fromJust $ lookup x vs)
    Meta m      -> maybe (VMeta m) id (M.lookup m ms)
    App t u     -> vApp (go vs t) (go vs u)
    Lam x t     -> VLam x (\u -> go ((x, Just u):vs) t)
    Pi x a b    -> VPi x (go vs a) (\u -> go ((x, Just u):vs) b)
    Let x _ t u -> go ((x, Just (go vs t)):vs) u
    U           -> VU

evalM :: Vals -> Tm -> M Val
evalM vs t = gets (\(_, ms) -> eval ms vs t)

quote :: MCxt -> Vals -> Val -> Tm
quote ms = go where
  go vs v = case force ms v of
    VNe h sp -> foldr (\v acc -> App acc (go vs v))
                      (case h of HMeta m -> Meta m; HVar x -> Var x)
                      sp
    VLam (inventName vs -> x) t ->
      Lam x (go ((x, Nothing):vs) (t (VVar x)))
    VPi (inventName vs -> x) a b ->
      Pi x (go vs a) (go ((x, Nothing):vs) (b (VVar x)))
    VU -> U

quoteM :: Vals -> Val -> M Tm
quoteM vs v = gets $ \(_, ms) -> quote ms vs v

nf :: MCxt -> Vals -> Tm -> Tm
nf ms vs = quote ms vs . eval ms vs

nfM :: Vals -> Tm -> M Tm
nfM vs t = gets $ \(_, ms) -> nf ms vs t

nf₀ :: MCxt -> Tm -> Tm
nf₀ ms = nf ms []

-- | Check that all entries in a spine are bound variables.
checkSp :: [Val] -> M [Name]
checkSp vs = forM vs $ \v -> forceM v >>= \case
  VVar x -> pure x
  _      -> throwError "non-variable value in meta spine"

-- | Check that a solution candidate (in normal form) for a meta is well-scoped.
checkSolution :: Meta -> [Name] -> Tm -> M ()
checkSolution m sp rhs = go sp rhs where
  go :: [Name] -> Tm -> M ()
  go ns = \case
    Var x    -> unless (elem x ns) $
                  throwError ("scope error: " ++ show (m, sp, rhs))
    App t u  -> go ns t >> go ns u
    Lam x t  -> go (x:ns) t
    Pi x a b -> go ns a >> go (x:ns) b
    U        -> pure ()
    Meta m'  -> when (m == m') $
                  throwError ("occurs check: " ++ show (m, rhs))
    Let{}    -> error "impossible"

solve :: Vals -> Meta -> [Val] -> Val -> M ()
solve vs m sp t = do
  sp <- checkSp sp
  t  <- quoteM vs t
  checkSolution m sp t
  rhs <- evalM [] (foldl' (flip Lam) t sp)
  modify (\(i, mcxt) -> (i, M.insert m rhs mcxt))

newMeta :: Vals -> M Tm
newMeta vs = do
  let sp = map Var (nub [x | (x, Nothing) <- vs])
  (i, ms) <- get
  put (i + 1, ms)
  pure (foldr (flip App) (Meta i) sp)

unify :: Vals -> Val -> Val -> M ()
unify = go where
  go vs t u = do
    t <- forceM t
    u <- forceM u
    case (t, u) of
      (VLam (inventName vs -> gx) t, VLam x' t') ->
        go ((gx, Nothing):vs) (t (VVar gx)) (t' (VVar gx))
      (VLam (inventName vs -> gx) t, u) ->
        go ((gx, Nothing):vs) (t (VVar gx)) (vApp u (VVar gx))
      (u, VLam (inventName vs -> gx) t) ->
        go ((gx, Nothing):vs) (vApp u (VVar gx)) (t (VVar gx))
      (VPi (inventName vs -> gx) a b, VPi x' a' b') -> do
        unify vs a a'
        go ((gx, Nothing):vs) (b (VVar gx)) (b' (VVar gx))
      (VU, VU) -> pure ()
      (VNe h sp, VNe h' sp') | h == h' -> zipWithM_ (go vs) sp sp'
      (VNe (HMeta m) sp, t) -> solve vs m sp t
      (t, VNe (HMeta m) sp) -> solve vs m sp t
      _ -> throwError "can't unify"

type VTy   = Val
type Types = Sub VTy

checkShadowing :: Vals -> Name -> M ()
checkShadowing vs "_" = pure ()
checkShadowing vs x =
  maybe (pure ())
        (\_ -> throwError $ "name shadowing not allowed: " ++ show x)
        (lookup x vs)

check :: Vals -> Types -> Raw -> VTy -> M Tm
check vs tys topT topA = case (topT, topA) of
  (RLam x t, VPi (inventName vs -> gx) a b) -> do
    checkShadowing vs x
    Lam x <$> check ((x, Just (VVar gx)):vs) ((x, a):tys) t (b (VVar gx))
  (RLet x a t u, topA) -> do
    checkShadowing vs x
    a  <- check vs tys a VU
    va <- evalM vs a
    t  <- check vs tys t va
    vt <- evalM vs t
    u  <- check ((x, Just vt):vs) ((x, va):tys) u topA
    pure $ Let x a t u
  _ -> do
    (t, va) <- infer vs tys topT
    unify vs va topA
    pure t

infer :: Vals -> Types -> Raw -> M (Tm, VTy)
infer vs tys = \case
  RVar "_" -> throwError "_ is not a valid name"
  RVar x   -> maybe (throwError ("var not in scope: " ++ x))
                    (\a -> pure (Var x, a))
                    (lookup x tys)
  RU -> pure (U, VU)

  RApp t u -> do
    (t, va) <- infer vs tys t
    forceM va >>= \case
      VPi _ a b -> do
        u  <- check vs tys u a
        vu <- evalM vs u
        pure (App t u, b vu)
      _ -> throwError "expected a function type"

  RLam x t -> do
    checkShadowing vs x
    va <- evalM vs =<< newMeta vs
    (t, vb) <- infer ((x, Nothing):vs) ((x, va):tys) t
    b <- quoteM ((x, Nothing):vs) vb
    ms <- gets snd
    pure (Lam x t, VPi x va $ \u -> eval ms ((x, Just u):vs) b)

  RPi x a b -> do
    checkShadowing vs x
    a  <- check vs tys a VU
    va <- evalM vs a
    b <- check ((x, Nothing):vs) ((x, va):tys) b VU
    pure (Pi x a b, VU)

  RHole -> do
    a  <- newMeta vs
    vb <- evalM vs =<< newMeta vs
    pure (a, vb)

  RLet x a t u -> do
    checkShadowing vs x
    a  <- check vs tys a VU
    va <- evalM vs a
    t  <- check vs tys t va
    vt <- evalM vs t
    (u, uty) <- infer ((x, Just vt):vs) ((x, va):tys) u
    pure (Let x a t u, uty)

infer0 :: Raw -> IO ()
infer0 t = do
  case evalStateT (do {(_, a) <- infer [] [] t; quoteM [] a}) (0, mempty) of
    Left e  -> putStrLn e
    Right a -> print a

nf0 :: Raw -> IO ()
nf0 t = do
  case evalStateT (do {(t, _) <- infer [] [] t; nfM [] t})
                  (0, mempty) of
    Left e  -> putStrLn e
    Right t -> print t

elab0 :: Raw -> IO ()
elab0 t =
  case runStateT (infer [] [] t)
                  (0, mempty) of
    Left e             -> putStrLn e
    Right ((t, _), (_, ms)) -> print (zonk ms [] t)

--------------------------------------------------------------------------------

-- | Inline all meta solutions.
zonk :: MCxt -> Vals -> Tm -> Tm
zonk ms = go where
  q = quote ms

  goSp :: Vals -> Tm -> Either Val Tm
  goSp vs = \case
    Meta m | Just v <- M.lookup m ms -> Left v
    App t u -> either (\t -> Left (vApp t (eval ms vs u)))
                      (\t -> Right (App t (go vs u)))
                      (goSp vs t)
    t -> Right (go vs t)

  go :: Vals -> Tm -> Tm
  go vs = \case
    Var x        -> Var x
    Meta m       -> maybe (Meta m) (q vs) (M.lookup m ms)
    U            -> U
    Pi x a b     -> Pi x (go vs a) (go ((x, Nothing):vs) b)
    App t u      -> either (\t -> q vs (vApp t (eval ms vs u)))
                           (\t -> App t (go vs u))
                           (goSp vs t)
    Lam x t      -> Lam x (go ((x, Nothing):vs) t)
    Let x a t u  -> Let x (go vs a) (go vs t)
                          (go ((x, Nothing):vs) u)

prettyTm :: Int -> Tm -> ShowS
prettyTm prec = go (prec /= 0) where

  goArg :: Tm -> ShowS
  goArg t = go True t

  goPiBind :: Name -> Tm -> ShowS
  goPiBind x a =
    showParen True ((x++) . (" : "++) . go False a)

  goLamBind :: Name -> ShowS
  goLamBind x = (x++)

  goLam :: Tm -> ShowS
  goLam (Lam x t) = (' ':) . goLamBind x . goLam t
  goLam t         = (". "++) . go False t

  goPi :: Bool -> Tm -> ShowS
  goPi p (Pi x a b)
    | x /= "_" = goPiBind x a . goPi True b
    | otherwise =
       (if p then (" → "++) else id) .
       go (case a of App{} -> False; _ -> True) a .
       (" → "++) . go False b
  goPi p t = (if p then (" -> "++) else id) . go False t

  go :: Bool -> Tm -> ShowS
  go p = \case
    Var x -> (x++)

    App (App t u) u' ->
      showParen p (go False t . (' ':) . goArg u . (' ':) . goArg u')

    App t u  -> showParen p (go True t . (' ':) . goArg u)
    Lam x t  -> showParen p (("λ "++) . goLamBind x . goLam t)
    Pi x a b -> showParen p (goPi False (Pi x a b))

    Let x a t u ->
      ("let "++) . (x++) . (" : "++) . go False a . ("\n    = "++)
      . go False t  . ("\nin\n"++) . go False  u
    U      -> ('*':)
    Meta m -> (("?"++).(show m++))

instance Show Tm where showsPrec = prettyTm


--------------------------------------------------------------------------------

instance IsString Raw where
  fromString = RVar

(∙) = RApp
infixl 6 ∙

(==>) a b = RPi "_" a b
infixr 4 ==>

(↦) :: Name -> Raw -> Raw
(↦) = RLam
infixr 0 ↦
all x b = RPi x RU b
make = RLet
u = RU
h = RHole

-- elab0 test / nf0 test / infer0 test
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

  "const" ∙ h ∙ h ∙ u ∙ u
