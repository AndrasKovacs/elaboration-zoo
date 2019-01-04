
{-# language OverloadedStrings, UnicodeSyntax, LambdaCase,
             ViewPatterns, NoMonomorphismRestriction #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

{- Minimal bidirectional dependent type checker with type-in-type. Related to Coquand's
   algorithm. #-}

module MinimalTC where

import Prelude hiding (all)

import Data.String
import Data.Maybe
import Control.Monad

type Name = String
type Ty   = Tm
type Raw  = Tm

data Tm
  = Var Name           -- x
  | Lam Name Tm        -- \x. t
  | App Tm Tm          -- t u
  | U                  -- U
  | Pi Name Ty Ty      -- (x : A) -> B
  | Let Name Ty Tm Tm  -- let x : A = t in u
  deriving Show

data Val
  = VVar Name
  | VApp Val Val
  | VLam Name (Val -> Val)
  | VPi Name Val (Val -> Val)
  | VU

type Bind a = (Name, a)
type Sub  a = [Bind a]
type Env    = [(Name, Maybe Val)]

-- An better implementation would just use de Bruijn indices for
-- conversion checking and quoting, instead of inventing names.
-- We stick to names for simplicity.
inventName :: Env -> Name -> Name
inventName env "_" = "_"
inventName env x = case lookup x env of
  Just _  -> inventName env (x ++ "'")
  Nothing -> x

eval :: Env -> Tm -> Val
eval env = \case
  Var x       -> maybe (VVar x) id (fromJust $ lookup x env)
  App t u     -> case (eval env t, eval env u) of
                   (VLam _ t, u) -> t u
                   (t       , u) -> VApp t u
  Lam x t     -> VLam x (\u -> eval ((x, Just u):env) t)
  Pi x a b    -> VPi x (eval env a) (\u -> eval ((x, Just u):env) b)
  Let x _ t u -> eval ((x, Just (eval env t)):env) u
  U           -> VU

quote :: Env -> Val -> Tm
quote env = \case
  VVar x   -> Var x
  VApp t u -> App (quote env t) (quote env u)
  VLam (inventName env -> x) t -> Lam x (quote ((x, Nothing):env) (t (VVar x)))
  VPi (inventName env -> x) a b ->
    Pi x (quote env a) (quote ((x, Nothing):env) (b (VVar x)))
  VU -> U

nf :: Env -> Tm -> Tm
nf env = quote env . eval env

nf0 :: Tm -> Tm
nf0 = nf []

-- | Beta-eta conversion checking
conv :: Env -> Val -> Val -> Bool
conv env t u = case (t, u) of
  (VU, VU) -> True

  (VPi (inventName env -> gx) a b, VPi x' a' b') ->
    conv env a a' && conv ((gx, Nothing):env) (b (VVar gx)) (b' (VVar gx))

  (VLam (inventName env -> gx) t, VLam x' t') ->
    conv ((gx, Nothing):env) (t (VVar gx)) (t' (VVar gx))

  -- checking eta conversion for Lam
  (VLam (inventName env -> gx) t, u) ->
    conv ((gx, Nothing):env) (t (VVar gx)) (VApp u (VVar gx))
  (u, VLam (inventName env -> gx) t) ->
    conv ((gx, Nothing):env) (VApp u (VVar gx)) (t (VVar gx))

  (VVar x  , VVar x'   ) -> x == x'
  (VApp t u, VApp t' u') -> conv env t t' && conv env u u'

  _ -> False

type VTy = Val

-- Val here is a value for types of name
type Cxt = [(Name, VTy)]
type M = Either String

check :: Env -> Cxt -> Raw -> VTy -> M ()
check env cxt t a = case (t, a) of
  (Lam x t, VPi (inventName env -> gx) a b) ->
    check ((x, Just (VVar gx)):env) ((x, a):cxt) t (b (VVar gx))

  (Let x a' t' u, _) -> do
    check env cxt a' VU
    let a'' = eval env a'
    check env cxt t' a''
    check ((x, Just (eval env t')):env) ((x, a''):cxt) u a

  _ -> do
    tty <- infer env cxt t
    unless (conv env tty a) $
      Left ("type mismatch:\nexpected:\n" ++ show (quote env a) ++
            "\ninferred:\n" ++ show (quote env tty))

infer :: Env -> Cxt -> Raw -> M VTy
infer env cxt = \case
  Var "_" -> Left "_ is not a valid name"
  Var x   -> maybe (Left ("var not in scope: " ++ x)) Right (lookup x cxt)
  U       -> pure VU

  App t u -> do
    tty <- infer env cxt t
    case tty of
      VPi _ a b -> do
        check env cxt u a
        pure (b (eval env u)) -- important: "eval env u" should be lazy
      _ -> Left "expected a function type"

  Lam{} -> Left "can't infer type for lambda"

  Pi x a b -> do
    check env cxt a VU
    check ((x, Nothing):env) ((x, eval env a):cxt) b VU
    pure VU

  Let x a t u -> do
    check env cxt a VU
    let a' = eval env a
    check env cxt t a'
    infer ((x, Just (eval env t)):env) ((x, a'):cxt) u

infer0 :: Tm -> IO ()
infer0 t =
  either putStrLn print (quote [] <$> infer [] [] t)

unsafeNf0 :: Tm -> IO ()
unsafeNf0 t = infer0 t >> print (nf0 t)

-- Syntactic sugar for inputting terms
------------------------------------------------------------

instance IsString Tm where
  fromString = Var

(∙) = App
infixl 6 ∙

(==>) a b = Pi "_" a b
infixr 4 ==>

(↦) ∷ Name → Tm → Tm
(↦) = Lam
infixr 0 ↦

all x b = Pi x U b

-- Example (try "nf0 test" or "infer0 test")
------------------------------------------------------------

test =
  Let "id" (all "a" $ "a" ==> "a")
    ("a" ↦ "x" ↦ "x") $

  Let "const" (all "a" $ all "b" $ "a" ==> "b" ==> "a")
    ("a" ↦ "b" ↦ "x" ↦ "y" ↦ "x") $

  Let "nat" U
    (all "n" $ ("n" ==> "n") ==> "n" ==> "n") $
    -- (N : U) → (N → N) → N → N

  Let "zero" "nat"
    (Lam "n" $ Lam "s" $ Lam "z" "z") $
    -- λ N s z . z

  Let "suc" ("nat" ==> "nat")
    (Lam "a" $ Lam "n" $ Lam "s" $ Lam "z" $ "s" ∙ ("a" ∙ "n" ∙ "s" ∙ "z")) $
    -- λ (a : Nat) N s z. s (a N s z)

  Let "four" "nat"
    ("suc" ∙ ("suc" ∙ ("suc" ∙ ("suc" ∙ "zero")))) $

  Let "mul" ("nat" ==> "nat" ==> "nat")
    (Lam "a" $ Lam "b" $ Lam "n" $ Lam "s" $
       Lam "z" $ "a" ∙ "n" ∙ ("b" ∙ "n" ∙ "s") ∙ "z") $

  Let "bool" U (all "b" $ "b" ==> "b" ==> "b") $

  Let "true"  "bool" ("b" ↦ "t" ↦ "f" ↦ "t") $
  Let "false" "bool" ("b" ↦ "t" ↦ "f" ↦ "f") $

  "mul" ∙ ("mul" ∙ "four" ∙ "four") ∙ ("mul" ∙ "four" ∙ "four")
