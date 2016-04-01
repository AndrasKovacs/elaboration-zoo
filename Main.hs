{-# language LambdaCase, OverloadedStrings, BangPatterns, ViewPatterns #-}

import Prelude hiding (pi)

import Control.Monad
import Data.Maybe
import qualified Data.HashMap.Strict as HM
import Data.String
import Control.Monad.State.Strict
import Control.Monad.Except
import Data.Either

import TCBE.Syntax (RawTerm)
import qualified TCBE.Syntax as S
import Text.Show
import Data.Bifunctor
import Text.Printf
import Debug.Trace

data Term
  = Var !Int
  | App Term Term
  | Lam Term Term
  | Pi Term Term
  | Star

  | Nat
  | Z | S Term
  | NatInd Term Term Term Term  -- NatInd P s z n

  deriving (Eq)

pretty :: Int -> Term -> ShowS
pretty prec = go (prec /= 0) where

  unwords' :: [ShowS] -> ShowS
  unwords' = foldr1 (\x acc -> x . (' ':) . acc)

  spine :: Term -> Term -> [Term]
  spine f x = go f [x] where
    go (App f y) args = go f (y : args)
    go t         args = t:args

  go :: Bool -> Term -> ShowS
  go p (Var i)   = (show i++)
  go p (App f x) = showParen p (unwords' $ map (go True) (spine f x))
  go p (Lam a t) = showParen p (("λ "++) . go True a . (" -> "++) . go False t)
  go p Star      = ('*':)
  go p (Pi a b)  = showParen p (go True a . (" -> "++) . go False b)
  go p Z         = ('Z':)
  go p (S n)     = showParen p $ ("S "++) . go True n
  go p Nat       = ("Nat"++)
  go p (NatInd mot s z n) =
    showParen p $ ("NatInd "++) .
      go True mot . (' ':) . go True s . (' ':) . go True z . (' ':) . go True n


instance Show Term where
  showsPrec = pretty

data Val
  = VVar !Int
  | VApp Val Val
  | VLam Type (Val -> Val)
  | VPi  Type (Val -> Val)
  | VStar

data TC
  = Ret Type
  | CheckPi Type (Val -> Check TC)

type Type = Val
type Cxt = ([Type], [Val], Int)

type Check = Either String

cxt0 :: Cxt
cxt0 = ([], [], 0)

(<:) :: (Type, Val) -> Cxt -> Cxt
(<:) (t, v) (ts, vs, d) = (t:ts, v:vs, d + 1)

(<::) :: Type -> Cxt -> Cxt
(<::) t (ts, vs, d) = (t:ts, VVar d:vs, d + 1)

lookupTy :: Cxt -> Int -> Type
lookupTy (ts, vs, d) i = ts !! (d - i - 1)

lookupVal :: Cxt -> Int -> Type
lookupVal (ts, vs, d) i = vs !! (d - i - 1)

($$) :: Val -> Val -> Val
($$) (VLam _ f) x = f x
($$) f          x = VApp f x
infixl 9 $$

runTC :: Cxt -> TC -> Check Term
runTC (_, _, d) = go d where
  go d (Ret ty)      = pure $ quote' d ty
  go d (CheckPi a b) = Pi (quote' d a) <$> (go (d + 1) =<< b (VVar d))

showTC :: Cxt -> TC -> String
showTC cxt tc = show $ runTC cxt tc

size (a, b, c) = c

{- Note:

Without nfEval, types in the environment are cached up to whnf.
With nfEval, types should be fully cached.

-}

quote :: Cxt -> Val -> Term
quote (_, _, d) = quote' d

quote' :: Int -> Val -> Term
quote' d = \case
  VVar i   -> Var i
  VApp f x -> App (quote' d f) (quote' d x)
  VLam a t -> Lam (quote' d a) (quote' (d + 1) (t (VVar d)))
  VPi  a b -> Pi  (quote' d a) (quote' (d + 1) (b (VVar d)))
  VStar    -> Star

eval :: Cxt -> Term -> Val
eval (ts, vs, d) = go vs d where
  go vs !d = \case
    Var i   -> vs !! (d - i - 1)
    App f x -> go vs d f $$ go vs d x
    Lam a t -> VLam (go vs d a) $ \v -> go (v:vs) (d + 1) t
    Pi  a t -> VPi  (go vs d a) $ \v -> go (v:vs) (d + 1) t
    Star    -> VStar

valEq :: Int -> Val -> Val -> Bool
valEq d a b = go d a b where
  go d (VVar i)   (VVar i')    = i == i'
  go d (VApp f x) (VApp f' x') = go d f f' && go d x x'
  go d (VPi  a t) (VPi  a' t') = go d a a' && go (d + 1) (t (VVar d)) (t' (VVar d))
  go d (VLam a t) (VLam a' t') = go d a a' && go (d + 1) (t (VVar d)) (t' (VVar d))
  go d VStar      VStar        = True
  go _ _          _            = False

tcEq :: Cxt -> Val -> TC -> Check Bool
tcEq (_, _, d) = go d where
  go d (VPi a t) (CheckPi a' t') =
    (&&) (valEq d a a') <$> (go (d + 1) (t (VVar d)) =<< (t' (VVar d)))
  go d t (Ret t') = pure (valEq d t t')
  go _ _ _        = pure False

-- Input is a normal term!
unquote :: Cxt -> Term -> Val
unquote (ts, vs, d) = go [] d where
  go vs !d' = \case
    Var i | i < d     -> VVar i
          | otherwise -> vs !! (d' - i - 1)
    App f x -> go vs d' f $$ go vs d' x
    Lam a t -> VLam (go vs d' a) $ \v -> go (v:vs) (d' + 1) t
    Pi  a t -> VPi  (go vs d' a) $ \v -> go (v:vs) (d' + 1) t
    Star    -> VStar

nfEval :: Cxt -> Term -> Val
nfEval cxt = unquote cxt . quote cxt . eval cxt

check :: Cxt -> Term -> Type -> Check ()
check cxt t ty = do
  let ty' = quote cxt ty
  -- tt <- runTC cxt =<< infer cxt t

  tt <- infer cxt t
  check <- tcEq cxt ty tt

  unless check $ do
    throwError $ printf
      "Can't match expected type for %s: %s with actual type: %s in context: %s"
      (show t) (show ty') (show $ runTC cxt tt) (unlines $ map show $ quoteCxt cxt)

infer :: Cxt -> Term -> Check TC
infer cxt = \case
  Var i   -> pure $ Ret (lookupTy cxt i)
  Star    -> pure $ Ret VStar
  Lam a t -> do
    check cxt a VStar
    let a' = eval cxt a
    pure $ CheckPi a' $ \v -> infer ((a', v) <: cxt) t
  Pi a b -> do
    check cxt a VStar
    check (eval cxt a <:: cxt) b VStar
    pure $ Ret VStar
  App f x -> do
    tf <- infer cxt f
    case tf of
      CheckPi a b -> do
        check cxt x a
        b (eval cxt x)
      Ret (VPi a b) -> do
        check cxt x a
        pure $ Ret $ b (eval cxt x)
      _ -> throwError $
             printf "Can't apply non-function: %s when checking %s"
             (showTC cxt tf) (show $ App f x)

quoteCxt :: Cxt -> [(Term, Term)]
quoteCxt (t:ts, v:vs, d) = (quote cxt' t, quote cxt' v) : quoteCxt cxt'
  where cxt' = (ts, vs, d - 1)
quoteCxt ([], [], 0) = []

infer0 :: Term -> Check Term
infer0 = runTC cxt0 <=< infer cxt0
-- Raw
--------------------------------------------------------------------------------

infer0' :: RawTerm -> Either String Term
infer0' t = runTC cxt0 =<< infer cxt0 (fromRaw t)

eval0 :: RawTerm -> Either String Term
eval0 t = quote cxt0 (eval cxt0 $ fromRaw t) <$ infer0' t

fromRaw :: RawTerm -> Term
fromRaw = go HM.empty 0 where
  go m !d (S.Var v)     = Var (m HM.! v)
  go m d  (S.Lam v a t) = Lam (go m d a) (go (HM.insert v d m) (d + 1) t)
  go m d  (S.Pi  v a t) = Pi  (go m d a) (go (HM.insert v d m) (d + 1) t)
  go m d  (S.App f x)   = App (go m d f) (go m d x)
  go m d  S.Star        = Star

v = S.Var
lam = S.Lam
pi = S.Pi
star = S.Star
forAll v = lam v star
-- nat = S.Con "Nat"
-- natInd =
--   lam "p" (nat ==> star) $
--   lam "s" (pi "n" nat $ ("p" $: "n") ==> "p" $: (s $: "n")) $
--   lam "z" ("p" $: z) $
--   lam "n" nat $
--   S.Con "NatInd" ["p", "s", "z", "n"]


($:) :: RawTerm -> RawTerm -> RawTerm
($:) = S.App
infixl 9 $:

(==>) :: RawTerm -> RawTerm -> RawTerm
a ==> b = pi "" a b
infixr 8 ==>

id' = forAll "a" $ lam "x" "a" $ "x"
const' = forAll "a" $ forAll "b" $ lam "x" "a" $ lam "y" "b" $ "x"

foo = forAll "a" $ lam "x" "a" $ "x"

bar = forAll "a" $ forAll "b" $ forAll "c" $ forAll "d" $ star

-- natId = lam "a" cnat $ "a"

compose =
  forAll "a" $
  forAll "b" $
  forAll "c" $
  lam "f" ("b" ==> "c") $
  lam "g" ("a" ==> "b") $
  lam "x" "a" $
  "f" $: ("g" $: "x")

-- cnat = pi "r" star $ ("r" ==> "r") ==> "r" ==> "r"
-- z = forAll "r" $ lam "s" ("r" ==> "r") $ lam "z" "r" $ "z"
-- s = lam "a" cnat $ forAll "r" $ lam "s" ("r" ==> "r") $
--   lam "z" "r" $ "s" $: ("a" $: "r" $: "s" $: "z")

-- add = lam "a" cnat $ lam "b" cnat $ forAll "r" $ lam "s" ("r" ==> "r") $
--       lam "z" "r" $ "a" $: "r" $: "s" $: ("b" $: "r" $: "s" $: "z")

-- five = s $: (s $: (s $: (s $: (s $: z))))

-- ten = add $: five $: five
-- hundred = mul $: ten $: ten

-- mul = lam "a" cnat $ lam "b" cnat $ forAll "r" $ lam "s" ("r" ==> "r") $
--       "a" $: "r" $: ("b" $: "r" $: "s")

-- nfun = lam "n" cnat $ "n" $: star $: (lam "t" star $ star ==> "t") $: star

-- -- Should not evaluate the huge number (and it doesn't)
-- lazy1 = nfun $: (mul $: hundred $: (mul $: hundred $: hundred))
-- nfunny = lam "n" cnat $ lam "f" (nfun $: "n") $ star

-- list = forAll "a" $ pi "r" star $ ("a" ==> "r" ==> "r") ==> "r" ==> "r"

-- nil = forAll "a" $ forAll "r" $ lam "c" ("a" ==> "r" ==> "r") $ lam "n" "r" $ "n"


-- nils  = nil $: star
-- conss x xs = cons $: star $: x $: xs

-- cons =
--   forAll "a" $
--   lam "x" "a" $
--   lam "as" (list $: "a") $
--   forAll "r" $ lam "c" ("a" ==> "r" ==> "r") $ lam "n" "r" $
--   "c" $: "x" $: ("as" $: "r" $: "c" $: "n")

-- test1 = (lam "f" (pi "x" star $ "x" ==> "x") $ "f") $: (forAll "a" $ lam "x" "a" $ "x")
-- test2 = (lam "f" (pi "x" star $ "x" ==> "x") $ lam "y" star $ "f") $: (forAll "a" $ lam "x" "a" $ "x")

-- test = all (isRight . infer0') [
--   id', const', five, add, cnat, mul, compose,
--   test1, test2, list, nil, conss star $ conss (star ==> star) nils,
--   nfun $: (s $: z), nfunny, nfunny $: ten]

-- hundredK = mul $: ten $: (mul $: hundred $: hundred)

-- nfShare =
--   let' "t" star (nfun $: hundredK) $
--   lam "x" "t" $
--   cons $: "t" $: "x" $:
--   (cons $: "t" $: "x" $:
--   (cons $: "t" $: "x" $:
--   (cons $: "t" $: "x" $:
--   (cons $: "t" $: "x" $:
--   (cons $: "t" $: "x" $:
--    (nil $: "t"))))))

-- main = print $ isRight $ infer0' nfShare

