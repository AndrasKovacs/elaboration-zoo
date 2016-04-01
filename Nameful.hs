{-

This version doesn't use de Bruijn names.
The only significant change from dB is that we need to implement
alpha equality explicitly

-}


{-# language BangPatterns, LambdaCase, OverloadedStrings #-}

import Prelude hiding (pi)
import Control.Monad
import Data.Either
import Data.String

import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as HM

data Term
  = Var String
  | App Term Term
  | Lam String Term Term
  | Pi String Term Term
  | Star

data Val
  = VVar String
  | BVar !Int  -- "bound" variable, only used for alpha equality check
  | VApp Val Val
  | VLam String Type (Val -> Val)
  | VPi  String Type (Val -> Val)
  | VStar

data Infer
  = Ok Type
  | InferLam String Type (Val -> TM Infer)

type Type  = Val
type Cxt   = (HashMap String Val, HashMap String Type, Int)
type TM    = Either String

cxt0 :: Cxt
cxt0 = (HM.empty, HM.empty, 0)

(<:) :: (String, Val, Type) -> Cxt -> Cxt
(<:) (k, v, t) (vs, ts, d) = (HM.insert k v vs, HM.insert k t ts, d + 1)

(<::) :: (String, Type) -> Cxt -> Cxt
(<::) (k, t) (vs, ts, d) = (HM.insert k (BVar d) vs, HM.insert k t ts, d + 1)

vapp :: Val -> Val -> Val
vapp (VLam _ _ f) x = f x
vapp f            x = VApp f x

eval :: HashMap String Val -> Term -> Val
eval vs = \case
  Var k     -> vs ! k
  App f x   -> eval vs f `vapp` eval vs x
  Lam k a t -> VLam k (eval vs a) $ \v -> eval (HM.insert k v vs) t
  Pi  k a b -> VPi  k (eval vs a) $ \v -> eval (HM.insert k v vs) b
  Star      -> VStar

quote :: Val -> Term
quote = \case
  VVar i     -> Var i
  VApp f x   -> App (quote f) (quote x)
  VLam k a t -> Lam k (quote a) (quote (t (VVar k)))
  VPi  k a b -> Pi  k (quote a) (quote (b (VVar k)))
  VStar      -> Star

quoteInfer :: Infer -> TM Term
quoteInfer = \case
  Ok t           -> pure $ quote t
  InferLam k a t -> Pi k (quote a) <$> (quoteInfer =<< (t (VVar k)))

-- alpha equality
--------------------------------------------------------------------------------

aeqInfer :: Type -> Infer -> TM Bool
aeqInfer = go 0 where
  go d t (Ok t') = pure $ aeq d t t'
  go d (VPi _ a t) (InferLam _ a' t') =
    (&&) (aeq d a a') <$> (go (d + 1) (t (BVar d)) =<< t' (BVar d))
  go _ _  _ = pure False

aeq :: Int -> Type -> Type -> Bool
aeq d (VVar i)     (VVar i')      = i == i'
aeq d (BVar i)     (BVar i')      = i == i'
aeq d (VApp f x)   (VApp f' x')   = aeq d f f' && aeq d x x'
aeq d (VPi  _ a t) (VPi  _ a' t') = aeq d a a' && aeq (d + 1) (t (BVar d)) (t' (BVar d))
aeq d (VLam _ a t) (VLam _ a' t') = aeq d a a' && aeq (d + 1) (t (BVar d)) (t' (BVar d))
aeq d VStar        VStar          = True
aeq d _            _              = False

-- check / infer
--------------------------------------------------------------------------------

check :: Cxt -> Term -> Type -> TM ()
check cxt@(_, _, d) t expect = do
  eq <- aeqInfer expect =<< infer cxt t
  unless eq $ Left "type mismatch"

infer :: Cxt -> Term -> TM Infer
infer cxt@(vs, ts, d) = \case
  Var i   -> pure $ Ok (ts ! i)
  Star    -> pure $ Ok VStar
  Lam k a t -> do
    check cxt a VStar
    let a' = eval vs a
    pure $ InferLam k a' $ \v -> infer ((k, v, a') <: cxt) t
  Pi k a b -> do
    check cxt a VStar
    check ((k, eval vs a) <:: cxt) b VStar
    pure $ Ok VStar
  App f x ->
    infer cxt f >>= \case
      InferLam k a b -> do
        check cxt x a
        b (eval vs x)
      Ok (VPi k a b) -> do
        check cxt x a
        pure $ Ok $ b (eval vs x)
      _ -> Left "Can't apply non-function"

-- Sugar & examples
--------------------------------------------------------------------------------

pretty :: Int -> Term -> ShowS
pretty prec = go (prec /= 0) where

  unwords' :: [ShowS] -> ShowS
  unwords' = foldr1 (\x acc -> x . (' ':) . acc)

  spine :: Term -> Term -> [Term]
  spine f x = go f [x] where
    go (App f y) args = go f (y : args)
    go t         args = t:args

  go :: Bool -> Term -> ShowS
  go p (Var i)     = (i++)
  go p (App f x)   = showParen p (unwords' $ map (go True) (spine f x))
  go p (Lam k a t) = showParen p
    (("λ "++) . showParen True ((k++) . (" : "++) . go False a) . (" -> "++) . go False t)
  go p (Pi k a b) = showParen p (arg . (" -> "++) . go False b)
    where arg = if freeIn k b then showParen True ((k++) . (" : "++) . go False a)
                              else go True a
  go p Star = ('*':)

  freeIn :: String -> Term -> Bool
  freeIn k = go where
    go (Var i)      = i == k
    go (App f x)    = go f || go x
    go (Lam k' a t) = go a || (k' /= k && go t)
    go (Pi  k' a b) = go a || (k' /= k && go b)
    go _            = False

instance Show Term where
  showsPrec = pretty

instance IsString Term where
  fromString = Var

infer0 :: Term -> TM Term
infer0 = quoteInfer <=< infer cxt0

eval0 :: Term -> TM Term
eval0 t = quote (eval HM.empty t) <$ infer0 t

pi            = Pi
lam           = Lam
star          = Star
forAll a b    = lam a star b
let' k ty x e = lam k ty e $$ x
infixl 9 $$
($$) = App

(==>) a b = pi "" a b
infixr 8 ==>

id'    = forAll "a" $ lam "x" "a" $ "x"
const' = forAll "a" $ forAll "b" $ lam "x" "a" $ lam "y" "b" $ "x"

compose =
  forAll "a" $
  forAll "b" $
  forAll "c" $
  lam "f" ("b" ==> "c") $
  lam "g" ("a" ==> "b") $
  lam "x" "a" $
  "f" $$ ("g" $$ "x")

nat = pi "a" star $ ("a" ==> "a") ==> "a" ==> "a"

z = forAll "a" $
    lam "s" ("a" ==> "a") $
    lam"z" "a"
    "z"

s = lam "n" nat $
    forAll "a" $
    lam "s" ("a" ==> "a") $
    lam "z" "a" $
    "s" $$ ("n" $$ "a" $$ "s" $$ "z")

add =
  lam "a" nat $
  lam "b" nat $
  forAll "r" $
  lam "s" ("r" ==> "r") $
  lam "z" "r" $
  "a" $$ "r" $$ "s" $$ ("b" $$ "r" $$ "s" $$ "z")

mul =
  lam "a" nat $
  lam "b" nat $
  forAll "r" $
  lam "s" ("r" ==> "r") $
  "a" $$ "r" $$ ("b" $$ "r" $$ "s")

two = s $$ (s $$ z)
five = s $$ (s $$ (s $$ (s $$ (s $$ z))))
ten = add $$ five $$ five
hundred = mul $$ ten $$ ten

nFunTy =
  lam "n" nat $
  "n" $$ star $$ (lam "t" star $ star ==> "t") $$ star

nFun =
  lam "n" nat $
  lam "f" (nFunTy $$ "n") $
  star

list = forAll "a" $ pi "r" star $ ("a" ==> "r" ==> "r") ==> "r" ==> "r"

nil = forAll "a" $ forAll "r" $ lam "c" ("a" ==> "r" ==> "r") $ lam "n" "r" $ "n"

cons =
   forAll "a" $
   lam "x" "a" $
   lam "xs" (list $$ "a") $
   forAll "r" $ lam "c" ("a" ==> "r" ==> "r") $ lam "n" "r" $
   "c" $$ "x" $$ ("xs" $$ "r" $$ "c" $$ "n")

map' =
  forAll "a" $
  forAll "b" $
  lam "f" ("a" ==> "b") $
  lam "as" (list $$ "a") $
  "as" $$ (list $$ "b") $$
    (lam "x" "a" $ lam "xs" (list $$ "b") $ cons $$ "b" $$ ("f" $$ "x") $$ "xs") $$
    (nil $$ "b")

sum' = lam "xs" (list $$ nat) $ "xs" $$ nat $$ add $$ z

natList = let c = cons $$ nat; n = nil $$ nat in
  c $$ z $$ (c $$ five $$ (c $$ ten $$ n))

test = all (isRight . infer0)
  [id', const', compose, nat, z, s, add, mul, two, five, nFunTy, nFun,
   nFun $$ five, sum' $$ natList, map']

