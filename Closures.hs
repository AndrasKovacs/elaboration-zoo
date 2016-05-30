{-|
Trying to use first-order closures and Term as much as possible.
-}

{-# language BangPatterns, LambdaCase, OverloadedStrings #-}

module Closures where

import Prelude hiding (pi)
import Control.Monad
import Data.Either
import Syntax (RawTerm)
import qualified Syntax as S
import qualified Data.HashMap.Strict as HM

data Term
  = Var !Int
  | App Term Term
  | Lam Term Term
  | Pi Term Term
  | Star
  deriving (Eq)

data Val
  = VVar !Int
  | VApp Val Val
  | VLam Term [Val] !Int Term
  | VPi  Term [Val] !Int Term
  | VStar

data Infer
  = Ok Type
  | IPi Term {-# unpack #-} !Cxt Term

type Type  = Val
type Cxt   = ([Val], [Term], Int)
type TM    = Either String

cxt0 :: Cxt
cxt0 = ([], [], 0)

(<:) :: (Val, Term) -> Cxt -> Cxt
(<:) (v, t) (vs, ts, d) = (v:vs, t:ts, d + 1)

(<::) :: Term -> Cxt -> Cxt
(<::) t (vs, ts, d) = (VVar d:vs, t:ts, d + 1)

vapp :: Val -> Val -> Val
vapp (VLam _ vs d t) x = whnf (x:vs) (d + 1) t
vapp f               x = VApp f x

quoteInfer :: Int -> Infer -> TM Term
quoteInfer d = \case
  Ok ty -> pure $ quote d ty
  IPi a cxt@(vs, ts, d') b ->
    Pi (nf vs d d' a) <$> (quoteInfer (d + 1) =<< infer ((VVar d, a) <: cxt) b)

whnf :: [Val] -> Int -> Term -> Val
whnf vs d = \case
  Var i   -> vs !! (d - i - 1)
  App f x -> whnf vs d f `vapp` whnf vs d x
  Lam a t -> VLam a vs d t
  Pi  a b -> VPi  a vs d b
  Star    -> VStar

nf :: [Val] -> Int -> Int -> Term -> Term
nf vs d d' = quote d . whnf vs d'

quote :: Int -> Val -> Term
quote d = \case
  VVar i         -> Var i
  VApp f x       -> App (quote d f) (quote d x)
  VLam a vs d' t -> Lam (nf vs d d' a) (quote (d + 1) (whnf (VVar d:vs) (d' + 1) t))
  VPi  a vs d' b -> Pi  (nf vs d d' a) (quote (d + 1) (whnf (VVar d:vs) (d' + 1) b))
  VStar          -> Star

check :: Cxt -> Term -> Term -> TM ()
check cxt@(_, _, d) t expect = do
  tt <- quoteInfer d =<< infer cxt t
  unless (tt == expect) $ Left "type mismatch"

infer :: Cxt -> Term -> TM Infer
infer cxt@(vs, ts, d) = \case
  Var i   -> pure $ Ok $ whnf (drop (d - i) vs) i (ts !! (d - i - 1))
  Star    -> pure $ Ok VStar
  Lam a t -> do
    check cxt a Star
    pure $ IPi a cxt t
  Pi a b -> do
    check cxt a Star
    check (a <:: cxt) b Star
    pure $ Ok VStar
  App f x ->
    infer cxt f >>= \case
      IPi a cxt'@(vs', ts', d') b -> do
        check cxt x (nf vs' d d' a)
        infer ((whnf vs d x, a) <: cxt') b
      Ok (VPi a vs' d' b) -> do
        check cxt x (nf vs' d d' a)
        pure $ Ok $ whnf (whnf vs d x: vs') (d' + 1) b
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
  go p (Var i)   = (show i++)
  go p (App f x) = showParen p (unwords' $ map (go True) (spine f x))
  go p (Lam a t) = showParen p (("λ "++) . go True a . (" -> "++) . go False t)
  go p Star      = ('*':)
  go p (Pi a b)  = showParen p (go True a . (" -> "++) . go False b)

fromRaw :: RawTerm -> Term
fromRaw = go HM.empty 0 where
  go m !d (S.Var v)     = Var (m HM.! v)
  go m d  (S.Lam v a t) = Lam (go m d a) (go (HM.insert v d m) (d + 1) t)
  go m d  (S.Pi  v a t) = Pi  (go m d a) (go (HM.insert v d m) (d + 1) t)
  go m d  (S.App f x)   = App (go m d f) (go m d x)
  go m d  S.Star        = Star

instance Show Term where
  showsPrec = pretty

infer0 :: RawTerm -> TM Term
infer0 = quoteInfer 0 <=< infer cxt0 . fromRaw

nf0 :: RawTerm -> TM Term
nf0 v = quote 0 (whnf [] 0 $ fromRaw v) <$ infer0 v

pi            = S.Pi
lam           = S.Lam
star          = S.Star
forAll a b    = lam a star b
let' k ty x e = lam k ty e $$ x
infixl 9 $$
($$) = S.App

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

       
