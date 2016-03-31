{-# language BangPatterns, LambdaCase #-}

import Prelude hiding (pi)
import Control.Monad
import Data.Either

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
  | VLam Type (Val -> Val)
  | VPi  Type (Val -> Val)
  | VStar

type Type  = Val
type Cxt   = ([Type], [Val], Int)
type Check = Either String

data TC
  = Ok Type
  | CheckLam Type (Val -> Check TC)

cxt0 :: Cxt
cxt0 = ([], [], 0)

(<:) :: (Type, Val) -> Cxt -> Cxt
(<:) (t, v) (ts, vs, d) = (t:ts, v:vs, d + 1)

(<::) :: Type -> Cxt -> Cxt
(<::) t (ts, vs, d) = (t:ts, VVar d:vs, d + 1)

lookupTy :: Cxt -> Int -> Type
lookupTy (ts, vs, d) i = ts !! (d - i - 1)

($$) :: Val -> Val -> Val
($$) (VLam _ f) x = f x
($$) f          x = VApp f x
infixl 9 $$

quoteTC :: Cxt -> TC -> Check Term
quoteTC (_, _, d) = go d where
  go d (Ok ty)        = pure $ quote' d ty
  go d (CheckLam a b) = Pi (quote' d a) <$> (go (d + 1) =<< b (VVar d))

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

check :: Cxt -> Term -> Term -> Check ()
check cxt t ty = do
  tt <- quoteTC cxt =<< infer cxt t
  unless (tt == ty) $ Left "type mismatch"

infer :: Cxt -> Term -> Check TC
infer cxt@(ts, vs, d) = \case
  Var i   -> pure $ Ok (ts !! (d - i - 1))
  Star    -> pure $ Ok VStar
  Lam a t -> do
    check cxt a Star
    let a' = eval cxt a
    pure $ CheckLam a' $ \v -> infer ((a', v) <: cxt) t
  Pi a b -> do
    check cxt a Star
    check (eval cxt a <:: cxt) b Star
    pure $ Ok VStar
  App f x ->
    infer cxt f >>= \case
      CheckLam a b -> do
        check cxt x (quote cxt a)
        b (eval cxt x)
      Ok (VPi a b) -> do
        check cxt x (quote cxt a)
        pure $ Ok $ b (eval cxt x)
      _ -> Left "Can't apply non-function"



-- Sugar & examples
--------------------------------------------------------------------------------

-- Be careful with strictness and ill-typed code when writing HOAS.
-- 'infer0' reduces to normal form before checking,
-- which may lead to nontermination or excessive computation.

-- Of course, the proper way is to define sample code with 'Term' instead of 'Val'.
-- That's both much lazier and safe.

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

instance Show Term where
  showsPrec = pretty

infer0 :: Term -> Check Term
infer0 = quoteTC cxt0 <=< infer cxt0

quote0 :: Val -> Term
quote0 = quote cxt0

infer0' :: Val -> Check Term
infer0' = infer0 . quote0

eval0' :: Val -> Check Term
eval0' v = quote cxt0 v <$ infer0 (quote cxt0 v)

pi          = VPi
lam         = VLam
star        = VStar
forAll      = lam star
let' ty x e = lam ty e $$ x

(==>) a b = pi a (const b)
infixr 8 ==>

id'    = forAll $ \a -> lam a $ \x -> x
const' = forAll $ \a -> forAll $ \b -> lam a $ \x -> lam b $ \_ -> x

compose =
  forAll $ \a ->
  forAll $ \b ->
  forAll $ \c ->
  lam (b ==> c) $ \f ->
  lam (a ==> b) $ \g ->
  lam a $ \x ->
  f $$ (g $$ x)

nat = pi star $ \a -> (a ==> a) ==> a ==> a

z = forAll $ \a ->
    lam (a ==> a) $ \s ->
    lam a $ \z ->
    z

s = lam nat $ \n ->
    forAll $ \a ->
    lam (a ==> a) $ \s ->
    lam a $ \z ->
    s $$ (n $$ a $$ s $$ z)

add =
  lam nat $ \a ->
  lam nat $ \b ->
  forAll $ \r ->
  lam (r ==> r) $ \s ->
  lam r $ \z ->
  a $$ r $$ s $$ (b $$ r $$ s $$ z)

mul =
  lam nat $ \a ->
  lam nat $ \b ->
  forAll $ \r ->
  lam (r ==> r) $ \s ->
  a $$ r $$ (b $$ r $$ s)

two = s $$ (s $$ z)
five = s $$ (s $$ (s $$ (s $$ (s $$ z))))
ten = add $$ five $$ five
hundred = mul $$ ten $$ ten

nFunTy =
  lam nat $ \n ->
  n $$ star $$ (lam star $ \t -> star ==> t) $$ star

nFun =
  lam nat $ \n ->
  lam (nFunTy $$ n) $ \f ->
  star

list = forAll $ \a -> pi star $ \r -> (a ==> r ==> r) ==> r ==> r

nil  = forAll $ \a -> forAll $ \r -> lam (a ==> r ==> r) $ \c -> lam r $ \n -> n

cons =
  forAll $ \a ->
  lam a $ \x ->
  lam (list $$ a) $ \xs ->
  forAll $ \r ->
  lam (a ==> r ==> r) $ \c ->
  lam r $ \n ->
  c $$ x $$ (xs $$ r $$ c $$ n)

map' =
  forAll $ \a ->
  forAll $ \b ->
  lam (a ==> b) $ \f ->
  lam (list $$ a) $ \as ->
  as $$ (list $$ b) $$
    (lam a $ \x -> lam (list $$ b) $ \xs -> cons $$ b $$ (f $$ x) $$ xs) $$
    (nil $$ b)

sum' =
  lam (list $$ nat) $ \xs ->
  xs $$ nat $$ add $$ z

natList = let c = cons $$ nat; n = nil $$ nat in
  c $$ z $$ (c $$ five $$ (c $$ ten $$ n))

test = all (isRight . infer0')
  [id', const', compose, nat, z, s, add, mul, two, five, nFunTy, nFun,
   nFun $$ five, sum' $$ natList, map']


