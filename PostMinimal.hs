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

data Infer
  = Ok Type
  | IPi Type (Val -> TM Infer)

type Type  = Val
type Cxt   = ([Val], [Type], Int)
type TM = Either String

cxt0 :: Cxt
cxt0 = ([], [], 0)

(<:) :: (Val, Type) -> Cxt -> Cxt
(<:) (v, t) (vs, ts, d) = (v:vs, t:ts, d + 1)

(<::) :: Type -> Cxt -> Cxt
(<::) t (vs, ts, d) = (VVar d:vs, t:ts, d + 1)

($$) :: Val -> Val -> Val
($$) (VLam _ f) x = f x
($$) f          x = VApp f x
infixl 9 $$

quoteInfer :: Int -> Infer -> TM Term
quoteInfer d = \case
  Ok ty        -> pure $ quote d ty
  IPi a b -> Pi (quote d a) <$> (quoteInfer (d + 1) =<< b (VVar d))

eval :: [Val] -> Int -> Term -> Val
eval vs d = \case
  Var i   -> vs !! (d - i - 1)
  App f x -> eval vs d f $$ eval vs d x
  Lam a t -> VLam (eval vs d a) $ \v -> eval (v:vs) (d + 1) t
  Pi  a b -> VPi  (eval vs d a) $ \v -> eval (v:vs) (d + 1) b
  Star    -> VStar

quote :: Int -> Val -> Term
quote d = \case
  VVar i   -> Var i
  VApp f x -> App (quote d f) (quote d x)
  VLam a t -> Lam (quote d a) (quote (d + 1) (t (VVar d)))
  VPi  a b -> Pi  (quote d a) (quote (d + 1) (b (VVar d)))
  VStar    -> Star

check :: Cxt -> Term -> Term -> TM ()
check cxt@(_, _, d) t expect = do
  tt <- quoteInfer d =<< infer cxt t
  unless (tt == expect) $ Left "type mismatch"

infer :: Cxt -> Term -> TM Infer
infer cxt@(vs, ts, d) = \case
  Var i   -> pure $ Ok (ts !! (d - i - 1))
  Star    -> pure $ Ok VStar
  Lam a t -> do
    check cxt a Star
    let a' = eval vs d a
    pure $ IPi a' $ \v -> infer ((v, a') <: cxt) t
  Pi a b -> do
    check cxt a Star
    check (eval vs d a <:: cxt) b Star
    pure $ Ok VStar
  App f x ->
    infer cxt f >>= \case
      IPi a b -> do
        check cxt x (quote d a)
        b (eval vs d x)
      Ok (VPi a b) -> do
        check cxt x (quote d a)
        pure $ Ok $ b (eval vs d x)
      _ -> Left "Can't apply non-function"



-- Sugar & examples
--------------------------------------------------------------------------------

-- Be careful with strictness and ill-typed code when writing HOAS terms.
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

infer0 :: Term -> TM Term
infer0 = quoteInfer 0 <=< infer cxt0

quote0 :: Val -> Term
quote0 = quote 0

infer0' :: Val -> TM Term
infer0' = infer0 . quote0

eval0' :: Val -> TM Term
eval0' v = quote0 v <$ infer0 (quote0 v)

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


