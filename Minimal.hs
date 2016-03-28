
import Prelude hiding (pi)
import Control.Monad.Except
import Data.Either
import Text.Printf

data Term
  = Var !Int
  | App Term Term
  | Lam Term Term
  | Pi Term Term
  | Star
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

instance Show Term where
  showsPrec = pretty

data Val
  = VVar !Int
  | VApp Val Val
  | VLam Type (Val -> Val)
  | VPi  Type (Val -> Val)
  | VStar

data TC
  = Pure Type
  | TPi Type (Val -> Check TC)

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

($$) :: Val -> Val -> Val
($$) (VLam _ f) x = f x
($$) f          x = VApp f x
infixl 9 $$

runTC :: Cxt -> TC -> Check Term
runTC (_, _, d) = go d where
  go d (Pure ty) = pure $ quote' d ty
  go d (TPi a b)  = Pi (quote' d a) <$> (go (d + 1) =<< b (VVar d))

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
  tt <- runTC cxt =<< infer cxt t
  unless (tt == ty) $ do
    throwError $ printf
      "Couldn't match expected type %s for term %s with actual type: %s"
      (show ty) (show t) (show tt)

infer :: Cxt -> Term -> Check TC
infer cxt = \case
  Var i   -> pure $ Pure (lookupTy cxt i)
  Star    -> pure $ Pure VStar
  Lam a t -> do
    check cxt a Star
    let a' = eval cxt a
    pure $ TPi a' $ \v -> infer ((a', v) <: cxt) t
  Pi a b -> do
    check cxt a Star
    check (eval cxt a <:: cxt) b Star
    pure $ Pure VStar
  App f x -> do
    tf <- infer cxt f
    case tf of
      TPi a b -> do
        check cxt x (quote cxt a)
        b (eval cxt x)
      Pure (VPi a b) -> do
        check cxt x (quote cxt a)
        pure $ Pure $ b (eval cxt x)
      _ -> throwError $
             printf "Can't apply non-function type %s when checking term %s"
             (show $ runTC cxt tf) (show $ App f x)

infer0 :: Term -> Check Term
infer0 = runTC cxt0 <=< infer cxt0

infer0' :: Val -> Check Term
infer0' = infer0 . quote cxt0

eval0' :: Val -> Check Term
eval0' v = quote cxt0 v <$ infer0 (quote cxt0 v)


-- HOAS sugar
--------------------------------------------------------------------------------

-- Be careful with the strictness of HOAS! The "quote" in "infer0'" reduces
-- large literals to normal form. Use "let" binding in HOAS expressions
-- to reintroduce lazy type checking.

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

nat = VPi star $ \a -> (a ==> a) ==> a ==> a

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

test = all (isRight . infer0')
  [id', const', compose, nat, z, s, add, mul, two, five, nFunTy, nFun,
   nFun $$ five]


