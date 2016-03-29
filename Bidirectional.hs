
{-# language BangPatterns, LambdaCase #-}

import Prelude hiding (pi)
import Control.Monad.Except
import Data.Either
import Text.Printf

import TCBE.Syntax (RawTerm)
import qualified TCBE.Syntax as S

import qualified Data.HashMap.Strict as HM

data Term
  = Var !Int
  | App Term Term
  | Lam (Maybe Term) Term
  | Pi Term Term
  | Ann Term Term
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
  go p (Var i)    = (show i++)
  go p (App f x)  = showParen p (unwords' $ map (go True) (spine f x))
  go p (Lam a t)  =
    showParen p (("λ"++) . maybe id (((' ':).) . go True) a . (" -> "++) . go False t)
  go p Star       = ('*':)
  go p (Ann t ty) = showParen p (go True t . (" : "++) . go False ty)
  go p (Pi a b)   = showParen p (go True a . (" -> "++) . go False b)

instance Show Term where
  showsPrec = pretty

data Val
  = VVar !Int
  | VApp Val Val
  | VLam (Maybe Type) (Val -> Val)
  | VPi  Type (Val -> Val)
  | VStar

data TC
  = Ret Type
  | CheckPi Type (Val -> Check TC)

type Type = Val

type Cxt   = ([Type], [Val], Int)
type Check = Either String

cxt0 :: Cxt
cxt0 = ([], [], 0)

(<:) :: (Type, Val) -> Cxt -> Cxt
(<:) (t, v) (ts, vs, d) = (t:ts, v:vs, d + 1)

(<::) :: Type -> Cxt -> Cxt
(<::) t (ts, vs, d) = (t:ts, VVar d:vs, d + 1)

size :: Cxt -> Int
size (_, _, d) = d

lookupTy :: Cxt -> Int -> Type
lookupTy (ts, vs, d) i = ts !! (d - i - 1)

-- | Apply 'Val's.
($$) :: Val -> Val -> Val
($$) (VLam _ f) x = f x
($$) f          x = VApp f x
infixl 9 $$

runTC :: Cxt -> TC -> Check Term
runTC (_, _, d) = go d where
  go d (Ret ty)      = pure $ quote' d ty
  go d (CheckPi a b) = Pi (quote' d a) <$> (go (d + 1) =<< b (VVar d))

tcVal :: Cxt -> TC -> Check Type
tcVal cxt (Ret ty) = pure ty
tcVal cxt checkPi  = eval cxt <$> runTC cxt checkPi

quote :: Cxt -> Val -> Term
quote (_, _, d) = quote' d

quote' :: Int -> Val -> Term
quote' d = \case
  VVar i   -> Var i
  VApp f x -> App (quote' d f) (quote' d x)
  VLam a t -> Lam (quote' d <$> a) (quote' (d + 1) (t (VVar d)))
  VPi  a b -> Pi  (quote' d a) (quote' (d + 1) (b (VVar d)))
  VStar    -> Star

eval :: Cxt -> Term -> Val
eval (ts, vs, d) = go vs d where
  go vs !d = \case
    Var i   -> vs !! (d - i - 1)
    App f x -> go vs d f $$ go vs d x
    Ann t _ -> go vs d t
    Lam a t -> VLam (go vs d <$> a) $ \v -> go (v:vs) (d + 1) t
    Pi  a t -> VPi  (go vs d a) $ \v -> go (v:vs) (d + 1) t
    Star    -> VStar

check :: Cxt -> Term -> Type -> Check ()
check cxt t ty = case (t, ty) of
  (Lam Nothing t, VPi a b) -> do
    check (a <:: cxt) t (b (VVar (size cxt)))
  (t, ty) -> do
    let ty' = quote cxt ty
    tt <- runTC cxt =<< infer cxt t
    unless (tt == ty') $ do
      throwError $ printf
        "Couldn't match expected type %s for term %s with actual type: %s"
        (show ty') (show t) (show tt)

infer :: Cxt -> Term -> Check TC
infer cxt = \case
  Var i   -> pure $ Ret (lookupTy cxt i)
  Star    -> pure $ Ret VStar
  Lam (Just a) t -> do
    check cxt a VStar
    let a' = eval cxt a
    pure $ CheckPi a' $ \v -> infer ((a', v) <: cxt) t
  Lam a t ->
    throwError $ printf "Can't infer type for unannotated lambda: %s" (show $ Lam a t)
  Pi a b -> do
    check cxt a VStar
    check (eval cxt a <:: cxt) b VStar
    pure $ Ret VStar
  Ann t ty -> do
    check cxt ty VStar
    let ty' = eval cxt ty
    check cxt t ty'
    pure $ Ret ty'    
  App (Lam Nothing t) x -> do
    tx <- tcVal cxt =<< infer cxt x
    infer ((tx, eval cxt x) <: cxt) t    
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
             printf "Can't apply non-function type %s when checking term %s"
             (show $ runTC cxt tf) (show $ App f x)    


-- Test
--------------------------------------------------------------------------------

infer0 :: RawTerm -> Check Term
infer0 = runTC cxt0 <=< infer cxt0 . fromRaw

eval0 :: RawTerm -> Check Term
eval0 t = quote cxt0 (eval cxt0 $ fromRaw t) <$ infer0 t

fromRaw :: RawTerm -> Term
fromRaw = go HM.empty 0 where
  go m !d (S.Var v)     = Var (m HM.! v)
  go m d  (S.Lam v a t) = Lam (Just $ go m d a) (go (HM.insert v d m) (d + 1) t)
  go m d  (S.ILam v t)  = Lam Nothing (go (HM.insert v d m) (d + 1) t)
  go m d  (S.Ann t ty)  = Ann (go m d t) (go m d ty)
  go m d  (S.Pi  v a t) = Pi  (go m d a) (go (HM.insert v d m) (d + 1) t)
  go m d  (S.App f x)   = App (go m d f) (go m d x)
  go m d  S.Star        = Star
  
v = S.Var
lam = S.Lam
ilam = S.ILam
pi = S.Pi
star = S.Star
forAll v = lam v star
ann = flip S.Ann

let' a t x e = (lam a t e) $: x

($:) :: RawTerm -> RawTerm -> RawTerm
($:) = S.App
infixl 9 $:

(==>) :: RawTerm -> RawTerm -> RawTerm
a ==> b = pi "" a b
infixr 8 ==>

id'    = forAll "a" $ lam "x" "a" $ "x"
const' = forAll "a" $ forAll "b" $ lam "x" "a" $ lam "y" "b" $ "x"

id'' = ann
  (pi "a" star $ "a" ==> "a")
  (ilam "a" $ ilam "x" $ "x")

const'' = ann
  (pi "a" star $ pi "b" star $ "a" ==> "b" ==> "a")
  (ilam "a" $ ilam "b" $ ilam "x" $ ilam "y" $ "x")
