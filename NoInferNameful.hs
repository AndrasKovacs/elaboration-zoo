{-|
This version is hopefully the easiest to understand.

No inference for lambdas, nor de Bruijn indices.

This is probably the simplest dependent checker I've seen so far on the internet.
-}

{-# language BangPatterns, LambdaCase, OverloadedStrings #-}

module NoInferNameful where

import Prelude hiding (pi)
import Control.Monad
import Data.Either
import Data.String

import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as HM

data Term
  = Var !String
  | App !Term !Term
  | Lam !String !Term
  | Ann !Term !Term
  | Pi !String !Term !Term
  | Star

data Val
  = VVar !String
  | BVar !Int
  | VApp !Val Val
  | VLam !String !(Val -> Val)
  | VPi  !String !Type !(Val -> Val)
  | VStar

type Type  = Val
type Cxt   = HashMap String Type
type TM    = Either String

whnf :: Term -> Val
whnf = go HM.empty where
  go vs = \case
    Var v     -> maybe (VVar v) id (HM.lookup v vs)
    App f x   -> case (go vs f, go vs x) of
      (VLam _ f, x) -> f x
      (f       , x) -> VApp f x
    Ann t ty  -> go vs t
    Lam v t   -> VLam v $ \t' -> go (HM.insert v t' vs) t
    Pi  v a b -> VPi  v (go vs a) $ \t' -> go (HM.insert v t' vs) b
    Star      -> VStar

quote :: Val -> Term
quote = \case
  VVar i     -> Var i
  VApp f x   -> App (quote f) (quote x)
  VLam v t   -> Lam v (quote (t (VVar v)))
  VPi  v a b -> Pi  v (quote a) (quote (b (VVar v)))
  VStar      -> Star
  BVar _     -> error "quote: impossible BVar"

-- beta-alpha convertibility
--------------------------------------------------------------------------------

conv :: Type -> Type -> Bool
conv = go 0 where
  go d (VVar v)     (VVar v')      = v == v'
  go d (BVar i)     (BVar i')      = i == i'
  go d (VApp f x)   (VApp f' x')   = go d f f' && go d x x'
  go d (VPi  _ a b) (VPi  _ a' b') = go d a a' && go (d + 1) (b (BVar d)) (b' (BVar d))
  go d (VLam _ t)   (VLam _ t')    = go (d + 1) (t (BVar d)) (t' (BVar d))
  go d VStar        VStar          = True
  go d _            _              = False

-- check / infer
--------------------------------------------------------------------------------

check :: Cxt -> Term -> Type -> TM ()
check cxt t want = case (t, want) of
  (Lam v t, VPi _ a b) ->
    check (HM.insert v a cxt) t (b (VVar v))
  (t, _) -> do
    has <- infer cxt t
    unless (conv has want) $ Left "type mismatch"

infer :: Cxt -> Term -> TM Type
infer cxt = \case
  Var v    -> pure (cxt ! v)
  Star     -> pure VStar
  Lam v t  -> Left $ "can't infer type for lambda " ++ show (Lam v t)
  Ann t ty -> do
    check cxt ty VStar
    let ty' = whnf ty
    ty' <$ check cxt t ty'
  Pi v a b -> do
    check cxt a VStar
    check (HM.insert v (whnf a) cxt) b VStar
    pure VStar
  App f x ->
    infer cxt f >>= \case
      VPi v a b -> b (whnf x) <$ check cxt x a
      _         -> Left "can't apply non-function"

infer0 :: Term -> TM Term
infer0 t = quote <$> infer HM.empty t

nf0 :: Term -> TM Term
nf0 t = etaRed (quote (whnf t)) <$ infer0 t      

-- Sugar & print
--------------------------------------------------------------------------------

pretty :: Int -> Term -> ShowS
pretty prec = go (prec /= 0) where

  unwords' :: [ShowS] -> ShowS
  unwords' = foldr1 (\x acc -> x . (' ':) . acc)

  spine :: Term -> Term -> [Term]
  spine f x = go f [x] where
    go (App f y) args = go f (y : args)
    go t         args = t:args

  lams :: String -> Term -> ([String], Term)
  lams v t = go [v] t where
    go vs (Lam v t) = go (v:vs) t
    go vs t         = (vs, t)

  go :: Bool -> Term -> ShowS
  go p (Var i)    = (i++)
  go p (App f x)  = showParen p (unwords' $ map (go True) (spine f x))
  go p (Ann t ty) = showParen p (go False t . (" : "++) . go False ty)
  go p (Lam v t)  = case lams v t of
    (vs, t) -> showParen p (("λ "++) . (unwords (reverse vs)++) . (". "++) . go False t)
  go p (Pi v a b) = showParen p (arg . (" -> "++) . go False b)
    where arg = if freeIn v b then showParen True ((v++) . (" : "++) . go False a)
                              else go True a
  go p Star = ('*':)

instance Show Term where
  showsPrec = pretty

instance IsString Term where
  fromString = Var

-- eta reduce
--------------------------------------------------------------------------------

freeIn :: String -> Term -> Bool
freeIn v = go where
  go (Var v')     = v' == v
  go (App f x)    = go f || go x
  go (Lam v' t)   = v' /= v && go t
  go (Pi  v' a b) = go a || (v' /= v && go b)
  go (Ann t ty)   = go t || go ty
  go Star         = False

etaRed :: Term -> Term
etaRed = \case
  Var v   -> Var v
  App f x -> App (etaRed f) (etaRed x)
  Lam v t -> case etaRed t of
    App f (Var v') | v == v' && not (freeIn v f) -> f
    t -> Lam v t
  Pi v a b -> Pi v (etaRed a) (etaRed b)
  Ann t ty -> Ann (etaRed t) (etaRed ty)
  Star     -> Star

--------------------------------------------------------------------------------  

pi         = Pi
lam        = Lam
star       = Star
forAll a b = pi a star b
ann        = flip Ann
($$)       = App
infixl 9 $$

(==>) a b = pi "" a b
infixr 8 ==>

-- Examples
--------------------------------------------------------------------------------

id' =
  ann (pi "a" star $ "a" ==> "a") $
  lam "a" $ lam "x" $ "x"

const' =
  ann (pi "a" star $ pi "b" star $ "a" ==> "b" ==> "a") $
  lam "a" $ lam "b" $ lam "x" $ lam "y" $ "x"

compose =
  ann (forAll "a" $ forAll "b" $ forAll "c" $
       ("b" ==> "c") ==> ("a" ==> "b") ==> "a" ==> "c") $
  lam "a" $ lam "b" $ lam "c" $
  lam "f" $ lam "g" $ lam "x" $
  "f" $$ ("g" $$ "x")

nat = forAll "a" $ ("a" ==> "a") ==> "a" ==> "a"

z = ann nat $ lam "n" $ lam "s" $ lam "z" "z"

s =
  ann (nat ==> nat) $
  lam "a" $ lam "n" $ lam "s" $ lam "z" $
  "s" $$ ("a" $$ "n" $$ "s" $$ "z")

add =
  ann (nat ==> nat ==> nat) $
  lam "a" $ lam "b" $ lam "n" $ lam "s" $ lam "z" $
  "a" $$ "n" $$ "s" $$ ("b" $$ "n" $$ "s" $$ "z")

mul =
  ann (nat ==> nat ==> nat) $
  lam "a" $ lam "b" $ lam "n" $ lam "s" $
  "a" $$ "n" $$ ("b" $$ "n" $$ "s")

one = s $$ z
two = s $$ one
five = s $$ (s $$ (s $$ (s $$ (s $$ z))))
ten = add $$ five $$ five
hundred = mul $$ ten $$ ten

nFunTy =
  ann (nat ==> star) $
  lam "n" $ "n" $$ star $$ (lam "t" $ star ==> "t") $$ star

list = ann (star ==> star) $
  lam "a" $ forAll "r" $ ("a" ==> "r" ==> "r") ==> "r" ==> "r"

nil =
  ann (forAll "a" $ list $$ "a") $
  lam "a" $ lam "r" $ lam "c" $ lam "n" $ "n"

cons =
  ann (forAll "a" $ "a" ==> (list $$ "a") ==> (list $$ "a")) $
  lam "a" $ lam "x" $ lam "as" $ lam "r" $ lam "c" $ lam "n" $
  "c" $$ "x" $$ ("as" $$ "r" $$ "c" $$ "n")

-- non-fusing
map' =
  ann (forAll "a" $ forAll "b" $ ("a" ==> "b") ==> list $$ "a" ==> list $$ "b") $
  lam "a" $ lam "b" $ lam "f" $ lam "as" $
  "as" $$ (list $$ "b") $$ (lam "x" $ cons $$ "b" $$ ("f" $$ "x")) $$ (nil $$ "b")
  
-- fusing
map'' =
  ann (forAll "a" $ forAll "b" $ ("a" ==> "b") ==> list $$ "a" ==> list $$ "b") $
  lam "a" $ lam "b" $ lam "f" $ lam "as" $ lam "l" $ lam "c" $ lam "n" $
  "as" $$ "l" $$ (lam "x" $ "c" $$ ("f" $$ "x")) $$ "n"
  
-- non-fusing
sum' =
  ann (list $$ nat ==> nat) $
  lam "ns" $ "ns" $$ nat $$ add $$ z

-- fusing
sum'' =
  ann (list $$ nat ==> nat) $
  lam "ns" $ lam "r" $ lam "s" $ 
  "ns" $$ "r" $$ (lam "a" $ "a" $$ "r" $$ "s")

sumMapFuse =
  ann (list $$ nat ==> (nat ==> nat) ==> nat) $
  lam "ns" $ lam "f" $
  sum'' $$ (map'' $$ nat $$ nat $$ "f" $$ "ns")  

natList = let c = cons $$ nat; n = nil $$ nat in
  c $$ z $$ (c $$ five $$ (c $$ ten $$ n))

test = all (isRight . infer0)
  [id', const', compose, nat, z, s, add, mul, two, five, nFunTy, sum' $$ natList, map']

