
{-# language Strict #-}

import Debug.Trace

-- Glued eval
------------------------------------------------------------

data Tm   = Var Int | App Tm Tm | Lam Tm
data Val  = VVar Int | VApp Val {-# unpack #-} C ~Val | VLam Vals Tms Tm deriving Show
type Vals = [Val]
type Tms  = [C]
data C    = C Tms Tm deriving Show

mkC :: Tms -> Tm -> C
mkC ts (Var i) = ts !! (length ts - i - 1)
mkC ts t       = C ts t

eval :: Tms -> Vals -> Tm -> Val
eval ts vs t = case t of
  Var i -> vs !! (length vs - i - 1)
  App f x -> case (eval ts vs f, eval ts vs x, mkC ts x) of
    (VLam vs' ts' t, vx, !cx) -> traceShow "x" $ eval (cx:ts') (vx:vs') t
    (f, vx, cx)               -> VApp f cx vx
  Lam t -> VLam vs ts t

quote :: Int -> Val -> Tm
quote d t = case t of
  VVar i -> Var i
  VApp f _ x -> App (quote d f) (quote d x)
  VLam vs ts t -> Lam (quote (d + 1) (eval (C [] (Var d):ts) (VVar d:vs) t))

------------------------------------------------------------

pretty :: Int -> Tm -> ShowS
pretty prec = go (prec /= 0) where

  unwords' :: [ShowS] -> ShowS
  unwords' = foldr1 (\x acc -> x . (' ':) . acc)

  spine :: Tm -> Tm -> [Tm]
  spine f x = go f [x] where
    go (App f y) args = go f (y : args)
    go t         args = t:args

  go :: Bool -> Tm -> ShowS
  go p (Var i)   = (show i++)
  go p (App f x) = showParen p (unwords' $ map (go True) (spine f x))
  go p (Lam t)   = showParen p (("λ "++) . go False t)

instance Show Tm where
  showsPrec = pretty

($$) = App
infixl 6 $$

instance Num Tm where
  (+) = undefined; (-) = undefined; abs = undefined; signum = undefined; (*) = undefined
  fromInteger = Var . fromIntegral

nf = quote 0 . eval [] []


one = Lam $ Lam $ 0 $$ 1
two = Lam $ Lam $ 0 $$ (0 $$ 1)
z = Lam $ Lam 1
s = Lam $ Lam $ Lam $ 1 $$ (0 $$ 1 $$ 2)
add = Lam $ Lam $ Lam $ Lam $ 0 $$ 2 $$ (1 $$ 2 $$ 3)
mul = Lam $ Lam $ Lam $ Lam $ 0 $$ (1 $$ 2) $$ 3

five = s $$ (s $$ (s $$ (s $$ (s $$ z))))
ten  = add $$ five $$ five

