
{-# language Strict #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

import Debug.Trace

------------------------------------------------------------

-- data Tm = Var Int | App Tm Tm | Lam Tm | App1 Tm | App2 Tm

-- app1 ∷ Tm → Tm
-- app1 (App t _) = t
-- app1 t         = App1 t

-- app2 ∷ Tm → Tm
-- app2 (App _ u) = u
-- app2 t         = App2 t

-- data Val = VVar Int | VApp Val ~Val | VLam (Val → Val)

-- dive ∷ Tm → Int → Tm
-- dive (Lam t) g = t
-- dive t g       = App t (Var g)

-- conv ∷ Int → Val → Tm → Val → Tm → Bool
-- conv g v t v' t' = case (v, v') of
--   (VVar i,   VVar i')    → i == i'
--   (VApp v u, VApp v' u') → conv g v (app1 t) v' (app1 t') && conv g u (app2 t) u' (app2 t')
--   (VLam v,   VLam v')    →
--     conv (g + 1) (v (VVar g)) (dive t g) (v' (VVar g)) (dive t' g)

--   _ → traceShow (t, t') False


-- Glued eval
------------------------------------------------------------

data Tm  = Var Int | App Tm Tm | Lam Tm
data Val = VNe Int [Val] [C] | VLam [Val] [C] Tm
data C   = C [C] Tm

eval ∷ [Val] → [C] → Tm → Val
eval vs cs t = case t of
  Var i   → vs !! (length vs - i - 1)
  App t u → case (eval vs cs t, eval vs cs u) of
    (VLam vs' cs' t', u') → eval (u':vs') (C cs u:cs') t'
    (VNe i vs' cs'  , u') → VNe i (u':vs') (C cs u:cs')
  Lam t   → VLam vs cs t

conv ∷ Int → Val → C → Val → C → Bool
conv l v c v' c' = case (v, v') of
  (VNe i vs cs,  VNe i' vs' cs' ) →
    and $ zipWith (\(v, c) (v', c') → conv l v c v' c')
                  (zip vs cs) (zip vs' cs')
  (VLam vs cs t, VLam vs' cs' t') →
    let lcs  = C [] (Var l):cs
        lcs' = C [] (Var l):cs'
        lvs  = VNe l [] []:vs
        lvs' = VNe l [] []:vs'
    in conv (l + 1) (eval lvs  lcs  t ) (C lcs  t )
                    (eval lvs' lcs' t') (C lcs' t')
  _ → False


-- data Tm   = Var Int | App Tm Tm | Lam Tm
-- data Val  = VVar Int | VApp Val C ~Val | VLam [C] [Val] Tm
-- data C    = C [C] Tm

-- eval :: [C] -> [Val] -> Tm -> Val
-- eval cs vs t = case t of
--   Var i   -> vs !! (length vs - i - 1)
--   App t u -> case (eval cs vs t, eval cs vs u) of
--     (VLam cs' vs' t', u') -> eval (C cs u:cs') (u':vs') t
--     (t',              u') -> VApp t' (C cs u) u'
--   Lam t -> VLam cs vs t

-- conv ∷ Int → C → Val → C → Val → Bool
-- conv l c v c' v' = case (v, v') of
--   (VVar i    , VVar i'      ) → i == i'
--   (VApp t c u, VApp t' c' u') → conv l _ t _ t'

-- quote :: Int -> Val -> Tm
-- quote d t = case t of
--   VVar i       -> Var i
--   VApp f _ x   -> App (quote d f) (quote d x)
--   VLam cs vs t -> Lam (quote (d + 1) (eval (C [] (Var d):cs) (VVar d:vs) t))

------------------------------------------------------------

-- pretty :: Int -> Tm -> ShowS
-- pretty prec = go (prec /= 0) where

--   unwords' :: [ShowS] -> ShowS
--   unwords' = foldr1 (\x acc -> x . (' ':) . acc)

--   spine :: Tm -> Tm -> [Tm]
--   spine f x = go f [x] where
--     go (App f y) args = go f (y : args)
--     go t         args = t:args

--   go :: Bool -> Tm -> ShowS
--   go p (Var i)   = (show i++)
--   go p (App f x) = showParen p (unwords' $ map (go True) (spine f x))
--   go p (Lam t)   = showParen p (("λ "++) . go False t)
--   -- go p (App1 t)  = showParen p (("app1 " ++) . go False t)
--   -- go p (App2 t)  = showParen p (("app2 " ++) . go False t)

-- instance Show Tm where
--   showsPrec = pretty

-- ($$) = App
-- infixl 6 $$

-- instance Num Tm where
--   (+) = undefined; (-) = undefined; abs = undefined; signum = undefined; (*) = undefined
--   fromInteger = Var . fromIntegral

-- -- nf = quote 0 . eval [] []


-- one = Lam $ Lam $ 0 $$ 1
-- two = Lam $ Lam $ 0 $$ (0 $$ 1)
-- z = Lam $ Lam 1
-- s = Lam $ Lam $ Lam $ 1 $$ (0 $$ 1 $$ 2)
-- add = Lam $ Lam $ Lam $ Lam $ 0 $$ 2 $$ (1 $$ 2 $$ 3)
-- mul = Lam $ Lam $ Lam $ Lam $ 0 $$ (1 $$ 2) $$ 3

-- five = s $$ (s $$ (s $$ (s $$ (s $$ z))))
-- ten  = add $$ five $$ five
