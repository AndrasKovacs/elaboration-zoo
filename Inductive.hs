{-# language BangPatterns, Strict, LambdaCase, PatternGuards, OverloadedStrings #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

{-|
Design:
- Indexed inductive families + dependent pattern matching + recursive definitions.
- Type in Type, no positivity check, manual annotation for structurally decreasing params.
- No built-in mutual recursion/induction (but encodable, of course).
- A single structurally decr. argument for each recursive function.
- Recursive definitions are unfolded iff they are applied to their decreasing
  argument, and the argument is canonical (i. e. non-neutral).


Things to ponder

  1. Dependent pattern matching actually causes *bound* variables to be
     arbitrarily substituted during type checking! For example:

       foo : (A : U)(x y : A) -> x ≡ y -> y ≡ x
       foo A x y =
         let bar : A × A × A
             bar = x , x , x
         in λ {refl ->
                let baz : bar ≡ (y , y , y)
                    bar = refl
                in refl}

     Here, we may first evaluate "bar" lazily to whnf, but later
     in the pattern lambda "x" gets substituted to "y", so we need
     to refresh "bar" in the new value environment.During conversion check
     and lhs unification we need to refresh neutrals headed by bound variables.

     Where/how should we store BVar substitutions?


TODO: revamp value environments to accomodate bound vars and their substitutions.
-}

import qualified Data.Text as T



type Name    = T.Text
type Unfold  = Int
type Generic = Int
type Sub a   = [(Name, a)]
type ValEnv  = Sub ValEntry

data ValEntry
  = VE_Defined ~Val Unfold
  | VE_Bound
  | VE_Substituted ~Val

data TyInfo
  = TI_Con Name
  | TI_Inductive


data Head
data Tm
data Val


{-


-- type Name    = T.Text
-- type Unfold  = Int
-- type Generic = Int
-- type Sub a   = [(Name, a)]
-- type ValEnv  = Sub (Val, Unfold)
-- type Ty      = Tm
-- type VTy     = Val
-- type TyEnv   = Sub (VTy, TyInfo)
-- type Program = Sub TopDecl

-- data TyInfo
--   = TyDCon Name
--   | TyTCon [Name]
--   | TyBound
--   | TyLet

-- data Pat
--   = PDCon Name [Name]
--   | PVar Name

-- data Tm
--   = Var Name
--   | Con Name
--   | App Tm Tm
--   | Lam [Pat] [Tm]
--   | Pi Name Tm Tm
--   | Let Name Tm Tm Unfold Tm
--   | U

-- data Head
--   = HDefined Name ~Val Unfold
--   | HCon Name
--   | HBound Name
--   | HGen Generic  
--   | HLam [Pat] (Val -> Val)

-- data Val
--   = VNe Head [Val]
--   | VLam [Pat] (Val -> Val)
--   | VPi Name ~Val (Val -> Val)
--   | VU

-- data TopDecl
--   = TopDef Tm Tm Unfold
--   | TopInductive (Sub Tm) Tm (Sub Tm)

-- pattern VLam1 :: Name -> (Val -> Val) -> Val
-- pattern VLam1 x t = VLam [PVar x] t

-- -- Evaluation
-- --------------------------------------------------------------------------------

-- (<:) :: (Name, Val) -> ValEnv -> ValEnv
-- (x, v) <: e = (x, (v, 0)) : e

-- evalVar :: ValEnv -> Name -> Val
-- evalVar e x = case lookup x e of
--   Just (v, 0) -> v
--   Just (v, u) -> VNe (HDefined x v u) []
--   _           -> VNe (HBound x) []

-- canonical :: Val -> Bool
-- canonical = \case
--   VNe HCon{} _ -> True
--   VLam{}       -> True
--   _            -> False

-- evalApp :: Val -> Val -> Val
-- evalApp f ~a = case f of
--   VLam _ t                -> t a
--   VNe (HDefined x v 1) vs | canonical a -> evalApp (foldr (flip evalApp) v vs) a    
--   VNe (HDefined x v u) vs -> VNe (HDefined x v (u - 1)) (a:vs)
--   VNe h                vs -> VNe h (a:vs)
--   _                       -> error "evalApp: impossible"

-- bindPat :: [Name] -> [Val] -> ValEnv -> ValEnv
-- bindPat (x:xs) (v:vs) e = (x, v) <: bindPat xs vs e
-- bindPat _      _      e = e

-- evalLam :: ValEnv -> [Pat] -> [Tm] -> Val -> Val
-- evalLam e ps ts = go ps ts where
--   go (PVar x:ps)     (t:ts) ~a = eval ((x, (a, 0)):e) t
--   go (PDCon x xs:ps) (t:ts)  a | VNe (HCon x') vs <- a, x == x' = eval (bindPat xs vs e) t
--   go (_:ps)          (_:ts)  a = go ps ts a
--   go _               _       a = VNe (HLam ps (evalLam e ps ts)) [a]

-- eval :: ValEnv -> Tm -> Val
-- eval e = \case
--   Var x           -> evalVar e x
--   Con x           -> VNe (HCon x) []
--   App f a         -> evalApp (eval e f) (eval e a)
--   Lam ps ts       -> VLam ps (evalLam e ps ts)
--   Pi x a b        -> VPi x (eval e a) (\a -> eval ((x, a) <: e) b)
--   U               -> VU
--   Let x ty t u t' -> let ~vt = eval ((x, (vt, u)):e) t
--                      in eval ((x, (vt, u)):e) t

-- qNe :: Tm -> [Val] -> Tm
-- qNe = foldr (\a t -> App t (quote a))

-- uBound :: Name -> Val
-- uBound x = VNe (HBound x) []

-- uPat :: Pat -> Val
-- uPat = \case
--   PVar x     -> uBound x
--   PDCon x xs -> VNe (HCon x) (map uBound xs)

-- qLam :: [Pat] -> (Val -> Val) -> [Tm]
-- qLam ps t = map (\p -> quote (t (uPat p))) ps

-- quote :: Val -> Tm
-- quote = \case
--   VNe h vs -> case h of
--     HDefined x v u -> qNe (Var x) vs
--     HCon x         -> qNe (Con x) vs
--     HBound x       -> qNe (Var x) vs
--     HLam ps t      -> qNe (Lam ps (qLam ps t)) vs
--     _              -> error "quote: impossible"
--   VLam ps t -> Lam ps (qLam ps t)
--   VPi x a b -> Pi x (quote a) (quote (b (uBound x)))
--   VU        -> U

-- --------------------------------------------------------------------------------

-- ulookup :: Eq a => a -> [(a, b)] -> b
-- ulookup a xs = fromJust $ lookup a xs

-- type M = Either T.Text

-- gen :: Generic -> Val
-- gen g = VNe (HGen g) []

-- genPat :: Generic -> Pat -> (Val, Generic)
-- genPat g = \case
--   PVar _     -> (VNe (HGen g) [], g + 1)
--   PDCon _ xs -> let l = length xs in (VNe (HGen g) (map gen [g + 1..l-1]), g + 1 + l)

-- conv :: Val -> Val -> Bool
-- conv = go 0 where
  
--   go g v v' = case (v, v') of
--     (VNe h vs , VNe h' vs'  ) -> goHead g h h' && and (zipWith (go g) vs vs')
--     (VLam ps t, VLam ps' t' ) -> goPats ps ps' && goLam g ps t t'
--     (VLam1 x t, t'          ) -> go (g + 1) (t (gen g)) (evalApp t' (gen g))
--     (t        , VLam1 x' t' ) -> go (g + 1) (evalApp t (gen g)) (t' (gen g))
--     (VPi x a b, VPi x' a' b') -> go g a a' && go (g + 1) (b (gen g)) (b' (gen g))
--     (VU       , VU          ) -> True
--     (_        , _           ) -> False

--   goHead g h h' = case (h, h') of
--     (HDefined x _ _ , HDefined x' _ _) -> x == x'
--     (HCon x         , HCon x')         -> x == x'
--     (HBound x       , HBound x')       -> x == x'
--     (HGen g         , HGen g')         -> g == g'
--     (HLam ps t      , HLam ps' t')     -> goPats ps ps' && goLam g ps t t'
--     _                                  -> False

--   goLam g ps t t' =
--     and (map (\p -> let (gp, g') = genPat g p in go g' (t gp) (t' gp)) ps)

--   goPat p p' = case (p, p') of
--     (PVar{}   , PVar{}    ) -> True
--     (PDCon x _, PDCon x' _) -> x == x'
--     _                       -> False
  
--   goPats ps ps' = case (ps, ps') of
--      (p:ps, p':ps') -> goPat p p' && goPats ps ps'
--      ([]  , []    ) -> True
--      _              -> False

-- indCons :: TyEnv -> VTy -> Maybe [(Name, VTy)]
-- indCons tys a = case a of
--   VNe (HCon x) vs | Just (TyTCon cs) <- snd <$> (lookup x tys) ->
--                     Just (map (\c -> (c, fst $ ulookup c tys)) cs)
--   _ -> Nothing

-- patternType :: [Name] -> VTy -> VTy
-- patternType = go where
--   go (x:xs) (VPi _ a b) = go xs (b (uBound x))
--   go _      t           = t

-- data Decision = Yes | No | Perhaps

-- instance Monoid Decision where
--   mempty = No
--   mappend No  _   = No
--   mappend _   No  = No
--   mappend Yes Yes = Yes
--   mappend _   _   = Perhaps

-- fromBool :: Bool -> Decision
-- fromBool = \case True -> Yes; _ -> No

-- unify :: VTy -> VTy -> State (Map Name Val) Decision
-- unify = go 0 where
--   go g a b = case (a, b) of
--     (VNe h vs, VNe h' vs') -> (<>) <$> goHead g h h' <*> _

--   goHead g h h' = case (h, h') of
--     (HDefined x _ _ , HDefined x' _ _) -> pure $ fromBool (x == x')
--     (HCon x         , HCon x')         -> pure $ fromBool (x == x')
--     (HBound x       , HBound x')       -> pure $ fromBool (x == x')
--     (HGen g         , HGen g')         -> pure $ fromBool (g == g')
--     (HLam ps t      , HLam ps' t')     -> _
--     _                                  -> pure No

--   -- goHead h h' = case (h, h') of
--   --   (


-- checkLam :: TyEnv -> ValEnv -> [Pat] -> [Tm] -> VTy -> (VTy -> VTy) -> M ()
-- checkLam tys vs ps ts a b = go (indCons tys a) [] ps where
--   go :: Maybe [(Name, VTy)] -> [Name] -> [Pat] -> M ()
--   go ~cs seen = \case
--     []            -> undefined
--     PVar x:[]     -> pure ()
--     PVar x:_      -> Left "unreachable pattern"
--     PDCon x xs:ps -> case cs of
--       Nothing -> Left "can only split on elements of inductive types"
--       Just cs -> do
--         when (elem x seen) $
--           Left $ "duplicate pattern"
--         cty <- maybe (Left "not a valid constructor") pure (lookup x cs)
--         let cs' = filter ((/=x).fst) cs
--         let pty = patternType xs cty
                
--         undefined

-- check :: TyEnv -> ValEnv -> Tm -> VTy -> M ()
-- check tys vs has want = case (has, want) of
--   (Lam ps ts, VPi x a b) ->
--     checkLam tys vs ps ts a b
--   (t, _) -> do
--     vt <- infer tys vs t
--     unless (conv vt want) $
--       Left $ "type mismatch"

-- inferName :: TyEnv -> Name -> M VTy
-- inferName tys x =
--   maybe (Left "infer: name not in scope") (pure . fst) $ lookup x tys

-- infer :: TyEnv -> ValEnv -> Tm -> M VTy
-- infer tys vs = \case
--   Var x -> inferName tys x
--   Con x -> inferName tys x
--   Lam ps ts -> Left "can't infer type for Lam"
--   Pi x a b -> do
--     check tys vs a VU
--     let ~va = eval vs a
--     check ((x, (va, TyBound)):tys) vs b VU
--     pure VU
--   U -> pure VU
--   Let x ty t u t' -> do
--     check tys vs ty VU
--     let ~vty = eval vs ty
--     check ((x,(vty, TyLet)):tys) vs t vty
--     let ~vt = eval ((x, (vt, u)):vs) t
--     infer ((x,(vty, TyLet)):tys) ((x, (vt, u)):vs) t'
--   App f a -> do
--     tf <- infer tys vs f
--     case tf of
--       VPi x ta tb -> do
--         check tys vs a ta
--         pure $ tb (eval vs a)
--       _ -> Left "infer: can't apply non-function"

-}
