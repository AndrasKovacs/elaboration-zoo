{-# language BangPatterns, Strict, LambdaCase, PatternGuards, OverloadedStrings #-}

import Control.Monad
import qualified Data.Text as T
import Data.Maybe

type Name    = T.Text
type Unfold  = Int
type Generic = Int
type Sub a   = [(Name, a)]
type ValEnv  = Sub (Val, Unfold)
type Ty      = Tm
type VTy     = Val
type TyEnv   = Sub (VTy, TyInfo)
type Program = Sub TopDecl

data TyInfo
  = TyDCon Name
  | TyTCon [Name]
  | TyBound
  | TyLet

data Pat
  = PDCon Name [Name]
  | PVar Name

data Tm
  = Var Name
  | App Tm Tm
  | Lam [Pat] [Tm]
  | Pi Name Tm Tm
  | Let Name Tm Tm Unfold Tm
  | U

data Head
  = HDefined Name ~Val Unfold
  | HRigid Name
  | HLam [Pat] (Val -> Val)
  | HGen Generic

data Val
  = VNe Head [Val]
  | VLam [Pat] (Val -> Val)
  | VPi Name ~Val (Val -> Val)
  | VU

data TopDecl
  = TopDef Tm Tm Unfold
  | TopInductive (Sub Tm) Tm (Sub Tm)

pattern VLam1 :: Name -> (Val -> Val) -> Val
pattern VLam1 x t = VLam [PVar x] t

-- Evaluation
--------------------------------------------------------------------------------

(<:) :: (Name, Val) -> ValEnv -> ValEnv
(x, v) <: e = (x, (v, 0)) : e

evalName :: ValEnv -> Name -> Val
evalName e x = case lookup x e of
  Just (v, 0) -> v
  Just (v, u) -> VNe (HDefined x v u) []
  _           -> VNe (HRigid x) []

evalApp :: Val -> Val -> Val
evalApp f ~a = case f of
  VLam _ t                -> t a
  VNe (HDefined x v 1) vs -> foldr evalApp v vs
  VNe (HDefined x v u) vs -> VNe (HDefined x v (u - 1)) (a:vs)
  VNe h                vs -> VNe h (a:vs)
  _                       -> error "evalApp: impossible"

bindPat :: [Name] -> [Val] -> ValEnv -> ValEnv
bindPat (x:xs) (v:vs) e = (x, v) <: bindPat xs vs e
bindPat _      _      e = e

evalLam :: ValEnv -> [Pat] -> [Tm] -> Val -> Val
evalLam e ps ts = go ps ts where
  go (PVar x:ps)     (t:ts) ~a = eval ((x, (a, 0)):e) t
  go (PDCon x xs:ps) (t:ts)  a | VNe (HRigid x') vs <- a, x == x' = eval (bindPat xs vs e) t
  go (_:ps)          (_:ts)  a = go ps ts a
  go _               _       a = VNe (HLam ps (evalLam e ps ts)) [a]

eval :: ValEnv -> Tm -> Val
eval e = \case
  Var x           -> evalName e x
  App f a         -> evalApp (eval e f) (eval e a)
  Lam ps ts       -> VLam ps (evalLam e ps ts)
  Pi x a b        -> VPi x (eval e a) (\a -> eval ((x, a) <: e) b)
  U               -> VU
  Let x ty t u t' -> let ~vt = eval ((x, (vt, u)):e) t
                     in eval ((x, (vt, u)):e) t

qNe :: Tm -> [Val] -> Tm
qNe = foldr (\a t -> App t (quote a))

uName :: Name -> Val
uName x = VNe (HRigid x) []

uPat :: Pat -> Val
uPat = \case
  PVar x     -> uName x
  PDCon x xs -> VNe (HRigid x) (map uName xs)

qLam :: [Pat] -> (Val -> Val) -> [Tm]
qLam ps t = map (\p -> quote (t (uPat p))) ps

quote :: Val -> Tm
quote = \case
  VNe h vs -> case h of
    HDefined x v u -> qNe (Var x) vs
    HRigid x       -> qNe (Var x) vs
    HLam ps t      -> qNe (Lam ps (qLam ps t)) vs
    _              -> error "quote: impossible"
  VLam ps t -> Lam ps (qLam ps t)
  VPi x a b -> Pi x (quote a) (quote (b (uName x)))
  VU        -> U

--------------------------------------------------------------------------------

ulookup :: Eq a => a -> [(a, b)] -> b
ulookup a xs = fromJust $ lookup a xs

type M = Either T.Text

gen :: Generic -> Val
gen g = VNe (HGen g) []

conv :: Val -> Val -> Bool
conv = go 0 where
  go g (VNe h vs)  (VNe h' vs')   = goHead g h h' && goVals g vs vs'
  go g (VLam ps t) (VLam ps' t')  = goPats g ps ps' && goLam g ps t t'
  go g (VLam1 x t) t'             = go (g + 1) (t (gen g)) (evalApp t' (gen g))
  go g t           (VLam1 x' t')  = go (g + 1) (evalApp t (gen g)) (t' (gen g))
  go g (VPi x a b) (VPi x' a' b') = go g a a' && go (g + 1) (b (gen g)) (b' (gen g))
  go g VU          VU             = True
  go g _           _              = False

  goHead g h h'   = undefined
  goLam g ps t t' = undefined
  goPats g ps ps' = undefined
  goVals g vs vs' = undefined

indDCons :: TyEnv -> VTy -> Maybe [(Name, VTy)]
indDCons tys a = case a of
  VNe (HRigid x) vs | Just (TyTCon cs) <- snd <$> (lookup x tys) ->
                      Just (map (\c -> (c, fst $ ulookup c tys)) cs)
  _ -> Nothing

checkPats :: TyEnv -> [Pat] -> VTy -> M ()
checkPats tys ps a = go ps where
  ~dcons = indDCons tys a
  go []              = pure ()
  go (PVar x:[])     = pure ()
  go (PVar x:_)      = Left "unreachable pattern"
  go (PDCon x xs:ps) = case dcons of
    Nothing    -> Left "can't split on type"
    Just dcons -> do
      _

checkLam :: TyEnv -> ValEnv -> [Pat] -> [Tm] -> VTy -> (VTy -> VTy) -> M ()
checkLam tys vs ps ts a b = undefined

check :: TyEnv -> ValEnv -> Tm -> VTy -> M ()
check tys vs has want = case (has, want) of
  (Lam ps ts, VPi x a b) -> do
    checkPats tys ps a
    checkLam tys vs ps ts a b
  (t, _) -> do
    vt <- infer tys vs t
    unless (conv vt want) $
      Left $ "type mismatch"

infer :: TyEnv -> ValEnv -> Tm -> M VTy
infer tys vs = \case
  Var x -> maybe (Left "infer: name not in scope") (pure . fst) $ lookup x tys
  Lam ps ts -> Left "can't infer type for Lam"
  Pi x a b -> do
    check tys vs a VU
    let ~va = eval vs a
    check ((x, (va, TyBound)):tys) vs b VU
    pure VU
  U -> pure VU
  Let x ty t u t' -> do
    check tys vs ty VU
    let ~vty = eval vs ty
    check ((x,(vty, TyLet)):tys) vs t vty
    let ~vt = eval ((x, (vt, u)):vs) t
    infer ((x,(vty, TyLet)):tys) ((x, (vt, u)):vs) t'
  App f a -> do
    tf <- infer tys vs f
    case tf of
      VPi x ta tb -> do
        check tys vs a ta
        pure $ tb (eval vs a)
      _ -> Left "infer: can't apply non-function"
