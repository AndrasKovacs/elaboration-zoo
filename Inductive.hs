{-# language BangPatterns, MagicHash, LambdaCase, Strict, CPP, PatternGuards #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

{-| A minimal U : U type theory with simple inductive types -}

module Inductive where

import Data.Maybe

type Name = String
type Gen  = Int

-- Terms
type Ty = Tm
type Fn = Tm

data Tm
  = Var Name
  | Gen Gen
  | Let Name Ty Tm Tm

  -- Universe
  | U

  -- Functions
  | Pi Name Ty Ty
  | Lam Name Tm
  | App Tm Tm

  -- Inductive types
  | F
  | FI | FK Ty | FProd Fn Fn | FSum Fn Fn
  | Fix Fn
  | Con Tm
  | Ind Tm Tm Tm

  -- Top
  | Top
  | Tt

  -- Identity functor
  | Id Ty
  | I Tm
  | GetI Tm

  -- Constant functor
  | Const Ty Ty
  | K Tm
  | GetK Tm

  -- Products
  | Prod Ty Ty
  | Pair Tm Tm
  | Fst Tm
  | Snd Tm

  -- Coproducts
  | Sum Ty Ty
  | Inj1 Tm
  | Inj2 Tm
  | Case Tm Tm Tm Tm
  deriving Show

-- Values
type VTy = VTm
type VFn = VTm

data VTm
  = VVar Name
  | VGen Gen

  | VU

  -- Inductive types
  | VF
  | VFI | VFK VTm | VFProd VTm VTm | VFSum VTm VTm
  | VFix VFn
  | VCon VTm
  | VInd ~VTm VTm

  -- Functions
  | VPi VTy (VTm -> VTy)
  | VLam (VTm -> VTm)
  | VApp VTm ~VTm

  -- Top
  | VTop
  | VTt

  -- Identity functor
  | VId VTy
  | VI VTm
  | VGetI VTm

  -- Constant functor
  | VConst VTy VTy
  | VK VTm
  | VGetK VTm

  -- Products
  | VProd VTy VTy
  | VPair VTm VTm
  | VFst VTm
  | VSnd VTm

  -- Coproducts
  | VSum VTy VTy
  | VInj1 VTm
  | VInj2 VTm
  | VCase ~VTm ~VTm VTm

-- Evaluation
--------------------------------------------------------------------------------

impossible :: a
impossible = error "impossible"

type Sub a = [(Name, a)]
type VTms = Sub (Maybe VTm)

vApp :: VTm -> VTm -> VTm
vApp t ~u = case t of
  VLam t -> t u
  t      -> VApp t u

vInd :: VTm -> VTm -> VTm
vInd ~m = \case
  VCon t -> (m `vApp` t) `vApp` go t where
    go = \case
      VI t    -> vInd m t
      VK t    -> VTt
      VInj1 t -> _
      VInj2 t -> _

  t      -> VInd m t

vGetI :: VTm -> VTm
vGetI = \case VI t -> t; t -> VGetI t

vGetK :: VTm -> VTm
vGetK = \case VK t -> t; t -> VGetK t

vFst :: VTm -> VTm
vFst = \case VPair t _ -> t; t -> VFst t

vSnd :: VTm -> VTm
vSnd = \case VPair _ u -> u; t -> VSnd t

vCase :: VTm -> VTm -> VTm -> VTm
vCase ~l ~r = \case
  VInj1 t -> vApp l t
  VInj2 t -> vApp r t
  t       -> VCase l r t

eval :: Int -> VTms -> Tm -> VTm
eval g vs = \case
  Var x        -> maybe (VVar x) id (maybe impossible id $ lookup x vs)
  Gen g'       -> VGen g'
  Let x a t u  -> eval (g + 1) ((x, Just (eval g vs t)):vs) u
  U            -> VU
  Pi x a b     -> VPi (eval g vs a) (\v -> eval (g + 1) ((x, Just v):vs) b)
  Lam x t      -> VLam (\v -> eval (g + 1) ((x, Just v):vs) t)
  App t u      -> vApp (eval g vs t) (eval g vs u)
  F            -> VF
  FI           -> VFI
  FK a         -> VFK (eval g vs a)
  FProd f g'   -> VFProd (eval g vs f) (eval g vs g')
  FSum f g'    -> VFSum (eval g vs f) (eval g vs g')
  Fix f        -> VFix (eval g vs f)
  Con t        -> VCon (eval g vs t)
  Ind a t u    -> vInd (eval g vs t) (eval g vs u)
  Top          -> VTop
  Tt           -> VTt
  Id a         -> VId (eval g vs a)
  I t          -> VI (eval g vs t)
  GetI t       -> vGetI (eval g vs t)
  Const a b    -> VConst (eval g vs a) (eval g vs b)
  K t          -> VK (eval g vs t)
  GetK t       -> vGetK (eval g vs t)
  Prod a b     -> VProd (eval g vs a) (eval g vs b)
  Pair t u     -> VPair (eval g vs t) (eval g vs u)
  Fst t        -> vFst (eval g vs t)
  Snd t        -> vSnd (eval g vs t)
  Sum a b      -> VSum (eval g vs a) (eval g vs b)
  Inj1 t       -> VInj1 (eval g vs t)
  Inj2 t       -> VInj2 (eval g vs t)
  Case a l r t -> vCase (eval g vs l) (eval g vs r) (eval g vs t)
