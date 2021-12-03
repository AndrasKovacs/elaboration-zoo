
{-# language LambdaCase, Strict, OverloadedStrings, DerivingVia #-}
{-# options_ghc -Wincomplete-patterns #-}

{-|
Simple universe polymorphism. Features:

  - Non-first-class levels: there is a distinct Pi, lambda and application for
    levels. Levels are distinct from terms in syntax/values.
  - The surface language only allows abstraction over finite levels. Internally,
    the type of level-polymorphic functions is (U omega), but that's not
    accessible to programmers.
  - Bidirectional elaboration.
  - We have zero, suc, maximum and bound variables in finite levels.
  - Pi returns in (U (max i j)).
  - Conversion checking for finite levels is complete w.r.t. the obvious
    semantics for the supported operations. For example, (suc (max x (max y z)))
    is convertible to (max (suc y) (max (suc z) (suc x))).

Remark: even if we add metavariables to this system, it should be in fact
sufficient to *not* thread levels in infer/check, not store levels in binders,
and to have unification which is heterogeneous in levels, i.e. when unifying
types, their levels my differ.

The reason is that non-first-class levels have no impact on
computation. Intuitively, if all levels are erased from the elaborator, we just
recover elaboration for a type-in-type system, and this elaboration is already
sound and semidecidable.

-}

module UnivPoly where

import qualified Data.IntMap.Strict as M

import Data.Foldable
import Data.Maybe
import Data.String
import Debug.Trace
import Data.Coerce

--------------------------------------------------------------------------------

-- | De Bruijn indices.
newtype Ix  = Ix Int deriving (Eq, Show, Ord, Num) via Int

-- | De Bruijn levels.
newtype Lvl = Lvl Int deriving (Eq, Show, Ord, Num) via Int

lvlToIx :: Lvl -> Lvl -> Ix
lvlToIx l x = coerce (l - x - 1)

-- Universe levels
--------------------------------------------------------------------------------

data FinLevel
  = FLVar Ix
  | FLSuc FinLevel
  | FLZero
  | FLMax FinLevel FinLevel
  deriving Show

data Level
  = Omega
  | FinLevel FinLevel
  deriving Show

-- | Finite levels are of the form `maximum [n₀, x₁ + n₁, x₂ + n₂, ... xᵢ + nᵢ]`,
-- | where the `n₀` is the first `Int` field, and the `M.Map` maps zero or more xᵢ rigid
--   level variables to the nᵢ values.
data VFinLevel = VFL Int (M.IntMap Int)
  deriving (Eq, Show)

-- | Universe levels.
data VLevel
  -- | The limit of all finite levels.
  = VOmega
  | VFinLevel {-# unpack #-} VFinLevel
  deriving (Eq, Show)

instance Semigroup VFinLevel where
  VFL n xs <> VFL n' xs' = VFL (max n n') (M.unionWith max xs xs')

instance Monoid VFinLevel where
  mempty = VFL 0 mempty

instance Semigroup VLevel where
  VFinLevel i <> VFinLevel j = VFinLevel (i <> j)
  _           <> _           = VOmega

instance Monoid VLevel where
  mempty = VFinLevel mempty

vFinLevelVar :: Lvl -> VFinLevel
vFinLevelVar x = VFL 0 (M.singleton (coerce x) 0)

addToVFinLevel :: Int -> VFinLevel -> VFinLevel
addToVFinLevel n (VFL m xs) = VFL (n + m) ((+n) <$> xs)

addToFinLevel :: Int -> FinLevel -> FinLevel
addToFinLevel n i = go n i where
  go 0 i = i
  go n i = go (n - 1) (FLSuc i)

vSuc :: VFinLevel -> VFinLevel
vSuc = addToVFinLevel 1

-- Raw syntax
--------------------------------------------------------------------------------

type Name = String
type RTy  = RTm

data RLevel
  = RLVar Name
  | RLSuc RLevel          -- ^ suc i
  | RLZero                -- ^ 0
  | RLMax RLevel RLevel   -- ^ i ⊔ j
  deriving Show

data RTm
  = RVar Name
  | RApp RTm RTm          -- ^ t u
  | RLvlApp RTm RLevel    -- ^ t @i
  | RLam Name RTm         -- ^ λ x. t
  | RLvlLam Name RTm      -- ^ λ (i : Level). t
  | RPi Name RTm RTm      -- ^ (x : A)     → B
  | RLvlPi Name RTm       -- ^ (i : Level) → B
  | RLet Name RTy RTm RTm -- ^ let x : A = t; u
  | RU RLevel             -- ^ U i
  deriving Show

--------------------------------------------------------------------------------

type Ty = Tm

data Tm
  = Var Ix
  | App Tm Tm
  | LvlApp Tm FinLevel
  | Lam Name Tm
  | LvlLam Name Tm
  | Pi Name Tm Tm
  | LvlPi Name Tm
  | Let Name Ty Tm Tm
  | U Level
  deriving Show

type VTy = Val

data Val
  = VVar Lvl
  | VApp Val ~Val
  | VLvlApp Val VFinLevel
  | VLam Name (Val -> Val)
  | VLvlLam Name (VFinLevel -> Val)
  | VPi Name Val (Val -> Val)
  | VLvlPi Name (VFinLevel -> Val)
  | VU VLevel

data Env = ENil | EVal Env ~Val | EFinLevel Env {-# unpack #-} VFinLevel

levelVar :: Env -> Ix -> VFinLevel
levelVar (EFinLevel _ i) 0 = i
levelVar (EFinLevel e i) x = levelVar e (x - 1)
levelVar (EVal _ _     ) 0 = undefined
levelVar (EVal e _     ) x = levelVar e (x - 1)
levelVar ENil            _ = undefined

var :: Env -> Ix -> Val
var (EFinLevel _ i) 0 = undefined
var (EFinLevel e i) x = var e (x - 1)
var (EVal _ t     ) 0 = t
var (EVal e _     ) x = var e (x - 1)
var ENil            _ = undefined

finLevel :: Env -> FinLevel -> VFinLevel
finLevel e = \case
  FLZero    -> mempty
  FLSuc i   -> addToVFinLevel 1 (finLevel e i)
  FLMax i j -> finLevel e i <> finLevel e j
  FLVar x   -> levelVar e x

level :: Env -> Level -> VLevel
level e = \case
  Omega       -> VOmega
  FinLevel i  -> VFinLevel (finLevel e i)

eval :: Env -> Tm -> Val
eval e = \case
  Var x       -> var e x
  App t u     -> case (eval e t, eval e u) of
                   (VLam _ t, u) -> t u
                   (t, u)        -> VApp t u
  LvlApp t u  -> case (eval e t, finLevel e u) of
                   (VLvlLam _ t, u) -> t u
                   (t, u)           -> VLvlApp t u
  Lam x t     -> VLam x (\u -> eval (EVal e u) t)
  LvlLam x t  -> VLvlLam x (\i -> eval (EFinLevel e i) t)
  Pi x a b    -> VPi x (eval e a) (\u -> eval (EVal e u) b)
  LvlPi x b   -> VLvlPi x (\i -> eval (EFinLevel e i) b)
  Let x a t u -> eval (EVal e (eval e t)) u
  U i         -> VU (level e i)

conv :: Lvl -> Val -> Val -> Bool
conv l t t' = case (t, t') of
  (VVar x      , VVar x'     ) -> x == x'
  (VApp t u    , VApp t' u'  ) -> conv l t t' && conv l u u'
  (VLam x t    , VLam _ t'   ) -> conv (l + 1) (t (VVar l)) (t' (VVar l))
  (VLam x t    , t'          ) -> conv (l + 1) (t (VVar l)) (VApp t' (VVar l))
  (t           , VLam x t'   ) -> conv (l + 1) (VApp t (VVar l)) (t' (VVar l))
  (VPi x a b   , VPi _ a' b' ) -> conv l a a' && conv (l + 1) (b (VVar l)) (b' (VVar l))
  (VU i        , VU i'       ) -> i == i'
  _                            -> False

quoteFinLevel :: Lvl -> VFinLevel -> FinLevel
quoteFinLevel l (VFL n xs) =
  M.foldlWithKey
    (\i x n -> FLMax i (addToFinLevel n (FLVar (lvlToIx l (Lvl x)))))
    (addToFinLevel n FLZero)
    xs

quoteLevel :: Lvl -> VLevel -> Level
quoteLevel l = \case
  VOmega      -> Omega
  VFinLevel i -> FinLevel (quoteFinLevel l i)

quote :: Lvl -> Val -> Tm
quote l = \case
  VVar x      -> Var (lvlToIx l x)
  VApp t u    -> App (quote l t) (quote l u)
  VLvlApp t i -> LvlApp (quote l t) (quoteFinLevel l i)
  VLam x t    -> Lam x (quote (l + 1) (t (VVar l)))
  VLvlLam x t -> LvlLam x (quote (l + 1) (t (vFinLevelVar l)))
  VPi x a b   -> Pi x (quote l a) (quote (l + 1) (b (VVar l)))
  VLvlPi x b  -> LvlPi x (quote (l + 1) (b (vFinLevelVar l)))
  VU i        -> U (quoteLevel l i)

nf :: Tm -> Tm
nf = quote 0 . eval ENil

--------------------------------------------------------------------------------

type M = Either String

data Binders = BNil | BType Binders Name ~VTy | BLevel Binders Name

data Cxt = Cxt {env :: Env, binders :: Binders, lvl :: Lvl}

define :: Name -> VTy -> Val -> Cxt -> Cxt
define x a ~t (Cxt e bs l) = Cxt (EVal e t) (BType bs x a) (l + 1)

bind :: Name -> VTy -> Cxt -> Cxt
bind x a (Cxt e bs l) = Cxt (EVal e (VVar l)) (BType bs x a) (l + 1)

bindLevel :: Name -> Cxt -> Cxt
bindLevel x (Cxt e bs l) =
  Cxt (EFinLevel e (vFinLevelVar l)) (BLevel bs x) (l + 1)

check :: Cxt -> RTm -> VTy -> M Tm
check cxt t a = case (t, a) of

  (RLam x t, VPi x' a b) -> do
    Lam x <$> check (bind x a cxt) t (b (VVar (lvl cxt)))

  (RLvlLam x t, VLvlPi x' b) -> do
    LvlLam x <$> check (bindLevel x cxt) t (b (vFinLevelVar (lvl cxt)))

  (RLet x a t u, b) -> do
    (a, _) <- checkTy cxt a
    let ~va = eval (env cxt) a
    u <- check cxt t va
    t <- check (define x va (eval (env cxt) u) cxt) t b
    pure (Let x a t u)

  (t, a) -> do
    (t, a') <- infer cxt t
    if conv (lvl cxt) a a'
      then pure t
      else Left $ "Type mismatch, expected\n\n    "
            ++ show (quote (lvl cxt) a)
            ++ "\n\ninferred\n\n    " ++ show (quote (lvl cxt) a')

checkTy :: Cxt -> RTm -> M (Tm, VLevel)
checkTy cxt t = do
  (t, a) <- infer cxt t
  case a of
    VU l -> pure (t, l)
    _    -> Left "expected a type"

inferLevelVar :: Cxt -> Name -> M Lvl
inferLevelVar (Cxt _ bs l) x = go l bs where
  go l BNil                       = Left $ "Name not in scope: " ++ x
  go l (BType bs _ _)             = go (l - 1) bs
  go l (BLevel bs x') | x == x'   = pure $! l - 1
                      | otherwise = go (l - 1) bs

inferVar :: Cxt -> Name -> M (Lvl, VTy)
inferVar (Cxt _ bs l) x = go l bs where
  go l BNil                        = Left $ "Name not in scope: " ++ x
  go l (BLevel vs _)               = go (l - 1) bs
  go l (BType bs x' a) | x == x'   = pure (l - 1, a)
                       | otherwise = go (l - 1) bs

checkFinLevel :: Cxt -> RLevel -> M FinLevel
checkFinLevel cxt = \case
  RLVar x   -> do x <- inferLevelVar cxt x
                  pure (FLVar (lvlToIx (lvl cxt) x))
  RLSuc i   -> FLSuc <$> checkFinLevel cxt i
  RLZero    -> pure FLZero
  RLMax i j -> FLMax <$> checkFinLevel cxt i <*> checkFinLevel cxt j

infer :: Cxt -> RTm -> M (Tm, VTy)
infer cxt = \case

  RVar x -> do
    (x, a) <- inferVar cxt x
    pure (Var (lvlToIx (lvl cxt) x), a)

  RApp t u -> do
    (t, a) <- infer cxt t
    case a of
      VPi x a b -> do
        u <- check cxt u a
        pure (App t u, b (eval (env cxt) u))
      _ ->
        Left "expected a function"

  RLvlApp t i -> do
    (t, a) <- infer cxt t
    case a of
      VLvlPi x b -> do
        i <- checkFinLevel cxt i
        pure (LvlApp t i, b (finLevel (env cxt) i))
      _ ->
        Left "expected a level-polymorphic function"

  RLvlPi x b -> do
    (b, bl) <- checkTy (bindLevel x cxt) b
    pure (LvlPi x b, VU VOmega)

  RLam{} ->
    Left "can't infer type for lambda"

  RLvlLam{} ->
    Left "can't infer type for lambda"

  RPi x a b -> do
    (a, al) <- checkTy cxt a
    (b, bl) <- checkTy (bind x (eval (env cxt) a) cxt) b
    pure (Pi x a b, VU (al <> bl))

  RLet x a t u -> do
    (a, al) <- checkTy cxt a
    let ~va = eval (env cxt) a
    t <- check cxt t va
    (u, b) <- infer (define x va (eval (env cxt) t) cxt) u
    pure (Let x a t u, b)

  RU i -> do
    i <- checkFinLevel cxt i
    pure (U (FinLevel i), VU (VFinLevel (vSuc (finLevel (env cxt) i))))


elab :: RTm -> IO ()
elab t = do
  case infer (Cxt ENil BNil 0) t of
    Left err -> putStrLn err
    Right (t, a) -> do
      putStrLn "---- term ----"
      print t
      putStrLn "---- nf   ----"
      print $ nf t
      putStrLn "---- type ----"
      print $ quote 0 a


instance IsString RTm where fromString = RVar
instance IsString RLevel where fromString = RLVar

infixl 7 $$
infixl 7 $$$
infixr 4 ==>
($$)  = RApp
($$$) = RLvlApp
(==>) = RPi "_"

--------------------------------------------------------------------------------

-- elab p1
p1 =
  RLet "id" (RLvlPi "i" $ RPi "A" (RU "i") $ "A" ==> "A")
            (RLvlLam "i" $ RLam "A" $ RLam "x" "x") $
  "id" $$$ RLSuc (RLSuc RLZero) $$ RU (RLSuc RLZero) $$ RU RLZero

p2 = RLvlPi "i" $ RPi "A" (RU "i") $ "A" ==> "A"
