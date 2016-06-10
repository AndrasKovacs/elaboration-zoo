
{-# language PatternSynonyms, BangPatterns, MagicHash, LambdaCase #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

module Glued where

import Prelude hiding (pi)
import Data.String
import Control.Monad
import Control.Applicative
import Control.Monad.Except
import Data.Either
import GHC.Prim (reallyUnsafePtrEquality#)
import GHC.Types (isTrue#)

import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as M

import Syntax (RawTerm)
import qualified Syntax as S

ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y)
{-# inline ptrEq #-}

-- Data
--------------------------------------------------------------------------------

-- Concrete
type QType = QTerm
data QTerm
  = QVar !String
  | QApp !QTerm !QTerm
  | QPi !String !QType !QTerm
  | QLam !String !QTerm
  | QStar
  | QAnn !QTerm !QType
  deriving (Show)

-- Abstract
type AType = ATerm
data ATerm
  = AVar !String
  | AApp !ATerm !ATerm -- ^ We can apply to 'Pi' as well.
  | APi !String !AType !ATerm
  | ALam !String !AType !ATerm
  | AStar
  | Close {-# unpack #-} !Closure
  deriving (Show)

-- Weak head normal
data Whnf
  = VVar !String
  | Alpha !Int
  | VApp !Whnf Whnf
  | VPi  !String !AType {-# unpack #-} !Closure
  | VLam !String !AType {-# unpack #-} !Closure
  | VStar
  deriving (Show)

data Closure = C !Env !ATerm
  deriving (Show)

type GType = Glued
data Glued = G {-# unpack #-} !Closure Whnf deriving (Show)

_unreduced (G u _) = u
_whnf      (G _ v) = v

data Entry = E {-# unpack #-} !Glued {-# unpack #-} !Glued deriving (Show)

_term (E t _) = t
_type (E _ v) = v

type Env = HashMap String Entry
type TM  = Either String

instance IsString ATerm where fromString = AVar
instance IsString Whnf  where fromString = VVar
instance IsString QTerm where fromString = QVar

-- Reduction
--------------------------------------------------------------------------------

glued :: Env -> ATerm -> Glued
glued e t = G (C e t) (whnf e t)

whnf :: Env -> ATerm -> Whnf
whnf e = \case
  AApp f x -> case whnf e f of
    VLam v ty (C e' t) -> whnf (M.insert v (E (glued e x) (glued e ty)) e') t
    VPi  v ty (C e' t) -> whnf (M.insert v (E (glued e x) (glued e ty)) e') t
    f'                 -> VApp f' (whnf e x)
  AVar v         -> _whnf $ _term $ e ! v
  APi  v ty t    -> VPi  v ty (C e t)
  ALam v ty t    -> VLam v ty (C e t)
  AStar          -> VStar
  Close (C e' t) -> whnf e' t

quoteVar :: Env -> String -> GType -> Entry
quoteVar e v ty = E (G (C e (AVar v)) (VVar v)) ty

-- TODO: eta-expansion (need to add Alpha to ATerm too)
alpha :: Int -> Env -> AType -> Entry
alpha a e ty = E (G (C e (error "alpha")) (Alpha a)) (glued e ty)

nf :: Env -> ATerm -> ATerm
nf e t = quote (whnf e t)

quote :: Whnf -> ATerm
quote = \case
  VVar v            -> AVar v
  VApp f x          -> AApp (quote f) (quote x)
  VPi  v ty (C e t) -> APi  v (nf e ty) (nf (M.insert v (quoteVar e v (glued e ty)) e) t)
  VLam v ty (C e t) -> ALam v (nf e ty) (nf (M.insert v (quoteVar e v (glued e ty)) e) t)
  VStar             -> AStar
  Alpha{}           -> error "quote: Alpha in Whnf"


-- Equality without reduction
--------------------------------------------------------------------------------

termSemiEq :: Env -> Env -> Int -> ATerm -> ATerm -> Maybe Bool
termSemiEq e e' !b t t' = case (t, t') of
  (Close (C e t), t')  -> termSemiEq e e' b t t'
  (t, Close (C e' t')) -> termSemiEq e e' b t t'

  (AVar v, AVar v') -> case (_whnf $ _term $ e ! v, _whnf $ _term $ e' ! v') of
    (Alpha b, Alpha b') -> Just (b == b')
    (x      , y       ) -> True <$ guard (ptrEq x y)
  (AVar{}, _) -> Nothing
  (_, AVar{}) -> Nothing

  (AApp f x, AApp f' x') ->
    True <$ do {guard =<< termSemiEq e e' b f f'; guard =<< termSemiEq e e' b x x'}
  (AApp{}, _) -> Nothing
  (_, AApp{}) -> Nothing

  (ALam v ty t, ALam v' ty' t') -> (&&) <$> termSemiEq e e' b ty ty' <*>
    (let al = alpha b e ty in termSemiEq (M.insert v al e) (M.insert v' al e') (b + 1) t t')
  (APi  v ty t, APi  v' ty' t') -> (&&) <$> termSemiEq e e' b ty ty' <*>
    (let al = alpha b e ty in termSemiEq (M.insert v al e) (M.insert v' al e') (b + 1) t t')
  (AStar, AStar) -> Just True
  _              -> Just False


-- Equality with reduction
--------------------------------------------------------------------------------

whnfEq :: Int -> Whnf -> Whnf -> Bool
whnfEq !b t t' = case (t, t') of
  (VVar v,   VVar v'   ) -> v == v'
  (VApp f x, VApp f' x') -> whnfEq b f f' && whnfEq b x x'
  (VLam v ty (C e t), VLam v' ty' (C e' t')) ->
    termEq e e' b ty ty' &&
    let al = alpha b e ty
    in termEq (M.insert v al e) (M.insert v' al e') (b + 1) t t'
  (VPi v ty (C e t), VPi v' ty' (C e' t')) ->
    termEq e e' 0 ty ty' &&
    let al = alpha b e ty
    in termEq (M.insert v al e) (M.insert v' al e') (b + 1) t t'
  (VStar, VStar) -> True
  _              -> False

termEq :: Env -> Env -> Int -> ATerm -> ATerm -> Bool
termEq e e' !b t t' = case (t, t') of
  (Close (C e t), t')  -> termEq e e' b t t'
  (t, Close (C e' t')) -> termEq e e' b t t'

  (AVar v, AVar v') -> case (_whnf $ _term $ e ! v, _whnf $ _term $ e' ! v') of
    (Alpha b, Alpha b') -> b == b'
    (x      , y       ) -> ptrEq x y || continue

  (AApp f x, AApp f' x') ->
    maybe False id (liftA2 (&&) (termSemiEq e e' b f f') (termSemiEq e e' b x x'))
    || continue
  _ -> continue

  where continue = whnfEq b (whnf e t) (whnf e' t')

gluedEq :: Glued -> Glued -> Bool
gluedEq (G (C e t) v) (G (C e' t') v') =
  maybe False id (termSemiEq e e' 0 t t') || whnfEq 0 v v'

-- Type checking / elaboration
--------------------------------------------------------------------------------

gstar :: GType
gstar = G (C mempty AStar) VStar

check :: Env -> QTerm -> GType -> TM ATerm
check e t want = case (t, _whnf want) of
  (QLam v t, VPi v' a (C e' b)) -> do
    let a' = glued e' a
    t' <- check (M.insert v (quoteVar e v a') e) t
                (glued (M.insert v' (quoteVar e' v' a') e') b)
    pure $ ALam v (Close (_unreduced a')) t'

  _ -> do
    (t', has) <- infer e t
    unless (gluedEq has want) $ Left "type mismatch"
    pure t'

infer :: Env -> QTerm -> TM (ATerm, Glued)
infer e = \case
  QVar v    -> pure (AVar v, _type $ e ! v)
  QStar     -> pure (AStar, gstar)
  QAnn t ty -> do
    ty' <- glued e <$> check e ty gstar
    t'  <- check e t ty'
    pure (t', ty')
  QLam{} -> Left "can't infer type for lambda"
  QPi v ty t -> do
    ty' <- check e ty gstar
    t'  <- check (M.insert v (quoteVar e v (glued e ty')) e) t gstar
    pure (APi v ty' t', gstar)
  QApp f x -> do
    (f', tf) <- infer e f
    case _whnf tf of
      VPi v a (C e' b) -> do
        let a' = glued e' a
        x' <- check e x a'
        pure (AApp f' x',
              G (C e (AApp (Close (_unreduced tf)) x'))
                (whnf (M.insert v (E (glued e x') a') e') b))
      _ -> Left "can't apply to non-function"


-- tests
--------------------------------------------------------------------------------


nf0 = nf mempty
termSemiEq0 = termSemiEq mempty mempty
termEq0 = termEq mempty mempty
whnf0 = whnf mempty



