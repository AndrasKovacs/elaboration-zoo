
{-# language
  PatternSynonyms, BangPatterns, MagicHash,
  DataKinds, LambdaCase, ViewPatterns,
  TypeFamilies, GADTs, EmptyCase, OverloadedStrings #-}

{-# options_ghc -fwarn-incomplete-patterns #-}

module Glued3 where

import Prelude hiding (pi)
import Control.Monad
import Data.Either
import Control.Monad.Except
import GHC.Prim (reallyUnsafePtrEquality#)
import GHC.Types (isTrue#)
import Data.String

import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as M

import Debug.Trace

tracing :: Show a => a -> a
tracing a = traceShow a a

{-

  Glued principles:

    1. We infer unreduced and lazy whnf types simulataneously

    2. Whenever we have a Term, we must also have at hand:
      - its lazy whnf form
      - its unreduced type
      - its lazy whnf type
      - all of the previous for all of its free variables, recursively

    3. We never recompute whnf, types, or whnf of types for any Term

    4. Time and space overhead of storing unreduced terms must be O(1)
       in the size of the source code, compared to non-glued type checking
       with beta-eta conversions.

    5. NOT YET IMPLEMENTED: we don't retain more entries in environments
       than an STG machine would.

    6. No new Terms may be created and stored during type checking,
       expect when created by PiApp. Since PiApp-s are bounded by
       source code size, Terms in general are bounded by source code size as well.

    7. No new Var-s may be created. All Var-s come from the source code.
       The only available operations on Var-s are equality checking and
       Env insertion/lookup.

-}


{-
  Notes:
    - Separate raw and core syntax. Core may have type annotations inside spines
      or elsewhere.
    - Question: how to properly convert unannotated arg lambdas to annotated?
    - Include metadata on binders: lam | pi | let | unfolding rules etc.

    - Question: what is the best spine / App data shape?
      - Outer application first: easier to apply
      - Inner application first: faster to wapp

    - Can't fully ditch PiApp in favor of metadata:
          - "PiApp (Sp sp)" y can't be reduced
          - Only PiApp "PiApp (Pi v a b) y" can be reduced to "b [v := (y, a)]"

    - Have proper env entries for Gen and Bound variables.
    - One unchanging global env + small closures
    - Closure conversion for Core syntax.
    - How to easily switch between untyped and typed local closures?
    - Unique global binder identifiers

  Implementation niceties:
    put Env in a Reader, use "local"
    use phantom tags on Env-Term pairs ?
    Revamp diving and quoting nomeclature, maybe introduce overloading?
    Think about better scoping and reducing API

    phantom tag Term-s with their Env-s, pass the Env around implicitly,
      a bit like Reflection?

-}

type Var   = String
type Gen   = Int
type Depth = Int

data Sp
  = Var !Var
  | Gen !Gen !GType -- only for syntactic equality
  | App !Sp !Term
  deriving Show

data Term
  = Sp !Sp
  | Pi !Var !Type !Term
  | Let !Var !Term !Type !Term
  | Star
  | Lam !Var !Term
  | PiApp !Term {-# unpack #-} !Entry -- only in inferred types
  deriving Show

data WSp
  = WGen !Gen
  | WVar !Var -- only for quoting
  | WApp !WSp WTerm WType
  deriving Show

data WTerm
  = WSp !WSp
  | WPi  {-# unpack #-} !WPi_
  | WLam {-# unpack #-} !WLam_
  | WStar
  deriving Show

type Type    = Term
type WType   = WTerm
data Closure = C !Env !Term deriving Show
data GTerm   = G {-# unpack #-} !Closure WTerm deriving Show
type GType   = GTerm
data Entry   = E {-# unpack #-} !GTerm {-# unpack #-} !GType deriving Show
type Env     = HashMap Var Entry
data WPi_    = WPi_ !Env !Var !Type WType !Term deriving Show
data WLam_   = WLam_ !Env !Var !Term deriving Show
type M       = Either String

-- misc
--------------------------------------------------------------------------------

gen :: Gen -> GType -> GTerm
gen g gty = G (C mempty (Sp (Gen g gty))) (WSp (WGen g))

var :: Var -> GTerm
var v = G (C mempty (Sp (Var v))) (WSp (WVar v))

domG :: WPi_ -> GType
domG (WPi_ e v a wa b) = G (C e a) wa

domW :: WPi_ -> WType
domW (WPi_ _ _ _ wa _) = wa

lamVar :: WLam_ -> Var
lamVar (WLam_ e v t) = v

domVar :: WPi_ -> Var
domVar (WPi_ _ v _ _ _) = v

getW :: GTerm -> WTerm
getW (G _ wt) = wt

gstar :: GType
gstar = G (C mempty Star) WStar

(<:) :: Env -> (Var, GTerm, GType) -> Env
e <: (v, gt, gty) = M.insert v (E gt gty) e

-- Whnf
--------------------------------------------------------------------------------

wapp :: WPi_ -> WTerm -> GTerm -> WTerm
wapp pi (WLam lam) gt = instLam lam pi gt
wapp pi (WSp  sp ) gt = WSp (WApp sp (getW gt) (domW pi))
wapp _  _          _  = error "wapp: impossible"

whnfSp :: Env -> Sp -> WTerm
whnfSp e = fst . go where
  go :: Sp -> (WTerm, WType)
  go (Var v)    = let E (G _ wt) gty = e ! v in (wt, getW gty)
  go Gen{}      = error "whnfSp: Gen"
  go (App sp t) = let gt = glue e t in case go sp of
    (wt, WPi pi) -> (wapp pi wt gt, instPi pi gt)
    _            -> error "whnfSp: non-Pi spine type"

glue :: Env -> Term -> GTerm
glue e t = G (C e t) (whnf e t)

whnf :: Env -> Term -> WTerm
whnf !e = \case
  Sp sp         -> whnfSp e sp
  Pi v a b      -> WPi (WPi_ e v a (whnf e a) b)
  Lam v t       -> WLam (WLam_ e v t)
  Let v t ty t' -> whnf (e <: (v, glue e t, glue e ty)) t'
  Star          -> WStar
  PiApp{}       -> error "whnf: PiApp"

-- Quoting to beta normal form
--------------------------------------------------------------------------------

-- NOTE: quoting to eta-beta normal form requires fresh name generation, or
-- generic/de Bruijn vars used as actual variables!
-- That's why we're not doing eta-expansion here.

quote :: WTerm -> WType -> Term
quote WStar      _        = Star
quote (WPi  pi)  _        = Pi (domVar pi) (quote (domW pi) WStar) (quote (quotePi pi) WStar)
quote (WLam lam) (WPi pi) = Lam (lamVar lam) (quote (quoteLam lam pi) (quotePi pi))
quote (WSp sp)   _        = Sp (quoteSp sp)
quote _          _        = error "quote: impossible"

quoteSp :: WSp -> Sp
quoteSp (WVar v)         = Var v
quoteSp (WApp sp wt wty) = App (quoteSp sp) (quote wt wty)
quoteSp WGen{}           = error "quoteSp: WGen"

-- Going under binders
--------------------------------------------------------------------------------

instLam :: WLam_ -> WPi_ -> GTerm -> WTerm
instLam (WLam_ e v t) pi gt = whnf (e <: (v, gt, domG pi)) t

quoteLam :: WLam_ -> WPi_ -> WType
quoteLam lam pi = instLam lam pi (var (lamVar lam))

instPi :: WPi_ -> GTerm -> WType
instPi pi@(WPi_ e v a wa b) gt = whnf (e <: (v, gt, domG pi)) b

quotePi :: WPi_ -> WType
quotePi pi = instPi pi (var (domVar pi))

instGPi :: Closure -> WPi_ -> GTerm -> GType
instGPi (C e t) pi gt = G (C e (PiApp t (E gt (domG pi)))) (instPi pi gt)

divePi :: Gen -> WPi_ -> WType
divePi g pi = instPi pi (gen g (domG pi))


-- Beta-eta conversion check
--------------------------------------------------------------------------------

conv :: WType -> WType -> Bool
conv = go 0 WStar where

  go :: Gen -> WType -> WTerm -> WTerm -> Bool
  go !g ty WStar WStar = True

  go g ty (WPi pi) (WPi pi') =
    go g (domW pi) (domW pi') WStar && go (g + 1) (divePi g pi) (divePi g pi') WStar

  go g (WPi pi) t t' =
    go (g + 1) (divePi g pi) (wapp pi t (gen g (domG pi))) (wapp pi t' (gen g (domG pi)))

  go g _ (WSp sp) (WSp sp') = goSp g sp sp'
  go _ _ _ _ = error "conv: impossible"

  goSp :: Gen -> WSp -> WSp -> Bool
  goSp !g (WGen v)         (WGen v')           = v == v'
  goSp !g (WVar v)         (WVar v')           = v == v'
  goSp  g (WApp sp wt wty) (WApp sp' wt' wty') = goSp g sp sp' && go g wty wt wt'
  goSp  _ _                _                   = False

-- Syntactic equality (semidecision)
--------------------------------------------------------------------------------

-- | Try to decide equality by doing PiApp elimination, n-depth delta-reduction
--   and eta-expansion. Beta reduction is *not* performed.
--   A 'Nothing' result indicates that equality can't be decided this way.
synEqN :: Gen -> Depth -> Closure -> Closure -> WType -> Maybe Bool
synEqN g d ct@(C e t) ct'@(C e' t') wty = case wty of
  WPi pi -> synEqN (g + 1) d (synEta g pi ct) (synEta g pi ct') (divePi g pi)
  _      -> case (t, t') of

    (PiApp (Pi v a b) x, t')    -> synEqN g d (C (M.insert v x e) b) (C e' t') wty
    (t, PiApp (Pi v' a' b') x') -> synEqN g d (C e t) (C (M.insert v' x' e') b') wty

    (PiApp (Sp sp) (E (G ct _) gty), PiApp (Sp sp') (E (G ct' _) _)) ->
      True <$ do {guard =<< synEqNSp g d e e' sp sp'; guard =<< synEqN g d ct ct' (getW gty)}

    (Sp sp, Sp sp')  -> synEqNSp g d e e' sp sp'
    (Sp (Var v), t') -> fst <$> varTerm g d e e' v t'
    (t, Sp (Var v')) -> fst <$> varTerm g d e e' v' t

    (Pi v a b, Pi v' a' b') -> (&&) <$> synEqN g d (C e a) (C e' a') WStar <*>
      (let ga = glue e a; gvar = gen g ga in
       synEqN (g + 1) d (C (e <: (v, gvar, ga)) b) (C (e' <: (v', gvar, ga)) b') WStar)

    (Star, Star) -> Just True
    _            -> Just False

ptrEq :: a -> a -> Bool
ptrEq !x !y = isTrue# (reallyUnsafePtrEquality# x y)
{-# inline ptrEq #-}

synEta :: Gen -> WPi_ -> Closure -> Closure
synEta g pi (C e t) = case t of
  Sp sp   -> C e (Sp (App sp (Sp (Gen g (domG pi)))))
  Lam v t -> C (e <: (v, gen g (domG pi), domG pi)) t
  _       -> error "synEta: impossible"

varVar :: Gen -> Depth -> Env -> Env -> Var -> Var -> Maybe (Bool, WType)
varVar !g !d !e !e' v v' = case (M.lookup v e, M.lookup v' e') of
  (Just entry@(E (G (C e t) _) gt), Just entry'@(E (G (C e' t') _) _))
    | ptrEq entry entry' -> Just (True, getW gt)
    | d == 0             -> Nothing
    | otherwise          -> (,getW gt) <$> synEqN g (d - 1) (C e t) (C e' t') (getW gt)
  _ -> Nothing

synEqNSp :: Gen -> Depth -> Env -> Env -> Sp -> Sp -> Maybe Bool
synEqNSp g d e e' sp sp' = fst <$> go sp sp' where
  go :: Sp -> Sp -> Maybe (Bool, WType)
  go (Gen v gty) (Gen v' _)  = Just (v == v', getW gty)
  go (Var v    ) (Var v'  )  = varVar g d e e' v v'
  go (Var v    ) sp'         = varTerm g d e e' v (Sp sp')
  go sp          (Var v')    = varTerm g d e e' v' (Sp sp)
  go (App sp t) (App sp' t') = do
    (b, WPi pi) <- go sp sp'
    guard b
    guard =<< synEqN g d (C e t) (C e' t') (domW pi)
    pure (True, instPi pi (glue e t))
  go _ _ = Nothing

varTerm :: Gen -> Depth -> Env -> Env -> Var -> Term -> Maybe (Bool, WType)
varTerm g d e e' v t' = do
  guard (d /= 0)
  E (G (C e t) _) gt <- M.lookup v e
  (,getW gt) <$> synEqN g (d - 1) (C e t) (C e' t') (getW gt)

-- Full equality
--------------------------------------------------------------------------------

deltaDepth :: Depth
deltaDepth = 1

eq :: GType -> GType -> Bool
eq (G ct wt) (G ct' wt') = case synEqN 0 deltaDepth ct ct' WStar of
  Just b -> b
  _      -> conv wt wt'

-- Check & infer
--------------------------------------------------------------------------------

check :: Env -> Term -> GType -> M ()
check !e t want = case (t, want) of
  (Lam v t, G cpi (WPi pi)) ->
    check (e <: (v, var v, domG pi)) t (instGPi cpi pi (var v))
  _ -> do
    has <- infer e t
    unless (eq has want) $ throwError "type mismatch"

inferSp :: Env -> Sp -> M GType
inferSp e = \case
  Var v    -> let E _ gty = e ! v in pure gty
  App sp t -> do
    G spTy wSpTy <- inferSp e sp
    case wSpTy of
      WPi pi -> do
        check e t (domG pi)
        pure $ instGPi spTy pi (glue e t)
      _ -> throwError "can't apply non-function"
  Gen{} -> error "inferSp: Gen"

infer :: Env -> Term -> M GType
infer !e t = case t of
  Sp sp    -> inferSp e sp
  Star     -> pure gstar
  Lam{}    -> throwError "can't infer type for lambda"
  Pi v a b -> do
    check e a gstar
    check (e <: (v, var v, glue e a)) b gstar
    pure gstar
  Let v t ty t' -> do
    check e ty gstar
    let gty = glue e ty
    check e t gty
    infer (e <: (v, glue e t, gty)) t'
  PiApp{} -> error "infer: PiApp"

infer0 :: Term -> M GType
infer0 = infer mempty

-- eval0 :: Term -> M Term
eval0 t = do
  gty <- infer0 t
  -- pure $ whnf mempty t
  pure $ quote (whnf mempty t) (getW gty)

--------------------------------------------------------------------------------

instance IsString Term where fromString = Sp . Var
instance IsString Sp   where fromString = Var

a ==> b = Pi "" a b
($$) = App
infixl 8 $$
infixr 3 ==>

test =
  Let "id" (Lam "a" $ Lam "x" "x") (Pi "a" Star $ "a" ==> "a") $

  Let "const" (Lam "a" $ Lam "b" $ Lam "x" $ Lam "y" "x")
              (Pi "a" Star $ Pi "b" Star $ "a" ==> "b" ==> "a") $
  Let "nat" (Pi "r" Star $ ("r" ==> "r") ==> "r" ==> "r") Star $

  Let "list" (Lam "a" $ Pi "r" Star $ ("a" ==> "r" ==> "r") ==> "r" ==> "r")
             (Star ==> Star) $

  Let "foo" (Lam "f" "f") ((Star ==> Star) ==> Star ==> Star) $
  "list"




-- print
--------------------------------------------------------------------------------

-- prettyTerm :: Int -> Term -> ShowS
-- prettyTerm prec = go (prec /= 0) where

--   go = _

--   unwords' :: [ShowS] -> ShowS
--   unwords' = foldr1 (\x acc -> x . (' ':) . acc)

  -- spine :: Sp -> Term -> ShowS
  -- spine f x = go f [x] where
  --   go (QApp f y) args = go f (y : args)
  --   go (Var v)    args = t:args

--   go :: Bool -> QTerm -> ShowS
--   go p (QVar i)   = (i++)
--   go p (QApp f x) = showParen p (unwords' $ map (go True) (spine f x))
--   go p (QLam k t) = showParen p
--     (("λ "++) . (k++) . (". "++) . go False t)
--   go p (QPi k a b) = showParen p (arg . (" -> "++) . go False b)
--     where arg = if freeIn k b then showParen True ((k++) . (" : "++) . go False a)
--                               else go True a
--   go p QStar = ('*':)
--   go p (QAnn t ty) = showParen p (go False t . (" ∈ "++) . go False ty)
--   go p (QLet v t1 t2) =
--     showParen p (("let "++) . (v++) . (" = "++) . go False t1 . (" in \n"++) .
--                 go False t2)

--   freeIn :: Var -> QTerm -> Bool
--   freeIn k = go where
--     go (QVar i)      = i == k
--     go (QApp f x)    = go f || go x
--     go (QLam k' t)   = (k' /= k && go t)
--     go (QPi  k' a b) = go a || (k' /= k && go b)
--     go _             = False

-- prettyATerm :: Int -> ATerm -> ShowS
-- prettyATerm prec = go (prec /= 0) where

--   unwords' :: [ShowS] -> ShowS
--   unwords' = foldr1 (\x acc -> x . (' ':) . acc)

--   spine :: ATerm -> ATerm -> [ATerm]
--   spine f x = go f [x] where
--     go (AApp f y) args = go f (y : args)
--     go t          args = t:args

--   go :: Bool -> ATerm -> ShowS
--   go p (AVar i)     = (i++)
--   go p (AAlpha i)   = showParen p (("alpha " ++ show i)++)
--   go p (AApp f x)   = showParen p (unwords' $ map (go True) (spine f x))
--   go p (APiApp f x) = showParen p (unwords' $ map (go True) (spine f x))
--   go p (ALam k a t) = showParen p
--     (("λ "++) . showParen True ((k++) . (" : "++) . go False a) . (". "++) . go False t)
--   go p (APi k a b) = showParen p (arg . (" -> "++) . go False b)
--     where arg = if freeIn k b then showParen True ((k++) . (" : "++) . go False a)
--                               else go True a
--   go p AStar = ('*':)
--   go p (Close (C e t)) = go p t
--   go p (ALet v ty t1 t2) =
--     showParen p (("let "++) . (v++) . (" = "++) .
--                  go False t1 . (" ∈ "++) . go False ty .
--                  (" in \n"++) . go False t2)
--   freeIn :: String -> ATerm -> Bool
--   freeIn k = go where
--     go (AVar i)      = i == k
--     go (AApp f x)    = go f || go x
--     go (ALam k' a t) = go a || (k' /= k && go t)
--     go (APi  k' a b) = go a || (k' /= k && go b)
--     go _             = False

-- instance Show ATerm where
--   showsPrec = prettyATerm
-- -- deriving instance Show ATerm


