
{-# language Strict, LambdaCase, TypeFamilies, TypeInType,
    RecordWildCards, TemplateHaskell, ViewPatterns, PatternGuards,
    CPP, RankNTypes, MultiParamTypeClasses, FlexibleInstances,
    UnicodeSyntax, GADTs, FunctionalDependencies, TypeApplications,
    OverloadedStrings, ScopedTypeVariables #-}

{-# options_ghc -fwarn-incomplete-patterns #-}

module Precise7 where

import Prelude hiding (pi)

-- TODO: convert top-level defined metas to lets

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Except
import Data.List
import Data.String
import Data.Foldable
import Data.Maybe
import Data.Function

import qualified Data.HashSet as HS
import Data.HashSet (HashSet)

import Lens.Micro
import Lens.Micro.Mtl
import Lens.Micro.TH


type Name = String
type Sub a = [(Name, a)]

data PTm
  = PVar Name
  | PApp PTm PTm
  | PLam Name PTm
  | PLet Name PTm PTm PTm
  | PPi  Name PTm PTm
  | PU
  | PHole

data Tm
  = Var Name
  | App Tm Tm
  | Let Name Tm Tm Tm
  | Lam Name Tm
  | Pi Name Tm Tm
  | U

data Val
  = VNe Name [Val]
  | VLam Closure
  | VPi Val Closure
  | VU

type VTy     = Val
type Unfold  = Bool
data VEntry  = Bound | Def (Maybe Val)
type TEntry  = Maybe VTy
type Entry   = (VEntry, TEntry)
type Cxt     = Sub Entry
type Closure = (Name, Cxt, Tm)
type M       = StateT (Cxt, Int) (Except String)

_cxt ∷ Lens' (Cxt, Int) Cxt
_cxt = _1

_fresh ∷ Lens' (Cxt, Int) Int
_fresh = _2

_focusEntry ∷ Name → Lens' Cxt (Cxt, Entry, Cxt)
_focusEntry x f vs = case break ((==x).fst) vs of
  (as, (_, e):bs) → (\(as, e, bs) → as ++ (x, e):bs) <$> f (as, e, bs)
  _               → error "impossible"

_entry ∷ Name → Lens' Cxt Entry
_entry x = _focusEntry x . _2

lbound ∷ Entry
lbound = (Bound, Nothing)

ldef ∷ Val → Entry
ldef t = (Def (Just t), Nothing)

gdef ∷ Val → VTy → Entry
gdef ~t ~a = (Def (Just t), Just a)

gbound ∷ VTy → Entry
gbound ~a = (Bound, Just a)

noShadowing ∷ Name → M ()
noShadowing "_" = pure ()
noShadowing x = do
  cxt ← use _cxt
  maybe (pure ())
        (\_ → throwError ("Shadowing binder: " ++ x))
        (lookup x cxt)

------------------------------------------------------------

varⱽ ∷ Name → Val
varⱽ x = VNe x []

inst ∷ Closure → Val → Val
inst (x, vs, t) ~u = eval ((x, ldef u):vs) t

appⱽ ∷ Val → Val → Val
appⱽ t ~u = case t of
  VLam t   → inst t u
  VNe h sp → VNe h (u:sp)
  _        → error "impossible"

-- | Evaluate without unfolding definitions from elaboration context.
eval ∷ Cxt → Tm → Val
eval cxt = \case
  Var x | (Def (Just t), Nothing) ← cxt^._entry x → t
        | True → varⱽ x
  App t u     → appⱽ (eval cxt t) (eval cxt u)
  Let x a t u → eval ((x, ldef (eval cxt t)):cxt) u
  Lam x t     → VLam (x, cxt, t)
  Pi x a b    → VPi (eval cxt a) (x, cxt, b)
  U           → VU

unfold ∷ Unfold → TEntry → Bool
unfold uf a = uf || isNothing a

whnf ∷ Unfold → Cxt → Val → Val
whnf uf cxt = \case
  VNe x sp → case cxt^._entry x of
    (Def (Just t), a) | unfold uf a → whnf uf cxt (foldr (flip appⱽ) t sp)
    _                               → VNe x sp
  t → t

gen ∷ Cxt → Name → Name
gen cxt x = maybe x (\_ → x ++ show (length cxt)) (lookup x cxt)

quote ∷ Unfold → Cxt → Val → Tm
quote uf cxt t = case whnf uf cxt t of
  VNe x sp → foldr (\u t → App t (quote uf cxt u)) (Var x) sp
  VLam t   → let x = gen cxt (t^._1)
             in Lam x (quote uf ((x, lbound):cxt) (inst t (varⱽ x)))
  VPi a b  → let x = gen cxt (b^._1)
             in Pi x (quote uf cxt a) (quote uf ((x, lbound):cxt) (inst b (varⱽ x)))
  VU       → U

------------------------------------------------------------

sees ∷ Cxt → Name → Name → Bool
sees env x x' = any ((==x').fst) (env^._focusEntry x._3)

liftMeta ∷ Name → Name → M ()
liftMeta x m = do
  _cxt %= \cxt →
    let (as, (Def Nothing, Just a), bs) = cxt^._focusEntry m
        (cs, xe, ds) = bs^._focusEntry x
        a' = eval (map (_2._2 .~ Nothing) cs ++ (x, xe & _2 .~ Nothing):ds)
                  (quote False cxt a)
    in as ++ cs ++ (x, xe):(m, (Def Nothing, Just a')):ds

-- | Check whether a *normal* term is valid in the scope seen by the
--   first Name argument. We supply [] for [Name] if we're not working
--   with a meta RHS. As side effect, unsolved out-of-scope metas in
--   the term are lifted.
strengthen ∷ Name → [Name] → Tm → M ()
strengthen m = go where
  go ∷ [Name] → Tm → M ()
  go sp = \case
    Var x → do
      cxt ← use _cxt
      case cxt^._entry x of
        (Bound, _) → do
          unless (sees cxt m x || elem x sp) $
            throwError "solution scope error"
        (Def Nothing, Just a) →
          if sees cxt m x
            then pure ()
            else do
              strengthen m [] =<< quote True <$> use _cxt <*> pure a
              liftMeta m x
        _ → error "impossible"
    App t u     → go sp t >> go sp u
    Lam x t     → go (x:sp) t
    Pi x a b    → go sp a >> go (x:sp) b
    Let x a t u → go sp a >> go sp t >> go (x:sp) u
    U           → pure ()

lams ∷ [Name] → Tm → Tm
lams xs t = foldl' (flip Lam) t xs

solve ∷ Name → [Val] → Val → M ()
solve m sp t = do
  -- Check that sp only has variables
  sp ← forM sp $ \case
         VNe x [] → use (_cxt._entry x) >>= \case
           (Bound{}, _) → pure x
           _ → throwError "non-variable in meta spine"
         _ → throwError "non-variable in meta spine"

  -- Check linearity
  envVars ← use _cxt <&> \e → HS.fromList [x | (x, (Bound{}, _)) ← e]
  foldrM (\x xs → if HS.member x xs
                    then throwError "nonlinear meta spine"
                    else pure (HS.insert x xs))
         envVars sp

  -- Check that "t" is valid in "m"-s scope
  strengthen m sp =<< quote True <$> use _cxt <*> pure t

  -- Solve with locally evaluated "t" (no need to rename, since
  -- sp is unique and fresh in the target scope; this would not be
  -- the case if we tolerated irrelevant nonlinear occurrences)
  _cxt . _focusEntry m %= \(as, e, bs) →
    let cxt' = map (_2._2 .~ Nothing) as ++ (m, e):bs
        t'   = eval cxt' (lams sp (quote False cxt' t))
    in (as, (e & _1 .~ Def (Just t')), bs)

unify ∷ Val → Val → M ()
unify t t' = do
  cxt ← use _cxt
  case (whnf True cxt t, whnf True cxt t') of
    (VU      , VU         ) → pure ()

    (VPi a b , VPi a' b'  ) → do
      let x = VNe (gen cxt (b^._1)) []
      unify a a'
      unify (inst b x) (inst b' x)

    (VLam t  , VLam t'    ) → do
      let x = VNe (gen cxt (t^._1)) []
      unify (inst t x) (inst t' x)

    (VLam t  , t'         ) → do
      let x = VNe (gen cxt (t^._1)) []
      unify (inst t x) (appⱽ t' x)

    (t       , VLam t'    ) → do
      let x = VNe (gen cxt (t'^._1)) []
      unify (appⱽ t x) (inst t' x)

    (VNe x sp, VNe x' sp' )
      | Bound ← cxt^._entry x._1, Bound ← cxt^._entry x'._1, x == x'
      → zipWithM_ unify sp sp'

    (VNe x sp, VNe x' sp' )
      | Def Nothing ← cxt^._entry x._1, Def Nothing ← cxt^._entry x'._1
      → if x == x' then
          zipWithM_ unify sp sp'
        else if sees cxt x x' then
          solve x sp (VNe x' sp')
        else
          solve x' sp' (VNe x sp)

    (VNe x sp, t') | Def Nothing ← cxt^._entry x._1
      → solve x sp t'

    (t, VNe x' sp') | Def Nothing ← cxt^._entry x'._1
      → solve x' sp' t

    _ → throwError "can't unify"

------------------------------------------------------------

-- | Right-to-left Applicative map
mapAr ∷ Applicative m ⇒ (a → m b) → [a] → m [b]
mapAr f []     = pure []
mapAr f (a:as) = flip (:) <$> mapAr f as <*> f a

-- | Create a fresh unsolved meta entry with type
newMetaEntry ∷ VTy → M (Name, Entry)
newMetaEntry ~a = do
  i ← _fresh <<%= (+1)
  pure ("?" ++ show i, (Def Nothing, Just a))

-- | Push a new meta to the top of the context
pushMeta ∷ VTy → M Name
pushMeta ~a = do
  (m, e) ← newMetaEntry a
  _cxt %= ((m, e):)
  pure m

-- | Insert a new entry after a name
insertAfter ∷ Name → (Name, Entry) → M ()
insertAfter x ye = _cxt . _focusEntry x ._3 %= (ye:)

-- | Insert a new meta after a name
newMetaAfter ∷ Name → VTy → M Name
newMetaAfter x ~a = do
  me ← newMetaEntry a
  insertAfter x me
  pure (fst me)

-- -- | Re-evaluate a Val in a possibly more permissive context
-- --   than it was created in.
-- reevalLocal ∷ Val → M Val
-- reevalLocal t = do
--   cxt ← use _cxt
--   pure $ eval cxt (quote False cxt t)

check ∷ PTm → VTy → M Tm
check t tty = do
  tty ← whnf True <$> use _cxt <*> pure tty
  case (t, tty) of
    (PLam x t, VPi a b) → do
      noShadowing x

      -- elaborate t in extended context
      _cxt %= ((x, gbound a):)
      t ← check t (inst b (VNe x []))

      -- get locally created new metas
      newMetas ← use (_cxt . _focusEntry x . _1)

      -- create list of new elab let bindings, while
      -- inserting new generalized unsolved metas after x
      (newLets ∷ [(Name, Tm, Tm)]) ←
        flip mapAr newMetas $ \(m, (ve, Just mty)) → do
          cxt ← use _cxt
          let mty' = quote False cxt mty
          case ve of
            Def (Just t) → do
              let t' = quote False cxt t
              pure ((m, mty', t'))
            Def Nothing  → do
              m' ← newMetaAfter x (VPi a (x, cxt, mty'))
              pure ((m, mty', App (Var m') (Var x)))
            _            → error "impossible"

      -- drop stuff from elab context
      _cxt <~ use (_cxt . _focusEntry x . _3)

      -- add new lets to elab result
      pure (Lam x (foldl' (\u (m, a, t) → Let m a t u) t newLets))

    (PLet x a t u, tty) → do
      noShadowing x
      a   ← check a VU
      ~a' ← eval <$> use _cxt <*> pure a
      t   ← check t a'
      ~t' ← eval <$> use _cxt <*> pure t

      -- elaborate u in extended context
      _cxt %= ((x, gdef t' a'):)
      u ← check u tty

      -- get new metas
      newMetas ← use (_cxt . _focusEntry x . _1)

      -- strengthen unsolved metas
      flip mapAr newMetas $ \(m, (ve, Just ma)) →
        case ve of
          Def (Just t) → pure ()
          Def Nothing  → liftMeta x m
          _            → error "impossible"

      -- convert solved metas to lets
      newMetas ← use (_cxt . _focusEntry x . _1)
      (newLets ∷ [(Name, Tm, Tm)]) ←
        flip mapAr newMetas $  \(m, (Def (Just t), Just ma)) → do
          t ← quote False <$> use _cxt <*> pure t
          ma ← quote False <$> use _cxt <*> pure ma
          pure (m, ma, t)

      -- drop new metas
      _cxt <~ use (_cxt._focusEntry x._3)

      pure (Let x a t (foldl' (\u (m, a, t) → Let m a t u) u newLets))

    (PHole, a) →
      Var <$> pushMeta a

    _ → do
      (t, tty') ← infer t
      t <$ unify tty tty'

infer ∷ PTm → M (Tm, VTy)
infer = \case
  PVar "_" → throwError "_ is not a valid identifier"
  PVar x → (lookup x <$> use _cxt) >>= \case
    Just (_, Just a) → pure (Var x, a)
    Just (_, _     ) → error "impossible"
    _                → throwError "name not in scope"

  PApp t u → do
    (t, tty) ← infer t
    (whnf True <$> use _cxt <*> pure tty) >>= \case
      VPi a b → do
        u ← check u a
        ~u' ← eval <$> use _cxt <*> pure u
        pure (App t u, inst b u')
      _ → throwError "expected function"

  PU → pure (U, VU)

  PPi x a b → do
    noShadowing x
    a ← check a VU

    ~a' ← eval <$> use _cxt <*> pure a
    _cxt %= ((x, gbound a'):)
    b ← check b VU

    -- get locally created new metas
    newMetas ← use (_cxt . _focusEntry x . _1)

    -- create list of new elab let bindings, while
    -- inserting new generalized unsolved metas after x
    (newLets ∷ [(Name, Tm, Tm)]) ←
      flip mapAr newMetas $ \(m, (ve, Just mty)) → do
        cxt ← use _cxt
        let mty' = quote False cxt mty
        case ve of
          Def (Just t) → do
            let t' = quote False cxt t
            pure ((m, mty', t'))
          Def Nothing  → do
            m' ← newMetaAfter x (VPi a' (x, cxt, mty'))
            pure ((m, mty', App (Var m') (Var x)))
          _            → error "impossible"

    -- drop stuff from elab context
    _cxt <~ use (_cxt . _focusEntry x . _3)

    pure (Pi x a (foldl' (\u (m, a, t) → Let m a t u) b newLets), VU)

  PLam{} → throwError "can't infer type for lambda"

  PHole → do
    ma ← pushMeta VU
    mt ← pushMeta (VNe ma [])
    pure (Var mt, VNe ma [])

  PLet x a t u → do
    noShadowing x
    a   ← check a VU
    ~a' ← eval <$> use _cxt <*> pure a
    t   ← check t a'
    ~t' ← eval <$> use _cxt <*> pure t

    -- elaborate u in extended context
    _cxt %= ((x, gdef t' a'):)
    (u, uty) ← infer u

    -- get new metas
    newMetas ← use (_cxt . _focusEntry x . _1)

    -- strengthen unsolved metas
    flip mapAr newMetas $ \(m, (ve, Just ma)) →
      case ve of
        Def (Just t) → pure ()
        Def Nothing  → liftMeta x m
        _            → error "impossible"

    -- convert solved metas to lets
    newMetas ← use (_cxt . _focusEntry x . _1)
    (newLets ∷ [(Name, Tm, Tm)]) ←
      flip mapAr newMetas $  \(m, (Def (Just t), Just ma)) → do
        t ← quote False <$> use _cxt <*> pure t
        ma ← quote False <$> use _cxt <*> pure ma
        pure (m, ma, t)

    -- drop new metas
    _cxt <~ use (_cxt._focusEntry x._3)

    pure (Let x a t (foldl' (\u (m, a, t) → Let m a t u) u newLets), uty)

------------------------------------------------------------

nf0 ∷ Tm → Tm
nf0 = quote True [] . eval []

evalTms ∷ [(Name, Tm, Tm)] → Sub Entry
evalTms =
  foldr (\(x, a, t) acc →
          (x, (Def (Just $ eval acc t), Just (eval acc a))):acc)
  []

localTest ∷ [(Name, Tm, Tm)] → Tm → Tm
localTest (evalTms → bs) t = quote False bs (eval bs t)

infer0 ∷ PTm → Either String (Tm, Tm)
infer0 t = runExcept $ do
  ((Let _ _ _ t, a), s) ← runStateT (infer (have "_" u u t)) ([], 0)
  pure (t, quote True [] a)

elab0 ∷ PTm → Either String Tm
elab0 t = fst <$> infer0 t

------------------------------------------------------------

emb ∷ PTm → Tm
emb = \case
  PVar x → Var x
  PApp t u → App (emb t) (emb u)
  PLam x t → Lam x (emb t)
  PLet x a t u → Let x (emb a) (emb t) (emb u)
  PPi x a b → Pi x (emb a) (emb b)
  PU → U
  PHole → Var "hole"

instance Show PTm where
  show = show . emb

instance IsString PTm where
  fromString = PVar

pretty :: Int -> Tm -> ShowS
pretty prec = go 0 (prec /= 0) where
  newline :: Int -> ShowS
  newline l = ('\n':) . (replicate l ' '++)

  unwords' :: [ShowS] -> ShowS
  unwords' = foldr1 (\x acc -> x . (' ':) . acc)

  spine :: Tm -> Tm -> [Tm]
  spine f x = go f [x] where
    go (App f y) args = go f (y : args)
    go t         args = t:args

  goLet ∷ Int → Bool → Bool → (Name, Tm, Tm, Tm) → ShowS
  goLet l p False (x, a, t, u) =
      ("let "++) . (x++) . (" : "++) . go l False a . newline l . ("  = "++)
      . go (l + 4) False t  . (" in"++) . newline l .  go l False  u
  goLet l p True (x, a, t, u) =
      ("let "++) . (x++) . (" : "++) . go l False a . (" = "++)
      . go (l + 4) False t  . (" in "++) . go l False  u

  go :: Int -> Bool -> Tm -> ShowS
  go l p (Var x)     = (x++)
  go l p (App f x)   = showParen p (unwords' $ map (go l True) (spine f x))
  go l p (Lam x t)   = showParen p
    (("λ "++) . (x++) . (". "++) . go l False t)

  go l p (Pi k a b@(Let x' a' t' u')) =
    showParen p (arg . (" -> "++) . goLet l False True (x', a', t', u'))
    where arg = if freeIn k b then showParen True ((k++) . (" : "++) . go l False a)
                              else go l True a

  go l p (Pi k a b) = showParen p (arg . (" -> "++) . go l False b)
    where arg = if freeIn k b then showParen True ((k++) . (" : "++) . go l False a)
                              else go l True a
  go l p U = ('*':)
  go l p (Let x a t u) = showParen p (goLet l p False (x, a, t, u))

  freeIn :: String -> Tm -> Bool
  freeIn x = go where
    go (Var x')     = x == x'
    go (App f x)    = go f || go x
    go (Lam x' t)   = (x' /= x && go t)
    go (Pi  x' a b) = go a || (x' /= x && go b)
    go _            = False

instance Show Tm where
  showsPrec = pretty

instance IsString Tm where
  fromString = Var

class Sugar a where
  pi   ∷ Name → a → a → a
  lam  ∷ Name → a → a
  have ∷ Name → a → a → a → a
  u    ∷ a
  (∙)  ∷ a → a → a
  (==>) ∷ a → a → a
  a ==> b = pi "_" a b

instance Sugar PTm where
  pi   = PPi
  lam  = PLam
  u    = PU
  have = PLet
  (∙)  = PApp

instance Sugar Tm where
  pi   = Pi
  lam  = Lam
  u    = U
  have = Let
  (∙)  = App

infixr 4 ==>
infixl 7 ∙

hole = PHole

------------------------------------------------------------

test1 ∷ PTm
test1 =
  have "id"
    (pi "a" u $ "a" ==> "a")
    (lam "a" $ lam "x" "x") $
  have "id2"
    (pi "a" u $ "a" ==> "a")
    (lam "a" $ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole)
             ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole)
             ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole)
             ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole)
             ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole)
             ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole)
             ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole)
             ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole) ∙ ("id" ∙ hole))
  "id"

test2 ∷ PTm
test2 =

  have "id" (pi "a" hole $ "a" ==> "a")
            (lam "a" $ lam "x" "x") $
  "id"

test3 ∷ PTm
test3 =
  have "const" (pi "a" hole $ pi "b" hole $ "a" ==> "b" ==> "a")
               (lam "a" $ lam "b" $ lam "x" $ lam "y" "x") $
  "const"

test4 ∷ PTm
test4 =
  have "nat" u (pi "n" u $ ("n" ==> "n") ==> "n" ==> "n") $
  have "z" "nat" (lam "n" $ lam "s" $ lam "z" "z") $
  have "s" ("nat" ==> "nat") (lam "a" $ lam "n" $ lam "s" $ lam "z'" $ "s" ∙ ("a" ∙ hole ∙ "s" ∙ "z'")) $
  have "add" ("nat" ==> "nat" ==> "nat")
             (lam "a" $ lam "b" $ lam "n" $ lam "s'" $ lam "z'" $ "a" ∙ hole ∙ "s'" ∙ ("b" ∙ hole ∙ "s'" ∙ "z'"))$
  "z"




-- test = localTest
--   [("id", (Pi "a" U $ "a" ==> "a"), (Lam "a" $ Lam "x" "x")),
--    ("app", (Pi "a" U $ Pi "b" U $ ("a" ==> "b") ==> "a" ==> "b"),
--             (Lam "a" $ Lam "b" $ Lam "f" $ Lam "x" $ "f" ∙ "x"))]

-- test =
--   Let "id" (Pi "a" U $ "a" ==> "a") (Lam "a" $ Lam "x" "x") $
--   "id"
  -- Let "app" (Pi "a" U $ Pi "b" U $ ("a" ==> "b") ==> "a" ==> "b")
  --           (Lam "a" $ Lam "b" $ Lam "f" $ Lam "x" $ "f" ∙ "x") $p
  -- "id" ∙ (Pi "a" U $ "a" ==> "a") ∙ "id"
