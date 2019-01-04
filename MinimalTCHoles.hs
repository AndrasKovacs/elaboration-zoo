{-# language
  OverloadedStrings, LambdaCase, TupleSections, StandaloneDeriving,
  PatternSynonyms, ViewPatterns, NoMonomorphismRestriction, RecordWildCards #-}

{-# options_ghc -Wall -Wno-unused-matches -Wno-name-shadowing
                -Wno-missing-signatures #-}

{-|
Minimal implementation of an elaborator with holes and pattern unification.
We use non-shadowing names everywhere instead of indices or levels for simplicity.

Additional references: Ulf Norell's PhD thesis, chapter 3.

Take a program with a hole, like:

    let id : (A : *) → A → A
      = λ A x. x
    in

    let id2 : (A : *) → A → A
      = λ A x. id _ x
    in

    id2

For every hole in the program, we create a metavariable, or meta in short.
Metas are conceptually in a topmost-level mutual let block, and we can plug a
hole by solving the meta corresponding to the hole.

However, notice that the hole has two bound variables, "A" and "x" in scope.  If
a meta is always at top level, how can the solution depend on local variables?
The simplest way is to make each meta a function which abstracts over all local
bound variables in the scope of the hole.

    let mutual
      α = λ A x. ?
    in

    let id : (A : *) → A → A
      = λ A x. x
    in

    let id2 : (A : *) → A → A
      = λ A x. id (α A x) x
    in

    id2

Hence, on encountering the hole, the elaborator creates a fresh meta "α" and
plugs the hole with α applied to the local bound variables. Note that metas
don't have to abstract over local *definitions*, because those can be always
unfolded in meta solutions.

In classic Hindley-Milner inference, the situation is similar except that
  a) there are only closed types, i.e. types which depend on nothing.
  b) holes can't stand for arbitrary terms, only for monomorphic types.

In H-M we would solve metas by simple structural unification. In depenent
type theory, most metas are *by default* solved with functions, because
metas abstract over local variables.

(Note: putting all metas in a topmost-level mutual block is *not* a good idea
 for real implementations, it's better to have more precise scoping. The current
 solution is just the simplest one.)

Hence, the notable change to unification is that we need to give functions
as solutions. Solvable equations look like this generally:

    α [t₁, t₂, t₃ ... tₙ] =? u

where the left side is a meta "α" applied to n number of terms. We may call this
a "meta-headed" equation. Meta-headed equations have unique solutions up
to βη-conversion if the so-called "pattern condition" holds.

Let us abbreviate a sequence of terms, (like t₁...tₙ) with σ, δ, and so on. Let
"FreeVars(t)" denote the set of free variables of a term including metas. Let "x
∈! σ" denote that "x" occurs exactly once in the sequence "σ".

Pattern condition for (α σ =? u):
  1. Spine check              : σ is of the form [x₁, x₂, ... xₙ] where xᵢ are all bound variables.
  2. Scope + linearity check  : ∀ x ∈ FreeVars(u). x ∈! σ
  3. Occurs check             : α ∉ FreeVars(u)

If 1-3 holds, then (α := λ σ. u) is the unique solution for (α σ =? u).

Some exaplanations. If the *spine check* fails, then it is easy see that unique solutions
can't be expected to exist. For example:

    α true =? true

is solvable with both of the following:

    α := λ x. x
    α := λ x. true

A heuristic called "dependency erasure" always picks the second solution in this case;
dependency erasure just throws away all parameters which are not bound variables. This
makes more program typecheck, at the cost of possibly more erratic behavior.

If the *scope check* fails, then the equation may or may not be solvable. In our simple
implementation, we always fail on scope check failure, but more powerful implementations
can sometimes find solutions. Example for unsolvable equation:

    α x y := (z -> z)

where (z -> z) is a function type and "z" is a bound variable. Since "α" is
defined on the top level, it cannot depend on any local variable, and all
dependency must be expressed through λ parameters. So, it's totally not possible
to put "z -> z" in the solution, because that's not meaningful in the top-level
scope. Another example, which is possibly solvable:

    α x y := (x -> β x z)

where α, β are metas and x,y,z are bound variables. This is solvable if the
solution of β is constant in the second parameter, because then (β x z) reduces
to an expression which does not contain the illegal "z" variable. Agda and Coq
can handle this situation by immediately refining β to be a function which is
constant in the appropriate parameter. This is called "pruning". We do not
implement pruning here.

The scope check also has a *linearity condition*: recall the "x ∈! σ" part.
This means that σ is linear in the variables which actually occur in the
right hand side. A nonlinear σ would be ambiguous, for example

    α x x =? x

is solvable as (α := λ x _. x) and also as (α := λ _ x. x).

The current implementation ignores the linearity condition, and always picks the
rightmost variable occurrence in solutions. This makes solutions non-unique, but
my expreience is that this is practically justifiable, and the rightmost occurence
is usually the correct pick.

In short, the current implementation has spine check, occurs check and scope check
but no linearity check.

-}

module MinimalTCHoles where

import Prelude hiding (all, pi)

import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Foldable hiding (all)
import Data.Maybe
import Data.String
import qualified Data.IntMap.Strict as M

type Name = String

-- | Elaboration input contains holes which are filled in the output.
data Raw
  = RVar Name
  | RLam Name Raw
  | RApp Raw Raw
  | RU
  | RPi Name Raw Raw
  | RLet Name Raw Raw Raw
  | RHole
  deriving Show

type Meta = Int

-- | Metacontext. An unsolved meta is just a meta which isn't contained in
--   the metacontext.
type MCxt = M.IntMap Val

type Ty  = Tm
type VTy = Val

-- | Environment for values. A `Nothing` denotes a bound variable.
type Vals = Sub (Maybe Val)

-- | Elaboration context. We distinguish types of bound and defined variables.
data TyEntry = Bound VTy | Def VTy
data Cxt = Cxt {_vals :: Vals, _types :: Sub TyEntry}

-- | Monad for elaboration. The 'Int' counts the number of allocated metas.
type ElabM = StateT (Int, MCxt) (Either String)

-- | Empty context.
nil :: Cxt
nil = Cxt [] []

-- | Add a bound variable to context.
bind :: Name -> VTy -> Cxt -> Cxt
bind x a (Cxt vs tys) = Cxt ((x, Nothing):vs) ((x, Bound a):tys)

-- | Add a defined name to context.
define :: Name -> Val -> VTy -> Cxt -> Cxt
define x v a (Cxt vs tys) = Cxt ((x, Just v):vs) ((x, Def a):tys)


-- | Well-typed core terms without holes.
data Tm
  = Var Name
  | Lam Name Tm
  | App Tm Tm
  | U
  | Pi Name Ty Ty
  | Let Name Ty Tm Tm
  | Meta Meta


data Head = HMeta Meta | HVar Name deriving Eq

-- | We use a spine form for neutral values, because we need to access heads
--   during unification.
data Val
  = VNe Head [Val]    -- [Val] here is in reverse order, i. e. the first Val in
                      -- the list is applied last to the head.
  | VLam Name (Val -> Val)
  | VPi Name Val (Val -> Val)
  | VU

type Bind a = (Name, a)
type Sub  a = [Bind a]

pattern VVar :: Name -> Val
pattern VVar x = VNe (HVar x) []

pattern VMeta :: Meta -> Val
pattern VMeta m = VNe (HMeta m) []

-- | Generate a name such that it does not shadow anything in the current
--   environment. De Bruijn indices would make this unnecessary in a more
--   sophisticated implementation.
inventName :: Vals -> Name -> Name
inventName vs "_" = "_"
inventName vs x = case lookup x vs of
  Just _  -> inventName vs (x ++ "'")
  Nothing -> x

-- | Evaluation is up to a metacontext, so whenever we inspect a value during
--   elaboration, we always have to force it first, i.e. unfold solved metas and
--   compute until we hit a rigid head.
force :: MCxt -> Val -> Val
force ms = \case
  VNe (HMeta m) sp | Just t <- M.lookup m ms ->
    force ms (foldr (flip vApp) t sp)
  v -> v

forceM :: Val -> ElabM Val
forceM v = gets (\(_, ms) -> force ms v)

vApp :: Val -> Val -> Val
vApp (VLam _ t) u = t u
vApp (VNe h sp) u = VNe h (u:sp)
vApp _          _ = error "vApp: impossible"

eval :: MCxt -> Vals -> Tm -> Val
eval ms = go where
  go vs = \case
    Var x       -> maybe (VVar x) id (fromJust $ lookup x vs)
    Meta m      -> maybe (VMeta m) id (M.lookup m ms)
    App t u     -> vApp (go vs t) (go vs u)
    Lam x t     -> VLam x (\u -> go ((x, Just u):vs) t)
    Pi x a b    -> VPi x (go vs a) (\u -> go ((x, Just u):vs) b)
    Let x _ t u -> go ((x, Just (go vs t)):vs) u
    U           -> VU

evalM :: Cxt -> Tm -> ElabM Val
evalM cxt t = gets (\(_, ms) -> eval ms (_vals cxt) t)

-- |  Quote into full forced normal forms.
quote :: MCxt -> Vals -> Val -> Tm
quote ms = go where
  go vs v = case force ms v of
    VNe h sp -> foldr (\v acc -> App acc (go vs v))
                      (case h of HMeta m -> Meta m; HVar x -> Var x)
                      sp
    VLam (inventName vs -> x) t ->
      Lam x (go ((x, Nothing):vs) (t (VVar x)))
    VPi (inventName vs -> x) a b ->
      Pi x (go vs a) (go ((x, Nothing):vs) (b (VVar x)))
    VU -> U

quoteM :: Vals -> Val -> ElabM Tm
quoteM vs v = gets $ \(_, ms) -> quote ms vs v

nf :: MCxt -> Vals -> Tm -> Tm
nf ms vs = quote ms vs . eval ms vs

nfM :: Vals -> Tm -> ElabM Tm
nfM vs t = gets $ \(_, ms) -> nf ms vs t


-- Unification
--------------------------------------------------------------------------------

-- | Check that all entries in a spine are bound variables.
checkSp :: [Val] -> ElabM [Name]
checkSp vs = forM vs $ \v -> forceM v >>= \case
  VVar x -> pure x
  _      -> throwError "non-variable value in meta spine"

-- | Scope check + occurs check a solution candidate. Inputs are a meta, a spine
--   of variable names (which comes from checkSp) and a RHS term in normal
--   form. In real implementations it would be a bad idea to solve metas with
--   normal forms (because of size explosion), but here it's the simplest thing
--   we can do. We don't have to worry about shadowing here, because normal
--   forms have no shadowing by our previos quote implementation.
checkSolution :: Meta -> [Name] -> Tm -> ElabM ()
checkSolution m sp rhs = lift $ go sp rhs where
  go :: [Name] -> Tm -> Either String ()
  go ns = \case
    Var x    -> unless (elem x ns) $
                  throwError ("solution scope error: " ++ show (m, sp, rhs))
    App t u  -> go ns t >> go ns u
    Lam x t  -> go (x:ns) t
    Pi x a b -> go ns a >> go (x:ns) b
    U        -> pure ()
    Meta m'  -> when (m == m') $
                  throwError ("occurs check: " ++ show (m, rhs))
    Let{}    -> error "impossible"

solve :: Vals -> Meta -> [Val] -> Val -> ElabM ()
solve vs m sp rhs = do
  -- check that spine consists of bound vars
  sp <- checkSp sp
  -- normalize rhs
  rhs <- quoteM vs rhs
  -- scope + ocurs check rhs
  checkSolution m sp rhs
  -- wrap rhs into lambdas
  rhs <- evalM nil (foldl' (flip Lam) rhs sp)
  -- add solution to metacontext
  modify (\(i, mcxt) -> (i, M.insert m rhs mcxt))

-- | Create fresh meta, return the meta applied to all current bound vars.
newMeta :: Cxt -> ElabM Tm
newMeta Cxt{..} = do
  let sp = [Var x | (x, Bound{}) <- _types]
  (i, ms) <- get
  put (i + 1, ms)
  pure (foldr (flip App) (Meta i) sp)

unify :: Vals -> Val -> Val -> ElabM ()
unify = go where
  go :: Vals -> Val -> Val -> ElabM ()
  go vs t u = do
    ms <- gets snd
    case (force ms t, force ms u) of
      (VLam (inventName vs -> gx) t, VLam x' t') ->
        go ((gx, Nothing):vs) (t (VVar gx)) (t' (VVar gx))

      -- these two lines implement eta conversion for functions
      (VLam (inventName vs -> gx) t, u) ->
        go ((gx, Nothing):vs) (t (VVar gx)) (vApp u (VVar gx))
      (u, VLam (inventName vs -> gx) t) ->
        go ((gx, Nothing):vs) (vApp u (VVar gx)) (t (VVar gx))

      (VPi (inventName vs -> gx) a b, VPi x' a' b') -> do
        go vs a a'
        go ((gx, Nothing):vs) (b (VVar gx)) (b' (VVar gx))
      (VU, VU) -> pure ()
      (VNe h sp, VNe h' sp') | h == h' -> zipWithM_ (go vs) sp sp'
      (VNe (HMeta m) sp, t) -> solve vs m sp t
      (t, VNe (HMeta m) sp) -> solve vs m sp t
      (t, t') -> throwError ("can't unify " ++ show (quote ms vs t) ++ " with " ++
                             show (quote ms vs t'))

-- Elaboration
--------------------------------------------------------------------------------

checkShadowing :: Cxt -> Name -> ElabM ()
checkShadowing _ "_" = pure ()
checkShadowing Cxt{..} x = do
  maybe (pure ())
        (\_ -> throwError $ "name shadowing not allowed: " ++ show x)
        (lookup x _types)

check :: Cxt -> Raw -> VTy -> ElabM Tm
check cxt@Cxt{..} topT topA = case (topT, topA) of
  (RLam x t, VPi (inventName _vals -> x') a b) -> do
    checkShadowing cxt x
    Lam x <$> check (Cxt ((x, Just (VVar x')):_vals)
                         ((x, Bound a):_types))
                  t (b (VVar x'))

  (RLet x a t u, topA) -> do
    checkShadowing cxt x
    a  <- check cxt a VU
    va <- evalM cxt a
    t  <- check cxt t va
    vt <- evalM cxt t
    u  <- check (define x vt va cxt) u topA
    pure $ Let x a t u

  (RHole, topA) ->
    newMeta cxt

  _ -> do
    (t, va) <- infer cxt topT
    unify _vals va topA
    pure t

infer :: Cxt -> Raw -> ElabM (Tm, VTy)
infer cxt@Cxt{..} = \case
  RVar "_" -> throwError "_ is not a valid name"
  RVar x   -> maybe (throwError ("var not in scope: " ++ x))
                    (\a -> pure (Var x, case a of Bound a -> a; Def a -> a))
                    (lookup x _types)
  RU -> pure (U, VU)

  RApp t u -> do
    (t, va) <- infer cxt t
    forceM va >>= \case
      VPi _ a b -> do
        u  <- check cxt u a
        vu <- evalM cxt u
        pure (App t u, b vu)
      _ -> throwError "expected a function type"

  RLam x t -> do
    checkShadowing cxt x
    va <- evalM cxt =<< newMeta cxt
    (t, vb) <- infer (bind x va cxt) t
    b <- quoteM ((x, Nothing):_vals) vb
    ms <- gets snd
    pure (Lam x t, VPi x va $ \u -> eval ms ((x, Just u):_vals) b)

  RPi x a b -> do
    checkShadowing cxt x
    a  <- check cxt a VU
    va <- evalM cxt a
    b <- check (bind x va cxt) b VU
    pure (Pi x a b, VU)

  RHole -> do
    a  <- newMeta cxt
    vb <- evalM cxt =<< newMeta cxt
    pure (a, vb)

  RLet x a t u -> do
    checkShadowing cxt x
    a       <- check cxt a VU
    va      <- evalM cxt a
    t       <- check cxt t va
    vt      <- evalM cxt t
    (u, vb) <- infer (define x vt va cxt) u
    pure (Let x a t u, vb)

-- Testing & printing
--------------------------------------------------------------------------------

-- | Inline all meta solutions. Used for displaying elaboration output.
zonk :: MCxt -> Vals -> Tm -> Tm
zonk ms = go where

  goSp :: Vals -> Tm -> Either Val Tm
  goSp vs = \case
    Meta m | Just v <- M.lookup m ms -> Left v
    App t u -> either (\t -> Left (vApp t (eval ms vs u)))
                      (\t -> Right (App t (go vs u)))
                      (goSp vs t)
    t -> Right (go vs t)

  go :: Vals -> Tm -> Tm
  go vs = \case
    Var x        -> Var x
    Meta m       -> maybe (Meta m) (quote ms vs) (M.lookup m ms)
    U            -> U
    Pi x a b     -> Pi x (go vs a) (go ((x, Nothing):vs) b)
    App t u      -> either (\t -> quote ms vs (vApp t (eval ms vs u)))
                           (\t -> App t (go vs u))
                           (goSp vs t)
    Lam x t      -> Lam x (go ((x, Nothing):vs) t)
    Let x a t u  -> Let x (go vs a) (go vs t)
                          (go ((x, Nothing):vs) u)


-- infer/elaborate/normalize closed raw terms

infer0 :: Raw -> IO ()
infer0 t = do
  case evalStateT (do {(_, a) <- infer nil t; quoteM [] a}) (0, mempty) of
    Left e  -> putStrLn e
    Right a -> print a

nf0 :: Raw -> IO ()
nf0 t = do
  case evalStateT (do {(t, _) <- infer nil t; quoteM [] =<< evalM nil t})
                  (0, mempty) of
    Left e  -> putStrLn e
    Right t -> print t

elab0 :: Raw -> IO ()
elab0 t =
  case runStateT (infer nil t)
                  (0, mempty) of
    Left e                  -> putStrLn e
    Right ((t, _), (_, ms)) -> print (zonk ms [] t)


prettyTm :: Int -> Tm -> ShowS
prettyTm prec = go (prec /= 0) where

  goArg :: Tm -> ShowS
  goArg t = go True t

  goPiBind :: Name -> Tm -> ShowS
  goPiBind x a =
    showParen True ((x++) . (" : "++) . go False a)

  goLamBind :: Name -> ShowS
  goLamBind x = (x++)

  goLam :: Tm -> ShowS
  goLam (Lam x t) = (' ':) . goLamBind x . goLam t
  goLam t         = (". "++) . go False t

  goPi :: Bool -> Tm -> ShowS
  goPi p (Pi x a b)
    | x /= "_" = goPiBind x a . goPi True b
    | otherwise =
       (if p then (" → "++) else id) .
       go (case a of App{} -> False; _ -> True) a .
       (" → "++) . go False b
  goPi p t = (if p then (" -> "++) else id) . go False t

  go :: Bool -> Tm -> ShowS
  go p = \case
    Var x -> (x++)

    App (App t u) u' ->
      showParen p (go False t . (' ':) . goArg u . (' ':) . goArg u')

    App t u  -> showParen p (go True t . (' ':) . goArg u)
    Lam x t  -> showParen p (("λ "++) . goLamBind x . goLam t)
    Pi x a b -> showParen p (goPi False (Pi x a b))

    Let x a t u ->
      ("let "++) . (x++) . (" : "++) . go False a . ("\n    = "++)
      . go False t  . ("\nin\n"++) . go False  u
    U      -> ('*':)
    Meta m -> (("?"++).(show m++))

instance Show Tm where showsPrec = prettyTm


-- Syntactic sugar & examples
--------------------------------------------------------------------------------

instance IsString Raw where
  fromString = RVar

(==>) a b = RPi "_" a b
infixr 4 ==>

pi = RPi
all x b = RPi x RU b
make = RLet
lam = RLam
u = RU
h = RHole
($$) = RApp
infixl 6 $$

-- unicode sugar
(↦) :: Name -> Raw -> Raw
(↦) = RLam
infixr 0 ↦
(∙) = RApp
infixl 6 ∙

-- We can do: elab0 test / nf0 test / infer0 test
test =
  make "id" (all "a" $ "a" ==> "a")
    ("a" ↦ "x" ↦ "x") $

  make "idTest" h ("id" ∙ h ∙ "id") $

  make "const" (all "a" $ all "b" $ "a" ==> "b" ==> "a")
    ("a" ↦ "b" ↦ "x" ↦ "y" ↦ "x") $

  make "constTest" h
    ("const" ∙ h ∙ h ∙ "id" ∙ u) $

  make "nat" u
    (all "n" $ ("n" ==> "n") ==> "n" ==> "n") $

  make "zero" "nat"
    ("n" ↦ "s" ↦ "z" ↦ "z") $

  make "suc" ("nat" ==> "nat")
    ("a" ↦ "n" ↦ "s" ↦ "z" ↦ "s" ∙ ("a" ∙ h ∙ "s" ∙ "z")) $

  make "mul" ("nat" ==> "nat" ==> "nat")
    ("a" ↦ "b" ↦ "N" ↦ "s" ↦ "a" ∙ h ∙ ("b" ∙ h ∙ "s")) $

  make "n5" h
    ("suc" ∙ ("suc" ∙ ("suc" ∙ ("suc" ∙ ("suc" ∙ "zero"))))) $

  make "n10" h
    ("mul" ∙ ("suc" ∙ ("suc" ∙ "zero")) ∙ "n5") $

  make "n100" h
    ("mul" ∙ "n10" ∙ "n10") $

  make "Eq" (all "A" $ "A" ==> "A" ==> u)
    ("A" ↦ "x" ↦ "y" ↦ pi "P" ("A" ==> u) $ "P" ∙ "x" ==> "P" ∙ "y") $

  make "refl" (all "A" $ pi "x" h $ "Eq" ∙ "A" ∙ "x" ∙ "x")
    ("A" ↦ "x" ↦ "P" ↦ "px" ↦ "px") $

  make "trans" (all "A" $ pi "x" h $ pi "y" h $ pi "z" h $
                 "Eq" ∙ "A" ∙ "x" ∙ "y" ==> "Eq" ∙ h ∙ "y" ∙ "z"
                 ==> "Eq" ∙ h ∙ "x" ∙ "z")
    ("A" ↦ "x" ↦ "y" ↦ "z" ↦ "p" ↦ "q" ↦ "q" ∙ h ∙ "p") $

  make "test" ("Eq" ∙ h ∙ "zero" ∙ "zero")
    ("refl" ∙ h ∙ h) $

  make "List" (u ==> u)
    ("A" ↦ all "List" $ "List" ==> ("A" ==> "List" ==> "List") ==> "List") $

  make "nil" (all "A" $ "List" ∙ "A")
    ("A" ↦ "L" ↦ "n" ↦ "c" ↦ "n") $

  make "cons" (all "A" $ "A" ==> "List" ∙ "A" ==> "List" ∙ "A")
    ("A" ↦ "a" ↦ "as" ↦ "L" ↦ "n" ↦ "c" ↦ "c" ∙ "a" ∙ ("as" ∙ h ∙ "n" ∙ "c")) $

  make "listTest" h
    ("cons" ∙ h ∙ "zero" ∙ ("cons" ∙ h ∙ "zero" ∙ ("cons" ∙ h ∙ "zero" ∙ ("nil" ∙ h)))) $

  make "etaTest" ("Eq" ∙ ("nat" ==> "nat") ∙ ("x" ↦ "suc" ∙ "x") ∙ "suc")
    ("refl" ∙ h ∙ h)$

  "n100"
