{-# language
  OverloadedStrings, LambdaCase, TupleSections, StandaloneDeriving,
  PatternSynonyms, ViewPatterns, NoMonomorphismRestriction, RecordWildCards #-}

{-# options_ghc -Wall -Wno-unused-matches -Wno-name-shadowing
                -Wno-missing-signatures #-}

{-|
Minimal implementation of an elaborator with holes and pattern unification.

Further reading, roughly in preferred order:

    - Ulf Norell's PhD thesis, chapter 3,
      http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf This is the closest to
      the current implementation, also provides the most concise and digestible
      introduction to unification, implicit insertion and constraint
      postponing. A good reference to the implementation in Agda, but covers only a
      small part of the current far more sophisticated Agda.
    - http://www.cse.chalmers.se/~abela/unif-sigma-long.pdf Very good resource
      for some of the advanced tricks in Agda (which are not explained in the
      previous reference), but it's a bit heavier read, and by itself not very
      helpful with respect to actual implementation.
    - https://www.irif.fr/~sozeau/research/publications/drafts/unification-jfp.pdf
      This Coq unifier guide goes into lots of delicious dirty details. Very good
      read, although I disagree with a number of design decisions there.


### Basic setup

We use string names instead of indices or levels. This makes most operations
easier to understand and implement. There are subtleties that can go wrong with
names, but our general approach cuts out a large amount of name generation and
shuffling which would appear in more naive elaborators. In particular, we don't
ever use capture-avoiding substitution nor global fresh name generation.


### About holes and pattern unification


Take a program with a hole, like:

    let id : (A : *) → A → A
      = λ A x. x
    in

    let id2 : (A : *) → A → A
      = λ A x. id _ x
    in

    id2

The goal of the elaborator is to fill the holes in a sensible way. Sensible is
fairly subjective, but we always expect that elaboration output is well-typed.

Agda additionally adheres to the following principle: only fill a hole if there
is a unique solution. This is generally a good principle, because non-unique
solutions require arbitrary choices, which in turn makes for a fragile and more
annoying programming experience. While Coq generally follows this principle too,
it is a lot more lax than Agda and occasionaly makes unforced choices, for
pragmatic reasons. Our current implementation is between Agda and Coq in this
matter, but since it is very bare-bones, there are comparatively few design choices
to be made.

For every hole in the program, we create a metavariable, or meta in short.
Metas are conceptually in a topmost-level mutual let block, and we can plug a
hole by solving the meta corresponding to the hole.

However, notice that the hole has two bound variables, "A" and "x" in scope. If
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

On encountering the hole, the elaborator creates a fresh meta "α" and
plugs the hole with α applied to the local bound variables. The created meta
may or may not be solved later, during unification. In the above example, 
the solution will be "α = λ A x. A". Note that metas don't have to abstract 
over *definitions*, because those can be always unfolded in meta solutions.

(Putting all metas in a topmost-level mutual block is *not* a good idea
for real implementations. It's better to have more precise scoping. The current
solution is just the simplest one.)

In classic Hindley-Milner inference, the situation is similar except that
  a) there are only closed types, i.e. types which depend on nothing.
  b) holes can't stand for arbitrary terms, only for types.

In H-M we solve metas by simple first-order structural unification, and
the occurs check is the only noteworthy complication.

In the simpler elaborators for dependent type theory such as ours, metas are
usually solved with functions, because they abstract over local variables.

Hence, the notable change to unification is that we need to produce functions as
solutions. Equations which may immediately produce a solution look like this
generally:

    α t₁ t₂ t₃ ... tₙ =? u

where the left side is a meta "α" applied to a spine (sequence) of terms. We may
call this a "meta-headed" equation. Meta-headed equations have unique solutions
up to βη-conversion if the so-called "pattern condition" holds.

Let us abbreviate a sequence/spine of terms with "σ" or "δ", and a term applied
to a spine as "t σ". Let "FreeVars(t)" denote the set of free variables
(including metas) of a term. Let "t ∈! σ" denote that "t" occurs exactly once in
the sequence "σ".

Defining the pattern condition for (α σ =? u):

  1. Spine check              : σ is of the form x₁, x₂, ... xₙ where xᵢ are all bound variables.
  2. Scope + linearity check  : ∀ (x ∈ FreeVars(u)). x ∈! σ
  3. Occurs check             : α ∉ FreeVars(u)

If 1-3 holds, then (α := λ σ. u) is the unique solution for (α σ =? u), where "λ σ" means
binding all variables in σ with lambdas.

Some explanations. If the *spine check* fails, then it is easy see that unique solutions
can't be expected to exist. For example:

    α true =? true

is solvable with both of the following:

    α := λ x. x
    α := λ x. true

A heuristic called "dependency erasure" always picks the second solution in this case;
dependency erasure just throws away all parameters which are not bound variables. This
makes more program typecheck, at the cost of possibly more erratic behavior.

The *occurs check* may be familiar from Hindley-Milner inference. If we fail
this check, then the solution would be circular, or "infinite", as in GHC's
infamous infinite type error messages. For example:

    α := (α -> α)

is circular, hence unsolvable.

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
solution of β is constant in the second parameter, because then "β x z" reduces
to an expression which does not contain the illegal "z" variable. Agda and Coq
can handle this situation by attempting to refine β to a function which is
constant in the appropriate parameter. This is called "pruning", and it is
analogously applicable when the illegal occurring variable is "α" itself (occurs
check). We do not implement pruning here.

The scope check also has a *linearity condition*: recall the "x ∈! σ" part.
This means that σ is linear in the variables which actually occur in the
right hand side. A nonlinear σ would be ambiguous, for example

    α x x =? x

is solvable as (α := λ x _. x) and also as (α := λ _ x. x).

The current implementation ignores the linearity condition, and always picks the
rightmost variable occurrence in solutions. This makes solutions non-unique, but
my experience is that this is practically justifiable, and the rightmost occurence
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
--   We use non-shadowing names everywhere instead of indices or levels.
data Tm
  = Var Name
  | Lam Name Tm
  | App Tm Tm
  | U
  | Pi Name Ty Ty
  | Let Name Ty Tm Tm
  | Meta Meta


data Head = HMeta Meta | HVar Name deriving Eq

-- | We use a spine form for neutral values, i.e. we have the head variable and
--   all arguments in a list. We need convenient access to both head and spine
--   when unifying and when solving metas.
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
--
--   We only need to invent non-shadowing names when we want to go under
--   a (Val -> Val) closure. See 'quote' and 'unify' for examples of doing so.
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

-- |  Quote into fully forced normal forms.
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
--   forms have no shadowing by our previous quote implementation.
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

  -- Wrap rhs into lambdas. NOTE: this operation ignores nonlinearity, because
  -- the innermost nonlinear variable occurrence simply shadows the other occurrences.
  rhs <- evalM nil (foldl' (flip Lam) rhs sp)

  -- add solution to metacontext
  modify (\(i, mcxt) -> (i, M.insert m rhs mcxt))

-- | Create fresh meta, return the meta applied to all current bound vars.
newMeta :: Cxt -> ElabM Tm
newMeta Cxt{..} = do

  -- There might be shadowed names in the context, but we don't care
  -- about that, since 'solve' ignores nonlinearity anyway.
  let sp = [Var x | (x, Bound{}) <- _types]
  (i, ms) <- get
  put (i + 1, ms)
  pure (foldr (flip App) (Meta i) sp)

-- | Unify two values. After unification succeeds, the LHS and RHS become
--   definitionally equal in the newly updated metacontext. We only need here
--   the value environment for generating non-shadowing names; with de Bruijn
--   levels we would only need an Int denoting the size of the environment.
unify :: Vals -> Val -> Val -> ElabM ()
unify = go where
  go vs t u = do
    ms <- gets snd
    case (force ms t, force ms u) of
      (VLam (inventName vs -> x) t, VLam _ t') ->
        go ((x, Nothing):vs) (t (VVar x)) (t' (VVar x))

      -- these two lines implement eta conversion for functions
      (VLam (inventName vs -> x) t, u) ->
        go ((x, Nothing):vs) (t (VVar x)) (vApp u (VVar x))
      (u, VLam (inventName vs -> x) t) ->
        go ((x, Nothing):vs) (vApp u (VVar x)) (t (VVar x))

      (VPi (inventName vs -> x) a b, VPi _ a' b') -> do
        go vs a a'
        go ((x, Nothing):vs) (b (VVar x)) (b' (VVar x))

      (VU, VU) -> pure ()
      (VNe h sp, VNe h' sp') | h == h' -> zipWithM_ (go vs) sp sp'
      (VNe (HMeta m) sp, t) -> solve vs m sp t
      (t, VNe (HMeta m) sp) -> solve vs m sp t
      (t, t') -> throwError ("can't unify " ++ show (quote ms vs t) ++ " with " ++
                             show (quote ms vs t'))

-- Elaboration
--------------------------------------------------------------------------------


check :: Cxt -> Raw -> VTy -> ElabM Tm
check cxt@Cxt{..} topT topA = case (topT, topA) of

  -- This is a bit tricky. We can only go under the VPi closure with a
  -- non-shadowing name, but we also need to ensure that the RLam binder is the
  -- same as the VPi binder. So we go under the binder with a common fresh
  -- non-shadowing name. In classic "locally nameless" style, the new name
  -- would be immediatly substituted into "t", but that's not only very slow,
  -- but also supposes that "t" is already well-scoped. So instead we just
  -- define "x" to be the new var when going under the binder. This acts as
  -- an efficient delayed substitution when we do unification under the binder.
  -- This subtlety does not come up with de Bruijn indices or levels.
  (RLam x t, VPi (inventName _vals -> x') a b) -> do
    let v = VVar x'
    Lam x <$> check (Cxt ((x, Just v):_vals) ((x, Bound a):_types)) t (b v)

  (RLet x a t u, topA) -> do
    a  <- check cxt a VU
    va <- evalM cxt a
    t  <- check cxt t va
    vt <- evalM cxt t
    u  <- check (define x vt va cxt) u topA
    pure $ Let x a t u

  (RHole, topA) ->
    newMeta cxt

  -- we unify the expected and inferred types
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

  -- an upgrade to this would be to also proceed if the inferred type for "t"
  -- is meta-headed, in which case we would need to create two fresh metas and
  -- refine "t"-s type to a function type.
  RApp t u -> do
    (t, va) <- infer cxt t
    forceM va >>= \case
      VPi _ a b -> do
        u  <- check cxt u a
        vu <- evalM cxt u
        pure (App t u, b vu)
      _ -> throwError "expected a function type"

  -- inferring a type for a lambda is a bit awkward and slow here.  We get a new
  -- meta for the binder type, then infer a type for the body. However, to get a
  -- VPi with that right body, we basically need to normalize and re-evaluate
  -- the Val body. A potentially faster solution would be to implement a
  -- substitution operation directly on Vals. I don't implement that, partly for
  -- brevity, partly because in a real implementation we would do something much
  -- better than that anyway.
  RLam x t -> do
    va <- evalM cxt =<< newMeta cxt
    (t, vb) <- infer (bind x va cxt) t
    b <- quoteM ((x, Nothing):_vals) vb
    ms <- gets snd
    pure (Lam x t, VPi x va $ \u -> eval ms ((x, Just u):_vals) b)

  RPi x a b -> do
    a  <- check cxt a VU
    va <- evalM cxt a
    b <- check (bind x va cxt) b VU
    pure (Pi x a b, VU)

  -- inferring a type for the hole: we create two metas, one for the hole
  -- and one for its type.
  RHole -> do
    a  <- newMeta cxt
    vb <- evalM cxt =<< newMeta cxt
    pure (a, vb)

  RLet x a t u -> do
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
have = RLet
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

--  elab0 test / nf0 test / infer0 test
test =
  have "id" (all "a" $ "a" ==> "a")
    ("a" ↦ "x" ↦ "x") $

  have "idTest" h ("id" ∙ h ∙ "id") $

  have "const" (all "a" $ all "b" $ "a" ==> "b" ==> "a")
    ("a" ↦ "b" ↦ "x" ↦ "y" ↦ "x") $

  have "constTest" h
    ("const" ∙ h ∙ h ∙ "id" ∙ u) $

  have "nat" u
    (all "n" $ ("n" ==> "n") ==> "n" ==> "n") $

  have "zero" "nat"
    ("nat" ↦ "s" ↦ "z" ↦ "z") $

  have "suc" ("nat" ==> "nat")
    ("a" ↦ "nat" ↦ "s" ↦ "z" ↦ "s" ∙ ("a" ∙ h ∙ "s" ∙ "z")) $

  have "mul" ("nat" ==> "nat" ==> "nat")
    ("a" ↦ "b" ↦ "nat" ↦ "suc" ↦ "a" ∙ h ∙ ("b" ∙ h ∙ "suc")) $

  have "n5" h
    ("suc" ∙ ("suc" ∙ ("suc" ∙ ("suc" ∙ ("suc" ∙ "zero"))))) $

  have "n10" h
    ("mul" ∙ ("suc" ∙ ("suc" ∙ "zero")) ∙ "n5") $

  have "n100" h
    ("mul" ∙ "n10" ∙ "n10") $

  have "Eq" (all "A" $ "A" ==> "A" ==> u)
    ("A" ↦ "x" ↦ "y" ↦ pi "P" ("A" ==> u) $ "P" ∙ "x" ==> "P" ∙ "y") $

  have "refl" (all "A" $ pi "x" h $ "Eq" ∙ "A" ∙ "x" ∙ "x")
    ("A" ↦ "x" ↦ "P" ↦ "px" ↦ "px") $

  have "trans" (all "A" $ pi "x" h $ pi "y" h $ pi "z" h $
                 "Eq" ∙ "A" ∙ "x" ∙ "y" ==> "Eq" ∙ h ∙ "y" ∙ "z"
                 ==> "Eq" ∙ h ∙ "x" ∙ "z")
    ("A" ↦ "x" ↦ "y" ↦ "z" ↦ "p" ↦ "q" ↦ "q" ∙ h ∙ "p") $

  have "test" ("Eq" ∙ h ∙ "zero" ∙ "zero")
    ("refl" ∙ h ∙ h) $

  have "List" (u ==> u)
    ("A" ↦ all "List" $ "List" ==> ("A" ==> "List" ==> "List") ==> "List") $

  have "nil" (all "A" $ "List" ∙ "A")
    ("A" ↦ "List" ↦ "nil" ↦ "cons" ↦ "nil") $

  have "cons" (all "A" $ "A" ==> "List" ∙ "A" ==> "List" ∙ "A")
    ("A" ↦ "a" ↦ "as" ↦ "List" ↦ "nil" ↦ "cons" ↦
       "cons" ∙ "a" ∙ ("as" ∙ h ∙ "nil" ∙ "cons")) $

  have "listTest" h
    ("cons" ∙ h ∙ "zero" ∙ ("cons" ∙ h ∙ "zero" ∙ ("cons" ∙ h ∙ "zero" ∙ ("nil" ∙ h)))) $

  have "etaTest" ("Eq" ∙ ("nat" ==> "nat") ∙ ("x" ↦ "suc" ∙ "x") ∙ "suc")
    ("refl" ∙ h ∙ h)$

  "n100"
