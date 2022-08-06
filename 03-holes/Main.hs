{-# options_ghc -Wno-missing-pattern-synonym-signatures #-}

module Main where

import Control.Applicative hiding (many, some)
import Control.Exception hiding (try)
import Control.Monad
import Data.Char
import Data.IORef
import Data.Void
import System.Environment
import System.Exit
import System.IO.Unsafe
import Text.Megaparsec
import Text.Printf

import qualified Data.IntMap                as IM
import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

{-

This file contains an implementation of bidirectional elaboration with untyped
pattern unification. The main change compared to the previous project is the
addition of holes. For example, we might have the following surface expression:

  let id : (A : U) -> A -> A = λ A x. x;
  let id2 : (A : U) -> A -> A = λ A x. id _ x;
  U

The _ stands for a term to be filled in by elaboration. We can replace any term
with _, but not all cases are inferable. The general idea for filling holes is
the following:

  - Elaboration works under a context of metavariables (metacontext). The
    metacontext is conceptually a mutually recursive block of definitions at the
    topmost level of the program, where each metavariable may or may not have a
    definition.
  - Elaboration traverses the raw syntax, and whenever it hits a hole, it
    creates a fresh metavariable, and plugs the hole with it.
  - Instead of conversion checking, we use *unification*, which has the possible
    side effect of solving metavariables. Therefore, holes get filled whenever
    some dependency forces a meta to be defined to a particular value.

Also, we have to allow meta solutions to depend on variables in local
scopes. How is this possible, if metas are defined at the topmost level? The
solution is to make each meta a *function* which abstracts over bound variables
in local scopes. At each hole, the freshly created meta is actually a function
which is applied to all bound variables in scope.  We get the following from the
previous code example:

  let ?α = ?;
  let id : (A : U) -> A -> A = λ A x. x;
  let id2 : (A : U) -> A -> A = λ A x. id (?α A x) x;
  U

This represents the state of elaboration right after we plug the hole. After
finishing elaboration, ?α is solved via unification of expected and inferred types
for "id (?α A x) x", and we get

  let ?α = λ A x. A;
  let id : (A : U) -> A -> A = λ A x. x;
  let id2 : (A : U) -> A -> A = λ A x. id (?α A x) x;
  U

We use the ?α notation with greek letters to refer to metas. Also note that the
declaration of ?α has no type annotation. This is because we only have *untyped*
unification in this project, which means that unification never looks at what
the type of a meta is. Most extensions of the current algorithm require
knowledge of types of metas.

Also note that ?α abstracts over "A" and "x", but not over "id". This is because
defined variables are not a "true" dependency, as the dependency can be always
removed by unfolding the definition. This means that in this project, meta
solutions cannot refer to definitions, and are fully unfolded (in fact,
normalized).  This can lead to a problematic size explosion, so smarter
implementations allow meta solutions to refer to other definitions. Here we only
have the simplest & dumbest implementation.

Because our metas are generally functions, we need to be able to produce
functions as meta solutions. This is called "higher-order unification", in
contrast to first-order unification where metas cannot have function types.

Higher-order unification is undecidable in general, so we only solve equations
belonging to a decidable class, the class of "pattern unification" problems.

Let's look informally at pattern problems. In general, a problem looks like
the following:

   ?α spine =? rhs

Where "spine" is a list of values, and "?α spine" is notation for ?α being
applied multiple values.

A problem is a pattern unification problem if the following hold:

  1. spine consists of distinct bound variables
  2. every free variable of rhs occurs in spine
  3. ?α does not occur in rhs

If 1-3 hold, the problem (informally) has the definitionally unique solution

  ?α := λ spine. rhs

Where "λ spine" denotes an iterated λ, binding all variables in spine. For
example,

  ?α x y z =? (x → y)

Is solved with

  ?α := λ x y z. (x → y)

(above, "x" and "y" are in U, and (x → y) is a function type)

--------------------------------------------------------------------------------

Let's look at examples where some of 1-3 fail.

  ?α x x =? x

Here, the variables in the spine are not distinct. This is called a non-linear
spine, or non-linear problem. There are two distinct solutions in this case:

  ?α := λ x _. x
  ?α := λ _ x. x

It is desirable that unification only produces unique solutions, so here we
don't make an arbitrary choice, and instead just fail to unify.

  ?α true =? true

Here, assume true : Bool. This also has multiple solutions, to list some

  ?α := λ _. true
  ?α := λ x. x
  ?α := λ x. if x then true else false

It's also possible that the return type of ?α is not always Bool:

  ?α : (b : Bool) → if b then Bool else (Bool → Bool)

So e.g. "?α := λ _. true" is not even well-typed in this case! In contrast, if
the spine only has distinct bound variables, even if the return type is
dependent, bound variables block all computation in the return type, and the
pattern solution is guaranteed to be well-typed.

Here's an example which fails condition 2.

  ?α x y =? z → z

where "z : U" is a bound variable. There is clearly no solution, because ?α is
the topmost-level scope, so its definition cannot refer to *any* bound variable;
it can only abstract over "x" and "y", but these don't occur in "z → z". In Haskell,
this class of errors is printed in error messages as "rigid Skolem variable escaping
scope". A classic example where we may encounter these messages is when we're using
the ST monad and runST.

Now for a violation of condition 3.

  ?α =? (?α → ?α)

Here ?α occurs in the right hand side. This is an "infinite solution" error in GHC.
Indeed, this equation does not have finite solutions. In some type systems, this is
solvable as an equi-recursive type:

  https://www.cs.cornell.edu/courses/cs4110/2012fa/lectures/lecture27.pdf

but we don't have such types.
-}


-- Metacontext
--------------------------------------------------------------------------------

newtype MetaVar = MetaVar {unMetaVar :: Int} deriving (Eq, Show, Num) via Int

data MetaEntry = Solved Val | Unsolved

nextMeta :: IORef Int
nextMeta = unsafeDupablePerformIO $ newIORef 0    -- alternative: ReaderT IO (reader has metacontext)
{-# noinline nextMeta #-}

mcxt :: IORef (IM.IntMap MetaEntry)               -- in "production", we'd have mutable array instead of IntMap
mcxt = unsafeDupablePerformIO $ newIORef mempty
{-# noinline mcxt #-}

lookupMeta :: MetaVar -> MetaEntry
lookupMeta (MetaVar m) = unsafeDupablePerformIO $ do
  ms <- readIORef mcxt
  case IM.lookup m ms of
    Just e  -> pure e
    Nothing -> error "impossible"

reset :: IO ()
reset = do
  writeIORef nextMeta 0
  writeIORef mcxt mempty

-- Snoc
--------------------------------------------------------------------------------

{-
We're only using snoc lists in this project. It can be confusing if we simply reuse
lists with the (:) constructor, so we define a flipped pattern synonym.
-}

infixl 4 :>
pattern xs :> x <- x:xs where (:>) xs ~x = x:xs
{-# complete (:>), [] #-}

-- Raw syntax
--------------------------------------------------------------------------------

type Name = String

data Raw
  = RVar Name              -- x
  | RLam Name Raw          -- \x. t
  | RApp Raw Raw           -- t u
  | RU                     -- U
  | RPi Name Raw Raw       -- (x : A) -> B
  | RLet Name Raw Raw Raw  -- let x : A = t; u
  | RSrcPos SourcePos Raw  -- source position for error reporting
  | RHole                  -- _
  deriving Show

-- Core syntax
--------------------------------------------------------------------------------

-- | De Bruijn index.
newtype Ix  = Ix {unIx :: Int} deriving (Eq, Show, Num) via Int

data BD = Bound | Defined
  deriving Show

type Ty = Tm

data Tm
  = Var Ix
  | Lam Name Tm
  | App Tm Tm
  | U
  | Pi Name Ty Ty
  | Let Name Ty Tm Tm
  | Meta MetaVar
  | InsertedMeta MetaVar [BD]

{-
The new additions are Meta and InsertedMeta.

Meta is fairly simple, as it's just a metavariable.

InsertedMeta is an optimized representation of newly inserted metavariables in
the core syntax. Recall the previous code example:

  let ?α = ?;
  let id : (A : U) -> A -> A = λ A x. x;
  let id2 : (A : U) -> A -> A = λ A x. id (?α A x) x;
  U

Here, "?α A x" is the result of plugging the original _ hole with a fresh meta.
Whenever we perform such plugging, we apply a fresh meta to all bound vars in
scope. So it makes sense to optimize the representation of these expressions.
During elaboration we carry around a [BD], and we put the current [BD] in
InsertedMeta when we elaborate a hole.
-}


  deriving Show

-- Evaluation
--------------------------------------------------------------------------------

-- | De Bruijn level.
newtype Lvl = Lvl {unLvl :: Int} deriving (Eq, Ord, Show, Num) via Int

type Env     = [Val]
type Spine   = [Val]
data Closure = Closure Env Tm
type VTy     = Val

data Val

  {- A flexible neutral value is a meta applied to zero or more arguments, represent as a Spine,
     a snoc-list of values. -}
  = VFlex MetaVar Spine

  {- A rigid neutral value is a bound variable applied to zero or more arguments -}
  | VRigid Lvl Spine

  | VLam Name {-# unpack #-} Closure
  | VPi Name ~VTy {-# unpack #-} Closure
  | VU

{-
In elaboration, the point of having VFlex and VRigid is to have immediate O(1)
access to the *reason* that some computation is blocked. Computations can block
on metas or variables. The meta case is "flexible" because the computation can
progress if the meta is solved. In contrast, VRigid is forever blocked.
-}

pattern VVar  x = VRigid x []
pattern VMeta m = VFlex m []

infixl 8 $$
($$) :: Closure -> Val -> Val
($$) (Closure env t) ~u = eval (env :> u) t

vApp :: Val -> Val -> Val
vApp t ~u = case t of
  VLam _ t    -> t $$ u
  VFlex  m sp -> VFlex m (sp :> u)  -- add the argument to the spine
  VRigid x sp -> VRigid x (sp :> u) -- add the argument to the spine
  _           -> error "impossible"

-- Apply single value to multiple values
vAppSp :: Val -> Spine -> Val
vAppSp t = \case
  []      -> t
  sp :> u -> vAppSp t sp `vApp` u

vMeta :: MetaVar -> Val
vMeta m = case lookupMeta m of
  Solved v -> v
  Unsolved -> VMeta m

-- We apply a value to a mask of entries from the environment.
vAppBDs :: Env -> Val -> [BD] -> Val
vAppBDs env ~v bds = case (env, bds) of
  ([]       , []            ) -> v
  (env :> t , bds :> Bound  ) -> vAppBDs env v bds `vApp` t
  (env :> t , bds :> Defined) -> vAppBDs env v bds
  _                           -> error "impossible"

eval :: Env -> Tm -> Val
eval env = \case
  Var x              -> env !! unIx x
  App t u            -> vApp (eval env t) (eval env u)
  Lam x t            -> VLam x (Closure env t)
  Pi x a b           -> VPi x (eval env a) (Closure env b)
  Let _ _ t u        -> eval (env :> eval env t) u
  U                  -> VU
  Meta m             -> vMeta m
  InsertedMeta m bds -> vAppBDs env (vMeta m) bds

{-
A crucial addition is *forcing*. This is required because we're working under an
evolving metacontext.  So it's possible that we compute some VFlex value, but
later we want to pattern match on the value, but in the meanwhile the blocking
meta is solved. So, in general we cannot pattern match on a Val; instead we
can pattern match on "force t", where "t :: Val".

Forcing brings a value up to date with respect to the current state of the metacontext.
Note that forcing only computes until it hits the next head Val constructor which cannot
be further unblocked, and does not recurse into values.

The reason is that in pattern matching, we usually only need the head
constructor to decide how to proceed. So recursing deeper on each forcing would
cause unnecessary work duplication.

Forcing with respect to a metacontext is very similar to forcing a thunk in a lazy language.
In plain Haskell, every "case" expression induces an implicit thunk forcing, where thunks
are computed until the next weak head normal form.

A difference between native thunk forcing in Haskell and our forcing, is that thunk forcing
causes *thunk update*, i.e. the value is overwritten (destructively) with the result. We
do no such update here. It is possible here to use destructive forcing update, but for that
we'd have to use explicit mutable references. And unfortunately those references stay with
us forever as indirections, unlike thunks which are eventually removed by GHC garbage collection.

Ideally, we'd have a runtime system which natively supports simulatenous forcing of thunks
and flexible values, with value update as well. That's a lot of work to implement, so we
stick with a less efficient shallow embedding in Haskell.
-}
force :: Val -> Val
force = \case
  VFlex m sp | Solved t <- lookupMeta m -> force (vAppSp t sp)
  t -> t

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quoteSp :: Lvl -> Tm -> Spine -> Tm
quoteSp l t = \case
  []      -> t
  sp :> u -> App (quoteSp l t sp) (quote l u)

quote :: Lvl -> Val -> Tm
quote l t = case force t of
  VFlex m sp  -> quoteSp l (Meta m) sp
  VRigid x sp -> quoteSp l (Var (lvl2Ix l x)) sp
  VLam x t    -> Lam x (quote (l + 1) (t $$ VVar l))
  VPi  x a b  -> Pi x (quote l a) (quote (l + 1) (b $$ VVar l))
  VU          -> U

nf :: Env -> Tm -> Tm
nf env t = quote (Lvl (length env)) (eval env t)


-- Metavariables and pattern unification
--------------------------------------------------------------------------------

freshMeta :: Cxt -> IO Tm
freshMeta cxt = do
  m <- readIORef nextMeta
  writeIORef nextMeta $! (m + 1)             -- increment nextMeta
  modifyIORef' mcxt $ IM.insert m Unsolved   -- add a new unsolved metaEntry
  pure $ InsertedMeta (MetaVar m) (bds cxt)  -- as I previously mentioned, we just drop the [BD] here
                                             -- Cxt has a (bds :: Cxt -> [BD]) field

{-
At this point, you might look at "pattern-unification.txt" in this project folder, which
contains a more formal description of pattern unification. If you're not familiar with
the formalism there, you can just skip it. Here I'll explain the same thing in a less formal
way which is also more directly related to the implementation.

I mentioned before that the solution to

  ?α spine = t

should be

  λ spine. t

However, we are working de Bruijn indices and levels, and we can't simply shuffle variables from
on side to the other!

In the "λ spine. t" solution, if we're thinking about de Bruijn levels, the "λ spine" becomes
"λ x₀ x₁ x₂ ... xₙ. t", where the length of the spine is n+1. The counting of levels must start from 0,
because the solution lives in the empty scope.

Hence, the nice and efficient solution is to

  1. Turn spine into a variable renaming, which maps the variables in spine to
     their correct final de Bruijn level in the solution. This operation can
     fail if spine does not consist of distinct bound vars. The resulting
     renaming only maps the vars which do occur. So this is a *partial* renaming.

  2. Quote rhs to a term, while at the same time using the renaming to rename local variables,
     failing if the partial renaming is not defined ("scope error"), and also checking
     for occurrence of ?α ("occurs check").

For example, if we have the following spine with dB levels:

  ?α [5, 4, 6]

The partial renaming will be [5 ↦ 0, 4 ↦ 1, 6 ↦ 2], and it's undefined for every
var other than 5, 4, 6.

In the actual PartialRenaming data type, we store not only the mapping,
but also the sizes of the domain and codomain contexts.

The domain is the *current context*, where rhs lives.  The codomain is the
length of the spine, it's the context where the body of the *meta solution*
lives.
-}

-- partial renaming from Γ to Δ
data PartialRenaming = PRen {
    dom :: Lvl                -- size of Γ
  , cod :: Lvl                -- size of Δ
  , ren :: IM.IntMap Lvl }    -- mapping from Δ vars to Γ vars

-- Lifting a partial renaming over an extra bound variable.
-- Given (σ : PRen Γ Δ), (lift σ : PRen (Γ, x : A[σ]) (Δ, x : A))
lift :: PartialRenaming -> PartialRenaming
lift (PRen dom cod ren) =
  PRen (dom + 1) (cod + 1) (IM.insert (unLvl cod) dom ren)

{-
This is step 1.

It's called invert for the following reason.

In the problem

  ?α spine =? rhs

We can view spine as a parallel substitution from some Δ to Γ, so that we have

  - ?α has closed iterated function type from Δ to A, let's note it as ∙ ⊢ ?α : Δ ⇒ A
  - Γ ⊢ rhs : A[spine]

We seek solution:

  Δ ⊢ solution : A

Such that we can solve ?α := λ Δ. solution, where λ Δ binds all Δ variables.

Hence, we seek an "inverse" substitution to spine, which can be applied to both sides to get

  ?α := λ Δ. rhs[spine⁻¹]

As I mentioned before, this spine⁻¹ is only a *partial* inverse, so performing rhs[spine⁻¹]
can fail.
-}

--  invert : (Γ : Cxt) → (spine : Sub Δ Γ) → PRen Γ Δ
invert :: Lvl -> Spine -> IO PartialRenaming
invert gamma sp = do

  let go :: Spine -> IO (Lvl, IM.IntMap Lvl)
      go []        = pure (0, mempty)
      go (sp :> t) = do
        (dom, ren) <- go sp
        case force t of
          VVar (Lvl x) | IM.notMember x ren -> pure (dom + 1, IM.insert x dom ren)
          _                                 -> throwIO UnifyError

  (dom, ren) <- go sp
  pure $ PRen dom gamma ren

-- perform the partial renaming on rhs, while also checking for "m" occurrences.
rename :: MetaVar -> PartialRenaming -> Val -> IO Tm
rename m pren v = go pren v where

  goSp :: PartialRenaming -> Tm -> Spine -> IO Tm
  goSp pren t []        = pure t
  goSp pren t (sp :> u) = App <$> goSp pren t sp <*> go pren u

  go :: PartialRenaming -> Val -> IO Tm
  go pren t = case force t of
    VFlex m' sp | m == m'   -> throwIO UnifyError -- occurs check
                | otherwise -> goSp pren (Meta m') sp

    VRigid (Lvl x) sp -> case IM.lookup x (ren pren) of
      Nothing -> throwIO UnifyError  -- scope error ("escaping variable" error)
      Just x' -> goSp pren (Var $ lvl2Ix (dom pren) x') sp

    VLam x t  -> Lam x <$> go (lift pren) (t $$ VVar (cod pren))
    VPi x a b -> Pi x <$> go pren a <*> go (lift pren) (b $$ VVar (cod pren))
    VU        -> pure U


{-
Wrap a term in lambdas.
-}
lams :: Lvl -> Tm -> Tm
lams l = go 0 where
  go x t | x == l = t
  go x t = Lam ("x"++show (x+1)) $ go (x + 1) t

--       Γ      ?α         sp       rhs
solve :: Lvl -> MetaVar -> Spine -> Val -> IO ()
solve gamma m sp rhs = do
  pren <- invert gamma sp
  rhs  <- rename m pren rhs
  let solution = eval [] $ lams (dom pren) rhs
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved solution)


{-
The actual unification algorithm is fairly simple, it works in a structural
fashion, like conversion checking before.  The main complication, as we've seen,
is the pattern unification case.
-}

unifySp :: Lvl -> Spine -> Spine -> IO ()
unifySp l sp sp' = case (sp, sp') of
  ([]     , []       ) -> pure ()
  (sp :> t, sp' :> t') -> unifySp l sp sp' >> unify l t t'
  _                    -> throwIO UnifyError -- rigid mismatch error

unify :: Lvl -> Val -> Val -> IO ()
unify l t u = case (force t, force u) of
  (VLam _ t   , VLam _ t'    ) -> unify (l + 1) (t $$ VVar l) (t' $$ VVar l)
  (t          , VLam _ t'    ) -> unify (l + 1) (t `vApp` VVar l) (t' $$ VVar l)
  (VLam _ t   , t'           ) -> unify (l + 1) (t $$ VVar l) (t' `vApp` VVar l)
  (VU         , VU           ) -> pure ()
  (VPi x a b  , VPi x' a' b' ) -> unify l a a' >> unify (l + 1) (b $$ VVar l) (b' $$ VVar l)

  (VRigid x sp, VRigid x' sp') | x == x' -> unifySp l sp sp'
  (VFlex m sp , VFlex m' sp' ) | m == m' -> unifySp l sp sp'

  (VFlex m sp , t'           ) -> solve l m sp t'
  (t          , VFlex m' sp' ) -> solve l m' sp' t
  _                            -> throwIO UnifyError  -- rigid mismatch error

-- Elaboration
--------------------------------------------------------------------------------

type Types = [(String, VTy)]


data Cxt = Cxt {           -- used for:
                           -----------------------------------
    env   :: Env           -- evaluation
  , lvl   :: Lvl           -- unification
  , types :: Types         -- raw name lookup, pretty printing
  , bds   :: [BD]          -- fresh meta creation
  , pos   :: SourcePos     -- error reporting
  }

instance Show Cxt where
  show = show . cxtNames

emptyCxt :: SourcePos -> Cxt
emptyCxt = Cxt [] 0 [] []

-- | Extend Cxt with a bound variable.
bind :: Cxt -> Name -> VTy -> Cxt
bind (Cxt env l types bds pos) x ~a =
  Cxt (env :> VVar l) (l + 1) (types :> (x, a)) (bds :> Bound) pos

-- | Extend Cxt with a definition.
define :: Cxt -> Name -> Val -> VTy -> Cxt
define (Cxt env l types bds pos) x ~t ~a  =
  Cxt (env :> t) (l + 1) (types :> (x, a)) (bds :> Defined) pos

-- | closeVal : (Γ : Con) → Val (Γ, x : A) B → Closure Γ A B
closeVal :: Cxt -> Val -> Closure
closeVal cxt t = Closure (env cxt) (quote (lvl cxt + 1) t)

unifyCatch :: Cxt -> Val -> Val -> IO ()
unifyCatch cxt t t' =
  unify (lvl cxt) t t'
  `catch` \UnifyError ->
    throwIO $ Error cxt $ CantUnify (quote (lvl cxt) t) (quote (lvl cxt) t')

check :: Cxt -> Raw -> VTy -> IO Tm
check cxt t a = case (t, force a) of
  (RSrcPos pos t, a) ->
    check (cxt {pos = pos}) t a

  (RLam x t, VPi _ a b) ->
    Lam x <$> check (bind cxt x a) t (b $$ VVar (lvl cxt))

  (RLet x a t u, a') -> do
    a <- check cxt a VU
    let ~va = eval (env cxt) a
    t <- check cxt t va
    let ~vt = eval (env cxt) t
    u <- check (define cxt x vt va) u a'
    pure (Let x a t u)

  (RHole, a) ->
    freshMeta cxt

  (t, expected) -> do
    (t, inferred) <- infer cxt t
    unifyCatch cxt expected inferred
    pure t

infer :: Cxt -> Raw -> IO (Tm, VTy)
infer cxt = \case
  RSrcPos pos t ->
    infer (cxt {pos = pos}) t

  RVar x -> do
    let go ix (types :> (x', a))
          | x == x'   = pure (Var ix, a)
          | otherwise = go (ix + 1) types
        go ix [] =
          throwIO $ Error cxt $ NameNotInScope x

    go 0 (types cxt)

  RLam x t -> do
    a      <- eval (env cxt) <$> freshMeta cxt
    (t, b) <- infer (bind cxt x a) t
    pure (Lam x t, VPi x a $ closeVal cxt b)

  RApp t u -> do
    (t, tty) <- infer cxt t

    -- ensure that tty is Pi
    (a, b) <- case force tty of
      VPi x a b ->
        pure (a, b)
      tty -> do
        a <- eval (env cxt) <$> freshMeta cxt
        b <- Closure (env cxt) <$> freshMeta (bind cxt "x" a)
        unifyCatch cxt (VPi "x" a b) tty
        pure (a, b)

    u <- check cxt u a
    pure (App t u, b $$ eval (env cxt) u)

  RU ->
    pure (U, VU)

  RPi x a b -> do
    a <- check cxt a VU
    b <- check (bind cxt x (eval (env cxt) a)) b VU
    pure (Pi x a b, VU)

  RLet x a t u -> do
    a <- check cxt a VU
    let ~va = eval (env cxt) a
    t <- check cxt t va
    let ~vt = eval (env cxt) t
    (u, b) <- infer (define cxt x vt va) u
    pure (Let x a t u, b)

  RHole -> do
    a <- eval (env cxt) <$> freshMeta cxt
    t <- freshMeta cxt
    pure (t, a)


-- Printing
--------------------------------------------------------------------------------

cxtNames :: Cxt -> [Name]
cxtNames = fmap fst . types

showVal :: Cxt -> Val -> String
showVal cxt v =
  prettyTm 0 (cxtNames cxt) (quote (lvl cxt) v) []

fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x | elem x ns = fresh ns (x ++ "'")
           | otherwise = x

-- printing precedences
atomp = 3  :: Int -- U, var
appp  = 2  :: Int -- application
pip   = 1  :: Int -- pi
letp  = 0  :: Int -- let, lambda

-- Wrap in parens if expression precedence is lower than
-- enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTm :: Int -> [Name] -> Tm -> ShowS
prettyTm prec = go prec where

  piBind ns x a =
    showParen True ((x++) . (" : "++) . go letp ns a)

  goBDS :: Int -> [Name] -> MetaVar -> [BD] -> ShowS
  goBDS p ns m bds = case (ns, bds) of
    ([]      , []             ) -> (("?"++show m)++)
    (ns :> n , bds :> Bound   ) -> par p appp $ goBDS appp ns m bds . (' ':) . (n++)
    (ns :> n , bds :> Defined ) -> goBDS appp ns m bds
    _                           -> error "impossible"

  go :: Int -> [Name] -> Tm -> ShowS
  go p ns = \case
    Var (Ix x)                -> ((ns !! x)++)

    App t u                   -> par p appp $ go appp ns t . (' ':) . go atomp ns u

    Lam (fresh ns -> x) t     -> par p letp $ ("λ "++) . (x++) . goLam (ns:>x) t where
                                   goLam ns (Lam (fresh ns -> x) t) =
                                     (' ':) . (x++) . goLam (ns:>x) t
                                   goLam ns t = (". "++) . go letp ns t

    U                         -> ("U"++)

    Pi "_" a b                -> par p pip $ go appp ns a . (" → "++) . go pip (ns:>"_") b

    Pi (fresh ns -> x) a b    -> par p pip $ piBind ns x a . goPi (ns:>x) b where
                                   goPi ns (Pi (fresh ns -> x) a b)
                                     | x /= "_" = piBind ns x a . goPi (ns:>x) b
                                   goPi ns b = (" → "++) . go pip ns b

    Let (fresh ns -> x) a t u -> par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
                                 . ("\n  = "++) . go letp ns t . (";\n\n"++) . go letp (ns:>x) u

    Meta m                    -> (("?"++show m)++)
    InsertedMeta m bds        -> goBDS p ns m bds

showTm0 :: Tm -> String
showTm0 t = prettyTm 0 [] t []

showTm :: Cxt -> Tm -> String
showTm cxt t = prettyTm 0 (cxtNames cxt) t []

displayMetas :: IO ()
displayMetas = do
  ms <- readIORef mcxt
  forM_ (IM.toList ms) $ \(m, e) -> case e of
    Unsolved -> printf "let ?%s = ?;\n" (show m)
    Solved v -> printf "let ?%s = %s;\n" (show m) (showTm0 $ quote 0 v)
  putStrLn ""

-- errors
--------------------------------------------------------------------------------

data UnifyError = UnifyError
  deriving (Show, Exception)

data ElabError = NameNotInScope Name | CantUnify Tm Tm
  deriving (Show, Exception)

data Error = Error Cxt ElabError
  deriving (Show, Exception)

displayError :: String -> Error -> IO ()
displayError file (Error cxt e) = do

  let SourcePos path (unPos -> linum) (unPos -> colnum) = pos cxt
      lnum = show linum
      lpad = map (const ' ') lnum
      msg = case e of
        NameNotInScope x ->
          "Name not in scope: " ++ x
        CantUnify t t'   ->
          ("Cannot unify expected type\n\n" ++
           "  " ++ showTm cxt t ++ "\n\n" ++
           "with inferred type\n\n" ++
           "  " ++ showTm cxt t')

  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg


-- Parsing
--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Raw -> Parser Raw
withPos p = RSrcPos <$> getSourcePos <*> p

lexeme   = L.lexeme ws
symbol s = lexeme (C.string s)
char c   = lexeme (C.char c)
parens p = char '(' *> p <* char ')'
pArrow   = symbol "→" <|> symbol "->"

keyword :: String -> Bool
keyword x = x == "let" || x == "λ" || x == "U"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pAtom :: Parser Raw
pAtom =
      withPos ((RVar <$> pIdent) <|> (RU <$ symbol "U") <|> (RHole <$ symbol "_"))
  <|> parens pRaw

pBinder = pIdent <|> symbol "_"
pSpine  = foldl1 RApp <$> some pAtom

pLam = do
  char 'λ' <|> char '\\'
  xs <- some pBinder
  char '.'
  t <- pRaw
  pure (foldr RLam t xs)

pPi = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pRaw)))
  pArrow
  cod <- pRaw
  pure $ foldr (\(xs, a) t -> foldr (\x -> RPi x a) t xs) cod dom

funOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _  -> RPi "_" sp <$> pRaw

pLet = do
  pKeyword "let"
  x <- pBinder
  symbol ":"
  a <- pRaw
  symbol "="
  t <- pRaw
  symbol ";"
  u <- pRaw
  pure $ RLet x a t u

pRaw = withPos (pLam <|> pLet <|> try pPi <|> funOrSpine)
pSrc = ws *> pRaw <* eof

parseString :: String -> IO Raw
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitSuccess
    Right t ->
      pure t

parseStdin :: IO (Raw, String)
parseStdin = do
  file <- getContents
  tm   <- parseString file
  pure (tm, file)


-- main
--------------------------------------------------------------------------------

helpMsg = unlines [
  "usage: elabzoo-holes [--help|nf|type]",
  "  --help : display this message",
  "  elab   : read & elaborate expression from stdin",
  "  nf     : read & typecheck expression from stdin, print its normal form and type",
  "  type   : read & typecheck expression from stdin, print its type"]

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getRaw = do

  let elab = do
        (t, file) <- getRaw
        infer (emptyCxt (initialPos file)) t
          `catch` \e -> displayError file e >> exitSuccess

  reset
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"]   -> do
      (t, a) <- elab
      putStrLn $ showTm0 $ nf [] t
      putStrLn "  :"
      putStrLn $ showTm0 $ quote 0 a
    ["type"] -> do
      (t, a) <- elab
      putStrLn $ showTm0 $ quote 0 a
    ["elab"] -> do
      (t, a) <- elab
      displayMetas
      putStrLn $ showTm0 t
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)
