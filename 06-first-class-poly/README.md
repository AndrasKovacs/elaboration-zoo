## elabzoo-first-class-poly

New feature: enhanced insertion behavior for implicit lambdas, also called
"first-class polymorphic inference". You can look at
[examples.txt](examples.txt) for a "benchmark" set of definitions which was used
in several previous works in the literature.

We merge `Unification.hs` into `Elaboration.hs` in this project, because the two
have a bit more mutual dependencies now, and it would be annoying to try to split
them or use `hs-boot` files.

### Motivation & Introduction

Consider the following definition:

    let foo : Maybe ({A} → A → A)
	  = Just (λ x. x);

Elabzoo-04 and 05 throw an error on this. The reason is the following,

- We check the definition by first inferring type for `Just (λ x. x)`, then
  unifying with `Maybe ({A} → A → A)`.
- We infer `{A} → A → Maybe A` for `Just`.
- We insert fresh meta to get `Just {?0} : ?0 → Maybe ?0`.
- We check `λ x. x` with `?0`. Since `?0` is not an implicit function type,
  we proceed to infer `?1 → ?1` for `λ x. x`, and solve `?0` to `?1 → ?1`.
- Thus, `Just {?1 → ?1} (λ x. x)` has inferred type `Maybe (?1 → ?1)`.
- We unify `Maybe (?1 → ?1)` with `Maybe ({A} → A → A)`, which fails because one
  function type is implicit, and the other is explicit.

Instead of getting this error, we would like to have the following elaboration output:

    Just {{A : U} → A → A} (λ {A : U} (x : A). x)

The problem in summary:

- We may only insert an implicit lambda when we check with an implicit function
  type. For example, in `let id : {A} → A → A = λ x. x`, we insert a lambda to
  get `id : {A : U} → A → A = λ {A} x. x` in the output.
- If the checking type is meta-headed (i.e. "flexible", a metavariable applied to a spine),
  the we simply *assume* that no lambda insertion should happen, and proceed.
- Later, we may learn that lambda insertion *should have* occurred, but at that
  point it's too late, as we've already elaborated a term without performing the
  insertion.

### Insertion problems, terminology

We may call this the **lambda insertion problem**. In the literature, solutions
to this are called "first-class polymorphism" or "impredicative polymorphism". I
advise to use the first name, since the second one collides with the notion of
impredicativity in type theory.

- In type theory: a *universe* is impredicative if function types whose codomains
  are in the universe are always in the universe, regardless of their domain types.
- An *elaboration algorithm* is impredicative if it is able to solve metavariables
  to implicit function types.

Historically, "impredicativity" in type theory and elaboration sometimes
coincided, which is the source of the terminology, but nowadays in practical
systems (Coq, Agda, GHC) they are actually orthogonal.

- Coq has predicative elaboration (because it lacks first-class implicit function types) but
  has impredicative Prop and Set universes.
- Agda has impredicative elaboration (because it can solve metas to arbitrary types) but
  has predicative universes.
- GHC prior to 9.2 had predicative elaboration (type variables in general cannot
  be instantiated to `forall`), but impredicative `*` universe, since e.g. `forall a. a -> a :: *`.

Hence, to avoid confusion, let's just avoid "impredicative" in the elaboration
sense altogether, and use "polymorphic instantiation" or "first-class
polymorphism" instead.

There is dually an **application insertion problem**. When we infer type for a
term, if the type is `{x : A} → B`, apply the term to a fresh meta with type
`A`. This is the basic insertion behavior that we know from Agda and GHC, which
lets us elaborate `id true` to `id {Bool} true`. But if the inferred type is
meta-headed, we again don't know for sure whether we should insert an
application. Consider:

    let f = λ g. (g true, g zero);

This may be typed as `({A} → A → A) → Pair Bool Nat`, but no existing systems
will succeed at inferring this. At `g true`, they assume that `g` does *not*
have an implicit function type, and refine its type to `Bool → ...`.

The application insertion problem is in general far more difficult than the
lambda insertion problem, because we would need to invent implicit function
types out of thin air, and try to somehow refine them. In contrast, lambda
insertion does not invent anything; at the end of the day it is only allowed to
work with implicit function types which originate from source annotations. The
problem with inventing implicit functions is that there are infinite elaboration
choices, and there isn't necessarily a minimal or obvious choice. In the above
example, we could also have as type

    ({A} → A → Bool) → Pair Bool Bool

or

    ({A} → A → A → A) → Pair (Bool → Bool) (Nat → Nat)

Hence, no real-world system ever attempted to infer type for this example. The
MLF system has some support for enhanced application insertion:

- http://gallium.inria.fr/~remy/mlf/mlf-type-inference.pdf
- http://www.cs.nott.ac.uk/~pszgmh/appsem-papers/lebotlan.pdf

But it also does not handle the exact above case.


### Lambda insertion solutions

There are two ways to solve the lambda insertion problem. I give a short summary
here, and will give more details about pros and cons later.

#### 1. Representing unknown insertions

Using this solution, when we are in doubt, we just insert an *unknown* number of
lambdas. When we later learn more information, this can be refined to zero or
more concrete implicit lambdas. This requires us to extend the core syntax with
a representation of unknown insertions. This is implemented in FCIF:

- https://dl.acm.org/doi/10.1145/3408983
- https://github.com/AndrasKovacs/implicit-fun-elaboration

#### 2. Postponing elaboration

Using this solution, we simply delay checking a preterm until we learn for sure
whether the checking type is `{x : A} → B`. However, in some cases we *never*
learn more about the checking type, for example when we have definitions with
unknown types, which are not referenced anywhere else in a module:

    let foo : _ = λ x y. x * x + y;
	let bar : _ = λ x y z. ...;

Hence, a postponing solution must at some point process all postponed checking
tasks, under the assumption that no lambda insertion should happen. This means
that postponing is generally less precise than solution 1. But I will argue that
it's practically more favorable, because it's a lot simpler and still very strong
for practical purposes.

### Dynamic order elaboration

I call the solution in this package **dynamic order elaboration**, or **DOE**
for short. It works the following way:

- When during checking we don't know if we should perform lambda insertion, we
  postpone the checking. We push the checking problem to a context of such problems.
- At the same time, we create a fresh *placeholder* metavariable, which stands
  for the eventual result of checking and evaluating the preterm. The
  placeholder metavariable can be freely unified during elaboration, but after we
  actually perform the postponed checking, we have to unify the checking result
  with the placeholder.
- We track for each meta the checking problems which are blocked on them.  When
  we solve a meta, we try to perform all blocked checkings. If after solving a
  meta, a blocked checking problem still has a meta-headed checking type, it
  remains blocked, but now on the new meta.
- After we elaborate the whole file, we perform all remaining checking problems
  with the assumption that no lambda insertion should be inserted. This may
  recursively spawn more checking problems but we just perform them until there
  is no more.

That's it. In this project, this is around 150 extra lines compared to
elabzoo-05.

- This is by a fair margin the simplest solution for first-class polymorphism
  that I know of.
- It appears to be stronger than all solutions in the literature except perhaps
  FCIF, and MLF in the System F fragment (but MLF does not scale to dependent
  types, and is extremely complex, so we don't really consider it as practical).
- It traverses the source input *exactly once* just like previous algorithms in
  this repo. Hence the name "dynamic order elaboration": we walk the presyntax
  once, but not necessarily in strict left-to-right dependency order.
- It is an orthogonal elaboration feature in basically every type system which
  features implicit function types. For example, the DOE implementation for
  System F is roughly the same amount of code and complexity as for
  MLTT. Moreover, we don't have to change core syntax, nor anything about
  unification.

Note that the choice of *when* to perform the remaining problems is the main
degree of freedom here. One choice would be to follow an Agda-like convention,
where we only keep postponed problems active for a single top-level binding
group. In this project I instead just keep them alive for the whole file.

DOE is currently implemented in one somewhat more mature (but still hobbyist)
language, called sixty:

- https://github.com/ollef/sixty

### Comparison

#### 1. Quick Look

Quick Look (QL) is notable as the algorithm implemented in GHC 9.2:

- https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0274-quick-look-impredicativity.rst
- https://www.microsoft.com/en-us/research/publication/a-quick-look-at-impredicativity/

It works the following way. Whenever we check a neutral spine, we process it twice:
- First, we do a quick look pass, which only traverses nested neutral spines
  (only variables, constructors and applications, no lambdas, let-s or case
  splits) and attempts to gather meta solutions, which might be solutions to
  `forall` types.
- Second, we do a "proper" pass, which is just ordinary bidirectional checking.

Revisiting the example:

    let foo : Maybe ({A} → A → A)
	  = Just (λ x. x);

QL handles this as follows:

- We insert a fresh meta to the `Just` head, so we get `Just {?0} : ?0 → Maybe ?0`.
- The QL pass skips over `λ x. x` because it is not a neutral spine.
- The QL pass unifies `Maybe ?0` with the expected `Maybe ({A} → A → A)`. Hence
  `?0` is solved.
- When we do the proper pass, we already know about `?0`, so we can check `λ
  x. x` without insertion ambiguity.

QL is strictly worse than DOE in terms of performance, complexity and power.

- QL traverses the presyntax multiple times. If we don't use additional
  memoization (as in the actual GHC implementation), this can be quadratic.  The
  QL pass can be viewed as an under-informed eager approximation of DOE: it
  *always* tries to do a pre-processing pass, even if we later learn that there
  is no point doing so. DOE on the other hand is *exact*: we do a postponing (which
  has some constant computational overhead) precisely at the point of insertion
  ambiguity.
- The QL pass duplicates elaboration logic. In GHC, the QL pass is intentionally
  restricted to the small language fragment of nested neutral expressions, in
  order to avoid excessive logic duplication. This fragment seems to be good
  enough in practice. But in DOE, we duplicate nothing, we reuse the existing
  elaboration pass, which means that DOE can effectively "quick look" into
  arbitrary expressions.

#### 2. FCIF

Let's give a bit more detail about FCIF as well. FCIF is the algorithm that I
first developed to address the lambda insertion problem.

- https://dl.acm.org/doi/10.1145/3408983

However, pretty much the same time FCIF was published I realized that DOE is
probably nicer in practice. In the FCIF paper I shortly touched upon a
DOE-like system, and concluded that it wouldn't work, because postponed things
are prone to pile up and block things in a cascading way.

- I was missing the small but important detail of generating a "placeholder"
  meta for each postponed checking. Placeholder metas dramatically reduce the
  amount of "blockage" caused.
- On the other hand I had not actually implemented a DOE-like system before so I was
  a bit presumptious in dismissing it. Even now, I'm not sure how useful it would
  be to have DOE without placeholder metas; maybe even that would be usable!

Let's summarize FCIF. At the point of an ambiguous lambda insertion, we insert
an unknown number of lambdas, and proceed to elaborate. As we learn more
information, the unknown lambdas are refined to zero or more concrete implicit
lambdas. Hence, there is a) no postponing b) no guessing involved. Analogously
to how basic bidirectional elaboration can compute in the presence of unknown
terms (represented by metavariables), FCIF can compute under unknown lambda
insertions.

However, this requires extra machinery in the core language. Concretely, we
have:

1. Telescopes: these are first-class generic record types. They live in
   a `Tel` "universe" of telescopes.
2. The computation rules expressing that currying for telescopes holds
   definitionally. For example, if we write `()` for the empty telescope, then
   we have that `() → A ≡ A`, definitionally. Writing `(x : A) * Γ` for a
   right-nested non-empty telescope, we also have:

    `((x : (a : A) * Γ a) → B x) ≡ ({a : A} → (γ : Γ a) → B (a , γ))`

   In short, a function type with telescope domain computes to an iterated
   implicit function type. We have the appropriate computation rules for
   term formers too.

An unknown insertion is implemented by creating a fresh meta with type `Tel`,
and inserting a lambda with that binder type.

We have some evident unification rules for function types with telescope
domains, e.g. if we see an unknown telescope domain on one side, but something
which is not a function type on the other side, we solve the telescope to be
empty, so it computes away.

Additionally, we make sure that all inserted implicits are actually relevant,
in other words we don't create *non-dependent* implicit functions. If we
have

    let foo = true;

We would like to have as output

    let foo : Bool = true;

And not something like

    let foo : {_ : Bool} → Bool = λ {_}. true;

Therefore, for each insertion, we add a *constancy constraint*: this causes
the telescope to be solved to empty as soon as we learn that the domain type
does not actually depend on the inserted variable.

It should be clear that FCIF is significantly more complicated than DOE. Let's
compare their strength now.

First, we can easily find examples where one works and the other does not.
In the current implementation, DOE fails on

    let foo = λ f x y. f x y;

The reason is that when DOE checks `x` in `f x`, the checking type is unknown,
so it postpones the checking and creates a placeholder meta. But when DOE tries
to refine the type of `f x` to a function type, the placeholder meta clogs up
pattern unification. The bound variable `x` in a meta spine is fine, but a
placeholder meta is not in the pattern fragment! So we can see that postponing
does have some ability to clog up unification.

This particular example would be OK with more sophisticated postponing, such as
the one in Agda. There, we can simply postpone the unification problem too, and
it would be shortly unblocked anyway. FCIF has no issue here, it just marches on
and inserts telescope binders around `x` and `y`.

FCIF fails in the following case, and DOE succeeds:

    let foo : (({A} → A → A) → Bool × Nat) = id (λ f. (f true, f zero));

FCIF here barges ahead, but runs into the impossible problem of inferring type
for `λ f. (f true, f zero)`. DOE instead skips over the explosive subterm, and
when it gets back to checking it, it exactly knows the checking type, so there
is no problem.

Despite of neither being strictly stronger, I conjecture that FCIF is
practically stronger, mainly because it never guesses lambda insertions.

### Evaluation

Overall, based on my current knowledge, I say that DOE is the best existing
implementation of first-class polymorphism for practical purposes. The practical
UX difference between FCIF and DOE appears to be minimal, but DOE is much
simpler.

Hence, I feel comfortable adding this package to elaboration-zoo "proper" as a
demonstration of *best practice*; as opposed to as an experimental demo package.
