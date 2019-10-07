## elabzoo-poly-instantiation

#### Background

This package implements enhanced elaboration with first-class implicit function
types. This means that `{x : A} → B` types are proper function types, differing
from explicit functions only in that lambdas and applications are given by
elaboration by default, not by the programmer. Agda has such function type, but
its elaborator is rather weak in relation to it. This manifests to Agda users
as situations where implicit lambdas have to be written out manually.

A simple example where Agda cannot correctly insert implicit lambdas:

```
open import Data.List

listError : List ({A : Set} → A → A)
listError = (λ x → x) ∷ []

listOK : List ({A : Set} → A → A)
listOK = (λ {A} x → x) ∷ []
```

In Haskell and ML-related literature, ergonomic support for this is called
"impredicative instantiation" or "impredicative polymorphism", and there it
means instantiating metas with implicit function types (denoted `∀ (a :: k). t`
in Haskell). This "impredicative" is unrelated to impredicativity in type
theory, and the naming appears to be a historic artifact.

There is extensive literature. Examples:

- [Boxy Types: Inference for Higher-Rank Types and Impredicativity](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/boxy-icfp.pdf)
- [HMF: Simple type inference for first-class polymorphism](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/hmf.pdf)
- [Guarded Impredicative Polymorphism](https://www.microsoft.com/en-us/research/uploads/prod/2017/07/impredicative-pldi18.pdf)
- https://github.com/ghc-proposals/ghc-proposals/pull/274

However, despite more than a decade of investigation, no practical
implementation has landed so far in production compilers. The topic has a
reputation for being a "swamp" of complicated and hacky solutions. The
GHC proposal for "quick look impredicativity" above has a chance of being
implemented, because although far from elegant, it is simple and practically
sufficient.

#### Basic bidirectional elaboration

I build the general and precise solution atop the bidirectional elaboration
algorithm of Agda. See Section 3.6 of [Ulf Norell's
thesis](http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf). I review the basic
principles here.

There are two elaboration modes, *checking* and *inferring*. The checking mode
has a raw term and a type as input, and produces a core term. The inferring
mode has a raw term as input and produces a core term and a type.

The handling of implicit functions is the following:

- When checking a non-implicit-lambda raw term with an implicit function type, insert
  a new implicit lambda in the output.
- When inferring, if the output type is an implicit lambda, insert an implicit
  application to a fresh meta.

In short, checking inserts implicit lambdas, inference inserts implicit applications.

Examples for checking:

```
id : {A : Set} → A → A
id = λ x → x
```

Checking `(λ x → x) : {A : Set} → A → A` results in `λ {A} x → x` as output. Example for inferring:

```
id2 : {A : Set} → A → A
id2 = λ {A} x → id x
```

Inferring `id` the type `{A : Set} → A → A` results in the `id {α A x} : α A x → α A x` output,
where `α A x` is a fresh meta applied to the bound variables in scope.

However, there is a problem when we:

- check a raw term with a meta-headed type
- infer a meta-headed type for a raw term

because we have no idea whether we should insert implicit things or not! If the
blocking meta is solved to be an implicit function type, we should insert, if
it's solved to something which is definitely not an implicit function, we should
not.

Agda makes the choice of *never* inserting in this situation. This is a general assumption
that as-of-yet-unknown types are not polymorphic. This is often correct to assume.

For a very simple example where checking with meta-headed type occurs:

```
b = id true

-- insert meta first
b = id {α} true

-- check (true : α)   -- !! note the checking with meta !!
-- unify Bool α
-- output
b = id {Bool} true
```

A naive solution would be to postpone checking with meta-headed types, until
the meta is solved. This works badly in practice, e.g. the above `b = id true`
example would produce an unsolved constraint. Two main problems:

- This assumes that *any* raw term could be wrapped in an implicit lambda, although
  in many cases it'd dumb to do so. E.g., since `true : Bool` is a closed term which
  cannot depend on anything, wrapping it in implicit lambda always yields a constant
  function `λ {_} → true` with a non-dependent implicit function type `{_ : A} → Bool`.
  We do not want elaboration to create non-dependent implicit functions, because their
  parameters are *never* inferable.
- Postponing checking makes a lot of typing information inaccessible, which we could
  otherwise learn from elaborating the term. Also, we cannot compute with a term
  whose checking is postponed (a "guarded constant" in Agda terminology).


#### Elaboration with telescopes

As we've seen, the core issue is uncertainty about implicit insertion.

The solution is to add new feature to a core type theory which let us
represent unknown arities of implicit functions. We add two type formers:

1. Telescopes. These behave as generic right-nested sigma types, can be
   viewed as generic "record" types as well. They are uncontroversial
   in type theory.
2. Implicit functions with *strict* telescope domain. This is an implicit
   function space which immediately computes to iterated implicit functions
   as soon as we know the domain arity.

Some rules and notation. We assume U Russell-style universe with U : U for brevity.

```

-- Telescopes
------------------------------------------------------------


─────────── type of telescopes
Γ ⊢ Tel : U

─────────── empty telescope
Γ ⊢ ∙ : Tel

Γ ⊢ A : U   Γ, x:A ⊢ B : Tel
──────────────────────────── extended telescope
   Γ ⊢ (x : A) ▶ B : Tel

 Γ ⊢ Δ : Tel
───────────── type of telescope terms ("record")
Γ ⊢ Rec Δ : U

────────────── empty telescope term
Γ ⊢ [] : Rec ∙

  Γ ⊢ t : A   Γ ⊢ u : B[x ↦ t]
─────────────────────────────── extended telescope term
Γ ⊢ (t ∷ u) : Rec ((x : A) ▶ B)

     Γ ⊢ t : Rec ((x : A) ▶ B)
─────────────────────────────────── projections
Γ ⊢ π₁ t : A   Γ ⊢ π₂ t : B[x↦π₁ t]

(π₁ (t ∷ u))	= t     -- beta
(π₂ (t ∷ u))	= u     -- beta
(π₂ t ∷ π₂ t)	= t     -- eta
t             = []    -- eta


-- Telescope functions
------------------------------------------------------------


Γ ⊢ Δ : Tel   Γ , x : Rec Δ ⊢ B : U
─────────────────────────────────── type formation
      Γ ⊢ {x : Δ} → B : U

   Γ, x : Rec Δ ⊢ t : B
────────────────────────── lambda
Γ ⊢ λ{x:Δ}.t : {x : Δ} → B

Γ ⊢ t : {x : Δ} → B   Γ ⊢ u : Rec Δ
─────────────────────────────────── application
       Γ ⊢ t{u:Δ} : B[x ↦ u]

{x : ∙} → B           = B[x ↦ []]
{x : (y : A) ▶ Δ} → B = {y : A} → {x₂ : Δ} → B[x ↦ (y ∷ x₂)]

(λ{x:∙}.t)            = t[x ↦ []]
(λ{x:(y : A) ▶ Δ}.t)  = λ{y}. λ{x₂:Δ}. t[x ↦ (y ∷ x₂)]

t{u:∙}                = t
t{u:(x : A) ▶ Δ}      = t{π₁ u}{π₂ u : Δ[x ↦ π₁ u]}

(λ{x:Δ}.t){u:Δ} = t[x ↦ u]
(λ{x:Δ}.t{x:Δ}) = t

```
