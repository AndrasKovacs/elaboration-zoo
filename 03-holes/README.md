
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
never use capture-avoiding substitution nor global fresh name generation.


### About holes and pattern unification


Take a program with a hole, like:

~~~
    let id : (A : *) → A → A
      = λ A x. x
    in

    let id2 : (A : *) → A → A
      = λ A x. id _ x
    in

    id2
~~~

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

~~~
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
~~~

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

~~~
    α t₁ t₂ t₃ ... tₙ =? u
~~~

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

~~~
    α true =? true
~~~

is solvable with both of the following:

~~~
    α := λ x. x
    α := λ x. true
~~~

A heuristic called "dependency erasure" always picks the second solution in this case;
dependency erasure just throws away all parameters which are not bound variables. This
makes more program typecheck, at the cost of possibly more erratic behavior.

The *occurs check* may be familiar from Hindley-Milner inference. If we fail
this check, then the solution would be circular, or "infinite", as in GHC's
infamous infinite type error messages. For example:

~~~
    α =? (α -> α)
~~~

is circular, hence unsolvable.

If the *scope check* fails, then the equation may or may not be solvable. In our simple
implementation, we always fail on scope check failure, but more powerful implementations
can sometimes find solutions. Example for unsolvable equation:

~~~
    α x y =? (z -> z)
~~~

where (z -> z) is a function type and "z" is a bound variable. Since "α" is
defined on the top level, it cannot depend on any local variable, and all
dependency must be expressed through λ parameters. So, it's totally not possible
to put "z -> z" in the solution, because that's not meaningful in the top-level
scope. Another example, which is possibly solvable:

~~~
    α x y =? (x -> β x z)
~~~

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

~~~
    α x x =? x
~~~

is solvable as (α := λ x _. x) and also as (α := λ _ x. x).

The current implementation ignores the linearity condition, and always picks the
rightmost variable occurrence in solutions. This makes solutions non-unique, but
my experience is that this is practically justifiable, and the rightmost occurence
is usually the correct pick.

In short, the current implementation has spine check, occurs check and scope check
but no linearity check.
