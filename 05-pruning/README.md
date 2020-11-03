## elabzoo-pruning

New features:
- ordered metacontext
- typed metas
- pruning

You can look at [example.txt](example.txt) for examples which can be elaborated thanks to new features.

#### Typed & ordered metacontext

Previously, the metacontext was conceptually an untyped mutual block of definitions.

Now it's typed and ordered by dependency. Hence, it can be viewed as an ordinary
sequence of let-definitions.

When every meta solution is in normal form, the ordering is not relevant in the
elaboration output, since no meta solution refers to any other meta solutions (everything is unfolded in normal forms).

However, it is a crucial optimization to allow meta solution in non-normal form.
We don't support it in this package, but later we will. In this case, meta solutions
can refer to other metas:

    let ?0 : A = .........
    let ?1 : B = ..... ?0 ......

This prevents size blowups of solutions. At the same time, we want the solutions
to form an ordinary non-mutual sequence of let-definitions, so that the
elaboration output is a legal core expression, and can be validated by type
checking. Additionally, we can use the dependency information to avoid unfolding
metas during occurs/scope checking in some situations.

**Implementation.** We use an *order-maintenance structure*. The metacontext is extended
with additional data. Now, entries form a doubly-linked list (linked by metavar indices),
which is in dependency-order at all times. Every meta entry has a floating point *weight*,
such that weights are in increasing order in the linked list of entries.

- We compare metas for dependency ordering by simply comparing the weights.
- Whenever we add a new meta, or move an existing meta, we have to update links and
  weights to maintain invariants.
- When a new entry is inserted between existing entries, we take the *average*
  of the weights of neighboring entries, as the new weight. This averaging may
  fail if we run out of floating point precision. In that case, we reassign
  every weight in the metacontext to get more precision headroom.


#### Pruning

Pruning removes dependencies of metavariables on some of their arguments.

Example: we want to solve `?0 x = (?1 x y → ?1 x y)`. This is not well-scoped
because `rhs` depends on `y`. However, we may be able to prune `y` from `?1`, by creating
a fresh meta `?2`, and solving as follows:

    ?1 := λ x y. ?2 x

Now the problem becomes	`?0 x = (?2 x → ?2 x)` which is eminently solvable.

However, we also have to check that `?1 := λ x y. ?2 x` is actually well-typed.
Pruning is only possible if `?1`'s type is well-formed after we remove all pruned
arguments.

This implies that we have to keep around the types of metas in the metacontext.

An example for pruning. We want to infer type for `λ f. f U`.

- `f` gets the fresh meta `?0` as a type.
- We infer type for the body.
- In `f U`, we refine `?0` to a fresh function type, i.e. perform `?0 =? (x : ?1 f) → ?2 f x`.
- This is ill-scoped, since rhs depends on `f`. We have to prune `f` from `?1` and `?2`.
  After pruning, we solve `?0 := (x : ?3) → ?4 x`.

In unification, we extend partial renaming to also prune metas. *Only a spine
which is a renaming may be pruned*. It is possible to generalize this, see e.g.
section 3.4. in:

  http://www.cse.chalmers.se/~abela/unif-sigma-long.pdf

We'll stick to the simple version.


#### Intersection & non-linear spines

We add two extra use-cases of pruning.

- Intersection: when solving `m spine =? m spine'`, if `spine` and `spine'`
  are both renamings, we prune all arguments from `m` which differ in the spines.
  For example, `m x y z =? m z x x` succeeds with `m := λ x y z. m' y` if the
  pruning is well-typed.
- Non-linear spines. When solving `m spine =? rhs`, if `spine` is non-linear, but
  `rhs` does not depend on non-linear vars, and those vars can be pruned from `m`,
  then we may solve `m` as usual.
