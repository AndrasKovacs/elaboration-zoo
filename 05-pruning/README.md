## elabzoo-pruning

New features:
- typed metas
- pruning

You can look at [example.txt](example.txt) for examples which can be elaborated thanks to new features.

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

We stick to the simple version.


#### Intersection & non-linear spines

We add two extra use-cases of pruning.

- Intersection: when solving `m spine =? m spine'`, if `spine` and `spine'`
  are both renamings, we prune all arguments from `m` which differ in the spines.
  For example, `m x y z =? m z y y` succeeds with `m := λ x y z. m' y` if the
  pruning is well-typed.
- Non-linear spines. When solving `m spine =? rhs`, if `spine` is non-linear, but
  `rhs` does not depend on non-linear vars, and those vars can be pruned from `m`,
  then we may solve `m` as usual.
