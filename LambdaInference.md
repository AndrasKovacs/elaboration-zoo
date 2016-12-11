### Adapting Coquand's algorithm to infer types for lambda terms with annotated bindings.

#### Intro

Dependent type checking involves evaluation of functional programs. Compilers and interpreters of functional languages have been acceptably fast since the 80s, and their evaluation strategies are well-understood, so why not use that for dependent type checking as well?

This could be seen as one basic idea behind [Coquand's algorithm](http://ac.els-cdn.com/0167642395000216/1-s2.0-0167642395000216-main.pdf?_tid=848e736c-944f-11e6-b999-00000aacb362&acdnat=1476698172_390e8fd4c6267a2fc9e68704b0e96c9e). The advantages are manifold:

- No syntactic substitution, therefore no need for shifting, renaming or any sort of capture avoidance.
- No need for fresh name generation (for simple type checkers).
- Tremendously faster than evaluation by substituting redexes away.
- Easier to implement correctly.
- Easily extended to type-directed evaluation and syntactic equality checks (equality with no/limited reduction).
- Possible to extend to [machine code](https://depositonce.tu-berlin.de/bitstream/11303/3095/1/Dokument_9.pdf) based evaluation or [JIT compilation](http://www.maximedenes.fr/download/coqonut.pdf) (even during type checking). 

Popular introductory materials on dependent type checking unfortunately fail to mention Coquand's algorithm and its variants. This post is not the introductory tutorial that should exist. You can refer to [this](http://www2.tcs.ifi.lmu.de/~abel/msfp08.pdf) and [this](http://www.cse.chalmers.se/~bengt/papers/GKminiTT.pdf), or may look at the files in this repository, which are all variations of the algorithm in question.

#### What we'd like to do

The problem is that the linked references don't support inferring types for lambdas, instead they mandate lambdas wrapped in explicit type annotations. [cubicaltt](https://github.com/mortberg/cubicaltt), another language with Coquand's algorithm, annotates binders on top-level functions but also requires annotated return types. What if we'd like to infer types for lambdas with annotated binders but no annotation for the return type? For example, we want to infer a type for `\(A : *). \(x : A). x`. Moreover, we'd like to stick to Coquand's algorithm and not start using substitution in any shape or form, since that reliably ruins performance. 

Now, this is not a huge problem, and in more sophisticated systems we'd have unification and metavariables anyway, which renders the problem and its solution largely irrelevant. But it's a nice solution, so I shall present it. 

#### The solution

Only the "not using substitution" part is slightly tricky here. The main issue is with applications to lambda terms:

    (\(x : A). t) t'
    
In the usual presentation of checking application expressions, first we infer a weak-head-normal type for the function, check that it's a pi type, then check the type of the argument against the input type of the pi. Finally, we apply the pi type to the argument value and evaluate the resulting type.

Here we can't do this. In order to infer type for the lambda, we need to go under the lambda binders, and we do that by recording in the environment their types and also the fact that they are bound variables. Since we're in an application expression, we'll need to apply the inferred pi type to the argument values, however the inferred pi type was inferred in an environment with rigid variables standing for all the lambda arguments. The pi type inferred this way is not a proper HOAS value or environement machine as it should be, it's just a piece of dead syntax, and we can't *run it* anymore, we can only *substitute* into it. 

So: let's delay type inference of lambda terms until either:

- There is an argument the resulting pi type can be applied to. In this case we infer a type for the lambda body
  using the argument value.
- It's clear that there is no argument. In this case we can safely infer a type using rigid bound variables.

Instead of having `infer` return in `TypeCheckingMonad Type`, we're going to return either a `Type` or a continuation for inferring pi types:

```haskell
data Infer
  = Ok Type
  | IPi Type (Val -> TM Infer)
```

Now, inference for lambdas just returns an `IPi` continuation without looking at the lambda body, and inference for applications does the following:

1. Infer type for the function.
2. If it's `IPi a k`, check the argument against `a`, then call `k` with the argument's value.
3. If it's `OK t`, do the same as we did before when checking applications.

You can look at [this](https://github.com/AndrasKovacs/tcbe/blob/master/Nameful.hs#L110) part of the code, for example.

