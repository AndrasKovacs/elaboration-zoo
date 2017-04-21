{-# language BangPatterns, Strict, LambdaCase, PatternGuards, OverloadedStrings #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

{-|
Design:
- Indexed inductive families + dependent pattern matching + recursive definitions.
- Type in Type, no positivity check, manual annotation for structurally decreasing params.
- No built-in mutual recursion/induction (but encodable, of course).
- A single structurally decr. argument for each recursive function.
- Recursive definitions are unfolded iff they are applied to their decreasing
  argument, and the argument is canonical (i. e. non-neutral).


Things to ponder

  1. Dependent pattern matching actually causes *bound* variables to be
     arbitrarily substituted during type checking! For example:

       foo : (A : U)(x y : A) -> x ≡ y -> y ≡ x
       foo A x y =
         let bar : A × A × A
             bar = x , x , x
         in λ {refl ->
                let baz : bar ≡ (y , y , y)
                    bar = refl
                in refl}

     Here, we may first evaluate "bar" lazily to whnf, but later
     in the pattern lambda "x" gets substituted to "y", so we need
     to refresh "bar" in the new value environment.During conversion check
     and lhs unification we need to refresh neutrals headed by bound variables.

     Where/how should we store BVar substitutions?

--------------------------------------------------------------------------------

**About dependent patterns**

- In Agda, if there are multiple pattern args, on any split the outer bindings can be refined.
- In Coq, no outer binding can be ever refined.
- We could in principle implement dep. pattern match which can refine *any* outer binding.

But: refining outer bindings makes it unsafe and non-type-preserving to evaluate under splits.

REFERENCE: http://gallium.inria.fr/~remy/coercions/Scherer-Remy!fth@long2014.pdf
   "Full reduction in the face of absurdity"

Example:

data Foo A : Set where
  Nat  : Foo Nat
  Bool : Foo Bool

f : ∀ {A} → A → Foo A → A
f = λ a (λ Nat → a + 0; Bool → not a)

Now, "f 0" reduces to (λ Nat → 0; Bool → not 0). Here, "not 0" is ill typed.
In the "Bool" branch we're operating under an assumed false definitional equality.

What can we do about this?

- The Agda way is to have all refinable bindings encapsulated in a single pattern, and
  a pattern is not unfolded unless it's applied all formal args:

  f : ∀ {A} → A → Foo A → A
  f a Nat  = a + 0
  f a Bool = not a

  Now, "f 0" is not unfoldable since it's missing an argument.

- In Coq, there's only single argument split which can't refine outside things.

Question: what needs to be implemented if we have arbitrary refinement, like in "f" above?

Can we rewrite dep match to typecase?

      f : ∀ {A} → A → Foo A → A
      f = λ {A} a → case A of
        Nat  → (λ Nat → a + 0)
        Bool → (λ Bool → not a)

    Now, "f {Nat} 0" reduces to ((λ Nat → 0) : Foo Nat → Nat)

    The overall goal is to eliminate impossible cases during eval (?). But it's not very efficient
    via unification. Also not clear what happens with stuck unification, like:

       f : Set → Set
       x : Set
       a : f x
       -----------
       f {f x} a |-> ?

    "f x ~ Nat" and "f x ~ Bool" both get stuck, and (λ Nat a + 0; Bool → not a) is ill-typed.

    Not worth it.

Solution: never evaluate under case split. Use dumb syntactic equality for split bodies (like mini-tt does).


--------------------------------------------------------------------------------
-- Latest version to consider
--------------------------------------------------------------------------------

Consider mini-tt's solution to symbol unfolding: just never evaluate under case split.
This works well even without termination information, because structurally recursive functions
can only make structurally recursive calls under splits.

  add = λ a (λ (zero → a; suc b → suc (add a b)))

We can mindlessly delta-reduce add, but when we check conversion
to another body, the recursive "add" never gets unfolded because it's
under a split.

Question though: what about structural recursion via function call? "f x" is structurally
smaller than "f" for all "x", and we can get an "f" input without case split. Then recursive
calls may not be under split, but they must be structural, so unfolding again terminates, if
the function itself terminates.

Design idea: use mini-tt's case split eval rule, but alongside the high-powered dep patterns
with arbitrary outer refinement.

In contrary to mini-tt/PiSigma, there's just no need for intensional equalities for types
and functions. In the long run, we just want univalence for types and funext for functions,
so who cares about intension. Even if we don't get univalence, we can make our own universes of
codes with as much intensional equality as needed.


-- Delayed instantiation:

When elaborating in checking direction, do NOT evaluate the target type if
its shape already matches the term at hand.

Special rule for checking "((λ p. t) x) <= B"? Case expr. on variables can desugar to
this, may be useful for desugaring nested patterns.



-}

import qualified Data.Text as T
import Control.Monad

type Name  = T.Text
type Gen   = Int
type Sub a = [(Name, a)]
type Env   = Sub (Maybe Val)
type Ty    = Tm
type VTy   = Val

data Tm
  = Var Name
  | App Tm Tm
  | Lam Name Tm
  | Split [(Pat, Tm)]
  | Pi Name Ty Tm
  | Let Name Ty Tm Tm
  | U

data Pat
  = PCon Name [Name]
  | PAny  

data Val
  = VVar Name
  | VGen Gen
  | VApp Val ~Val  
  | VLam Name Env Tm
  | VSplit Env [(Pat, Tm)]
  | VPi Name VTy Env Tm
  | VU






vapp :: Val -> Val -> Val
vapp (VLam x e t)  ~a = eval ((x, Just a):e) t
vapp (VSplit e ps) ~a = go ps where
  h = vhead a


  
vapp f             ~a = VApp f a

eval :: Env -> Tm -> Val
eval e = \case
  Var x   -> maybe (VVar x) id (join $ lookup x e)
  App f x -> _

  

