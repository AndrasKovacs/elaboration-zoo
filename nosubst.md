#### Dependent type checking without substitution

*Summary: interleaving normalization-by-evaluation and type checking gets us an algorithm that is extremely efficient, simple and obviously structurally recursive.*

In the well-known [Simply Easy!](https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf) tutorial, a minimal dependent type checker is presented that uses NbE (normalization by evaluation) with a [HOAS](https://en.wikipedia.org/wiki/Higher-order_abstract_syntax) representation for terms. However, as Danny Gratzer [bemoaned](http://jozefg.bitbucket.org/posts/2014-11-22-bidir.html), we still have to use explicit substitution when going under binders. Fortunately, it turns out we can get rid of substitution altogether - at least in the following small language.

Consider a simple dependent language with variables as de Bruijn levels (but we could switch to de Bruijn indices with minimal effort).

```haskell
data Term
  = Var !Int       -- ^ de Bruijn levels
  | App Term Term  
  | Lam Term Term  -- ^ Lam a t ~ \(x : a) -> t
  | Pi Term Term   -- ^ Pi a b ~ (x : a) -> b
  | Star           -- ^ The type of types (we also have (* : *) now)
  deriving (Eq)
```

And a HOAS for its semantic values (for simplicity, I'm not explicitly indicating that it's necessarily normal by using neutral values with spines):

```haskell
data Val
  = VVar !Int
  | VApp Val Val
  | VLam Val (Val -> Val)
  | VPi  Val (Val -> Val)
  | VStar
```

We also have `eval` and `quote` mapping between the two representations:

```haskell

-- Apply Val-s
($$) :: Val -> Val -> Val
($$) (VLam _ f) x = f x
($$) f          x = VApp f x

-- Here, we store the current depth (de Bruijn level) in "d"
eval :: Term -> Val
eval = go [] 0 where
  go env d (Var i)   = env !! (d - i - 1)
  go env d (App f x) = go env d f $$ go env d x
  go env d (Lam a t) = VLam (go env d a) $ \v -> go (v:env) (d + 1) t
  go env d (Pi  a b) = VPi  (go env d a) $ \v -> go (v:env) (d + 1) b
  go env d Star      = VStar

quote :: Val -> Term
quote = go 0 where
  go d (VVar i)   = VVar i
  go d (VApp f x) = App (go d f) (go d x)
  go d (VLam a t) = Lam (go d a) (go (d + 1) (t (VVar d)))
  go d (VPi  a b) = Pi  (go d a) (go (d + 1) (b (VVar d)))
  go d VStar      = Star
```

`quote . eval` performs normalization by evaluation, returning the normal form of a term. 

Let us observe that although `eval` and `quote` work in empty contexts, they could easily work in non-empty ones as well. We just have to lift out the environment and depth parameters from the `go` functions:

```haskell
eval :: [Val] -> Int -> Term -> Val
eval vs d = \case
  -- as before

quote :: Int -> Val -> Term
quote d = \case
  -- as before
```

Now, we might want to try performing type checking under this environment, thereby allowing us to directly normalize open terms using `quote` and `eval`. Let's define the context for type checking and some operations:

```haskell
type Type = Val
type Cxt  = ([Val], [Type], Int)

(<:) :: (Val, Type) -> Cxt -> Cxt
(<:) (v, t) (vs, ts, d) = (v:vs, t:ts, d + 1)

(<::) :: Type -> Cxt -> Cxt
(<::) t (vs, ts, d) = (VVar d:vs, t:ts, d + 1)
```

Our context contains `[Val]` and the `Int` depth needed for `eval/quote`, and it also contains a `Type` environment, which carries the types of the corresponding `Val`-s. The `Int` depth is always the same as the size of the context.

`(<:)` simply adds a value and type, while `(<::)` passes in a neutral variable as value.

Our key functions shall have the following types:

```haskell
type TM = Either String
check :: Cxt -> Term -> Term -> TM () -- check cxt term expectedType
infer :: Cxt -> Term -> TM ?
```

Notice the question mark in `infer`. I put it there because neither `Type` nor `Term` (which also denotes types here) are viable.

If we return `Term` we must use substitution in the `App` case:

```haskell
infer :: Cxt -> Term -> TM Term
infer cxt@(vs, ts, d) = \case
  App f x -> do
    infer cxt f >>= \case
      Pi a b -> do
        check cxt x a
        -- ?? we must substitute "x" into "b" now, but it's too late: "b" is a dumb "Term"
      _      -> Left "can't apply non-function"
```
    
And we can't return `Type` at all, because of the `Lam` case:

```haskell
infer :: Cxt -> Term -> TM Type
infer cxt@(vs, ts, d) = \case
  Lam a t -> do
    check cxt a Star
    let a' = eval vs d a
    tt <- infer (a' <:: cxt) t
    -- ?? now we should return a VPi Type (Val -> Val)`, but we simply don't have `Val -> Val`.
```
    
`Lam` is indeed at the heart of the issue. We might check lambdas by checking the body with a neutral variable substituted in, then abstracting over that variable after the checking is finished. However, if we have a lambda immediately applied to an argument, we could skip one round of instantiation and abstraction, and check the lambda body with the actual argument being stored in the environment:

```haskell
infer cxt@(vs, ts, d) (App (Lam a t) x) = do
  check cxt a Star
  let a' = eval vs d a
  check cxt x (quote d a')
  infer ((eval vs d x, a') <: cxt) t
```
      
However, if we try to generalize this rule in order to make all substitutions disappear, it gets a bit ugly, and we still can't return `Type`, because often there is no argument to be supplied, and we're left with a plain lambda, and as we've seen we can't infer `Type` from that. 

So let's make some sort of semantic value for type inference itself:

```haskell
data Infer
  = Ok Type
  | IPi Type (Val -> TM Infer)
```

The plan is to return `Infer` from `infer`, and also write a `quote` function for `Infer` which possibly yields a `Term`. Without further ado:

```haskell
quoteInfer :: Int -> Infer -> TM Term
quoteInfer d = \case
  Ok ty   -> pure $ quote d ty
  IPi a b -> Pi (quote d a) <$> (quoteInfer (d + 1) =<< b (VVar d))
  
check :: Cxt -> Term -> Term -> TM ()
check cxt@(_, _, d) t expect = do
  tt <- quoteInfer d =<< infer cxt t
  unless (tt == expect) $ Left "type mismatch"

infer :: Cxt -> Term -> TM Infer
infer cxt@(vs, ts, d) = \case
  Var i   -> pure $ Ok (ts !! (d - i - 1))
  Star    -> pure $ Ok VStar
  Lam a t -> do
    check cxt a Star
    let a' = eval vs d a
    pure $ IPi a' $ \v -> infer ((v, a') <: cxt) t
  Pi a b -> do
    check cxt a Star
    check (eval vs d a <:: cxt) b Star
    pure $ Ok VStar
  App f x -> 
    infer cxt f >>= \case
      IPi a b -> do
        check cxt x (quote d a)
        b (eval vs d x)
      Ok (VPi a b) -> do
        check cxt x (quote d a)
        pure $ Ok $ b (eval vs d x)
      _ -> Left "Can't apply non-function"
      
-- infer in the empty context
infer0 = quoteInfer 0 <=< infer ([], [], 0)
```

Essentially, we postpone checking lambdas until there's either an argument that can be recorded in the environment, or if there are no such arguments, we can use `quoteInfer` to plug in neutral `VVar`-s into all of the remaining binders. In the `App` case, we either supply the argument to the `IPi` continuation, or proceed as usual with the `VPi` extracted from `Ok`. And that's it!

Note that we only ever evaluate type checked terms, as we should, and we recurse on subterms without modifying them in any way. This makes me wonder if my trick could be put to interesting use in Agda (of course in Agda one would have to use a different `Val`, because the current one has positivity issues). Also, we don't store `Infer` anywhere, and we do `quoteInfer`  at most once for each `Infer`, so there's no work duplication. 

A self-contained source can be found [here](https://github.com/AndrasKovacs/tcbe/blob/master/Minimal.hs). 

It seems to me that there are great advantages to this scheme. First - although I haven't benchmarked yet - this algorithm should be much faster than those with explicit substitutions. Also, I find it very convenient that we have the entire context with values and types at our behest at any point. When we put something into the context, the rest of the term under consideration already contains the right `Var`-s pointing to it. 

We're also quite free to handle free or bound variables, since here there's no fundamental difference between them, and we can mix explicit and de Bruijn names as we like. 

If we ditch de Bruijn names altogether, we still only need a moderate amount of extra effort to implement alpha equality; an example can be found [here](https://github.com/AndrasKovacs/tcbe/blob/master/Nameful.hs). Since there's no substitution, there's no risk of capture, and no need for renaming. 

We're also not obligated to store HOAS values in the environment, or only store those. We can store raw `Term`-s as well for a variety of purposes (error reporting, checking equality without reduction), and we can access these `Term`-s through `VVar`-s from any extended context, and `eval` or process them.

----

Lately I've been reading about [dependent](https://pdfs.semanticscholar.org/0b74/a70ccad7829ad522337f0d3aa2106a59d4ee.pdf) [type inference](https://www.mpi-sws.org/~beta/papers/unicoq.pdf) and [elaboration](http://arxiv.org/pdf/1505.04324v2.pdf), partly because I'd like to understand how it works, partly because I'd like to investigate whether we can squeeze out more performance, which I believe would be important for adoption of dependently typed magics in practical software development. Next time I'll probably look at higher-order unification, still at "toy language" level, and try to find tricks and rationalizations that apply there. 


