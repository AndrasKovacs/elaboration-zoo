{-|

Type checking by evaluation.

Below's a type checker for a minimal dependent lambda calculus, much like Morte.

https://hackage.haskell.org/package/morte

This type checker doesn't use substitution at all. Only the "quote" and "eval"
functions of the "Normalization by Evaluation" technique are used. As a result,
this implementation is much more efficient and in some ways conceptually
simpler than exising implementations of minimal dependent LC such as the mentioned
Morte or LambdaPi (http://strictlypositive.org/Easy.pdf).

The key point of our implementation here is to not only use NBE for terms, but
interpret type checking itself into semantic values. We do evaluation of types
and type checking at the same time, carrying around an environment of (semantic values of)
normal terms and types. As opposed to in LambdaPi, evaluation and quoting depends on the
current context.

Also, this type checker is obviously structurally recursive on the to-be-checked term,
which is not the case with type checkers that substitute into terms under binders before
recursing on them. For this reason, it could be worthwhile to investigate this algorithm
in a formal (Agda, Coq) setting too.

Some ideas to be explored:

  - Sigma types or hard-coded inductive types with eliminators
  - Bidirectional type checking: on first thought, propagation of type information
    could be handled really well here.
  - Alternative variable binding: since there is no substitution, nameful (non-de-Bruijn)
    variables could be relatively convenient.
  - Handling of substitutions and constraints

-}

{-# language BangPatterns, LambdaCase #-}

import Prelude hiding (pi)
import Control.Monad.Except
import Data.Either
import Text.Printf

-- | Usual dependent LC terms.
-- We use de-Bruijn *levels*, because NBE is simpler
-- with it relative to de-Bruijn indices (or that's what I think).
data Term
  = Var !Int
  | App Term Term
  | Lam Term Term
  | Pi Term Term
  | Star
  deriving (Eq)

pretty :: Int -> Term -> ShowS
pretty prec = go (prec /= 0) where

  unwords' :: [ShowS] -> ShowS
  unwords' = foldr1 (\x acc -> x . (' ':) . acc)

  spine :: Term -> Term -> [Term]
  spine f x = go f [x] where
    go (App f y) args = go f (y : args)
    go t         args = t:args

  go :: Bool -> Term -> ShowS
  go p (Var i)   = (show i++)
  go p (App f x) = showParen p (unwords' $ map (go True) (spine f x))
  go p (Lam a t) = showParen p (("λ "++) . go True a . (" -> "++) . go False t)
  go p Star      = ('*':)
  go p (Pi a b)  = showParen p (go True a . (" -> "++) . go False b)

instance Show Term where
  showsPrec = pretty

-- | Usual HOAS values. We could have used explicit types for neutral
-- values. I ommited them for simplicity.
data Val
  = VVar !Int
  | VApp Val Val
  | VLam Type (Val -> Val)
  | VPi  Type (Val -> Val)
  | VStar

-- | TC stands for "type checking". It either returns a normal type,
-- or returns a continuation possibly yielding a Pi type.
data TC
  = Ret Type
  | CheckPi Type (Val -> Check TC)

type Type = Val

-- | The context is essentially [(Type, Val)], but we split
-- types and values because it's more efficient to only pass
-- around the list that's needed.
--
-- The 'Int' values carries the length of the lists.
-- We use it to compute lookup indices (which is needed because of
-- our use of de-Bruijn levels).
type Cxt   = ([Type], [Val], Int)
type Check = Either String

cxt0 :: Cxt
cxt0 = ([], [], 0)

-- | Append a 'Type'-'Value' pair to the context.
(<:) :: (Type, Val) -> Cxt -> Cxt
(<:) (t, v) (ts, vs, d) = (t:ts, v:vs, d + 1)

-- | Append a 'Type' to the context and plug in a neutral `VVar`
-- into the value slot. This is useful for quoting values.
(<::) :: Type -> Cxt -> Cxt
(<::) t (ts, vs, d) = (t:ts, VVar d:vs, d + 1)

-- | Lookup a 'Type' from the context.
lookupTy :: Cxt -> Int -> Type
lookupTy (ts, vs, d) i = ts !! (d - i - 1)

-- | Apply 'Val's.
($$) :: Val -> Val -> Val
($$) (VLam _ f) x = f x
($$) f          x = VApp f x
infixl 9 $$

-- | Perform a 'TC' in a context, yielding either a
-- syntactic type in normal form or an error.
-- This operation is essentially 'quote' for 'TC'.
runTC :: Cxt -> TC -> Check Term
runTC (_, _, d) = go d where
  go d (Ret ty)      = pure $ quote' d ty
  go d (CheckPi a b) = Pi (quote' d a) <$> (go (d + 1) =<< b (VVar d))

quote :: Cxt -> Val -> Term
quote (_, _, d) = quote' d

quote' :: Int -> Val -> Term
quote' d = \case
  VVar i   -> Var i
  VApp f x -> App (quote' d f) (quote' d x)
  VLam a t -> Lam (quote' d a) (quote' (d + 1) (t (VVar d)))
  VPi  a b -> Pi  (quote' d a) (quote' (d + 1) (b (VVar d)))
  VStar    -> Star

eval :: Cxt -> Term -> Val
eval (ts, vs, d) = go vs d where
  go vs !d = \case
    Var i   -> vs !! (d - i - 1)
    App f x -> go vs d f $$ go vs d x
    Lam a t -> VLam (go vs d a) $ \v -> go (v:vs) (d + 1) t
    Pi  a t -> VPi  (go vs d a) $ \v -> go (v:vs) (d + 1) t
    Star    -> VStar

check :: Cxt -> Term -> Term -> Check ()
check cxt t ty = do
  tt <- runTC cxt =<< infer cxt t
  unless (tt == ty) $ do
    throwError $ printf
      "Couldn't match expected type %s for term %s with actual type: %s"
      (show ty) (show t) (show tt)

{- |

In 'infer', the @Lam@ case is most important. Whenever we have a lambda we just
return a continuation that checks the lambda body. If the lambda is applied to an
argument, we can resume checking in the @App@ case, pushing the argument into 'CheckPi'.

Note that 'CheckPi' does not introduce work duplication or leaks, because 'TC' values
aren't stored anywhere. 'CheckPi's are either fully applied and reduce to `Ret t`, or
partially applied and then reduced to a pi 'Type' by 'runTC'.

We store `Val`-s in the context. `Val` by themselves aren't normal, but they yield
normal terms when quoted. Can we duplicate work by quoting the same `Type` or `Value`
multiple times, when checking for term equality? Well, we can. But note that:

  - 'eval' lets us share work up to whnf, and only computation under lambdas will
     be redone each time. This is often enough sharing.
  - We can actually share full normal form reduction by eval-ing, quoting and evaling again
    before insertion into context. The last eval is a bit tricky since we're operating under
    an environment, but it can be done and it's indeed done in Main.hs in this project. However,
    using full normal form sharing all the time has a considerable overhead (though of course
    normal forms too are only computed at all if forced). Benchmarks are warranted.
-}

infer :: Cxt -> Term -> Check TC
infer cxt = \case
  Var i   -> pure $ Ret (lookupTy cxt i)
  Star    -> pure $ Ret VStar
  Lam a t -> do
    check cxt a Star
    let a' = eval cxt a
    pure $ CheckPi a' $ \v -> infer ((a', v) <: cxt) t
  Pi a b -> do
    check cxt a Star
    check (eval cxt a <:: cxt) b Star
    pure $ Ret VStar
  App f x -> do
    tf <- infer cxt f
    case tf of
      CheckPi a b -> do
        check cxt x (quote cxt a)
        b (eval cxt x)
      Ret (VPi a b) -> do
        check cxt x (quote cxt a)
        pure $ Ret $ b (eval cxt x)
      _ -> throwError $
             printf "Can't apply non-function type %s when checking term %s"
             (show $ runTC cxt tf) (show $ App f x)

infer0 :: Term -> Check Term
infer0 = runTC cxt0 <=< infer cxt0

quote0 :: Val -> Term
quote0 = quote cxt0

infer0' :: Val -> Check Term
infer0' = infer0 . quote0

eval0' :: Val -> Check Term
eval0' v = quote cxt0 v <$ infer0 (quote cxt0 v)


-- HOAS sugar & examples
--------------------------------------------------------------------------------

-- Be careful with strictness and ill-typed code.
-- 'infer0' reduces to normal form before checking,
-- which may lead to nontermination or excessive computation.

-- Of course, the proper way is to define sample code with 'Term' instead of 'Val'.
-- That's both much lazier and safe.

pi          = VPi
lam         = VLam
star        = VStar
forAll      = lam star
let' ty x e = lam ty e $$ x

(==>) a b = pi a (const b)
infixr 8 ==>

id'    = forAll $ \a -> lam a $ \x -> x
const' = forAll $ \a -> forAll $ \b -> lam a $ \x -> lam b $ \_ -> x

compose =
  forAll $ \a ->
  forAll $ \b ->
  forAll $ \c ->
  lam (b ==> c) $ \f ->
  lam (a ==> b) $ \g ->
  lam a $ \x ->
  f $$ (g $$ x)

nat = pi star $ \a -> (a ==> a) ==> a ==> a

z = forAll $ \a ->
    lam (a ==> a) $ \s ->
    lam a $ \z ->
    z

s = lam nat $ \n ->
    forAll $ \a ->
    lam (a ==> a) $ \s ->
    lam a $ \z ->
    s $$ (n $$ a $$ s $$ z)

add =
  lam nat $ \a ->
  lam nat $ \b ->
  forAll $ \r ->
  lam (r ==> r) $ \s ->
  lam r $ \z ->
  a $$ r $$ s $$ (b $$ r $$ s $$ z)

mul =
  lam nat $ \a ->
  lam nat $ \b ->
  forAll $ \r ->
  lam (r ==> r) $ \s ->
  a $$ r $$ (b $$ r $$ s)

two = s $$ (s $$ z)
five = s $$ (s $$ (s $$ (s $$ (s $$ z))))
ten = add $$ five $$ five
hundred = mul $$ ten $$ ten

nFunTy =
  lam nat $ \n ->
  n $$ star $$ (lam star $ \t -> star ==> t) $$ star

nFun =
  lam nat $ \n ->
  lam (nFunTy $$ n) $ \f ->
  star

list = forAll $ \a -> pi star $ \r -> (a ==> r ==> r) ==> r ==> r

nil  = forAll $ \a -> forAll $ \r -> lam (a ==> r ==> r) $ \c -> lam r $ \n -> n

cons =
  forAll $ \a ->
  lam a $ \x ->
  lam (list $$ a) $ \xs ->
  forAll $ \r ->
  lam (a ==> r ==> r) $ \c ->
  lam r $ \n ->
  c $$ x $$ (xs $$ r $$ c $$ n)

map' =
  forAll $ \a ->
  forAll $ \b ->
  lam (a ==> b) $ \f ->
  lam (list $$ a) $ \as ->
  as $$ (list $$ b) $$
    (lam a $ \x -> lam (list $$ b) $ \xs -> cons $$ b $$ (f $$ x) $$ xs) $$
    (nil $$ b)

sum' =
  lam (list $$ nat) $ \xs ->
  xs $$ nat $$ add $$ z

natList = let c = cons $$ nat; n = nil $$ nat in
  c $$ z $$ (c $$ five $$ (c $$ ten $$ n))

test = all (isRight . infer0')
  [id', const', compose, nat, z, s, add, mul, two, five, nFunTy, nFun,
   nFun $$ five, sum' $$ natList, map']


