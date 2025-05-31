
{-# language Strict, LambdaCase, BlockArguments #-}
{-# options_ghc -Wincomplete-patterns #-}

{-
Minimal demo of "glued" evaluation in the style of Olle Fredriksson:

  https://github.com/ollef/sixty

The main idea is that during elaboration, we need different evaluation
strategies for different tasks; here in particular we have a distinction
between top and local scope, and we want to have control over unfolding
of top-level definitions.

- For generating terms (for error displaying, serialization, metavariable
  solutions), we want to avoid unfolding as much as possible, to avoid size
  blowups.

- For conversion checking, we want to have an efficient, preferably call-by-need
  evaluator which unfolds everything.

We want evaluation to be as fast as possible, and we also want to avoid
duplicating computation between the two unfolding modes which could be shared.

The solution here is to use normalization-by-evaluation extended with
lazy non-deterministic choice in the semantic domain. We extend values with

    ... | VTop Name Spine ~Val

where Name and Spine constitute a neutral expression whose head is a top-level
definition name, and ~Val is the lazy result of evaluating the same neutral
expression, but with the top definition unfolded.

Hence, when we hit VTop during processing Val-s, we can choose between
unfolding and not unfolding.

We also have to implement the semantic action of projections and eliminations
on VTop. In our case, we only have function application:

    vapp :: Val -> Val -> Val
    vapp (VLam _ t)    ~u = t u
    vapp (VLoc x sp)   ~u = VLoc x (SApp sp u)
    vapp (VTop x sp t) ~u = VTop x (SApp sp u) (vapp t u)

vapp acts on both branches of VTop. The neutral part is eagerly computed,
since the computation there is trivial, delaying it would be more costly
than just performing it. In contrast, the "vapp t u" can be arbitrarily costly,
so it is delayed.

Note that "u" is duplicated in "VTop x (SApp sp u) (vapp t u)". This means
that "u" is computed at most once regardless of which evaluation branch we
compute (of course, we can compute both too).
-}

import Data.Maybe

type Name = String

data Tm
  = Loc Name    -- local var
  | Top Name    -- top-level var
  | App Tm Tm
  | Let Name Tm Tm
  | Lam Name Tm
  deriving Show

data Spine = SNil | SApp Spine ~Val

data Val = VLam Name (Val -> Val) | VLoc Name Spine | VTop Name Spine ~Val

type TopEnv    = [(Name, Val)]
type LocalEnv  = [(Name, Val)]

eval :: TopEnv -> LocalEnv -> Tm -> Val
eval top loc = \case
  Loc x     -> fromJust $ lookup x loc
  Top x     -> VTop x SNil (fromJust $ lookup x top)
  App t u   -> vapp (eval top loc t) (eval top loc u)
  Let x t u -> eval top ((x, eval top loc t) : loc) u
  Lam x t   -> VLam x \u -> eval top ((x, u):loc) t

vapp :: Val -> Val -> Val
vapp (VLam _ t)    ~u = t u
vapp (VLoc x sp)   ~u = VLoc x (SApp sp u)
vapp (VTop x sp t) ~u = VTop x (SApp sp u) (vapp t u)

fresh :: LocalEnv -> Name -> Name
fresh env x = case lookup x env of
  Nothing -> x
  Just{}  -> fresh env (x ++ "'")

type UnfoldTop = Bool

quoteSp :: LocalEnv -> UnfoldTop -> Tm -> Spine -> Tm
quoteSp loc unf h = \case
  SNil      -> h
  SApp sp u -> App (quoteSp loc unf h sp) (quote loc unf u)

quote :: LocalEnv -> UnfoldTop -> Val -> Tm
quote loc unf = \case
  VLoc x sp   -> quoteSp loc unf (Loc x) sp
  VLam x t    -> let x' = fresh loc x
                     v  = VLoc x' SNil
                 in Lam x' (quote ((x, v):loc) unf (t v))
  VTop x sp t -> if unf then quote loc unf t
                        else quoteSp loc unf (Top x) sp

evalTop :: [(Name, Tm)] -> Tm -> Val
evalTop top t = eval topvals [] t where
  topvals = foldl (\top (x, t) -> (x, eval top [] t) : top) [] top

nfTop :: UnfoldTop -> [(Name, Tm)] -> Tm -> Tm
nfTop unf top t = quote [] unf (evalTop top t)

------------------------------------------------------------

($$) = App
infixl 8 $$

top :: [(Name, Tm)]
top = [
    ("zero", Lam "s" $ Lam "z" $ Loc "z")
  , ("suc",  Lam "n" $ Lam "s" $ Lam "z" $
        Loc "s" $$ (Loc "n" $$ Loc "s" $$ Loc "z"))
  , ("add",  Lam "a" $ Lam "b" $ Lam "s" $ Lam "z" $
        Loc "a" $$ Loc "s" $$ (Loc "b" $$ Loc "s" $$ Loc "z"))
  , ("mul",  Lam "a" $ Lam "b" $ Lam "s" $ Lam "z" $
        Loc "a" $$ (Loc "b" $$ Loc "s") $$ Loc "s" $$ Loc "z")
  , ("5", Top "suc" $$ (Top "suc" $$ (Top "suc" $$ (Top "suc" $$
           (Top "suc" $$ Top "zero")))))
  , ("10", Top "add" $$ Top "5" $$ Top "5")
  , ("100", Top "mul" $$ Top "10" $$ Top "10")
  ]

tm = Let "five" (Top "suc" $$ (Top "suc" $$ (Top "suc" $$ (Top "suc" $$
             (Top "suc" $$ Top "zero"))))) $
     Top "mul" $$ Loc "five" $$ Top "5"
