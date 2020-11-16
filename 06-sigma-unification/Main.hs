
module Main where

import Control.Exception
import System.Environment
import System.Exit

import Common
import Cxt
import Errors
import Evaluation
import Metacontext
import Parser
import Pretty
import Elaboration

import qualified Presyntax as P

--------------------------------------------------------------------------------

helpMsg = unlines [
  "usage: elabzoo-sigma-unification [--help|nf|type]",
  "  --help : display this message",
  "  elab   : read & elaborate expression from stdin",
  "  nf     : read & typecheck expression from stdin, print its normal form and type",
  "  type   : read & typecheck expression from stdin, print its type"]

mainWith :: IO [String] -> IO (P.Tm, String) -> IO ()
mainWith getOpt getRaw = do

  let elab = do
        (t, file) <- getRaw
        infer (emptyCxt (initialPos file)) t
          `catch` \e -> displayError file e >> exitSuccess

  reset
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"]   -> do
      (t, a) <- elab
      putStrLn $ showTm0 $ nf [] t
      putStrLn "  :"
      putStrLn $ showTm0 $ quote 0 a
    ["type"] -> do
      (t, a) <- elab
      putStrLn $ showTm0 $ quote 0 a
    ["elab"] -> do
      (t, a) <- elab
      displayMetas
      putStrLn $ showTm0 t
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)


ex1 :: IO ()
ex1 = main' "elab" $ unlines [

  "-- Examples for unification with ordered metacontext & pruning",
  "--------------------------------------------------------------------------------",

  "-- we use Eq to test unification",
  "let Eq : {A : U} → A → A → U",
  "    = λ {A} x y. (P : A → U) → P x → P y;",
  "let refl : {A : U}{x : A} → Eq {A} x x",
  "    = λ _ px. px;",

  "-- inline type annotation",
  "let the : (A : U) → A → A = λ _ x. x;",

  "-- 1. Solvable non-linear spine: (m a a =? λ x y. y) is solvable, because m's type does not",
  "--    depend on the non-linear arguments, and the rhs also does not depend on them.",
  "let m : (A : U)(B : U) → U → U → U = _;",
  "let test = λ a b. the (Eq (m a a) (λ x y. y)) refl;",

  "-- 2. Unsolvable non-linear spine: m's type depends on non-linear args.",
  "-- let m : (A : U)(B : U) → A → B → B = _;",
  "-- let test = λ a b. the (Eq (m a a) (λ x y. y)) refl;",

  "-- 3. Intersection solution: first & second args pruned from m.",
  "let m : U → U → U → U = _;",
  "let test = λ a b c. the (Eq (m a b a) (m c b c)) refl;",

  "-- 4. Examples requiring pruning",
  "let pr1 = λ f x. f x;",
  "let pr2 = λ f x y. f x y;",
  "let pr3 = λ f. f U;",
  "U"
  ]

ex2 :: IO ()
ex2 = main' "elab" $ unlines [
  "-- we use Eq to test unification",
  "let Eq : {A : U} → A → A → U",
  "    = λ {A} x y. (P : A → U) → P x → P y;",
  "let refl : {A : U}{x : A} → Eq {A} x x",
  "    = λ _ px. px;",

  "-- inline type annotation",
  "let the : (A : U) → A → A = λ _ x. x;",

  "-- singletons",
  "let Sing : {A} → A → U = λ a. (a' : _) × Eq a a';",
  "let sing : {A}(a : A) → Sing a = λ a. (a, refl);",

  "let Top : U = (Top : U) → Top → Top;",
  "let tt  : Top = λ _ x. x;",

  "let Cat =",
  "    (Obj : U)",
  "  × (Mor : Obj → Obj → U)",
  "  × (id : {i} → Mor i i)",
  "  × (comp : {i j k} → Mor j k → Mor i j → Mor i k) × Top;",

  "let Set : Cat = (U, λ A B. A → B,  λ x. x,  λ f g x. f (g x),  tt);",

  "let Functor : Cat → Cat → U = λ C D.",
  "    (Obj : C.Obj → D.Obj)",
  "  × (Mor : {i j} → C.Mor i j → D.Mor (Obj i) (Obj j)) × Top;",

  -- f C.Obj C.Obj  ~ f (C.Obj) (C.Obj)
  -- f x.1 y.1.2    ~ f (x.1) (y.1.2)

  ?0 C (Obj i) (Obj j) =? C.Mor (Obj i) (Obj j)

  "let Id : {C} → Functor C C",
  "  = λ {C}. (λ x. x, λ f. f, tt) ;",

  "let Id : {C} → Functor C C = Id;",  -- Functor injectivity!
                                       -- Functor : Cat → Cat → U
                                       --   is *not* injective up to definitional equality!
                                       --  Functor C D = Functor C' D'  -->   C = C' ∧ D = D'
                                       -- in Agda: records are primitive, record type constructors are injection w.r.t. unification

  -- injectivity/generativity of record type (derived type formers)
  --   (inductive type formers are derived from codes/generic scheme)

  -- my proposal: user injectivity annotations on definitions
  --      (they *only* relevant as convenience feature in elab, don't change conversion)

  -- let [generative] Functor : Cat → Cat → U = ...

  -- in unification :   Functor C D =? Functor C' D' --->  C =? C' ∧ D =? D'            (loses unif solutions!)
  --                    Functor C D =? rhs           --->  unfold Functor and continue  (complete w.r.t conversion)

  -- injectivity analysis: inserts this [generative] tags, whenever a definition is really injective definitionally

  -- ?α (Obj i) (Obj j) =? C.Mor (Obj i) (Obj j)
  -- ?α =? λ x y. C.Mor x y
  -- ?α =? C.Mor
  -- ?α =? λ _ _. C.Mor (Obj i) (Obj j)

  "let Comp : {C D E} → Functor D E → Functor C D → Functor C E",
  "  = λ {C}{D}{E} F G. (λ i. F.Obj (G.Obj i), λ f. F.Mor (G.Mor f), tt);",

  -- "let Comp : {C D E} → Functor D E → Functor C D → Functor C E",
  -- "  = λ F G. Comp F G;",              -- Functor injectivity!

  -- test for eta-expansion:
  "let m : U → U × U = _;",
  "let test = λ x. the (Eq ((m x).₁) x) (refl {_}{x});",

  -- test for currying:
  "let m : U × U → U = _;",
  "let test = λ A B. the (Eq (m (A, B)) A) refl;",

  "U"

  ]


ex3 :: IO ()
ex3 = main' "elab" $ unlines [
  "let Eq : {A : U} → A → A → U",
  "    = λ {A} x y. (P : A → U) → P x → P y;",
  "let refl : {A : U}{x : A} → Eq {A} x x",
  "    = λ _ px. px;",

  "-- inline type annotation",
  "let the : (A : U) → A → A = λ _ x. x;",

  "let m : U -> U * U = _;",
  "λ A. the (Eq (m A).₁ A) (refl {_}{A})"

  ]
