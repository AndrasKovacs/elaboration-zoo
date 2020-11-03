
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
  "usage: elabzoo-pruning [--help|nf|type]",
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
