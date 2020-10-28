
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
  "usage: elabzoo-implicit-args [--help|nf|type]",
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


ex1 = main' "elab" $ unlines [
  -- "let Eq : {A : U} → A → A → U",
  -- "    = λ {A} x y. (P : A → U) → P x → P y;",
  -- "let refl : {A : U}{x : A} → Eq {A} x x",
  -- "    = λ _ px. px;",

  -- "let a : U = _;",
  -- "let b : U = _;",
  -- "let c : U = _;",
  -- "let d : U = _;",

  -- "let p : Eq {U} a b = refl {U}{b};",
  -- "let p : Eq {U} b c = refl {U}{c};",
  -- "let p : Eq {U} c d = refl {U}{d};",
  -- -- "let p : Eq a U = refl;",
  -- "U"

  "let id : {A} → A → A = λ x. x;",
  "let id2 : {A} → A → A = λ x. id x;",
  "let const : {A B} → A → B → A",
  "    = λ x y. x;",
  "let constTy = {A B} → A → B → A;",
  "",
  "let the : (A : _) → A → A = λ _ x. x;",
  "",
  "let namedArgTest = const {B = U} U;",
  "let namedArgTest2 = the constTy (λ x y. x) {B = U} U;",
  "",
  "let Bool : U",
  "    = (B : _) → B → B → B;",
  "let true : Bool",
  "    = λ B t f. t;",
  "let false : Bool",
  "    = λ B t f. f;",
  "let not : Bool → Bool",
  "    = λ b B t f. b B f t;",
  "let List : U → U",
  "    = λ A. (L : _) → (A → L → L) → L → L;",
  "let nil : {A} → List A",
  "    = λ L cons nil. nil;",
  "let cons : {A} → A → List A → List A",
  "    = λ x xs L cons nil. cons x (xs L cons nil);",
  "let map : {A B} → (A → B) → List A → List B",
  "    = λ {A}{B} f xs L c n. xs L (λa. c (f a)) n;",
  "let list1 : List Bool",
  "    = cons true (cons false (cons true nil));",
  "",
  "-- dependent function composition",
  "let comp : {A}{B : A → U}{C : {a} → B a → U}",
  "           (f : {a}(b : B a) → C b)",
  "           (g : (a : A) → B a)",
  "           (a : A)",
  "           → C (g a)",
  "    = λ f g a. f (g a);",
  "",
  "let compExample = comp (cons true) (cons false) nil;",
  "",
  "let Nat : U",
  "    = (N : U) → (N → N) → N → N;",
  "let mul : Nat → Nat → Nat",
  "    = λ a b N s z. a _ (b _ s) z;",
  "let ten : Nat",
  "    = λ N s z. s (s (s (s (s (s (s (s (s (s z)))))))));",
  "let hundred = mul ten ten;",
  "",
  "let Eq : {A} → A → A → U",
  "    = λ {A} x y. (P : A → U) → P x → P y;",
  "let refl : {A}{x : A} → Eq x x",
  "    = λ_ px. px;",
  "",
  "let sym : {A x y} → Eq {A} x y → Eq y x",
  "  = λ {A}{x}{y} p. p (λ y. Eq y x) refl;",
  "",
  "the (Eq (mul ten ten) hundred) refl  "
  ]
