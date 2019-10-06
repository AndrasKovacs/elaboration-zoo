
module Main where

import Text.Printf
import Control.Monad.State.Strict
import Control.Monad.Reader
import System.Exit
import System.Environment

import Types
import Evaluation
import Elaboration
import Parser

helpMsg = unlines [
  "usage: holes [--help|nf|type]",
  "  --help : display this message",
  "  elab   : read & elaborate expression from stdin",
  "  nf     : read & elaborate expression from stdin, print its normal form",
  "  type   : read & elaborate expression from stdin, print its type"]

displayError :: String -> Err -> IO ()
displayError file (Err msg (SourcePos path (unPos -> linum) (unPos -> colnum))) = do
  let lnum = show linum
      lpad = map (const ' ') lnum
  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n\n" (show msg)

elabCxt0 :: ElabCxt
elabCxt0 = ElabCxt [] [] [] (initialPos "(stdin)")

st0 :: St
st0 = St 0 mempty

runElab0 :: ElabM a -> Either Err a
runElab0 ma = evalStateT (runReaderT ma elabCxt0) st0

mainWith :: IO [String] -> IO (Raw, String) -> IO ()
mainWith getOpt getTm = do

  let elab :: IO (Tm, Tm, Tm)
      elab = do
        (t, src) <- getTm
        let res = runElab0 $ do
              (t, a) <- infer MIYes t
              t      <- zonkM t
              -- traceShowM "inferred"
              nt     <- nfM t
              na     <- quoteM a
              pure (t, nt, na)
        case res of
          Left err -> displayError src err >> exitSuccess
          Right x  -> pure x

  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ["nf"] -> do
      (t, nt, na) <- elab
      print nt
    ["type"] -> do
      (t, nt, na) <- elab
      print na
    ["elab"] -> do
      (t, nt, na) <- elab
      print t
    _ -> putStrLn helpMsg

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)


ex1 = main' "elab" $ unlines [
  "let the : (A : U) → A → A = \\A x.x in",
  "let id : {A} → A → A = λ x. x in",
  "let choose : {A} → A → A → A = λ x y. x in",

  "let Nat : U",
  "    = (N : U) -> (N -> N) -> N -> N in",
  "let zero : Nat = λ _ s z. z in",
  "let inc : Nat → Nat = λ n _ s z. s (n _ s z) in",
  "let mul : Nat -> Nat -> Nat",
  "    = \\a b N s z. a _ (b _ s) z in",
  "let ten : Nat",
  "    = \\N s z. s (s (s (s (s (s (s (s (s (s z))))))))) in",
  "let hundred = mul ten ten in",

  "let List : U -> U",
  "    = \\A. (L : _) -> (A -> L -> L) -> L -> L in",
  "let nil : {A} -> List A",
  "    = \\cons L nil. nil in",
  "let cons : {A} -> A -> List A -> List A",
  "    = \\{A} x xs L cons nil. cons x (xs _ cons nil) in",
  "let append : {A} → List A → List A → List A",
  "    = λ xs ys L cons nil. xs _ cons (ys _ cons nil) in",
  "let map : {A B} → (A → B) → List A → List B = λ f as _ c n. as _ (λ a. c (f a)) n in",
  "let head : {A} → List A → A = λ as. _ in",

  "let single : {A} → A → List A = λ a L cons nil. cons a nil in",
  "let length : {A} → List A → Nat = λ as _ s z. as _ (λ _.s) z in",

  -- pruning plz
  -- "let List : U -> U",
  -- "    = \\A. {L} -> (A -> L -> L) -> L -> L in",
  -- "let nil : {A} -> List A",
  -- "    = \\cons nil. nil in",
  -- "let cons : {A} -> A -> List A -> List A",
  -- "    = \\{A} x xs cons nil. cons x (xs cons nil) in",
  -- "let append : {A} → List A → List A → List A",
  -- "    = λ xs ys cons nil. xs cons (ys cons nil) in",

  "let Pair = λ A B. (P : U) → (A → B → P) → P in",
  "let pair : {A B} → A → B → Pair A B = λ x y _ p. p x y in",
  "let fst : {A B} → Pair A B → A = λ p. p _ (λ x y. x) in",
  "let snd : {A B} → Pair A B → B = λ p. p _ (λ x y. y) in",

  "let Bool : U",
  "    = {B} -> B -> B -> B in",
  "let true : Bool",
  "    = \\t f. t in",
  "let false : Bool",
  "    = \\t f. f in",
  "let not : Bool → Bool",
  "   = λ b t f. b f t in",

  "let poly : ({A} → A → A) → Pair Nat Bool = λ f. pair (f zero) (f true) in",
  "let auto : ({A} → A → A) → ({A} → A → A) = id in",
  "let app  : {A B} → (A → B) → A → B = λ f a. f a in",
  "let revapp : {A B} → A → (A → B) → B = λ a f. f a in",

  "let IdTy : U = {A} -> A -> A in",
  "let id2 = λ x. x in",
  "let ids : List IdTy = cons id2 (cons (λx.x) nil) in",

  "let l1 = cons true (cons false nil) in",
  "let l2 : List Bool = nil in",
  "let l3 = append l1 l2 in",

  "let ST : U → U → U = λ A B. A → B in",
  "let runST : {A} → ({S} → ST S A) → A = _ in",
  "let argST : {S} → ST S Nat = _ in",

  "let const2 = λ x y. x in",
  "let l = cons const2 (nil {{A B} → A → B → A}) in",

  "let t1 = choose nil ids in",
  -- "let t2 = λ (x : IdTy). x x in",  -- pruning
  "let t3 = poly id in",
  "let t4 = id poly (λ x. x) in",

  -- "let t5 = λ xs. poly (head xs) in", -- pruning
  "let t6 = length ids in",
  "let t7 = append (single inc) (single id) in",
  "let t8 : ({A} → List A → List A → A) → _ = λ g. g (single id) ids in",
  "let t9 = map poly (single id) in",
  "let t10 = map head (single ids) in",

  "let t11 = app poly id in",
  "let t12 = revapp id poly in",
  "let t13 = app runST argST in",
  "let t14 : ({A} → A → {B} → B → B) → _ = λ r. r (λ x y. y) in",

  "length l3"
  ]

ex2 = main' "elab" $ unlines [
  "let id : {A} -> A -> A = \\x. x in",

  -- by default metas are inserted for implicit arguments, but
  -- (!) can be used to stop insertion at any point. The (id!) expression
  --  has a polymorphic type, {A} → A → A
  "let id2 : {A} → A → A = id id in",

  "let const : {A B} -> A -> B -> A",
  "    = \\x y. x in",

  -- definition types can be omitted
  "let constTy = {A B} → A → B → A in",

  -- explicit id function, used for annotation as in Idris
  "let the : (A : _) -> A -> A = \\_ x. x in",

  -- implicit application follows Agda convention.
  -- "let namedArgTest = const {B = U} U in",
  "let namedArgTest2 = the constTy (λ x y. x) {B = U} U in",

  -- bool
  "let Bool : U",
  "    = (B : _) -> B -> B -> B in",
  "let true : Bool",
  "    = \\B t f. t in",
  "let false : Bool",
  "    = \\B t f. f in",
  "let not : Bool -> Bool",
  "    = \\b B t f. b B f t in",

  -- lists
  "let List : U -> U",
  "    = \\A. (L : _) -> (A -> L -> L) -> L -> L in",
  "let nil : {A} -> List A",
  "    = \\L cons nil. nil in",
  "let cons : {A} -> A -> List A -> List A",
  "    = \\x xs L cons nil. cons x (xs L cons nil) in",
  "let map : {A B} -> (A -> B) -> List A -> List B",
  "    = \\{A}{B} f xs L c n. xs L (\\a. c (f a)) n in",
  "let list1 : List Bool",
  "    = cons true (cons false (cons true nil)) in",

  -- using ! when mapping over lists
  -- idlist has type "List ({A} -> A -> A)"
  "let idlist = map (const (id!)) list1 in",

  -- dependent function composition
  "let comp : {A}{B : A -> U}{C : {a} -> B a -> U}",
  "           (f : {a}(b : B a) -> C b)",
  "           (g : (a : A) -> B a)",
  "           (a : A)",
  "           -> C (g a)",
  "    = \\f g a. f (g a) in",

  "let compExample = comp (cons true) (cons false) nil in",

  -- nat
  "let Nat : U",
  "    = (N : U) -> (N -> N) -> N -> N in",
  "let mul : Nat -> Nat -> Nat",
  "    = \\a b N s z. a _ (b _ s) z in",
  "let ten : Nat",
  "    = \\N s z. s (s (s (s (s (s (s (s (s (s z))))))))) in",
  "let hundred = mul ten ten in",

  -- Leibniz equality
  "let Eq : {A} -> A -> A -> U",
  "    = \\{A} x y. (P : A -> U) -> P x -> P y in",
  "let refl : {A}{x : A} -> Eq x x",
  "    = \\_ px. px in",

  "the (Eq (mul ten ten) hundred) refl"
  ]
