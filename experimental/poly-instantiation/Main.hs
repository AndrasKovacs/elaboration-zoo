
module Main where

import Text.Printf
import Control.Monad.State.Strict
import Control.Monad.Reader
import System.Exit
import System.Environment

import Types
import Evaluation
import Elaboration

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
  "let List : U -> U",
  "    = \\A. (L : U) -> (A -> L -> L) -> L -> L in",
  "let nil : {A : U} -> List A",
  "    = \\L cons nil. nil in",
  "let cons : {A : U} -> A -> List A -> List A",
  "    = \\{A} x xs L cons nil. cons x (xs L cons nil) in",

  -- "let IdTy : U = {A : U} -> A -> A in",
  "let id : {A : U} -> A -> A = \\x.x in",

  "let ids : List ({A : U} -> A -> A) = cons id (cons id nil) in",

  -- "let css : List ({A B} -> A -> B -> A) = cons (\\x y . x) nil in",
  "U"
  ]
