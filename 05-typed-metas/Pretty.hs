
module Pretty (prettyTm, showTm0, displayMetas) where

import Control.Monad
import Data.IORef
import Text.Printf
import Data.List (sortBy)
import Data.Ord (comparing)

import qualified Data.IntMap.Strict as IM

import Common
import Evaluation
import Metacontext
import Syntax

--------------------------------------------------------------------------------

fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x | elem x ns = fresh ns (x ++ "'")
           | otherwise = x

-- printing precedences
atomp = 3  :: Int -- U, var
appp  = 2  :: Int -- application
pip   = 1  :: Int -- pi
letp  = 0  :: Int -- let, lambda

-- Wrap in parens if expression precedence is lower than
-- enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTm :: Int -> [Name] -> Tm -> ShowS
prettyTm prec = go prec where

  bracket :: ShowS -> ShowS
  bracket ss = ('{':).ss.('}':)

  piBind ns x Expl a = showParen True ((x++) . (" : "++) . go letp ns a)
  piBind ns x Impl a = bracket        ((x++) . (" : "++) . go letp ns a)

  lamBind x Impl = bracket (x++)
  lamBind x Expl = (x++)

  goMCl :: Int -> [Name] -> MetaVar -> MetaClosure -> ShowS
  goMCl p ns m mcl = case (ns, mcl) of
    ([]      , Nil             ) -> (("?"++show m)++)
    (ns :> n , Bind mcl _ _    ) -> par p appp $ goMCl appp ns m mcl . (' ':) . (n++)
    (ns :> n , Define mcl _ _ _) -> goMCl appp ns m mcl
    _                            -> error "impossible"

  go :: Int -> [Name] -> Tm -> ShowS
  go p ns = \case
    Var (Ix x)                -> ((ns !! x)++)

    App t u Expl              -> par p appp $ go appp ns t . (' ':) . go atomp ns u
    App t u Impl              -> par p appp $ go appp ns t . (' ':) . bracket (go letp ns u)

    Lam (fresh ns -> x) i t   -> par p letp $ ("λ "++) . lamBind x i . goLam (ns:>x) t where
                                   goLam ns (Lam x i t) = (' ':) . lamBind x i . goLam (ns:>x) t
                                   goLam ns t           = (". "++) . go letp ns t

    U                         -> ("U"++)

    Pi "_" Expl a b           -> par p pip $ go appp ns a . (" → "++) . go pip (ns:>"_") b

    Pi (fresh ns -> x) i a b  -> par p pip $ piBind ns x i a . goPi (ns:>x) b where
                                   goPi ns (Pi x i a b) | x /= "_" = piBind ns x i a . goPi (ns:>x) b
                                   goPi ns b = (" → "++) . go pip ns b

    Let (fresh ns -> x) a t u -> par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
                                 . ("\n  = "++) . go letp ns t . (";\n\n"++) . go letp (ns:>x) u

    Meta m                    -> (("?"++show m)++)
    InsertedMeta m mcl        -> goMCl p ns m mcl

showTm0 :: Tm -> String
showTm0 t = prettyTm 0 [] t []
-- showTm0 = show

displayMetas :: IO ()
displayMetas = do
  ms <- readIORef mcxt
  forM_ (sortBy (comparing (order . link . snd)) $ IM.toList ms) $ \(m, e) -> case e of
    Unsolved _ a -> printf "let ?%s : %s = ?;\n"  (show m) (showTm0 $ quote 0 a)
    Solved _ v a -> printf "let ?%s : %s = %s;\n" (show m) (showTm0 $ quote 0 a) (showTm0 $ quote 0 v)
  putStrLn ""
