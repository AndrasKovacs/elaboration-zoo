
module Pretty (prettyTm, showTm0, displayMetas) where

import Control.Monad
import Data.IORef
import Text.Printf

import qualified Data.IntMap.Strict as IM

import Common
import Evaluation
import Metacontext
import Syntax
import Cxt.Type

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

  goPr :: Int -> [Name] -> [Name] -> Tm -> Pruning -> ShowS
  goPr p topNs ns t pr = goPr' p ns pr (0 :: Int) where
    goPr' p ns pr x = case (ns, pr) of
      ([]      , []           ) -> go p topNs t
      (ns :> n , pr :> Just i ) -> par p appp $ goPr' appp ns pr (x + 1) . (' ':)
                                   . icit i bracket id (case n of "_" -> (("@"++show x)++); n -> (n++))
      (ns :> n , pr :> Nothing) -> goPr' appp ns pr (x + 1)
      _                         -> impossible

  goIx :: [Name] -> Ix -> ShowS
  goIx ns topIx = go ns topIx where
    go []       _ = (("@"++show topIx)++)
    go ("_":ns) 0 = (("@"++show topIx)++)
    go (n:ns)   0 = (n++)
    go (n:ns)   x = go ns (x - 1)

  goCheck :: Int -> [Name] -> CheckVar -> ShowS
  goCheck p ns c = case lookupCheck c of
    Unchecked cxt t a m -> go p ns (appPruning (Meta m) (pruning cxt))
    Checked t           -> go p ns t

  go :: Int -> [Name] -> Tm -> ShowS
  go p ns = \case
    Var x                     -> goIx ns x

    App t u Expl              -> par p appp $ go appp ns t . (' ':) . go atomp ns u
    App t u Impl              -> par p appp $ go appp ns t . (' ':) . bracket (go letp ns u)

    Lam (fresh ns -> x) i t   -> par p letp $ ("λ "++) . lamBind x i . goLam (ns:>x) t where
                                   goLam ns (Lam (fresh ns -> x) i t) =
                                     (' ':) . lamBind x i . goLam (ns:>x) t
                                   goLam ns t =
                                     (". "++) . go letp ns t

    U                         -> ("U"++)

    Pi "_" Expl a b           -> par p pip $ go appp ns a . (" → "++) . go pip (ns:>"_") b

    Pi (fresh ns -> x) i a b  -> par p pip $ piBind ns x i a . goPi (ns:>x) b where
                                   goPi ns (Pi (fresh ns -> x) i a b)
                                     | x /= "_" = piBind ns x i a . goPi (ns:>x) b
                                   goPi ns b = (" → "++) . go pip ns b

    Let (fresh ns -> x) a t u -> par p letp $ ("let "++) . (x++) . (" : "++) . go letp ns a
                                 . ("\n  = "++) . go letp ns t . (";\n\n"++) . go letp (ns:>x) u

    Meta m                    -> (("?"++show m)++)
    AppPruning t pr           -> goPr p ns ns t pr
    PostponedCheck c          -> goCheck p ns c

showTm0 :: Tm -> String
showTm0 t = prettyTm 0 [] t []
-- showTm0 = show

displayMetas :: IO ()
displayMetas = do
  ms <- readIORef mcxt
  forM_ (IM.toList ms) $ \(m, e) -> case e of
    Unsolved _ a -> printf "let ?%s : %s = ?;\n"  (show m) (showTm0 $ quote 0 a)
    Solved v a   -> printf "let ?%s : %s = %s;\n" (show m) (showTm0 $ quote 0 a) (showTm0 $ quote 0 v)
  putStrLn ""
