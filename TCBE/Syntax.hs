
module TCBE.Syntax (
    RawTerm(..)
  , TCBE.Syntax.parse
  ) where

import Control.Monad
import Control.Applicative
import Data.Bifunctor
import qualified Data.HashSet as S

import Text.Megaparsec
import Text.Megaparsec.String
import qualified Text.Megaparsec.Lexer as L

import qualified Data.IntMap.Strict as IM

data RawTerm
  = Var !String
  | Lam !String !RawTerm !RawTerm
  | Pi  !String !RawTerm !RawTerm
  | App !RawTerm !RawTerm
  | Star
  deriving Show
    

-- Pretty printing
--------------------------------------------------------------------------------
-- pretty :: Int -> RawTerm -> ShowS
-- pretty prec = go (prec /= 0) where

--   unwords' :: [ShowS] -> ShowS
--   unwords' = foldr1 (\x acc -> x . (' ':) . acc)

--   spine :: RawTerm -> RawTerm -> [RawTerm]
--   spine f x = go f [x] where
--     go (App f y) args = go f (y : args)
--     go t         args = t:args

--   lams :: ShowS -> RawTerm -> ([ShowS], RawTerm)
--   lams i t = first (i:) $ go t where
--     go (Lam i t) = first ((i++):) $ go t
--     go t         = ([], t)

--   go :: Bool -> RawTerm -> ShowS
--   go p (Var i)   = (i++)
--   go p (App f x) = showParen p (unwords' $ map (go True) (spine f x))
--   go p (Lam i t) = showParen p (("λ "++) . unwords' args . (". "++) . go False t')
--     where (args, t') = lams (i++) t

-- instance Show RawTerm where
--   showsPrec = pretty

-- Parsing
--------------------------------------------------------------------------------

lexing :: (Parser () -> b) -> b
lexing =
  ($ (L.space (() <$ spaceChar) (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")))

lexeme = lexing L.lexeme
keywords = S.fromList ["lam", "let", "in", "\\", "λ"]

symbol = try . lexing L.symbol

ident = try $ lexeme $ do
  id <- some alphaNumChar <|> symbol "_"
  guard $ not $ S.member id keywords
  pure id

letBind :: Parser RawTerm
letBind = do
  var  <- symbol "let" *> ident <* symbol ":"
  ty   <- term  <* symbol "="
  def  <- term <* symbol "in"
  body <- term
  pure $ App (Lam var ty  body) def

star = Star <$ symbol "*"
term = star <|> lamPi <|> letBind <|> apps

parens  = between (symbol "(") (symbol ")")
bind    = parens ((,) <$> ident <* symbol ":"  <*> term)

lamPi = do
  (t,ty) <- bind
  (symbol "." *> (Lam t ty <$> term))
    <|> (symbol "->" *> (Pi t ty <$> term))
    

apps = foldl1 App <$> some ((Var <$> ident) <|> star <|> parens term)

parse :: String -> Either String RawTerm
parse = first show . Text.Megaparsec.parse (term <* eof) ""

