
module Parser (
    parseString
  , parseStdin
  ) where

import Control.Monad
import Data.Char
import Data.Void
import System.Exit
import Text.Megaparsec

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

import Types

--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Raw -> Parser Raw
withPos p = RSrcPos <$> getSourcePos <*> p

lexeme     = L.lexeme ws
symbol s   = lexeme (C.string s)
char c     = lexeme (C.char c)
parens p   = char '(' *> p <* char ')'
braces p   = char '{' *> p <* char '}'
pArrow     = symbol "→" <|> symbol "->"
pBind      = pIdent <|> symbol "_"

keyword :: String -> Bool
keyword x = x == "let" || x == "in" || x == "λ" || x == "U"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pAtom :: Parser Raw
pAtom  =
      withPos (    (RVar <$> pIdent)
               <|> (RU <$ char 'U')
               <|> (RHole <$ char '_'))
  <|> parens pTm

pArg :: Parser (Maybe (Either Name Icit, Raw))
pArg = (Nothing <$ char '!')
  <|>  (Just <$> (
           (try $ braces $ do {x <- pIdent; char '='; t <- pTm; pure (Left x, t)})
       <|> ((Right Impl,) <$> (char '{' *> pTm <* char '}'))
       <|> ((Right Expl,) <$> pAtom)))

pSpine :: Parser Raw
pSpine = do
  h <- pAtom
  args <- many pArg
  pure $ foldl
    (\t -> \case Nothing     -> RStopInsertion t
                 Just (i, u) -> RApp t u i)
    h args

pLamBinder :: Parser (Name, Maybe Raw, Either Name Icit)
pLamBinder =
      ((,Nothing,Right Expl) <$> pBind)
  <|> parens ((,,Right Expl) <$> pBind <*> optional (char ':' *> pTm))
  <|> try (braces ((,,Right Impl) <$> pBind <*> optional (char ':' *> pTm)))
  <|> braces (do {x <- pIdent; char '='; y <- pBind; pure (y, Nothing, Left x)})

pLam :: Parser Raw
pLam = do
  char 'λ' <|> char '\\'
  xs <- some pLamBinder
  char '.'
  t <- pTm
  pure $ foldr (\(x, a, ni) t -> RLam x a ni t) t xs

pPiBinder :: Parser ([Name], Raw, Icit)
pPiBinder =
      braces ((,,Impl) <$> some pBind
                       <*> ((char ':' *> pTm) <|> pure RHole))
  <|> parens ((,,Expl) <$> some pBind
                       <*> (char ':' *> pTm))
pPi :: Parser Raw
pPi = do
  dom <- some pPiBinder
  pArrow
  cod <- pTm
  pure $ foldr (\(xs, a, i) t -> foldr (\x -> RPi x i a) t xs) cod dom

pFunOrSpine :: Parser Raw
pFunOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _  -> RPi "_" Expl sp <$> pTm

pLet :: Parser Raw
pLet = do
  symbol "let"
  x <- pIdent
  ann <- optional (char ':' *> pTm)
  char '='
  t <- pTm
  symbol "in"
  u <- pTm
  pure $ RLet x (maybe RHole id ann) t u

pTm :: Parser Raw
pTm = withPos (pLam <|> pLet <|> try pPi <|> pFunOrSpine)

pSrc :: Parser Raw
pSrc = ws *> pTm <* eof

parseString :: String -> IO Raw
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStdin :: IO (Raw, String)
parseStdin = do
  src <- getContents
  t <- parseString src
  pure (t, src)
