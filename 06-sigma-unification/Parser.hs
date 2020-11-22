
module Parser (parseString, parseStdin) where

import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Foldable
import Data.Char
import Data.Void
import System.Exit
import Text.Megaparsec

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

import Common
import Presyntax

--------------------------------------------------------------------------------

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Tm -> Parser Tm
withPos ptm = do
  pos <- getSourcePos
  ptm >>= \case
    t@SrcPos{} -> pure t
    t          -> pure (SrcPos (coerce pos) t)

lexeme     = L.lexeme ws
symbol s   = lexeme (C.string s)
char c     = lexeme (C.char c)
parens p   = char '(' *> p <* char ')'
braces p   = char '{' *> p <* char '}'
pArrow     = symbol "→" <|> symbol "->"
pProd      = char '*' <|> char '×'
pBind      = pIdent <|> symbol "_"

keyword :: String -> Bool
keyword x = x == "let" || x == "in" || x == "λ" || x == "U"

pIdent :: Parser Name
pIdent = try $ do
  x  <- C.letterChar
  xs <- takeWhileP Nothing (\c -> isAlphaNum c || c == '\'')
  guard (not (keyword (x:xs)))
  (x:xs) <$ ws

pAtom :: Parser Tm
pAtom  =
      withPos (    (Var  <$> pIdent)
               <|> (U    <$  char 'U')
               <|> (Hole <$  char '_'))
  <|> parens pTm

goProj :: Tm -> Parser Tm
goProj t =
  (char '.' *>
    (     ((char '₁' <|> char '1') *> goProj (Proj1 t))
      <|> ((char '₂' <|> char '2') *> goProj (Proj2 t))
      <|> do {x <- pIdent; goProj (ProjField t x)}
    )
  )
  <|> pure t

pProjExp :: Parser Tm
pProjExp = goProj =<< pAtom

pArg :: Parser (Either Name Icit, Tm)
pArg =  (try $ braces $ do {x <- pIdent; char '='; t <- pTm; pure (Left x, t)})
    <|> ((Right Impl,) <$> (char '{' *> pTm <* char '}'))
    <|> ((Right Expl,) <$> pProjExp)

pApp :: Parser Tm
pApp = do
  h <- pProjExp
  args <- many pArg
  pure $ foldl' (\t (i, u) -> App t u i) h args

pSigmaExp :: Parser Tm
pSigmaExp = do
  optional (try (char '(' *> pBind <* char ':')) >>= \case
    Nothing -> do
      t <- pApp
      (Sg "_" t <$> (pProd *> pSigmaExp)) <|> pure t
    Just x -> do
      a <- pTm
      char ')'
      pProd
      b <- pSigmaExp
      pure $ Sg x a b

pLamBinder :: Parser (Name, Maybe Tm, Either Name Icit)
pLamBinder =
      parens ((,,Right Expl) <$> pBind <*> optional (char ':' *> pTm))
  <|> ((,Nothing,Right Expl) <$> pBind)
  <|> try ((,,Right Impl) <$> (char '{' *> pBind) <*> (optional (char ':' *> pTm) <* char '}'))
  <|> braces (do {x <- pIdent; char '='; y <- pBind; ann <- optional (char ':' *> pTm); pure (y, ann, Left x)})

pLam :: Parser Tm
pLam = do
  char 'λ' <|> char '\\'
  xs <- some pLamBinder
  char '.'
  t <- pLamLet
  pure $ foldr (\(x, ann, ni) u -> Lam x ann ni u) t xs

pPiBinder :: Parser ([Name], Tm, Icit)
pPiBinder =
      braces ((,,Impl) <$> some pBind
                       <*> ((char ':' *> pTm) <|> pure Hole))
  <|> parens ((,,Expl) <$> some pBind
                       <*> (char ':' *> pTm))

pPiExp :: Parser Tm
pPiExp = do
  optional (try (some pPiBinder)) >>= \case

    Nothing -> do
      t <- pSigmaExp
      (pArrow *> (Pi "_" Expl t <$> pPiExp)) <|> pure t

    Just bs -> do
      case bs of
        [([x], a, Expl)] ->
              (Pi x Expl a <$> (pArrow *> pPiExp))
          <|> (do dom <- Sg x a <$> (pProd *> pSigmaExp)
                  (Pi "_" Expl dom <$> (pArrow *> pPiExp)) <|> pure dom)

        dom -> do
          pArrow
          b <- pPiExp
          pure $! foldr' (\(xs, a, i) t -> foldr' (\x -> Pi x i a) t xs) b dom

pLet :: Parser Tm
pLet = do
  symbol "let"
  x <- pIdent
  ann <- optional (char ':' *> pTm)
  char '='
  t <- pTm
  symbol ";"
  u <- pLamLet
  pure $ Let x (maybe Hole id ann) t u

pLamLet :: Parser Tm
pLamLet = withPos (pLam <|> pLet <|> pPiExp)

pTm :: Parser Tm
pTm = withPos $ do
  t <- pLamLet
  (Pair t <$> (char ',' *> pTm)) <|> pure t

pSrc :: Parser Tm
pSrc = ws *> pTm <* eof

parseString :: String -> IO Tm
parseString src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStdin :: IO (Tm, String)
parseStdin = do
  src <- getContents
  t <- parseString src
  pure (t, src)
