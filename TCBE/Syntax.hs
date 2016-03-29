
{-# LANGUAGE RecursiveDo, PatternGuards, OverloadedStrings #-}

module TCBE.Syntax (RawTerm(..)) where

import Prelude hiding (lex)
import Control.Applicative

import qualified Text.Earley as E (symbol, word)
import Text.Earley hiding (symbol, word)

import Data.Char
import Data.String

data Token = TStar | TId String | TOpen | TClose | TColon | TDot | TArr
  deriving (Eq, Show)

instance IsString Token where
  fromString = \case
    "*"  -> TStar
    "->" -> TArr
    "("  -> TOpen
    ")"  -> TClose
    ":"  -> TColon
    "."  -> TDot

data RawTerm
  = Var !String
  | Lam !String !RawTerm !RawTerm
  | ILam !String !RawTerm
  | Pi  !String !RawTerm !RawTerm
  | App !RawTerm !RawTerm
  | Arr !RawTerm !RawTerm
  | Ann !RawTerm !RawTerm
  | Star
  deriving Show

instance IsString RawTerm where
  fromString = Var
      
-- lex :: String -> [Token]
-- lex s = case dropWhile isSpace s of
--   '(':s -> TOpen  : lex s
--   ')':s -> TClose : lex s
--   ':':s -> TColon : lex s
--   '*':s -> TStar  : lex s
--   '.':s -> TDot   : lex s
--   s | ("->", s') <- splitAt 2 s -> TArr : lex s'
--   s | (i@(_:_) , s') <- span isAlpha s -> TId i : lex s'
--   [] -> []
--   _  -> error "lexical error"





test = mdo  
  spaces <- rule $ (E.symbol ' ' *> spaces) <|> pure ()

  let lexeme p = p <* spaces
      symbol   = lexeme . E.symbol
      word     = lexeme . E.word
      parens p = symbol '(' *> p <* symbol ')'
      
  ident <- mdo
    go <- rule $ ((:) <$> satisfy isAlpha <*> go) <|> ((:[]) <$> satisfy isAlpha)
    pure $ lexeme go

  var   <- rule $ Var <$> ident    
  star  <- rule $ Star <$ symbol '*'

  -- arr   <- rule $ Arr <$> pterm <*> (word "->" *> term)
  -- pi    <- rule $ parens (Pi  <$> ident <* symbol ':' <*> term) <*> (word "->" *> term)
  -- lam   <- rule $ parens (Lam <$> ident <* symbol ':' <*> term) <*> (word "." *> term)

  -- pi    <- rule $ parens (Pi <$> ident <* symbol ':' <*> term) <*> (word "->" *> term)


  term  <- rule $ var <|> star  
  arr   <- rule $ Arr  <$> term  <*> (word "->" *> (arr <|> var <|> star))
  ilam  <- rule $ ILam <$> ident <*> (word "." *> (ilam <|> var <|> star <|> arr))

  -- pterm  <- rule $ star <|> var <|> parens term  
  -- npterm <- rule $ star <|> var <|> arr <|> pi <|> lam <|> ilam
  
  -- term   <- rule $ (App <$> term <*> pterm) <|> npterm
  
  pure ilam
  



-- term :: Grammar r (Prod r Token Token RawTerm)
-- term = mdo
--   star  <- rule $ Star <$ symbol "*"
  
--   ident <- rule $ (\(TId i) -> Var i) <$> satisfy (\case TId{} -> True; _ -> False)

--   pterm <- rule $ star <|> ident <|> parens term

--   arr   <- rule $ Arr <$> pterm <*> (symbol "->" *> term)
--   -- pi    <- rule $ Pi  <$> 

--   term  <- rule $ star <|> ident <|> arr


--   pure term
                                                      
  -- test <- rule $ star <|> (App <$> test <*> star) 
  -- pure test  

-- term = mdo
--   star <- rule $ symbol Star
  
  

-- star = rule $ satisfy (=="*")
-- ident = 
  






-- import qualified Data.HashSet as HS

-- type Noun      = String
-- type Verb      = String
-- type Adjective = String

-- nouns, verbs, adjectives :: HS.HashSet String
-- nouns      = HS.fromList ["parsers", "sentences", "grammars"]
-- verbs      = HS.fromList ["parse", "munch", "annihilate", "confuse", "use"]
-- adjectives = HS.fromList ["many", "great", "long", "confusing"]


-- data Sentence = Sentence NounPhrase VerbPhrase
--   deriving Show
-- data NounPhrase = NounPhrase Adjective NounPhrase
--                 | Noun Noun
--   deriving Show
-- data VerbPhrase = VerbPhrase Verb NounPhrase
--                 | Verb Verb
--   deriving Show

-- sentence :: Grammar r (Prod r String String Sentence)
-- sentence = mdo
--   noun       <- rule $ satisfy (`HS.member` nouns)      <?> "noun"
--   verb       <- rule $ satisfy (`HS.member` verbs)      <?> "verb"
--   adjective  <- rule $ satisfy (`HS.member` adjectives) <?> "adjective"
--   nounPhrase <- rule $  NounPhrase <$> adjective <*> nounPhrase
--                     <|> Noun <$> noun
--                     <?> "noun phrase"
--   verbPhrase <- rule $  VerbPhrase <$> verb <*> nounPhrase
--                     <|> Verb <$> verb
--                     <?> "verb phrase"
--   return $ Sentence <$> nounPhrase <*> verbPhrase <?> "sentence"

-- main :: IO ()
-- main = do
--   let p = fullParses (parser sentence) . words
--   print $ p "parsers use grammars"
--   print $ p "parsers munch long sentences"
--   print $ p "many great sentences confuse parsers"
--   print $ p "parsers use use"
--   print $ p "grammars many great confusing"







-- {-# language RecursiveDo #-}

-- module TCBE.Syntax (
--     RawTerm(..)
-- --  , TCBE.Syntax.parse
--   ) where

-- import Prelude hiding (pi)
-- import Data.String

-- import Control.Applicative
-- import Text.Earley





-- data RawTerm
--   = Var !String
--   | Lam !String !RawTerm !RawTerm
--   | ILam !String !RawTerm
--   | Pi  !String !RawTerm !RawTerm
--   | App !RawTerm !RawTerm
--   | Arr !RawTerm !RawTerm
--   | Ann !RawTerm !RawTerm
--   | Star
--   deriving Show

-- instance IsString RawTerm where
--   fromString = Var


  











-- Parsing
--------------------------------------------------------------------------------

-- lexing :: (Parser () -> b) -> b
-- lexing =
--   ($ (L.space (() <$ spaceChar) (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")))

-- lexeme = lexing L.lexeme
-- keywords = S.fromList ["let", "in"]

-- symbol = try . lexing L.symbol
-- parens = between (symbol "(") (symbol ")")

-- ident = try $ lexeme $ do
--   id <- some alphaNumChar <|> symbol "_"
--   guard $ not $ S.member id keywords
--   pure id

-- star = Star <$ symbol "*"



-- term p =
--       (Arr <$> term True <*> (symbol "->" *> term False))  
--   <|> star
--   <|> (Var <$> ident)

-- term p = foldl1 App <$> some (star <|> (Var <$> ident) <|> par bound <|> par (term (not p)))
--   where par = if p then parens else id

-- bound = arr <|> pi <|> lam <|> ilam

-- arr  = Arr <$> term True <*> (symbol "->" *> term False)
-- pi   = parens (Pi <$> ident <* symbol ":" <*> term False) <*> (symbol "->" *> term False)
-- lam  = parens (Lam <$> ident <* symbol ":" <*> term False) <*> (symbol "." *> term False)
-- ilam = ILam <$> ident <*> (symbol "." *> term False)


-- letBind :: Parser RawTerm
-- letBind = do
--   var  <- symbol "let" *> ident <* symbol ":"
--   ty   <- term  <* symbol "="
--   def  <- term <* symbol "in"
--   body <- term
--   pure $ App (Lam var ty body) def

-- term = star <|> lamPi <|> letBind <|> apps

-- parens  = between (symbol "(") (symbol ")")
-- bind    = parens ((,) <$> ident <* symbol ":"  <*> term)

-- lamPi = do
--   (t,ty) <- bind 
--   (symbol "." *> (Lam t ty <$> term))
--     <|> (symbol "->" *> (Pi t ty <$> term))    

-- apps = foldl1 App <$> some ((Var <$> ident) <|> star <|> parens term)

-- parse :: String -> Either String RawTerm
-- parse = first show . Text.Megaparsec.parse (term <* eof) ""

