{-#LANGUAGE PackageImports, StandaloneDeriving, DeriveDataTypeable, FlexibleContexts#-}
module Parser where
import Syntax

import Text.Parsec hiding (ParseError,Empty, State)
import qualified Text.Parsec as P
import Text.Parsec.Language
import Text.Parsec.Char
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import qualified Text.Parsec.Token as Token
import Text.Parsec.Indent
import Control.Applicative hiding ((<|>),many, optional, Const)
import Control.Monad.State.Lazy
import "mtl" Control.Monad.Identity
import Control.Exception(Exception)

import qualified Data.IntMap as IM
import Data.Typeable
import Data.Char
import Data.List

parseModule :: String -> String -> Either P.ParseError Module
parseModule srcName cnts =
 runIndent $ runParserT gModule () srcName cnts

parseExp :: String -> Either P.ParseError Exp
parseExp s = runIndent $ runParserT (try (parens term) <|> term) () [] s

-- parseExps :: String -> Either P.ParseError [Exp]
-- parseExps s = runIndent [] $ runParserT (many1 (try (parens term) <|> term)) () [] s

type Parser a = IndentParser String () a

-- deriving instance Typeable P.ParseError
-- instance Exception P.ParseError 

-- parse module
gModule :: Parser Module
gModule = do
  bs <- many (try ruleDecl)
  ds <- many (try decl)
  qs <- many (try proof)
  sts <- many (try step)
  eof
  return $ Mod bs qs ds sts


decl :: Parser (Name, Exp, Exp)
decl = do
  n <- identifier
  when (isUpper (head n)) $ parserFail "expected to begin with lowercase letter"
  reservedOp ":"
  formula <- term
  n' <- identifier
  when (n /= n') $ parserFail ("unexpected definition" ++ n')
  vs <- many var
  reservedOp "="
  b <- term
  let b' = convert b
      bb = expand b'
      exp = foldr (\ x y -> Lambda x Nothing y) bb (map (\(Var x) -> x) vs)
  return $ (n, formula, exp)    
      
  
proof :: Parser ((Name, Exp), [Tactic])
proof = do
  reserved "lemma"
  n <- identifier
  reservedOp ":"
  t <- term
  reserved "proof"
  ts <- many tactic
  reserved "qed"
  return ((n, t), ts)

tactic :: Parser Tactic
tactic = tacIntros <|> tacApply <|> tacUse <|> tacCoind <|> tacApplyH

tacIntros = do
  reserved "intros"
  ns <- many1 identifier
  return $ Intros ns

tacCoind = reserved "coind" >> return Coind

tacUse = do
  reserved "use"
  n <- identifier
  ts <- optionMaybe term
  case ts of
    Nothing -> return $ Use n []
    Just ts' -> return $ Use n (flatten ts')

tacApply = do
  reserved "apply"
  n <- identifier
  ts <- optionMaybe term
  case ts of
    Nothing -> return $ Apply n []
    Just ts' -> return $ Apply n (flatten ts')

tacApplyH = do
  reserved "applyh"
  n <- identifier
  return $ ApplyH n 
  
step :: Parser (Name, Int)
step = do
  reserved "step"
  n <- identifier
  num <- integer
  return (n, fromIntegral num)

    
ruleDecl :: Parser (Name, Exp)
ruleDecl = do
  (Const c) <- con 
  reservedOp ":"
  t <- term
  return $ (c, t)
  
var :: Parser Exp
var = do
  n <- identifier
  when (isUpper (head n)) $ parserFail "expected to begin with lowercase letter"
  return (Var n)

con :: Parser Exp
con = do
  n <- identifier  
  when (isLower (head n)) $ parserFail "expected to begin with uppercase letter"
  return (Const n)

eigen :: Parser Exp
eigen = do
  n <- brackets identifier  
  when (isUpper (head n)) $ parserFail "expected to begin with lowercase letter"
  return (Const n)

-- parser for FType--
-- rule :: Parser Exp
-- rule = do
--   t1 <- term
--   reserved "->"
--   t2 <- term
--   return $ Arrow t1 t2

term :: Parser Exp
term = buildExpressionParser typeOpTable base

-- base :: Parser Exp
-- base = try compound <|> try forall <|> parens ftype

-- binOp :: Assoc -> String -> (a -> a -> a) -> Operator String u (State SourcePos) a
binOp assoc op f = Infix (reservedOp op >> return f) assoc

-- typeOpTable :: [[Operator String u (State SourcePos) Exp]]
typeOpTable = [[binOp AssocRight "=>" Imply, binOp AssocRight "<=" Arrow]]

-- parse type expression
base :: Parser Exp
base = forall <|> lambda <|> try compound <|> try (parens term)

lambda = do
  reservedOp "\\"
  as <- many1 var
  reservedOp "."
  p <- term
  return $ foldr (\ x y -> Abs x y) p (map (\(Var x) -> x) as)

forall = do
  reserved "forall"
  as <- many1 var
  reservedOp "."
  p <- term
  return $ foldr (\ x y -> Forall x y) p (map (\(Var x) -> x) as)

compound = do
  n <- eigen <|> try var <|> con <|> parens term 
  as <- compoundArgs
  if null as then return n
    else return $ foldl' (\ z x -> PApp z x) n as 

compoundArgs =
  many $ indented >> (try eigen <|> try con <|> try var <|> try (parens term))


-----------------------Positions -------
  
-- wrapPos :: Parser Exp -> Parser Exp
-- wrapPos p = pos <$> getPosition <*> p
--   where pos x (Pos y e) | x==y = (Pos y e)
--         pos x y = Pos x y


-------------------------------

-- Tokenizer definition

gottlobStyle :: (Stream s m Char, Monad m) => Token.GenLanguageDef s u m
gottlobStyle = Token.LanguageDef
                { Token.commentStart   = "{-"
                , Token.commentEnd     = "-}"
                , Token.commentLine    = "--"
                , Token.nestedComments = True
                , Token.identStart     = letter
                , Token.identLetter    = alphaNum <|> oneOf "_'"
                , Token.opStart        = oneOf ":!#$%&*+.,/<=>?@\\^|-"
                , Token.opLetter       = (oneOf ":!#$%&*+.,/<=>?@\\^|-") <|> alphaNum
                , Token.caseSensitive  = True
                , Token.reservedNames =
                  [
                    "forall", "iota", "reduce", 
                    "coind","use", "intros", "apply", "applyh",
                    "by", "from", "in", "let", "simpCmp", "step",
                    "case", "of",
                    "data", "if", "then", "else",
                    "axiom", "proof", "qed", "lemma", "auto",
                    "show",
                    "where", "module",
                    "infix", "infixl", "infixr", "pre", "post",
                    "formula", "prog", "set",
                    "tactic", "deriving", "Ind"
                  ]
               , Token.reservedOpNames =
                    ["\\", "->", "<=", ".","=", "::", ":", "=>"]
                }

-- tokenizer :: Token.GenTokenParser String u (State SourcePos)
tokenizer = Token.makeTokenParser gottlobStyle

-- identifier :: Parser String
identifier = Token.identifier tokenizer

-- whiteSpace :: ParsecT String u (State SourcePos) ()
whiteSpace = Token.whiteSpace tokenizer

-- reserved :: String -> ParsecT String u (State SourcePos) ()
reserved = Token.reserved tokenizer

-- reservedOp :: String -> ParsecT String u (State SourcePos) ()
reservedOp = Token.reservedOp tokenizer

-- operator :: ParsecT String u (State SourcePos) String
operator = Token.operator tokenizer

-- colon :: ParsecT String u (State SourcePos) String
colon = Token.colon tokenizer

-- integer :: ParsecT String u (State SourcePos) Integer
integer = Token.integer tokenizer

-- brackets :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) a
brackets = Token.brackets tokenizer

-- parens :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) a
parens  = Token.parens tokenizer

-- braces :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) a
braces = Token.braces tokenizer

-- dot :: ParsecT String u (State SourcePos) String
dot = Token.dot tokenizer

-- -- commaSep1 :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) [a]
-- commaSep1 = Token.commaSep1 tokenizer

-- --semiSep1 :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) [a]
-- semiSep1 = Token.semiSep1 tokenizer

-- comma :: ParsecT String u (State SourcePos) String
comma = Token.comma tokenizer

