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
import Control.Monad.Identity
import Control.Exception(Exception)

import qualified Data.IntMap as IM
import Data.Typeable
import Data.Char
import Data.List

parseModule :: String -> String -> Either P.ParseError [Decl]
parseModule srcName cnts = 
 runIndent $ runParserT decl () srcName cnts


-- parseExp :: String -> Either P.ParseError Exp
-- parseExp s = runIndent $ runParserT (try (parens term) <|> term) () [] s

-- parseExps :: String -> Either P.ParseError [Exp]
-- parseExps s = runIndent [] $ runParserT (many1 (try (parens term) <|> term)) () [] s

type Parser a = IndentParser String () a

-- deriving instance Typeable P.ParseError
-- instance Exception P.ParseError 

-- parse module
decl :: Parser [Decl]
decl = do
  reserved "module"
  name <- identifier
  reserved "where"
  bs <- many $ try dataDecl <|> try funDecl
  eof
  return $ bs


dataDecl :: Parser Decl
dataDecl = do
  reserved "data"
  n <- con
  reservedOp "::"
  k <- ty
  reserved "where"
  ls <- block $ do{c <- con; reservedOp "::"; t <- ty; return (c, t)}
  return $ DataDecl n k ls
  
-- (fun-name, [([pats], e)])    
funDecl :: Parser Decl
funDecl = do
  v <- var
  reservedOp "::"
  t <- ty
  ls <- block $
        do{ v' <- var;
            when (v /= v') $ parserFail ("expected to function to have name " ++ show (v));
            ps <- many pat;
            reservedOp "=";
            p <- term;
            return (ps, p)
          }
  return $ FunDecl v t ls
  
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

star :: Parser Exp
star = reserved "*" >> return Star

-- parser for types
ty :: Parser Exp
ty = buildExpressionParser typeOpTable bType

bType :: Parser Exp
bType = try atomType <|> try forall <|> parens ty

binOp assoc op f = Infix (reservedOp op >> return f) assoc

typeOpTable = [[binOp AssocRight "->" Imply]]

atomType = do
  n <- try star <|> try var <|> try con <|> parens atomType
  as <- args
  if null as then return n
    else return $ foldl' (\ z x -> App z x) n as 

args =
  many $ indented >> (try con <|> try var <|> try (parens atomType))

forall = do
  reserved "forall"
  as <- many1 var
  reservedOp "."
  p <- ty
  return $ foldr (\ x y -> Forall x y) p (map (\(Var x) -> x) as)

-- parse term
term :: Parser Exp
term = try lambda <|> try compound <|> try caseExp <|> parens term

lambda = do
  reservedOp "\\"
  as <- many1 var
  reservedOp "->"
  p <- term
  return $ foldr (\ x y -> Lambda x Nothing y) p (map (\(Var x) -> x) as)

compound = do
  n <- try var <|> try con <|> parens term 
  as <- compoundArgs
  if null as then return n
    else return $ foldl' (\ z x -> App z x) n as 

compoundArgs =
  many $ indented >> (try con <|> try var <|> try (parens term))

caseExp = do
  reserved "case"
  e <- term
  reserved "of"
  alts <- block $ do{a <- pat; reserved "->"; a' <- term; return (a, a')}
  return $ Case e Nothing alts

pat = do
  n <- con
  as <- patArgs
  if null as then return n
    else return $ foldl' (\ z x -> App z x) n as 

patArgs =
  many $ indented >> (try con <|> try var <|> try (parens pat))




  
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

tokenizer = Token.makeTokenParser gottlobStyle

identifier = Token.identifier tokenizer

whiteSpace = Token.whiteSpace tokenizer

reserved = Token.reserved tokenizer

reservedOp = Token.reservedOp tokenizer

operator = Token.operator tokenizer

colon = Token.colon tokenizer

integer = Token.integer tokenizer

brackets = Token.brackets tokenizer

parens  = Token.parens tokenizer

braces = Token.braces tokenizer

dot = Token.dot tokenizer

comma = Token.comma tokenizer

