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
  bs <- many $ try dataDecl <|> funDecl
  eof
  return $ bs


dataDecl :: Parser Decl
dataDecl = do
  reserved "data"
  n <- con
  reservedOp "::"
  k <- ty
  reserved "where"
  indented
  ls <- block $ do{c <- con; reservedOp "::"; t <- ty; return (c, t)}
  return $ DataDecl n k ls
  
-- (fun-name, [([pats], e)])    
funDecl :: Parser Decl
funDecl = do
  v <- var
  reservedOp "::"
  t <- ty
  ls <- manyTill eq (lookAhead (reserved "data") <|> (isNotVar v) <|> try eof)
  return $ FunDecl v t ls
    where eq = do
            var
            ps <- many pat
            reservedOp "="
            p <- term
            return (ps, p)
          isNotVar v = do
            v' <- lookAhead $ try var
            when (v' == v) $ parserFail "from funDecl"

            
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
bType = try forall <|> try atomType <|> parens ty

binOp assoc op f = Infix (reservedOp op >> return f) assoc

typeOpTable = [[binOp AssocRight "->" Imply]]

atomType = do
  n <- try star <|> try var <|> try con <|> parens atomType
  as <- many $ indented >> arg
  return $ foldl' (\ z x -> App z x) n as 

arg =  (try con <|> try var <|> try (parens atomType))

forall = do
  reserved "forall"
  as <- many1 var
  reservedOp "."
  p <- ty
  return $ foldr (\ x y -> Forall x y) p (map (\(Var x) -> x) as)

-- parse term
term :: Parser Exp
term = try lambda <|> try compound <|> try caseExp <|> try letExp <|> parens term 

lambda = do
  reservedOp "\\"
  as <- many1 pat
  reservedOp "->"
  p <- term
  return $ foldr (\ x y -> Lambda x y) p as -- (map (\(Var x) -> x) as)

compound = do
  n <- try var <|> try con <|> parens term 
  as <- try $ compoundArgs
  return $ foldl' (\ z x -> App z x) n as 

compoundArgs =
  many $ indented >> (try con <|> try var <|> try (parens term))

caseExp = do
  reserved "case"
  e <- term
  reserved "of"
  indented
  alts <- block $ do{n <- con; as <- many pat; reserved "->"; a' <- term;
                     let a = foldl' (\ z x -> App z x) n as in 
                       return (a, a')}
  return $ Case e alts

letExp = do
  reserved "let"
  defs <- block def
  reserved "in"
  e <- term
  return $ Let defs e
  where def = do
          p <- pat
          reservedOp "="
          t <- term
          return (p, t)
  

pat = try var <|> try con <|> parens patComp
  -- as <- patArgs
  -- if null as then return n
  --   else return $ foldl' (\ z x -> App z x) n as 

patComp = do
  n <- con
  ps <- many pat
  return $ foldl' (\ z x -> App z x) n ps



  
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

