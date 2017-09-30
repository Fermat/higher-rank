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
 runIndent $ runParserT decl initialParserState srcName cnts

type Parser a = IndentParser String ParserState a

data ParserState =
  ParserState {
    progParser :: IndentParser String ParserState Exp,
    typeParser :: IndentParser String ParserState Exp,
    progOpTable :: IM.IntMap [Operator String ParserState (IndentT Identity) Exp],
    typeOpTable :: IM.IntMap [Operator String ParserState (IndentT Identity) Exp]
    }

initialParserState :: ParserState
initialParserState = ParserState{
  progParser = buildExpressionParser [] termA, 
  typeParser = buildExpressionParser initialTypeOpTable bType,
  progOpTable = IM.fromAscList (zip [0 ..] [[]]),
  typeOpTable = IM.fromAscList (zip [0 ..] initialTypeOpTable)}

initialTypeOpTable = [[], [], [], [], [], [binOp AssocRight "->" Imply]]

binOp assoc op f = Infix (reservedOp op >> return f) assoc  

toOp op "infix" app var =
  Infix (reservedOp op >> getPosition >>= \ p -> return (\ x y -> app (app (var op p) x) y))
  AssocNone
-- binOp AssocNone op (binApp op app var)
toOp op "infixr" app var =
  Infix (reservedOp op >> getPosition >>= \ p -> return (\ x y -> app (app (var op p) x) y))
  AssocRight
  -- binOp AssocRight op (binApp op app var)
toOp op "infixl" app var =
  Infix (reservedOp op >> getPosition >>= \ p -> return (\ x y -> app (app (var op p) x) y))
  AssocLeft
-- binOp AssocLeft op (binApp op app var)

-- binApp op app var x y = app (app (var op) x) y

-- deriving instance Typeable P.ParseError
-- instance Exception P.ParseError 

-- parse module
decl :: Parser [Decl]
decl = do
  reserved "module"
  name <- identifier
  reserved "where"
  bs <- many $ try dataDecl <|> try primDecl <|> try typeSyn <|> funDecl
  eof
  return $ bs


typeOperatorDecl :: Parser Decl
typeOperatorDecl = do
  reserved "type"
  r <- choice [reserved i >> return i | i <- ["infix","infixr","infixl"]]
  level <- fromInteger <$> integer
  op <- operator
  st <- getState
  let table' = IM.insertWith (++) level [toOp op r TApp Var] $ typeOpTable st
      type' = buildExpressionParser (map snd (IM.toAscList table')) bType
  putState $ ParserState
    (progParser st)  type' (progOpTable st) table'
  return (TypeOperatorDecl op level r)

progOperatorDecl :: Parser Decl
progOperatorDecl = do
  reserved "prog"
  r <- choice [reserved i >> return i | i <- ["infix","infixr","infixl"]]
  level <- fromInteger <$> integer
  op <- operator
  st <- getState
  let table' = IM.insertWith (++) level [toOp op r App Var] $ progOpTable st
      prog' = buildExpressionParser (map snd (IM.toAscList table')) termA
  putState $ ParserState
    prog' (typeParser st) table' (typeOpTable st) 
  return (ProgOperatorDecl op level r)

primDecl :: Parser Decl
primDecl = do
  reserved "primitive"
  f <- var
  reservedOp "::"
  k <- ty
  return $ Prim f k

typeSyn :: Parser Decl
typeSyn = 
  do reserved "type"
     tycon <- con
     reservedOp "::"
     k <- ty
     reservedOp "="
     t <- ty
     return $ Syn tycon k t
     
dataDecl :: Parser Decl
dataDecl = do
  reserved "data"
  n <- con
  reservedOp "::"
  k <- ty
  reserved "where"
  ls <- option [] $ indented >> (block $ do{c <- con; reservedOp "::"; t <- ty; return (c, t)})
  return $ DataDecl n k ls
  
-- (fun-name, [([pats], e)])    
funDecl :: Parser Decl
funDecl = do
  v <- var
  reservedOp "::"
  t <- ty
  ls <- manyTill eq (lookAhead (reserved "data") <|> lookAhead (reserved "type") <|>lookAhead (reserved "primitive") <|> (isNotVar v) <|> try eof)
  return $ FunDecl v t ls
    where eq = do
            var
            ps <- many $ try con <|> try var <|> parens patComp
            reservedOp "="
            p <- term
            return (ps, p)
          isNotVar v = do
            v' <- lookAhead $ try var
            when (getName v' == getName v) $ parserFail "from funDecl"

            
var :: Parser Exp
var = do
  n <- identifier
  when (isUpper (head n)) $ parserFail "expected to begin with lowercase letter"
  p <- getPosition
  return (Var n p)

con :: Parser Exp
con = do
  n <- identifier  
  when (isLower (head n)) $ parserFail "expected to begin with uppercase letter"
  p <- getPosition
  return (Const n p)

star :: Parser Exp
star = reserved "*" >> return Star

-- parser for types
ty :: Parser Exp
ty = getState >>= \st -> typeParser st


bType :: Parser Exp
bType = try lamType <|> try forall <|> try atomType <|> parens ty


lamType = do
  reservedOp "\\"
  as <- many1 $ var
  reservedOp "."
  t <- ty
  return $ foldr (\ x y -> Lambda x y) t as  
  
atomType = do
  n <- try star <|> try var <|> try con <|> parens atomType
  as <- many $ indented >> arg
  return $ foldl' (\ z x -> App z x) n as 

arg =  (try con <|> try var <|> try (parens ty))

forall = do
  reserved "forall"
  as <- many1 var
  reservedOp "."
  p <- ty
  return $ foldr (\ x y -> Forall x y) p (map (\(Var x _) -> x) as)

-- parse term
termA :: Parser Exp
termA = try lambda <|> try compound <|> try caseExp <|> try letExp <|> parens term 

term = getState >>= \ st -> progParser st

lambda = do
  reservedOp "\\"
  as <- many1 $ try con <|> try var <|> parens patComp
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
  alts <- block $ do{p <- pat; reserved "->"; a' <- term;
                     -- let a = foldl' (\ z x -> App z x) n as in 
                     return (p, a')} -- n <- con; as <- many pat
  return $ Case e alts


letExp = do
  reserved "let"
  defs <- block (try def1 <|> def)
  reserved "in"
  e <- term
  return $ Let defs e
  where def = do
          p <- pat
          reservedOp "="
          t <- term
          return (p, t)
        def1 = do
          n <- var
          reservedOp "::"
          t <- ty
          var
          reservedOp "="
          e <- term
          return (Ann n t, e)
          
          
-- try con
pat = try var <|> parens patComp <|> patComp
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
                    "coind","use", "intros", "apply", "type",
                    "by", "from", "in", "let", "simpCmp", "step",
                    "case", "of",
                    "data", 
                    "axiom", "proof", "qed", "lemma", "auto", "primitive",
                    "show",
                    "where", "module",
                    "infix", "infixl", "infixr", "pre", "post",
                    "formula", "prog", "set",
                    "tactic", "deriving"
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

