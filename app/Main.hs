{-# LANGUAGE StandaloneDeriving #-}
module Main where
import Parser
import Syntax
import Pretty
import Matching
import TypeChecker

import Control.Monad.Except
import Text.PrettyPrint
import Control.Monad.State.Lazy
import Data.Typeable
import Text.Parsec(ParseError)
import Control.Exception
import System.Exit
import System.Environment
main = flip catches handlers $ do
  args <- getArgs
  case args of
    [filename] -> do
      cnts <- readFile filename
      case parseModule filename cnts of
             Left e -> throw e
             Right a -> do putStrLn $ "Parsing success! \n"
                           print $ disp a
                           let kEnv = [(d, k) | (DataDecl (Const d) k ls)<- a ]
                           kindData a kEnv
                           kindFunc a kEnv

                               

    _ -> putStrLn "usage: higher-rank <filename>"
  where handlers = [Handler parseHandler]
        parseHandler :: ParseError -> IO ()
        parseHandler e = print (disp e) >> exitFailure

deriving instance Typeable ParseError
instance Exception ParseError 
instance Exception Doc 

kindData :: [Decl] -> KindDef -> IO ()
kindData a g = do
  let ds = concat [cons | (DataDecl _ _ cons) <- a]
      res = mapM (\ (Const x, e) -> runKinding e g `catchError` (\ err -> throwError (err $$ text "in the type of the data constructor" <+> text x))) ds
  case res  of
    Left e -> throw e
    Right ks -> do
      putStrLn $ "kinding success for datatypes! \n"

kindFunc :: [Decl] -> KindDef -> IO ()
kindFunc a g = do
  let ds = [(f, t) | (FunDecl (Var f) t _) <- a]
  case mapM (\ (x, e) -> (runKinding e g) `catchError` (\ e -> throwError (e $$ text "in the type of the function" <+> text x))) ds of
    Left e -> throw e
    Right ks -> do
      putStrLn $ "kinding success for function's type! \n"

