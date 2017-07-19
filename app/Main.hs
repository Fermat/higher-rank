{-# LANGUAGE StandaloneDeriving #-}
module Main where
import Parser(parseModule)
import Pretty(disp)
import KindChecker(kindData, kindFunc, getKindDef)
import TypeChecker(ersm)


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
                           let kEnv = getKindDef a
                           kindData a kEnv
                           kindFunc a kEnv

                               

    _ -> putStrLn "usage: higher-rank <filename>"
  where handlers = [Handler parseHandler]
        parseHandler :: ParseError -> IO ()
        parseHandler e = print (disp e) >> exitFailure

deriving instance Typeable ParseError
instance Exception ParseError 

