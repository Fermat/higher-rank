{-# LANGUAGE StandaloneDeriving #-}
module Main where
import Parser(parseModule)
import Pretty(printTyped, disp)
import KindChecker(kinding)
import TypeChecker(checkDecls)


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
                           kinding a 
                           let res = checkDecls a
                           case res of
                             Left e -> throw e
                             Right pfs ->
                               do print $
                                    text
                                    "Type checking success, the following are the annotatated program: \n"
                                  print $ text "-----------------------------------------\n"
                                  print $ printTyped pfs



    _ -> putStrLn "usage: higher-rank <filename>"
  where handlers = [Handler parseHandler]
        parseHandler :: ParseError -> IO ()
        parseHandler e = print (disp e) >> exitFailure

deriving instance Typeable ParseError
instance Exception ParseError 

