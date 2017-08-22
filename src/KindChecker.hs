module KindChecker where

import Syntax
import Pretty
import Matching

import Text.PrettyPrint
import Control.Monad.State.Lazy
import Control.Monad.Reader
import Control.Monad.Except
import Data.Char
import Control.Exception

type KindDef = [(Name, Exp)]

type KCMonad a = StateT Int (StateT KindDef (ReaderT KindDef (Either Doc))) a  

grounding :: Exp -> Exp
grounding (Var x) = Star
grounding (Imply k1 k2) = Imply (grounding k1) (grounding k2)
grounding Star = Star

makeName name = 
  do m <- get
     modify (+1)
     return $ name ++ show m ++ "'"
  
inferKind :: Exp -> KCMonad Exp
inferKind (Const x) = 
  do genv <- ask
     case lookup x genv of
       Just k -> return k
       Nothing -> throwError $
                  text "Kinding error: " <+>
                  text "undefined type constructor:" <+> disp x

inferKind (Var x) = 
  do env <- lift get
     case lookup x env of
       Nothing -> throwError $
                  text "Kinding error: " <+>
                  text "unbound type variable:" <+> disp x
       Just k -> return k  

inferKind (App f1 f2) = 
  do k1 <- inferKind f1
     k2 <- inferKind f2
     k <- makeName "k"
     case runMatch k1 (Imply k2 (Var k)) of
       [] -> throwError $
             text "Kinding error:" $$
             (text "kind mismatch for" <+>
              disp f1 <+> text "::" <+> disp k1 <+>
               text "and" <+> disp f2 <+> text "::" <+> disp k2)
       x:_ -> 
         do env <- lift get
            let env' = map (\(y, e) -> (y, apply x e)) env
            lift $ put (env') 
            return $ apply x (Var k) 

inferKind (Forall x f) = 
  do k <- makeName "k"
     lift $ modify (\e -> (x, Var k): e)
     k <- inferKind f
     let k' = grounding k
     case k' of
       Star -> return Star
       _ -> throwError $ text "Kinding error:" $$
            (text "unexpected kind"<+> disp k' <+>
              text "for" <+> disp f)
                                                  
inferKind (Imply f1 f2) = 
  do k1 <- inferKind f1
     k2 <- inferKind f2
     case (grounding k1, grounding k2) of
       (Star, Star) -> return Star
       (a, b) -> throwError $ text "Kinding error:" $$
                 (text "unexpected kind"<+> disp a <+>
                   text "for" <+> disp f1)
                                                  
runKinding :: Exp -> KindDef -> Either Doc Exp
runKinding t g = do (k, sub) <- runReaderT (runStateT (evalStateT (inferKind t) 0) []) g 
                    return k


instance Exception Doc 

getKindDef a = [(d, k) | (DataDecl (Const d) k ls)<- a ]


splitDecl ((DataDecl _ _ cons):xs) =
  let (d, f, p) = splitDecl xs in
    (cons++d, f, p)
splitDecl ((FunDecl (Var fun) t _):xs) =
  let (d, f, p) = splitDecl xs in
    (d, (Var fun, t):f, p)
splitDecl ((Prim fun t):xs) =
  let (d, f, p) = splitDecl xs in
    (d, f, (fun, t):p)
splitDecl [] = ([], [], [])


kinding :: [Decl] -> IO ()
kinding a =
  let g = getKindDef a
      (ds, fs, ps) = splitDecl a
      res = mapM (\ (x, e) -> runKinding e g `catchError`
                   (\ err -> throwError
                             (err $$ text "in the type of the data constructor" <+> disp x)))
            ds in
    case res of
      Left e -> throw e
      Right _ ->
        let res1 = mapM (\ (x, e) -> (runKinding e g) `catchError`
                            (\ e -> throwError
                                    (e $$ text "in the type of the function" <+> disp x)))
                   fs in
          case res1 of
            Left e -> throw e
            Right _ ->
              let res2 = mapM (\ (x, e) -> (runKinding e g) `catchError`
                                (\ e -> throwError
                                        (e $$ text "in the type of the primitive function"
                                         <+> disp x)))
                         ps in
                case res2 of
                  Left e -> throw e
                  Right _ -> print "kinding success!\n"

      
