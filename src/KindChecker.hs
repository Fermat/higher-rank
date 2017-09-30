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
grounding (Var x _) = Star
grounding (Imply k1 k2) = Imply (grounding k1) (grounding k2)
grounding Star = Star

makeName name = 
  do m <- get
     modify (+1)
     return $ name ++ show m ++ "#"
  
inferKind :: Exp -> KCMonad Exp
inferKind (Const x p) = 
  do genv <- ask
     case lookup x genv of
       Just k -> return k
       Nothing ->
         -- Build-in type Void inhabited by nothing
         if x == "Void#" then return Star
         else 
           throwError $
           text "Kinding error" <+> disp p $$ nest 2
           (text "undefined type constructor:" <+> disp x)

inferKind (Var x p) = 
  do env <- lift get
     env' <- ask
     case lookup x (env++env') of
       Nothing -> throwError $
                  text "Kinding error" <+> disp p $$ nest 2
                  (text "unbound type variable:" <+> disp x)
       Just k -> return k  

inferKind (App f1 f2) = 
  do k1 <- inferKind f1
     k2 <- inferKind f2
     k <- makeName "k"
     case runMatch k1 (Imply k2 (Var k dummyPos)) of
       [] -> throwError $
             text "Kinding error:" $$
             (text "kind mismatch for" <+>
              disp f1 <+> text "::" <+> disp k1 <+>
               text "and" <+> disp f2 <+> text "::" <+> disp k2)
       x:_ -> 
         do env <- lift get
            let env' = map (\(y, e) -> (y, apply x e)) env
            lift $ put (env') 
            return $ apply x (Var k dummyPos) 

inferKind (Forall x f) = 
  do k <- makeName "k"
     lift $ modify (\e -> (x, Var k dummyPos): e)
     k <- inferKind f
     let k' = grounding k
     case k' of
       Star -> return Star
       _ -> throwError $ text "Kinding error:" $$
            (text "unexpected kind"<+> disp k' <+>
              text "for" <+> disp f)

inferKind (Lambda (Var x p) f) = 
  do k <- makeName "k"
     lift $ modify (\e -> (x, Var k dummyPos): e)
     fk <- inferKind f
     env <- lift get
     case lookup x env of
       Nothing -> error "internal error from inferKind"
       Just k'' -> return $ Imply k'' fk
     
     -- let k' = grounding k
     -- case k' of
     --   Star -> return Star
     --   _ -> throwError $ text "Kinding error:" $$
     --        (text "unexpected kind"<+> disp k' <+>
     --          text "for" <+> disp f)
            
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

runKinding' :: Exp -> KindDef -> Either Doc (Exp, [(Name, Exp)])
runKinding' t g = runReaderT (runStateT (evalStateT (inferKind t) 0) []) g 
                    


instance Exception Doc 

getKindDef ((DataDecl (Const d _) k ls):as) = (d, k) : getKindDef as
getKindDef ((Syn (Const d _) k t):as) = (d, k) : getKindDef as
getKindDef (_:as) = getKindDef as
getKindDef [] = []

splitDecl ((DataDecl _ _ cons):xs) =
  let (d, f, p, t) = splitDecl xs in
    (cons++d, f, p, t)
splitDecl ((FunDecl (Var fun p') t _):xs) =
  let (d, f, p, ty) = splitDecl xs in
    (d, (Var fun p', t):f, p, ty)
splitDecl ((Prim fun t):xs) =
  let (d, f, p, ty) = splitDecl xs in
    (d, f, (fun, t):p, ty)
splitDecl ((Syn ty k t):xs) =
  let (d, f, p, ty') = splitDecl xs in
    (d, f, p, (ty, t, k):ty')    
splitDecl [] = ([], [], [], [])

kindData ds g =
  let res = mapM (\ (x, e) -> runKinding e g `catchError`
                   (\ err -> throwError
                     (err $$ text "in the type of the data constructor" <+> disp x)))
            ds in
    case res of
      Left e -> throw e
      Right _ -> return ()

kindFunc fs g =
  let res1 = mapM (\ (x, e) -> (runKinding e g) `catchError`
                               (\ e -> throwError
                                 (e $$ text "in the type of the function" <+> disp x)))
             fs in
    case res1 of
      Left e -> throw e
      Right _ -> return ()

kindPrim ps g =
  let res2 = mapM (\ (x, e) -> (runKinding e g) `catchError`
                               (\ e -> throwError
                                       (e $$ text "in the type of the primitive function"
                                         <+> disp x)))
             ps in
    case res2 of
      Left e -> throw e
      Right _ -> return ()

kindTysyn tsyns g = 
  let res3 = mapM (\ (ty,t, k) ->
                      case runKinding t g of
                        Left e -> throw e
                        Right k' -> 
                          let k'' = grounding k' in 
                            if k == k'' then
                              return ()
                            else
                              throwError
                              (text "kind mistmatch for"
                                <+> disp ty $$ nest 2
                                (text "expected:" <+> disp k)
                                $$ nest 2 (text "but got:" <+> disp k')))
             tsyns in
    case res3 of
      Left e -> throw e
      Right _ -> return ()

kinding :: [Decl] -> IO ()
kinding a =
  do let g = getKindDef a
         (ds, fs, ps, tsyns) = splitDecl a
     kindData ds g
     kindTysyn tsyns g
     kindPrim ps g
     kindFunc fs g
     print $ text "kinding success!\n"
