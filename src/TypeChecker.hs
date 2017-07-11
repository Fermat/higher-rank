module TypeChecker where

import Syntax
import Pretty
import Matching

import Text.PrettyPrint
import Control.Monad.State.Lazy
import Control.Monad.Reader
import Control.Monad.Except
import Data.Char


type KindDef = [(Name, Exp)]

-- Well-formed kinds
wfKind :: Exp -> Bool
wfKind Star = True
wfKind (Imply x y) = wfKind x && wfKind y

type KCMonad a = StateT Int (StateT Subst (ReaderT KindDef (Either Doc))) a  

grounding :: Exp -> Exp
grounding (Var x) = Star
grounding (Imply k1 k2) = Imply (grounding k1) (grounding k2)
grounding Star = Star


makeName name = do
  m <- get
  modify (+1)
  return $ name ++ show m
  
inferKind :: Exp -> KCMonad Exp
inferKind (Const x) | isUpper (head x) =
                      do genv <- ask
                         case lookup x genv of
                           Just k -> return k
                           Nothing -> throwError $
                           -- lift $ lift $ lift $ Left $
                                      text "Kinding error: " <+>
                                      text "undefined type constructor:" <+> disp x

inferKind (Var x) = do
  Subst env <- lift get
  case lookup x env of
    Nothing -> do
      ki <- makeName "k"
      let kind = Var ki
      lift $ modify (\ (Subst e) -> Subst $ (x, kind):e)
      return kind
    Just k -> return k  

inferKind (App f1 f2) = do
  k1 <- inferKind f1
  k2 <- inferKind f2
  k <- makeName "k"
  case runMatch k1 (Imply k2 (Var k)) of
    [] -> throwError $ text "Kinding error:" $$ (text "kind mismatch for"
                                                  <+> disp f1 <+> text "::" <+> disp k1 <+> text "and" <+>
                                                  disp f2 <+> text "::" <+> disp k2)
    
    x:_ -> do
      Subst env <- lift get
      let env' = map (\(y, e) -> (y, apply x e)) env
      lift $ put (Subst env') 
      return $ apply x (Var k) 


inferKind (Lambda (Var x) _ t) = do
  lift $ modify (\ (Subst e) -> Subst $ (x, Star): e)
  k <- inferKind t
  let k' = grounding k
  return $ Imply Star k'

inferKind (Forall x f) = do
  k <- inferKind f
  let k' = grounding k
  case k' of
    Star -> return Star
    _ -> throwError $ text "Kinding error:" $$ (text "unexpected kind"
                                                  <+> disp k' <+> text "for" <+>
                                                  disp f)

inferKind (Imply f1 f2) = do
  k1 <- inferKind f1
  k2 <- inferKind f2
  case (grounding k1, grounding k2) of
    (Star, Star) -> return Star
    (a, b) -> throwError $ text "Kinding error:" $$ (text "unexpected kind"
                                                  <+> disp a <+> text "for" <+>
                                                  disp f1)


runKinding :: Exp -> KindDef -> Either Doc Exp
runKinding t g = do (k, sub) <- runReaderT (runStateT (evalStateT (inferKind t) 0) (Subst [])) g 
                    return k


                



