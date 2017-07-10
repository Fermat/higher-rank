module TypeChecker where

import Syntax
import Pretty
import Matching

import Text.PrettyPrint
import Control.Monad.State.Lazy
import Control.Monad.Reader
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
                           Nothing ->
                             lift $ lift $ lift $ Left $
                             text "Kinding error: " <+>
                             text "undefine type constructor:" <+> disp x

inferKind (Var x) = do
  Subst env <- lift get
  case lookup x env of
    Nothing -> do
      ki <- makeName "k"
      let kind = Var ki
      lift $ modify (\ (Subst e) -> Subst $ (x, kind):e)
      return kind
    Just k -> return k  

inferKind (PApp f1 f2) = do
  k1 <- inferKind f1
  k2 <- inferKind f2
  unificationK k2 Star
  k <- makeName "k"
  unificationK k1 $ KArrow Star (KVar k) 
  return (KVar k) 

inferKind (Abs x t) = do
  lift $ modify (\ e -> (x, Star): e)
  if x `elem` (free t) then
    do k <- inferKind t
       let k' = ground k
       case isTerm k' of
         True -> return $ KArrow Star k
         False -> lift $ lift $ lift $ Left $ text "the body " <+> (disp t) <+> text " is ill-kind"
    else lift $ lift $ lift $ Left $ text "no use of variable " <+> text x
