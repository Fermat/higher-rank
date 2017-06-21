module Syntax where

-- import Control.Monad.State.Lazy
-- import Control.Monad.Reader

import Data.Char
import qualified Data.Set as S
import Data.List hiding (partition)
import Debug.Trace

type Name = String

-- Variable convention: word begins with upper-case represents constant and
-- lower-case represents variable, lower-case constant represent eigenvariable

data Exp = Var Name
          | Const Name
          | App Exp Exp
          | Lambda Name (Maybe Exp) Exp
          | Imply Exp Exp
          | Forall Name Exp
          | Case Exp (Maybe Exp) [(Exp, Exp, Exp)]
          | Let [(Name, Exp)] Exp
          deriving (Show, Eq, Ord)

data Kind = Star
          | KVar Name
          | KArrow Kind Kind
          deriving (Show, Eq)

-- nameless for the type
data Nameless = V Int
              | C Name
              | IMP Nameless Nameless
              | ALL Nameless
              | AP Nameless Nameless
              | LAM Nameless
             deriving (Show, Eq)

data DataDecl = DataDecl Name Kind [(Exp, Exp)]
                deriving (Show)

data Module = Mod {funs :: [(Name, Exp, Exp)],
                   datas :: [DataDecl],
                   annFuns ::[(Name, Exp, Exp)]}
            deriving (Show)


{-
-- free vars of exp
free = S.toList . freeVar 
-- freeVar :: Exp -> [Name]
freeVar (Var x) =  S.insert x S.empty
freeVar (Const x) = S.empty
-- freeVar (Const x) = if isLower (head x) then S.insert x S.empty else S.empty
freeVar (Arrow f1 f2) = (freeVar f1) `S.union` (freeVar f2)
freeVar (App f1 f2) = (freeVar f1) `S.union` (freeVar f2)
freeVar (TApp f1 f2) = (freeVar f1) `S.union` (freeVar f2)
freeVar (PApp f1 f2) = (freeVar f1) `S.union` (freeVar f2)
freeVar (Forall x f) = S.delete x (freeVar f)
freeVar (Lambda x (Just f1) f) =
  S.delete x $ freeVar f `S.union` freeVar f1
freeVar (Lambda x Nothing f) =
  S.delete x $ freeVar f   
freeVar (Abs x f) = S.delete x (freeVar f)
freeVar (Imply b h) = freeVar b `S.union` freeVar h


free' = S.toList . freeVar'
-- freeVar :: Exp -> [Name]
freeVar' (Var x) =  S.insert x S.empty
freeVar' (Const x) = if isLower (head x) then S.insert x S.empty else S.empty
freeVar' (Arrow f1 f2) = (freeVar' f1) `S.union` (freeVar' f2)
freeVar' (App f1 f2) = (freeVar' f1) `S.union` (freeVar' f2)
freeVar' (TApp f1 f2) = (freeVar' f1) `S.union` (freeVar' f2)
freeVar' (PApp f1 f2) = (freeVar' f1) `S.union` (freeVar' f2)
freeVar' (Forall x f) = S.delete x (freeVar' f)
freeVar' (Lambda x (Just f1) f) =
  S.delete x $ freeVar' f `S.union` freeVar' f1
freeVar' (Lambda x Nothing f) =
  S.delete x $ freeVar' f   
freeVar' (Abs x f) = S.delete x (freeVar' f)
freeVar' (Imply b h) = freeVar' b `S.union` freeVar' h

freeKVar :: Kind -> S.Set Name
freeKVar Star = S.empty
freeKVar (KVar x) = S.insert x S.empty
freeKVar (KArrow f1 f2) = (freeKVar f1) `S.union` (freeKVar f2)

-- flatten of type
flatten :: Exp -> [Exp]
flatten (PApp f1 f2) = flatten f1 ++ [f2]
flatten (App f1 f2) = flatten f1 ++ [f2]
flatten (TApp f1 f2) = flatten f1 ++ [f2]
flatten a = [a]
getHead a = head $ flatten a
getArgs a = tail $ flatten a
reApp (y:ys) = foldl (\ z x -> App z x) y ys
flattenK :: Kind -> [Kind]
flattenK (KArrow f1 f2) =  f1 : flattenK f2
flattenK a = [a]

flattenF (Imply f1 f2) =  f1 : flattenF f2
flattenF a = [a]

-- convert eigenvariable to variable 
rebind :: Exp -> Exp
--rebind exp | trace ("rebind " ++show (exp)) False = undefined
rebind (Const x) | isUpper $ head x = Const x
                 | otherwise = (Var x)
rebind (Var x) = Var x
rebind (App t1 t2) = App (rebind t1) (rebind t2)
rebind (TApp t1 t2) = TApp (rebind t1) (rebind t2)
rebind (PApp t1 t2) = PApp (rebind t1) (rebind t2)
rebind (Imply t1 t2) = Imply (rebind t1) (rebind t2)
rebind (Lambda x Nothing t) =
  Lambda x Nothing (rebind t)
rebind (Lambda x (Just t') t) =
  Lambda x (Just $ rebind t') (rebind t)
rebind (Abs x t) = Abs x (rebind t)
rebind (Forall x t) = Forall x (rebind t)
rebind a = error $ show a
  
type BindCxt a = Reader [(Name, Int)] a

-- debruijn representation of type 
debruijn :: Exp -> BindCxt Nameless
debruijn (Const x) = return $ C x

debruijn (Var x) = do
  n' <- asks (lookup x)
  case n' of
    Just n -> return $ V n
    Nothing -> error $ show x ++ "what"


debruijn (Forall x f) = do 
  a <- local (((x,0):) . plus1) $ debruijn f 
  return $ ALL a
  
debruijn (Imply f1 f2) = do
  a1 <- debruijn f1
  a2 <- debruijn f2
  return $ IMP a1 a2

debruijn (PApp b1 b2) = do
  a <- debruijn b1
  a1 <- debruijn b2
  return $ AP a a1

debruijn (Abs x f) = do
  a <- local (((x,0):) . plus1) $ debruijn f 
  return $ LAM a

plus1 = map $ \(x, y) -> (x, y + 1)

-- alphaEq of two type
alphaEq :: Exp -> Exp -> Bool
alphaEq t1 t2 =
    let t1' = foldl' (\t x -> Forall x t) t1 (free t1)
        t2' = foldl' (\t x -> Forall x t) t2 (free t2) in
    runReader (debruijn t1') [] == runReader (debruijn t2') []



type GVar a = State Int a

type Subst = [(Name, Exp)]
-- kind level sub
applyK :: [(Name, Kind)] -> Kind -> Kind
applyK s Star = Star
applyK s Formula = Formula
applyK s (KVar x) = case lookup x s of
                       Just t -> t
                       Nothing -> (KVar x)
applyK s (KArrow k1 k2) = KArrow (applyK s k1) (applyK s k2)
-- both type level and evidence level substitution
applyE :: Subst -> Exp -> Exp
applyE [] e = e
applyE ((n,t):xs) e = applyE xs $ runSubst t (Var n) e

runSubst :: Exp -> Exp -> Exp -> Exp
runSubst t x t1 = fst $ runState (subst t x t1) 0
  
subst :: Exp -> Exp -> Exp -> GVar Exp
subst s (Var x) (Const y) = return $ Const y

subst s (Var x) (Var y) =
  if x == y then return s else return $ Var y
                               
subst s (Var x) (Imply f1 f2) = do
  c1 <- subst s (Var x) f1
  c2 <- subst s (Var x) f2
  return $ Imply c1 c2

subst s (Var x) (App f1 f2) = do
  c1 <- subst s (Var x) f1
  c2 <- subst s (Var x) f2
  return $ App c1 c2

subst s (Var x) (TApp f1 f2) = do
  c1 <- subst s (Var x) f1
  c2 <- subst s (Var x) f2
  return $ TApp c1 c2

subst s (Var x) (PApp f1 f2) = do
  c1 <- subst s (Var x) f1
  c2 <- subst s (Var x) f2
  return $ PApp c1 c2

subst s (Var x) (Forall a f) =
  if x == a || not (x `elem` free f) then return $ Forall a f
  else if not (a `elem` free s)
       then do
         c <- subst s (Var x) f
         return $ Forall a c
       else do
         n <- get
         modify (+1)
         c1 <- subst (Var (a++ show n)) (Var a) f
         subst s (Var x) (Forall (a ++ show n) c1)

subst s (Var x) (Abs a f) =
  if x == a || not (x `elem` free f) then return $ Abs a f
  else if not (a `elem` free s)
       then do
         c <- subst s (Var x) f
         return $ Abs a c
       else do
         n <- get
         modify (+1)
         c1 <- subst (Var (a++ show n)) (Var a) f
         subst s (Var x) (Abs (a ++ show n) c1)

subst s (Var x) (Lambda a Nothing f) =
  if x == a || not (x `elem` free f) then return $ Lambda a Nothing f
  else if not (a `elem` free s)
       then do
         c <- subst s (Var x) f
         return $ Lambda a Nothing c
       else do
         n <- get
         modify (+1)
         c1 <- subst (Var (a++ show n)) (Var a) f
         subst s (Var x) (Lambda (a ++ show n) Nothing c1)         


subst p (Var x) (Lambda y (Just t) p1) =
  if x == y || not (x `elem` free p1)
    then do
    t1 <- subst p (Var x) t
    return $ Lambda y (Just t1) p1
    else if not (y `elem` free p)
         then do
           t1 <- subst p (Var x) t
           c <- subst p (Var x) p1
           return $ Lambda y (Just t1) c
         else do
           n <- get
           modify (+1)
           c1 <- subst (Var (y++ show n)) (Var y) p1
           subst p (Var x) (Lambda (y++ show n) (Just t) c1)

normEvidence (Var y) = (Var y)
normEvidence (Const y) = (Const y)
normEvidence (Imply f1 f2) = Imply (normEvidence f1)
                             (normEvidence f2)

normEvidence (App f1 f2) = App (normEvidence f1)
                           (normEvidence f2)
normEvidence (TApp f1 f2) = TApp (normEvidence f1)
                            (normalize f2)

normEvidence a@(PApp f1 f2) = normalize a
normEvidence a@(Abs b f2) = normalize a
normEvidence (Forall a f2) = Forall a $ normalize f2
normEvidence (Lambda a Nothing f) = Lambda a Nothing (normEvidence f)
normEvidence (Lambda y (Just t) p1) = Lambda y (Just $ normalize t) (normEvidence p1)
-- normalize type expresion
normalize :: Exp -> Exp
-- normalize r | trace ("normalize " ++ show r) False = undefined
normalize t = let t1 = norm t
                  t2 = norm t1
              in if t1 == t2 then t1 else normalize t2 -- `alphaEq`
                                                 
norm (Var a) = Var a
norm (Const a) = Const a
norm (Abs x t) = Abs x (norm t)
norm (PApp (Abs x t') t) = runSubst t (Var x) t'
norm (PApp (Var x) t) = PApp (Var x) (norm t)
norm (PApp (Const x) t) = PApp (Const x) (norm t)
norm (PApp t' t) = 
  case (PApp (norm t') (norm t)) of
    a@(PApp (Abs x t') t) -> norm a
    b -> b
norm (Imply t t') = Imply (norm t) (norm t')
norm (Forall x t) = Forall x (norm t)

  
-}
