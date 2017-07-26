module Syntax where

-- import Control.Monad.State.Lazy
import Control.Monad.Reader

import Data.Char
import qualified Data.Set as S
import Data.List hiding (partition)
import Debug.Trace

type Name = String

-- Variable convention: word begins with upper-case represents constant and
-- lower-case represents variable, lower-case constant represent eigenvariable

data Exp = Var Name
         | Star
         | Const Name
         | App Exp Exp
         | Lambda Exp Exp
         | Imply Exp Exp
         | Forall Name Exp
         | Case Exp [(Exp, Exp)]
         | Let [(Exp, Exp)] Exp
         | Ann Exp (Maybe Exp)
         deriving (Show, Eq, Ord)


data Decl = DataDecl Exp Exp [(Exp, Exp)]
          | FunDecl Exp Exp [([Exp], Exp)]
          deriving (Show)


-- free vars of exp
freeVars = S.toList . freeVar 

freeVar (Var x) =  S.insert x S.empty
freeVar (Const x) = S.empty
freeVar Star = S.empty
freeVar (App f1 f2) = (freeVar f1) `S.union` (freeVar f2)
freeVar (Forall x f) = S.delete x (freeVar f)
freeVar (Lambda p f) =
  freeVar f `S.difference` freeVar p
freeVar (Imply b h) = freeVar b `S.union` freeVar h
freeVar (Ann (Var x) _) = S.insert x S.empty

free' e =freeVars e ++ eigenVar e
  
eigenVar = S.toList . eigen

eigen (Var x) =  S.insert x S.empty
eigen (Const x) = if isLower (head x) then S.insert x S.empty else S.empty
eigen (App f1 f2) = (eigen f1) `S.union` (eigen f2)
eigen (Forall x f) = S.delete x (eigen f)
eigen (Imply b h) = eigen b `S.union` eigen h
eigen (Lambda p f) = eigen f 


-- flatten of type
flatten :: Exp -> [Exp]
flatten (App f1 f2) = flatten f1 ++ [f2]
flatten a = [a]

-- substitution that blindly substitutes
newtype Subst = Subst [(String, Exp)] deriving (Show, Eq)

apply :: Subst -> Exp -> Exp
apply (Subst s) (Var x) = case lookup x s of
                            Nothing -> Var x
                            Just t -> t
apply s a@(Const _) = a
apply s (App f1 f2) = App (apply s f1) (apply s f2)
apply s (Imply f1 f2) = Imply (apply s f1) (apply s f2)
apply s (Forall x f2) = Forall x (apply (minus s [x]) f2)
apply s (Lambda x f2) = Lambda x (apply (minus s (freeVars x)) f2)
-- apply s (Forall x f2) = Forall x (apply s f2)
-- apply s (Lambda x f2) = Lambda x (apply s f2)

apply s Star = Star
apply s (Case e cons) = Case (apply s e) cons'
  where cons' = map (\(p,exp) -> (apply s p, apply s exp)) cons
  
apply s e = error $ show e ++ "from apply"

minus :: Subst -> [Name] -> Subst
minus (Subst sub) x = Subst [(y, e) | (y, e) <- sub, not $ y `elem` x]

extend :: Subst -> Subst -> Subst
extend (Subst s1) (Subst s2) = Subst $ s2 ++ s1
-- extend (Subst s1) (Subst s2) = Subst $ [(x, normalize $ apply (Subst s1) e) | (x, e) <- s2] ++ s1


-- normalize type expresion
normalize :: Exp -> Exp
-- normalize r | trace ("normalize " ++ show r) False = undefined
normalize t = let t1 = norm t
                  t2 = norm t1
              in if t1 == t2 then t1 else normalize t2 -- `alphaEq`

norm Star = Star
norm (Var a) = Var a
norm (Const a) = Const a
norm (Lambda x t) = Lambda x (norm t)
norm (App (Lambda (Var x) t') t) = apply (Subst [(x, t)]) t'
norm (App (Var x) t) = App (Var x) (norm t)
norm (App (Const x) t) = App (Const x) (norm t)
norm (App t' t) = 
  case (App (norm t') (norm t)) of
    a@(App (Lambda x t') t) -> norm a
    b -> b
norm (Imply t t') = Imply (norm t) (norm t')
norm (Forall x t) = Forall x (norm t)
norm (Case e alts) = Case (norm e) alts'
  where alts' = map (\(p, exp) -> (p, norm exp)) alts

data Nameless = V Int
              | C Name
              | ALL Nameless
              | AP Nameless Nameless
              | IMP Nameless Nameless
              | LAM Nameless
             deriving (Show, Eq)

type BindCxt a = Reader [(Name, Int)] a

-- debruijn representation of type 
debruijn :: Exp -> BindCxt Nameless
debruijn (Const x) = return $ C x

debruijn (Var x) = do
  n' <- asks (lookup x)
  case n' of
    Just n -> return $ V n
    Nothing -> error $ show x ++ "from debruijn"


debruijn (Forall x f) = do 
  a <- local (((x,0):) . plus1) $ debruijn f 
  return $ ALL a
  
debruijn (App b1 b2) = do
  a <- debruijn b1
  a1 <- debruijn b2
  return $ AP a a1

debruijn (Imply b1 b2) = do
  a <- debruijn b1
  a1 <- debruijn b2
  return $ IMP a a1

debruijn (Lambda (Var x) f) = do
  a <- local (((x,0):) . plus1) $ debruijn f 
  return $ LAM a

plus1 = map $ \(x, y) -> (x, y + 1)

-- alphaEq of two type
alphaEq :: Exp -> Exp -> Bool
alphaEq t1 t2 =
    let t1' = foldl' (\t x -> Forall x t) t1 (freeVars t1)
        t2' = foldl' (\t x -> Forall x t) t2 (freeVars t2) in
    runReader (debruijn t1') [] == runReader (debruijn t2') []

{-
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
