module Syntax where


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
         | TApp Exp Exp
         | Lambda Exp Exp
         | Imply Exp Exp
         | Forall Name Exp
         | Abs Name Exp
         | Case Exp [(Exp, Exp)]
         | Let [(Exp, Exp)] Exp
         | Ann Exp Exp
         deriving (Show, Eq, Ord)


data Decl = DataDecl Exp Exp [(Exp, Exp)]
          | FunDecl Exp Exp [([Exp], Exp)]
          | Prim Exp Exp
          deriving (Show)


-- free variable of a type/kind exp
freeVars = S.toList . freeVar 

freeVar (Var x) =  S.insert x S.empty
freeVar (Const x) = S.empty
freeVar Star = S.empty
freeVar (App f1 f2) = (freeVar f1) `S.union` (freeVar f2)
freeVar (Forall x f) = S.delete x (freeVar f)
freeVar (Lambda p f) = freeVar f `S.difference` freeVar p
freeVar (Imply b h) = freeVar b `S.union` freeVar h

-- eigen variable of a type exp  
eigenVar = S.toList . eigen

eigen (Var x) = S.empty
eigen (Const x) = if isLower (head x) then S.insert x S.empty else S.empty
eigen (App f1 f2) = (eigen f1) `S.union` (eigen f2)
eigen (Forall x f) = S.delete x (eigen f)
eigen (Imply b h) = eigen b `S.union` eigen h
eigen (Lambda p f) = eigen f 



flatten :: Exp -> [Exp]
flatten (App f1 f2) = flatten f1 ++ [f2]
flatten a = [a]

flattenT :: Exp -> [Exp]
flattenT (TApp f1 f2) = flatten f1 ++ [f2]
flattenT a = [a]

getHB ::  Exp -> ([Exp],Exp)
getHB (Imply x y) = let (bs, t') = getHB y in (x:bs, t')
getHB t = ([], t)

getVars :: Exp -> ([Name],Exp)
getVars (Forall x t) = let (xs, t') = getVars t in (x:xs, t')
getVars t = ([], t)

separate f =
  let (vars, imp) = getVars f
      (bs, h) = getHB imp
  in (vars, h, bs)

isAtom (Const x) = True
isAtom (Var _) = True
isAtom _ = False

isVar (Var _) = True
isVar _ = False

erase (Const x) = Const x
erase (Var x) = Var x
erase (Abs x e) = erase e
erase (TApp e t) = erase e
erase (App a1 a2) = App (erase a1) (erase a2)

getName (Const x) = x
getName (Var x) = x
getName _ = error "from getName"

newtype Subst = Subst [(String, Exp)] deriving (Show, Eq)

apply' :: Subst -> Maybe Exp -> Maybe Exp
apply' s = fmap $ apply s

-- applying a substitution to a type or mixed type/term expression
-- the substitution is blind, i.e. no renaming of bound variables
apply :: Subst -> Exp -> Exp
apply (Subst s) (Var x) =
  case lookup x s of
    Nothing -> Var x
    Just t -> t
    
apply s a@(Const _) = a
apply s (App f1 f2) = App (apply s f1) (apply s f2)
apply s (TApp f1 f2) = TApp (apply s f1) (apply s f2)
apply s (Imply f1 f2) = Imply (apply s f1) (apply s f2)
apply s (Forall x f2) = Forall x (apply s f2)
apply s (Abs x f2) = Abs x (apply s f2)
apply s (Lambda (Ann (Var x) t) f2) =
  Lambda (Ann (Var x) (apply s t)) (apply s f2)
apply s (Lambda x f2) = Lambda x (apply s f2)
apply s Star = Star
apply s (Case e cons) = Case (apply s e) cons'
  where cons' = map (\(p,exp) -> (apply s p, apply s exp)) cons
apply s (Let defs e) = Let def' (apply s e)
  where def' = map (\(p, exp) -> (apply s p, apply s exp)) defs
apply s (Ann x e) = Ann (apply s x) (apply s e)  
-- apply s e = error $ show e ++ "from apply"


extend :: Subst -> Subst -> Subst
extend (Subst s1) (Subst s2) =
  Subst $ [(x, normalize $ apply (Subst s1) e) | (x, e) <- s2] ++ s1

normalize' :: Maybe Exp -> Maybe Exp
normalize' = fmap normalize

-- normalize a type/mixed term expression 
normalize :: Exp -> Exp
normalize t = let t1 = norm t
                  t2 = norm t1
              in if t1 == t2 then t1 else normalize t2 

norm Star = Star
norm (Var a) = Var a
norm (Const a) = Const a
norm (Ann a t) = Ann (norm a) (norm t)
norm (Lambda x t) = Lambda x (norm t)
norm (Abs x t) = Abs x (norm t)
norm (TApp t1 t2) = TApp (norm t1) (norm t2)
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
  where alts' = map (\(p, exp) -> (norm p, norm exp)) alts
norm (Let alts e) = Let alts' (norm e) 
  where alts' = map (\(p, exp) -> (norm p, norm exp)) alts

data Nameless = V Int
              | C Name
              | ALL Nameless
              | AP Nameless Nameless
              | IMP Nameless Nameless
              | LAM Nameless
              | S
             deriving (Show, Eq)

type BindCxt a = Reader [(Name, Int)] a
         
-- debruijn representation of a type expression
debruijn :: Exp -> BindCxt Nameless
debruijn (Const x) = return $ C x
debruijn (Star) = return $ S

debruijn (Var x) = 
  do n' <- asks (lookup x)
     case n' of
       Just n -> return $ V n
       Nothing -> error $ show x ++ "from debruijn"

debruijn (Forall x f) = 
  do a <- local (((x,0):) . plus1) $ debruijn f 
     return $ ALL a
  
debruijn (App b1 b2) = 
  do a <- debruijn b1
     a1 <- debruijn b2
     return $ AP a a1

debruijn (Imply b1 b2) = 
  do a <- debruijn b1
     a1 <- debruijn b2
     return $ IMP a a1

debruijn (Lambda (Var x) f) = 
  do a <- local (((x,0):) . plus1) $ debruijn f 
     return $ LAM a

debruijn a = error $ show a

plus1 = map $ \(x, y) -> (x, y + 1)

-- alpha equivalence of two type expressions
alphaEq :: Exp -> Exp -> Bool
alphaEq t1 t2 =
    let t1' = foldl' (\t x -> Forall x t) t1 (freeVars t1)
        t2' = foldl' (\t x -> Forall x t) t2 (freeVars t2) in
    runReader (debruijn t1') [] == runReader (debruijn t2') []

