module Syntax where


import Control.Monad.Reader
import Control.Monad.State.Lazy
import Data.Char
import qualified Data.Set as S
import Data.List hiding (partition)
import Debug.Trace
import Text.Parsec.Pos
type Name = String

-- Variable convention: word begins with upper-case represents constant and
-- lower-case represents variable, lower-case constant represent eigenvariable

data Exp = Var Name SourcePos
         | Star
         | Const Name SourcePos
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
          | Syn Exp Exp Exp
          | TypeOperatorDecl String Int String
          | ProgOperatorDecl String Int String
          deriving (Show)


dummyPos = initialPos "dummy"

-- free variable of a type/kind exp
freeVars = S.toList . freeVar 
freeVar (Var x _) =  S.insert x S.empty
freeVar (Const x _) = S.empty
freeVar Star = S.empty
freeVar (App f1 f2) = (freeVar f1) `S.union` (freeVar f2)
freeVar (Forall x f) = S.delete x (freeVar f)
freeVar (Lambda p f) = freeVar f `S.difference` freeVar p
freeVar (Imply b h) = freeVar b `S.union` freeVar h

-- eigen variable of a type exp  
eigenVar = S.toList . eigen
eigen Star = S.empty
eigen (Var x _) = S.empty
eigen (Const x _) = if isLower (head x) then S.insert x S.empty else S.empty
eigen (App f1 f2) = (eigen f1) `S.union` (eigen f2)
eigen (Forall x f) = S.delete x (eigen f)
eigen (Imply b h) = eigen b `S.union` eigen h
eigen (Lambda p f) = eigen f 

flatten :: Exp -> [Exp]
flatten (App f1 f2) = flatten f1 ++ [f2]
flatten a = [a]

flattenT :: Exp -> [Exp]
flattenT (TApp f1 f2) = flattenT f1 ++ [f2]
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

isAtom (Const x _) = True
isAtom (Var _ _) = True
isAtom _ = False

isVar (Var _ _) = True
isVar _ = False

erase (Const x p) = Const x p
erase (Var x p) = Var x p
erase (Abs x e) = erase e
erase (TApp e t) = erase e
erase (App a1 a2) = App (erase a1) (erase a2)

getName (Const x _) = x
getName (Var x _) = x
getName a = error ("from getName: " ++ show a)

getPos (Const _ x) = x
getPos (Var _ x) = x
getPos a = error ("from getPos: " ++ show a)


newtype Subst = Subst [(String, Exp)] deriving (Show, Eq)


-- applying a substitution to a type or mixed type/term expression
-- the substitution is blind, i.e. no renaming of bound variables
apply :: Subst -> Exp -> Exp
apply (Subst s) (Var x p) =
  case lookup x s of
    Nothing -> Var x p
    Just t -> t  
    
apply s a@(Const _ _) = a
apply s (App f1 f2) = App (apply s f1) (apply s f2)
apply s (TApp f1 f2) = TApp (apply s f1) (apply s f2)
apply s (Imply f1 f2) = Imply (apply s f1) (apply s f2)
apply s (Forall x f2) = Forall x (apply (minus s [x]) f2)
apply s (Abs x f2) = Abs x (apply (minus s [x]) f2)
apply s (Lambda (Ann p t) f2) =
  Lambda (Ann (apply s p) (apply s t)) (apply s f2)
-- type level lambda  
apply s (Lambda (Var x p) f2) =
  Lambda (Var x p) (apply (minus s [x]) f2)
  
-- apply s (Lambda x f2) = Lambda x (apply (minus s $ freeVars x) f2)
apply s Star = Star
apply s (Case e cons) = Case (apply s e) cons'
  where cons' = map (\(p,exp) -> (p, apply s exp)) cons
apply s (Let defs e) = Let def' (apply s e)
  where def' = map (\(Ann p t, exp) -> (Ann p (apply s t), apply s exp)) defs
apply s (Ann x e) = Ann (apply s x) (apply s e)  
-- apply s e = error $ show e ++ "from apply"

minus (Subst sub) fv = Subst $ [ (x, e) | (x, e) <- sub, not $ x `elem` fv]

extend :: Subst -> Subst -> Subst
extend (Subst s1) (Subst s2) =
  Subst $ [(x, normalize $ apply (Subst s1) e) | (x, e) <- s2] ++ s1

eta (Lambda (Var x p) t) =
  case eta t of
    App t' e' | isVar e' && getName e' == x -> 
                let fv = freeVars t' in
                  if not (x `elem` fv) then t'
                  else Lambda (Var x p) (App t' e')
    c -> Lambda (Var x p) c
eta (App e1 e2) = App (eta e1) (eta e2)
eta a = a

-- normalize a type/mixed term expression without type definitions 
normalize :: Exp -> Exp
normalize t = eta $ norm [] t

norm g Star = Star
norm g (Var a p) = Var a p
norm g (Const a p) =
  case lookup a g of
    Nothing -> Const a p
    Just b -> norm g b
norm g (Ann a t) = Ann (norm g a) (norm g t)
norm g (Lambda x t) =  Lambda (norm g x) (norm g t)
norm g (Abs x t) = Abs x (norm g t)
norm g (TApp t1 t2) = TApp (norm g t1) (norm g t2)
norm g (App (Lambda (Var x p) t') t) = norm g $ runSubst t (Var x p) t'
norm g (App t' t) = 
  case (App (norm g t') (norm g t)) of
    a@(App (Lambda x t') t) -> norm g a
    b -> b
norm g (Imply t t') = Imply (norm g t) (norm g t')
norm g (Forall x t) = Forall x (norm g t)
norm g (Case e alts) = Case (norm g e) alts'
  where alts' = map (\(p, exp) -> (norm g p, norm g exp)) alts
norm g (Let alts e) = Let alts' (norm g e) 
  where alts' = map (\(p, exp) -> (norm g p, norm g exp)) alts

-- normalizeTy t g | trace ("normalizeTy " ++show ("hi") ++"\n") False = undefined
normalizeTy t g = eta $ norm g t

type GVar a = State Int a

runSubst :: Exp -> Exp -> Exp -> Exp
runSubst t x t1 = fst $ runState (subst t x t1) 0
  
subst :: Exp -> Exp -> Exp -> GVar Exp
subst s (Var x _) (Const y p) = return $ Const y p

subst s (Var x p1) (Var y p2) =
  if x == y then return s else return $ Var y p2
                               
subst s (Var x p) (Imply f1 f2) = do
  c1 <- subst s (Var x p) f1
  c2 <- subst s (Var x p) f2
  return $ Imply c1 c2

subst s (Var x p) (App f1 f2) = do
  c1 <- subst s (Var x p) f1
  c2 <- subst s (Var x p) f2
  return $ App c1 c2

subst s (Var x p) (Forall a f) =
  if x == a || not (x `elem` freeVars f) then return $ Forall a f
  else if not (a `elem` freeVars s)
       then do
         c <- subst s (Var x p) f
         return $ Forall a c
       else do
         n <- get
         modify (+1)
         c1 <- subst (Var (a++ show n++"#") p) (Var a p) f
         subst s (Var x p) (Forall (a ++ show n ++"#") c1)

subst s (Var x p1) (Lambda (Var a p2) f) =
  if x == a || not (x `elem` freeVars f) then return $ Lambda (Var a p2) f
  else if not (a `elem` freeVars s)
       then do
         c <- subst s (Var x p1) f
         return $ Lambda (Var a p2) c
       else do
         n <- get
         modify (+1)
         c1 <- subst (Var (a++ show n++ "#") p2) (Var a p2) f
         subst s (Var x p1) (Lambda (Var (a ++ show n++"#") p2) c1)         

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
debruijn (Const x _) = return $ C x
debruijn (Star) = return $ S

debruijn (Var x _) = 
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

debruijn (Lambda (Var x _) f) = 
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

