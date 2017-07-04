{-# LANGUAGE GeneralizedNewtypeDeriving, NamedFieldPuns #-}
module Matching where
import Syntax
import Pretty

import Text.PrettyPrint
import Control.Monad.State.Lazy
import Control.Monad.Except
import Data.List
-- substitution
type Subst = [(String, Exp)]

-- As we have second-order matching, the state will be a list of
-- all possible success substitutions
data MatchState = MatchState {subst :: [Subst], counter :: Int }
                deriving (Show)

updateSubst :: Subst -> MatchState -> MatchState
updateSubst sub s@(MatchState{subst}) = s{subst = map (extend sub) subst}

extend :: Subst -> Subst -> Subst
extend s1 s2 = [(x, apply s1 e) | (x, e) <- s2] ++ s1

-- fresh assumption: I am assuming the domain of the substitution
-- to be fresh variables.

apply :: Subst -> Exp -> Exp
apply s (Var x) = case lookup x s of
                    Nothing -> Var x
                    Just t -> t
apply s a@(Const _) = a
apply s (App f1 f2) = App (apply s f1) (apply s f2)
apply s (Imply f1 f2) = Imply (apply s f1) (apply s f2)
apply s (Forall x f2) = Forall x (apply s f2)

  
newtype MatchMonad a = MatchMonad {runM :: StateT Int [] a }
                     deriving (Functor, Applicative, Monad, MonadState Int)
                               

-- runMatchMonad :: MatchState -> MatchMonad a -> Either Doc (a, MatchState)
-- runMatchMonad s a = runExcept $ runStateT (runM a) s


-- initMatchState = MatchState [[]] 0

match :: Exp -> Exp -> MatchMonad Subst
match (Var x) e = if x `elem` freeVars e then
                    fail "occur check failures"
                  else return [(x, e)]


match (Imply a1 a2) (Imply b1 b2) = do s <- match a1 b1
                                       s' <- match (apply s a2) (apply s b2)
                                       return $ extend s' s

match (Forall x e) (Forall y e') = let e1 = apply [(x, Const x)] e
                                       e2 = apply [(y, Const x)] e' in
                                     do s <- match e1 e2
                                        if or $ map (elem x . eigenVar . snd) s
                                          then fail "eigen variable condition for forall"
                                          else return s

match (Const x) (Const y) = if x == y then return [] else fail "constructor mismatch"

match e (Var x) = if x `elem` freeVars e then
                    fail "occur check failures"
                  else return [(x, e)]

match e1 e2 | (Const x):xs <- flatten e1,
              (Const y):ys <- flatten e2,
              x == y,
              length xs == length ys =
                foldM (\ x (a, b) ->
                         do{s <- match (apply x a) (apply x b); return $ extend s x})
                [] (zip xs ys)

match e1 e2 | (Var x):xs <- flatten e1,
              (Var y):ys <- flatten e2,
              x == y,
              length xs == length ys =
                foldM (\ x (a, b) ->
                         do{s <- match (apply x a) (apply x b); return $ extend s x})
                [] (zip xs ys)
                

match e1 e2 | (Var x):xs <- flatten e1, y:ys <- flatten e2,
              (Var x) /= y  =
              do
                let argL = length xs
                    argL' = length ys
                    prjs = genProj argL
                imi <- genImitation y argL argL'
                let renew = normalize $ apply [(x, imi)] e1
                    pis = map (\ (a, b) -> (normalize $ apply [(x, a)] b, e2)) (zip prjs xs)
                    imiAndProj = (renew, e2) : pis
                    oldsubst = [(x, imi)]: map (\ y -> [(x,y)]) prjs
                bs <- sequence $ concat $
                      mapM (\ (a, b) -> map (\ u -> do{s <- match a b; return $ extend s u})
                                        oldsubst)
                      imiAndProj
                bs
                      
                
                      
               

              


genProj :: Int -> [Exp]
genProj l = if l == 0 then []
            else let vars = map (\ y -> "x"++ show y ++ "'") $ take l [1..]
                     ts = map (\ z ->
                                  foldr (\ x y -> Lambda (Var x) Nothing y) (Var z) vars) vars
                 in ts

genImitation :: Exp -> Int -> Int -> MatchMonad Exp
genImitation head arity arity' = 
  do n <- get
     let
       l = take arity' [n..]
       lb = take arity [1..]
       n' = n + arity'
       fvars = map (\ x -> "h" ++ show x ++ "'") l
       bvars = map (\ x -> "m" ++ show x ++ "'") lb
       bvars' = map Var bvars
       args = map (\ c -> (foldl' (\ z x -> App z x) (Var c) bvars')) fvars
       body = foldl' (\ z x -> App z x) head args
       res = foldr (\ x y -> Lambda (Var x) Nothing y) body bvars
     put n'
     return res
                                        
  
