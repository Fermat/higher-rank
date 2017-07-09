{-# LANGUAGE GeneralizedNewtypeDeriving, NamedFieldPuns #-}
module Matching where
import Syntax
import Pretty

import Text.PrettyPrint
import Control.Monad.State.Lazy
import Control.Monad.Except
import Data.List
import qualified Data.Set as S
-- As we have second-order matching, the state will be a list of
-- all possible success substitutions
-- list of success pattern, [] indicates failure, identity sub for free var is x |-> x.

-- fresh assumption: I am assuming the domain of the substitution
-- to be fresh variables.

-- runMatch run the matching function, and postprocess the results by removing
-- duplications and unused substitutions for generated variables.
runMatch e1 e2 = let subs = evalState (match e1 e2) 0
                     fvs = freeVar e1 `S.union` freeVar e2
                     subs' = [ s'  | Subst s <- subs,
                               let s' = [ (x, e) | (x, e) <- s, x `S.member` fvs]]
                     subs'' = nub $ map S.fromList subs'
                     subs''' = map (Subst . S.toList) subs'' 
                             
  in subs'''
                   
match :: Exp -> Exp -> State Int [Subst]

match (Var x) e | (Var x) == e = return $ [Subst [(x, e)]]
                | x `elem` freeVars e = return []
                | otherwise = return $ [Subst [(x, e)]]

match (Imply a1 a2) (Imply b1 b2) = do s <- match a1 b1
                                       s' <- mapM (\ sub -> match (apply sub a2) (apply sub b2))
                                             s
                                       let res = [map (\ x -> extend x sub) subs |
                                                  sub <- s, subs <- s']
                                       return $ concat res

match (Forall x e) (Forall y e') = let e1 = apply (Subst [(x, Const x)]) e
                                       e2 = apply (Subst [(y, Const x)]) e' in
                                     do s <- match e1 e2
                                        let res = [ ss | ss@(Subst sub) <- s,
                                                    and $ map ((not . elem x) . eigenVar . snd) sub ]
                                        return res
                                          

match e (Var x) | (Var x) == e = return [Subst [(x, e)]]
                | x `elem` freeVars e = return []
                | otherwise = return [Subst [(x, e)]]

match e1 e2 | (Const x):xs <- flatten e1,
              (Const y):ys <- flatten e2,
              x == y,
              length xs == length ys =
                foldM (\ x (a, b) ->
                          do{s' <- mapM (\ sub -> match (apply sub a) (apply sub b)) x;
                             return $ concat [map (\ y -> extend y sub) subs
                                             | sub <- x, subs <- s']})
                [Subst []] (zip xs ys)

match e1 e2 | (Var x):xs <- flatten e1,
              (Var y):ys <- flatten e2,
              x == y,
              length xs == length ys =
                foldM (\ x (a, b) ->
                          do{s' <- mapM (\ sub -> match (apply sub a) (apply sub b)) x;
                             return $ concat [map (\ y -> extend y sub) subs
                                             | sub <- x, subs <- s']})
                [Subst []] (zip xs ys)

                
match e1 e2 | (Var x):xs <- flatten e1, y:ys <- flatten e2,
              (Var x) /= y  =
              do
                let argL = length xs
                    argL' = length ys
                    prjs = genProj argL
                imi <- genImitation y argL argL'
                let renew = normalize $ apply (Subst [(x, imi)]) e1
                    pis = map (\ (a, b) -> (normalize $ apply (Subst [(x, a)]) b, e2)) (zip prjs xs)
                    imiAndProj = (renew, e2) : pis
                    oldsubst = [(x, imi)]: map (\ y -> [(x,y)]) prjs
                bs <- mapM (\ ((a, b), u) -> do{s <- match a b;
                                                return $ map (\ y -> extend y (Subst u)) s})
                      (zip imiAndProj oldsubst)
                return $ concat bs

match e1 e2 = return [] 

genProj :: Int -> [Exp]
genProj l = if l == 0 then []
            else let vars = map (\ y -> "x"++ show y ++ "'") $ take l [1..]
                     ts = map (\ z ->
                                  foldr (\ x y -> Lambda (Var x) Nothing y) (Var z) vars) vars
                 in ts

genImitation :: Exp -> Int -> Int -> State Int Exp
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
                                        
  
