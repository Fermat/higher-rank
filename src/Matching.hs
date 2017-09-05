module Matching where
import Syntax
import Pretty

import Text.PrettyPrint
import Control.Monad.State.Lazy
import Control.Monad.Except
import Data.List
import qualified Data.Set as S
import Debug.Trace
-- As we have second-order matching, the state will be a list of
-- all possible success substitutions
-- list of success pattern, [] indicates failure, (Subst []) indicates identity sub 

-- convert a type expression that contains Imply to App (Const "->")
convert :: Exp -> Exp
convert (Imply x y) = App (App (Const "->") (convert x)) (convert y)
convert Star = Star
convert a@(Var _) = a
convert a@(Const _) = a
convert (App x y) = App (convert x) (convert y)
convert (Forall x e) = Forall x (convert e)

-- inversion of convert
invert Star = Star
invert a@(Var _) = a
invert a@(Const _) = a
invert (Forall x e) = Forall x (invert e)
invert (Lambda x e) = Lambda x (invert e)
invert (App (App (Const "->") x) y) = Imply (invert x) (invert y)
invert (App x y) = App (invert x) (invert y)

-- runMatch run the matching function, and postprocess the results by removing
-- unused substitutions and duplicatations

runMatch e1 e2 =
  let subs = evalState (match (convert e1) (convert e2)) 0
      fvs = freeVar e1 `S.union` freeVar e2
      subs' = [ s'  | Subst s <- subs, agree s, 
                      let s' = [(x, invert e) | (x, e) <- s, x `S.member` fvs]]
      subs'' = nub $ map S.fromList subs'
      subs''' = map (Subst . S.toList) subs'' 
  in subs'''

agree :: [(Name, Exp)] -> Bool
agree s =
  let xs = [(x, e) | (x, e) <- s,
                     let a = filter (\ (y, e') -> y == x) s,
                     all (\ (x', e'') -> e `alphaEq` e'') a]
  in length s == length xs 
  

-- match two types expression or two kind expression

match :: Exp -> Exp -> State Int [Subst]
-- match e1 e2 | trace ("\n matching " ++ show (disp e1) ++"\n" ++ show (disp e2)) False = undefined
match Star Star = return [Subst []]
match (Var x) e | (Var x) == e = return $ [Subst []]
                | x `elem` freeVars e = return []
                | otherwise = return $ [Subst [(x, e)]]

match (Forall x e) (Forall y e') =
  let e1 = apply (Subst [(x, Const x)]) e
      e2 = apply (Subst [(y, Const x)]) e' in
    do s <- match e1 e2
       let res = [ ss | ss@(Subst sub) <- s,
                   and $ map ((not . elem x) . eigenVar . snd) sub ]
       return res
                                          
match e (Var x) | (Var x) == e = return [Subst []]
                | x `elem` freeVars e = return []
                | otherwise = return [Subst [(x, e)]]

-- rigid-rigid first-order simp
match e1 e2 | (Const x):xs <- flatten e1,
              (Const y):ys <- flatten e2,
              x == y, length xs == length ys =
                foldM (\ x (a, b) ->
                          do{s' <- mapM (\ sub ->
                                            match (normalize $ apply sub a)
                                            (normalize $ apply sub b))
                                   x;
                             return $
                              concat [map (\ y -> extend y sub') subs
                                     | (sub', subs) <- zip x s']})
                [Subst []] (zip xs ys)

-- first-order simp
match e1 e2 | (Var x):xs <- flatten e1,
              (Var y):ys <- flatten e2,
              x == y,
              length xs == length ys =
                foldM (\ x (a, b) ->
                          do{s' <- mapM (\ sub -> match (normalize $ apply sub a)
                                                  (normalize $ apply sub b))
                                   x;
                             return $ concat [map (\ y -> extend y sub') subs
                                             | (sub', subs) <- zip x s']})
                [Subst []] (zip xs ys)

-- braiding
match e1 e2 | (Const x):xs <- flatten e1, (Var z):ys <- flatten e2  = match e2 e1

-- rigid-flexible, 
match e1 e2 | (Var x):xs <- flatten e1, (Const y):ys <- flatten e2 =
                do let argL = length xs
                       argL' = length ys
                       prjs = genProj argL
                   imi <- genImitation (Const y) argL argL'
                   let renew = normalize $ apply (Subst [(x, imi)]) e1
                       pis = map (\ (a, b) ->
                                  (normalize $ apply (Subst [(x, a)]) b,
                                    e2)) -- normalize $ apply (Subst [(x, a)]) 
                             (zip prjs xs)
                       imiAndProj = (renew, e2) : pis -- normalize $ apply (Subst [(x, imi)]) e2
                       oldsubst = [(x, imi)]: map (\ y -> [(x,y)]) prjs
                   bs <- mapM (\ ((a, b), u) ->
                                  do{s <- match a b;
                                     return $ map (\ y -> extend y (Subst u)) s})
                         (zip imiAndProj oldsubst)
                   return $ concat bs

match e1 e2 = return [] -- error $ show (disp e1 <+> disp e2) --  

genProj :: Int -> [Exp]
genProj l =
  if l == 0 then []
  else let vars = map (\ y -> "x"++ show y ++ "#") $ take l [1..]
           ts = map (\ z -> foldr (\ x y -> Lambda (Var x) y) (Var z) vars) vars
       in ts

genImitation :: Exp -> Int -> Int -> State Int Exp
genImitation head arity arity' = 
  do n <- get
     let
       l = take arity' [n..]
       lb = take arity [1..]
       n' = n + arity'
       fvars = map (\ x -> "h" ++ show x ++ "#") l
       bvars = map (\ x -> "m" ++ show x ++ "#") lb
       bvars' = map Var bvars
       args = map (\ c -> (foldl' (\ z x -> App z x) (Var c) bvars')) fvars
       body = foldl' (\ z x -> App z x) head args
       res = foldr (\ x y -> Lambda (Var x) y) body bvars
     put n'
     return res
                                        
  
