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
-- convert (Pos _ e) = convert e
convert (Imply x y) = App (App (Const "->" dummyPos) (convert x)) (convert y)
convert Star = Star
convert a@(Var _ _) = a
convert a@(Const _ _) = a
convert (App x y) = App (convert x) (convert y)
convert (Forall x e) = Forall x (convert e)
convert (Lambda x e) = Lambda x (convert e)
convert e = error $ show e ++ "from convert"
-- inversion of convert
invert Star = Star
invert a@(Var _ _) = a
invert a@(Const _ _) = a
invert (Forall x e) = Forall x (invert e)
invert (Lambda x e) = Lambda x (invert e)
invert (App (App (Const "->" _) x) y) = Imply (invert x) (invert y)
invert (App x y) = App (invert x) (invert y)

-- runMatch run the matching function, and postprocess the results by removing
-- unused substitutions and duplicatations

runMatch e1 e2 =
  let states = match ([(convert e1, convert e2)], [], Subst [], 0)
      fvs = freeVar e1 `S.union` freeVar e2
      subs = [sub | ([], vars, sub, _) <- states, apart sub, agree sub, apartEV sub vars]
      subs' = [ s'  | Subst s <- subs, 
                let s' = [(x, invert e) | (x, e) <- s, x `S.member` fvs]]
      subs'' = nub $ map S.fromList subs'
      subs''' = map (Subst . S.toList) subs'' 
  in subs'''

apartEV :: Subst -> [Name] -> Bool
apartEV (Subst sub) vars =
  let codom = concat $ map (eigenVar . snd) sub in
    null $ codom `intersect` vars
apart :: Subst -> Bool
apart (Subst sub) = let dom = map fst sub
                        codom = concat $ map (freeVars . snd) sub in 
                      null $ dom `intersect` codom

agree :: Subst -> Bool
agree (Subst s) =
  let xs = [(x, e) | (x, e) <- s,
                     let a = filter (\ (y, e') -> y == x) s,
                     all (\ (x', e'') -> e `alphaEq` e'') a]
  in length s == length xs 
  

type MatchState = ([(Exp, Exp)], [Name], Subst, Int)

match :: MatchState -> [MatchState]
match ((Star, Star):xs, vars, sub, i) = match (xs, vars, sub, i)

match ((Var a p, Var b p'):xs, vars, sub, i) | b == a = match (xs, vars, sub, i)
match ((Var a p, e):xs, vars, sub, i)
  | a `elem` freeVars e = []
  | otherwise =
    let newSub = Subst [(a, e)] in
      match (map (\ (a1, a2) -> (apply newSub a1, apply newSub a2)) xs,
              vars, extend newSub sub, i)
match ((e, Var a p):xs, vars, sub, i) = match ((Var a p, e):xs, vars, sub, i)

match ((Forall x e, (Forall y e')):xs, vars, sub, i)
  = let fresh = "u"++ show i ++ "#"
        e1 = apply (Subst [(x, Const fresh dummyPos)]) e
        e2 = apply (Subst [(y, Const fresh dummyPos)]) e' in
      match ((e1, e2):xs, fresh:vars, sub, i+1)

match ((e1, e2):res, vars, sub, i)
  | (Const x _):xs <- flatten e1,
    (Const y _):ys <- flatten e2,
    x == y, length xs == length ys = match (zip xs ys ++ res, vars, sub, i)

match ((e1, e2):res, vars, sub, i)
  | (Const x _):xs <- flatten e1,
    (Var z _):ys <- flatten e2 = match ((e2, e1):res, vars, sub, i)
    
match ((e1, e2):res, vars, sub, i)
  | (Var x p1):xs <- flatten e1,
    (Const y p2):ys <- flatten e2 =
      let argL = length xs
          argL' = length ys
          prjs = genProj argL
          (imi, j) = genImitation i (Const y p2) argL argL'
          iminew = normalize $ apply (Subst [(x, imi)]) e1
          newsubs = Subst [(x, imi)] : map (\ p -> Subst [(x, p)]) prjs
          neweqs = (iminew, e2) : map (\ x -> (x, e2)) xs
      in 
        concat [match (eq:res, vars, extend sub' sub, j) | (sub', eq) <- zip newsubs neweqs]
           
match ((e1, e2):res, vars, sub, i) = []
match ([], vars, sub, i) = [([], vars, sub, i)]
  
genProj :: Int -> [Exp]
genProj l =
  if l == 0 then []
  else let vars = map (\ y -> "x"++ show y ++ "#") $ take l [1..]
           ts = map (\ z ->
                        foldr (\ x y -> Lambda (Var x dummyPos) y) (Var z dummyPos) vars)
                vars
       in ts

genImitation :: Int -> Exp -> Int -> Int -> (Exp, Int)
genImitation n head arity arity' = 
  let l = take arity' [n..]
      lb = take arity [1..]
      n' = n + arity'
      fvars = map (\ x -> "h" ++ show x ++ "#") l
      bvars = map (\ x -> "m" ++ show x ++ "#") lb
      bvars' = map (\ x -> Var x dummyPos) bvars
      args = map (\ c -> (foldl' (\ z x -> App z x) (Var c dummyPos) bvars')) fvars
      body = foldl' (\ z x -> App z x) head args
      res = foldr (\ x y -> Lambda (Var x dummyPos) y) body bvars in
    (res, n')

                                        
  
