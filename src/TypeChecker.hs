module TypeChecker where

import Syntax
import Pretty
import Matching
import KindChecker

import Text.PrettyPrint


type Pos = [Int] 

-- Global type environment
type TyEnv = [(Name, Exp)]

data Phi = Phi{
              position :: Pos,
              currentGoal :: Exp,
              currentProg :: Exp,
              env :: TyEnv,
              scope :: [Name] }
           deriving (Show)

-- Resolution state
data ResState = Res{
  kindDefs :: KindDef,
  fun :: Name,
  mixedTerm :: Exp,
  phi :: [Phi],
  errMessage :: Maybe Doc,
  counter :: Int
  } deriving (Show)

getHB ::  Exp -> ([Exp],Exp)
getHB (Imply x y) = let (bs, t') = getHB y in (x:bs, t')
getHB t = ([], t)

reImp :: [Exp] -> Exp -> Exp
reImp [] h = h
reImp (x:xs) h = Imply x (reImp xs h)

patternVars :: Exp -> Int -> (TyEnv, Int)
patternVars p i = let fvs = freeVars p
                      j = (i+(length fvs))-1
                      ns = [i..j]
                      vars = map (\ n -> Var $ "y"++show n++"'") ns in
                    (zip fvs vars, j)

makePatEnv :: [Exp] -> Int -> ([TyEnv], Int)
makePatEnv [] i = ([], i)
makePatEnv (x:xs) i = let (env, j) = patternVars x i
                          (res, n) = makePatEnv xs j in
                        (env:res, n)

-- Postion encoding scheme:
-- App 0 1
-- Lambda 0 1
-- Case 0 1 [(0, 0, 1), (1, 0, 1),... (n, 0, 1)]

replace :: Exp -> Pos -> Exp -> Exp
replace e [] r = r
replace (App t1 t2) (x:xs) r | x ==1 = App t1 (replace t2 xs r)
                             | x ==0 = App (replace t1 xs r) t2

replace (Lambda t t2) (x:xs) r | x == 1 = Lambda t (replace t2 xs r)
                               | x == 0 = Lambda (replace t xs r) t2

replace (Case e alts) (x:xs) r | x == 0 = Case (replace e xs r) alts
                               | x == 1 =
                                   case xs of
                                     [] -> error "internal: wrong position for case"
                                     y:y':ys -> Case e $ replaceL y y' ys alts r

replaceL y y' ys [] r = error "internal: wrong position for case branch"
replaceL 0 0 ys ((p,e):alts) r = ((replace p ys r), e):alts
replaceL 0 1 ys ((p,e):alts) r = (p, (replace e ys r)):alts
replaceL y y' ys (a:alts) r | y > 0 = a : replaceL (y-1) y' ys alts r
                                     

stream1 = 1 : stream1
takeOnes 1 = [[]]
takeOnes n | n > 1 = (take (n-1) stream1):takeOnes (n-1)
  
transit :: ResState -> [ResState]
transit (Res ks f pf ((Phi pos goal@(Imply _ _) exp@(Lambda _ _ ) gamma lvars):phi) Nothing i) =
  let (bs, h) = getHB goal
      (vars, b) = (viewLArgs exp, viewLBody exp)
      len = length vars
  in
      if len > length bs then
        let m' = Just $
                   text "the number of lambda abstractions is more than the body" $$
                   (nest 2 (text "current goal: " <+> disp goal)) $$ nest 2
                   (text "current program:"<+> disp exp) $$
                   (nest 2 $ text "current mixed proof term" $$ nest 2 (disp pf)) in
          [(Res ks f pf ((Phi pos goal exp gamma lvars):phi) m' i)]
      else let (thetas, j) = makePatEnv vars i
               h' = reImp (drop len bs) h  
               positionsVars = map (\ p -> pos ++ p ++[0]) (reverse $ takeOnes len)
               pairs = zip (zip (zip positionsVars bs) vars) thetas
               newEnv = map (\ (((pos', g), pat), thetaP) -> (Phi pos' g pat (thetaP++gamma) lvars)) pairs
               boPos = pos++(take (len-1) stream1)++[1]
               newEnv' = newEnv ++ [(Phi boPos h' b (concat thetas ++ gamma) lvars)]
               newLam = foldr (\ a b -> Lambda a b) h' (take len bs)
               pf' = replace pf pos newLam
           in [(Res ks f pf' (newEnv' ++ phi) Nothing j)]

transit (Res ks f pf ((Phi pos goal exp@(Case e alts) gamma lvars):phi) Nothing i) =
  let
    pats = map fst alts
    y = "y"++show i
    (thetas, j) = makePatEnv pats (i+1)
    altsEnv = undefined 
    newEnv = (Phi (pos++[0]) (Var y) e gamma lvars):altsEnv
