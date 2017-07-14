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

patternVars :: Exp -> Int -> (TyEnv, Int)
patternVars p i = let fvs = freeVars p
                      j = (i+(length fvs))-1
                      ns = [i..j]
                      vars = map (\ n -> Var $ "y"++show n++"'") ns in
                    (zip fvs vars, j)

-- makePatEnv :: [Exp] -> Int -> ([TyEnv], Int)


transit :: ResState -> [ResState]
transit (Res ks f pf ((Phi pos goal@(Imply _ _) exp@(Lambda _ _ ) gamma lvars):phi) Nothing i) =
  let (bs, h) = getHB goal
      (vars, b) = (viewLArgs exp, viewLBody exp) in
      if length vars < length bs then
        let m' = Just $
                   text "arity mismatch when handling lambda abstraction" $$
                   (nest 2 (text "current goal: " <+> disp goal)) $$ nest 2
                   (text "current program:"<+> disp exp) $$
                   (nest 2 $ text "current mixed proof term" $$ nest 2 (disp pf)) in
          [(Res ks f pf ((Phi pos goal exp gamma lvars):phi) m' i)]
      else undefined -- let theta = foldr (\ n pat -> patternVars pat i) i vars i
  

