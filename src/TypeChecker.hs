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

transit :: ResState -> [ResState]
transit = undefined
