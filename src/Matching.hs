{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Matching where
import Syntax

import Text.PrettyPrint
import Control.Monad.State.Lazy
import Control.Monad.Except
-- substitution
type Subst = [(String, Exp)]
data MatchState = MatchState {subst :: Subst, counter :: Int }
                deriving (Show)

newtype MatchMonad a = MatchMonad {runMatch :: StateT MatchState (Except Doc) a }
                     deriving (Functor, Applicative, Monad,
                                MonadState MatchState, MonadError Doc)

initMatchState = MatchState [] 0

match :: Exp -> Exp -> MatchMonad ()
match (Var x) e = undefined -- if x `elem` freeVars e then
                  --   return 
