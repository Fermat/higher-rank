{-# LANGUAGE GeneralizedNewtypeDeriving, NamedFieldPuns #-}
module Matching where
import Syntax
import Pretty
import Text.PrettyPrint
import Control.Monad.State.Lazy
import Control.Monad.Except

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

  
newtype MatchMonad a = MatchMonad {runM :: StateT MatchState (Except Doc) a }
                     deriving (Functor, Applicative, Monad,
                                MonadState MatchState, MonadError Doc)

runMatchMonad :: MatchState -> MatchMonad a -> Either Doc (a, MatchState)
runMatchMonad s a = runExcept $ runStateT (runM a) s


initMatchState = MatchState [] 0

-- match :: Exp -> Exp -> MatchMonad ()
-- match (Var x) e = if x `elem` freeVars e then
--                     throwError $ text "variable" <+> text x <+> text "in" <+> disp e
--                   else do 
