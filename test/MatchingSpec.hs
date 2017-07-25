module MatchingSpec where
import Matching
import Syntax
import Pretty
import Test.Hspec
import Data.List

      
spec :: Spec
spec = do
  describe "match" $ do
    it "can work as first order unification " $ do
      runMatch exp1 exp2 `shouldBe` [Subst [("y", exp1)]]
      runMatch exp2 exp1 `shouldBe` [Subst [("y", exp1)]]
      runMatch (Var "x") exp1 `shouldBe` []
      runMatch (Var "x") (Var "x") `shouldBe` [Subst [("x",Var "x")]]
      and [apply s exp3 == apply s exp4 | s <- sub1] `shouldBe` True
      and [apply s exp3 == apply s exp4 | s <- sub2] `shouldBe` True
      runMatch exp5 exp6 `shouldBe` [Subst []]
      runMatch exp5 exp7 `shouldBe` []

--    it "can work as second order matching " $ do
      

exp1 = App (Var "x") (Const "C")
exp2 = Var "y"
exp3 = let hx = App (Const "H") (Var "x") in
  App hx (App hx (App (Const "F") (Var "y")))

exp4 = let gy = App (Const "G") (Var "y")
           a1 = (App (Const "H") gy)
           a2 = App a1 (Var "y")
       in
         App (App (Const "H") a2) (Var "z")

sub1 = runMatch exp3 exp4
sub2 = runMatch exp4 exp3 
-- showTest1 = disp sub1

exp5 = Forall "x" (Imply (Var "x") (Var "x"))

exp6 = Forall "y" (Imply (Var "y") (Var "y"))

exp7 = Forall "y" (Imply (Var "z") (Var "z"))

exp8 = App (App (Var "d") (Const "Z")) (Const "Z")
exp9 = App (App (Const "D") (Const "Z")) (App (Const "S") (Const "Z"))
sub3 = runMatch exp8 exp9
sub3' = disp $ nub $ map (\ (Subst x) -> head x) sub3

exp10 = App (Const "S") (Const "Z")
exp11 = App (Var "x") (Const "Z")
sub4 = runMatch exp11 exp10
sub5 = runMatch (Imply Star Star) (Imply Star (Var "x"))
exp12 = App (Const "S") (Var "a")
exp13 = App (Const "S") (Const "Z")
exp14 = App (App  (Var "x") (Lambda (Var "y") (Var "y"))) (Const "C")
exp15 = Forall "z" $ App (Const "F") (App (Var "x") (Var "z"))
exp16 = Forall "z" $ App (Var "x")  (App (Const "F") (Var "z"))
test1 = runMatch exp14 (Const "C")

exp17 = App (Var "x") (App (Var "y") (Const "C"))
exp18 = App (Const "Term") (App (Const "Tree") (App (Const "List") (Const "C")))

