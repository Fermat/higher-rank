module MatchingSpec where
import Matching
import Syntax
import Pretty
import Test.Hspec


      
spec :: Spec
spec = do
  describe "match" $ do
    it "can work as first order unification " $ do
      runMatch exp1 exp2 `shouldBe` [[("y", exp1)]]
      runMatch exp2 exp1 `shouldBe` [[("y", exp1)]]
      runMatch (Var "x") exp1 `shouldBe` [[]]
      runMatch (Var "x") (Var "x") `shouldBe` [[("x", Var "x")]]
      apply sub1 exp3 == apply sub1 exp4 `shouldBe` True
      apply sub2 exp3 == apply sub2 exp4 `shouldBe` True
      runMatch exp5 exp6 `shouldBe` [[]]
      runMatch exp5 exp7 `shouldBe` [[]]

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

sub1 = concat $ runMatch exp3 exp4
sub2 = concat $ runMatch exp4 exp3 
showTest1 = disp sub1

exp5 = Forall "x" (Imply (Var "x") (Var "x"))

exp6 = Forall "y" (Imply (Var "y") (Var "y"))

exp7 = Forall "y" (Imply (Var "z") (Var "z"))

exp8 = App (App (Var "d") (Const "Z")) (Const "Z")
exp9 = App (App (Const "D") (Const "Z")) (App (Const "S") (Const "Z"))
sub3 = disp $ concat $ runMatch exp8 exp9
