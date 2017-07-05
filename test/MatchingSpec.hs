module MatchingSpec where
import Matching
import Syntax
import Test.Hspec


      
spec :: Spec
spec = do
  describe "match" $ do
    it "can work as first order unification " $ do
      runMatch exp1 exp2 `shouldBe` [[("y", exp1)]]



exp1 = App (Var "x") (Const "C")
exp2 = Var "y"

