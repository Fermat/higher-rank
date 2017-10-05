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
      runMatch (Var "x" dummyPos) exp1 `shouldBe` []
      runMatch (Var "x" dummyPos) (Var "x" dummyPos) `shouldBe` [Subst []]
      and [apply s exp3 == apply s exp4 | s <- sub1] `shouldBe` True
      and [apply s exp3 == apply s exp4 | s <- sub2] `shouldBe` True
      runMatch exp5 exp6 `shouldBe` [Subst []]
      runMatch exp5 exp7 `shouldBe` []

--    it "can work as second order matching " $ do
      

exp1 = App (Var "x" dummyPos) (Const "C" dummyPos)
exp2 = Var "y" dummyPos
exp3 = let hx = App (Const "H" dummyPos) (Var "x" dummyPos) in
  App hx (App hx (App (Const "F" dummyPos) (Var "y" dummyPos)))

exp4 = let gy = App (Const "G" dummyPos) (Var "y" dummyPos)
           a1 = (App (Const "H" dummyPos) gy)
           a2 = App a1 (Var "y" dummyPos)
       in
         App (App (Const "H" dummyPos) a2) (Var "z" dummyPos)

sub1 = runMatch exp3 exp4
sub2 = runMatch exp4 exp3 
-- showTest1 = disp sub1

exp5 = Forall "x" (Imply (Var "x" dummyPos) (Var "x" dummyPos))

exp6 = Forall "y" (Imply (Var "y" dummyPos) (Var "y" dummyPos))

exp7 = Forall "y" (Imply (Var "z" dummyPos) (Var "z" dummyPos))

exp8 = App (App (Var "d" dummyPos) (Const "Z" dummyPos)) (Const "Z" dummyPos)
exp9 = App (App (Const "D" dummyPos) (Const "Z" dummyPos)) (App (Const "S" dummyPos) (Const "Z" dummyPos))
sub3 = map disp $ runMatch exp8 exp9
--sub3' = disp $ nub $ map (\ (Subst x) -> head x) sub3

exp10 = App (Const "S" dummyPos) (Const "Z" dummyPos)
exp11 = App (Var "x" dummyPos) (Const "Z" dummyPos)
sub4 = map disp $ runMatch exp11 exp10
sub5 = map disp $ runMatch (Imply Star Star) (Imply Star (Var "x" dummyPos))
exp12 = App (Const "S" dummyPos) (Var "a" dummyPos)
exp13 = App (Const "S" dummyPos) (Const "Z" dummyPos)
exp14 = App (App  (Var "x" dummyPos) (Lambda (Var "y" dummyPos) (Var "y" dummyPos))) (Const "C" dummyPos)
exp15 = Forall "z" $ App (Const "F" dummyPos) (App (Var "x" dummyPos) (Var "z" dummyPos))
exp16 = Forall "z" $ App (Var "x" dummyPos)  (App (Const "F" dummyPos) (Var "z" dummyPos))
test1 = map disp $ runMatch exp14 (Const "C" dummyPos)

exp17 = App (Var "f" dummyPos) (App (Var "g" dummyPos) (Const "String" dummyPos))
exp19 = Const "String" dummyPos
exp20 = (App (Var "g" dummyPos) (Const "String" dummyPos))
exp18 =  (Imply (Const "String" dummyPos) (Imply (Const "Int" dummyPos) (Const "String" dummyPos)))
-- test2 = map disp $ runMatch' (exp17) exp18
-- test3 = map disp $ runMatch'' (exp17) exp18
-- minimal test case for matching.
-- test4 = map disp $ runMatch' (exp17) (Imply (Const "String") (Const "String"))
-- test5 = map disp $ runMatch'' (exp17) (Imply (Const "String") (Const "String"))
-- test6 = map disp $ runMatch'' (App (Var "p") (App (Const "F") (Var "x"))) (App (Const "F") (Var "y"))

-- test7 = map disp $ runMatch' (App (Var "p") (App (Const "F") (Var "x"))) (App (Const "F") (Var "y"))

-- exp21 =  (App (Const "C") (App (Var "x") (Const "Nil")))
exp22 =  (App (Var "x" dummyPos) (App (Const "C" dummyPos) (Const "Nil" dummyPos)))
exp23 =  (App (Var "C" dummyPos) (App (Var "x" dummyPos) (Const "Nil" dummyPos)))
exp24 =  (Forall "a" (Forall "b" (Var "a" dummyPos))) -- (App (Const "C") (Var "a")) -- (Var "a") --(App (Const "D") (Var "a")) -- Imply (App (Const "C") (Var "a")) (App (Const "D") (Var "a"))
exp25 =  (Forall "a" (Forall "c" (Var "c" dummyPos))) -- (Const "E") --(App (Const "D") (Const "E"))  -- Imply (App (Var "m") (Const "E")) (App (Const "D") (Const "E"))

test7 = map disp $ runMatch exp25 exp24
test8 = map disp $ runMatch exp22 exp23

exp26 = Imply (App (Var "p" dummyPos) (Const "Bot" dummyPos)) (App (Var "p" dummyPos) (Const "N" dummyPos))
exp27 = Imply (App (Const "F" dummyPos) (Const "Bot" dummyPos)) (App (Const "F" dummyPos) (Const "N" dummyPos))

exp28 = Lambda (Var "m1" dummyPos)
        (Lambda (Var "m2" dummyPos)
         (Lambda (Var "m3" dummyPos)
          (App (App (App (Const "F" dummyPos) (Var "m1" dummyPos)) (Var "m2" dummyPos)) (Var "m3" dummyPos))))
          
test9 = map disp $ runMatch exp26 exp27
test10 = eta exp28

exp29 = App (Var "p7" dummyPos) (App (App (Const "G" dummyPos) (App (App (App (Const "F" dummyPos) (Const "Z" dummyPos)) (Var "x8" dummyPos)) (App (Const "S" dummyPos) (Var "y9" dummyPos)))) (App (App (App (Const "F" dummyPos) (Var "x8" dummyPos)) (Var "y9" dummyPos)) (App (Const "S" dummyPos) (App (Const "S" dummyPos) (Const "Z" dummyPos)))))
exp29' = App (Var "p7" dummyPos) (Const "P" dummyPos)
exp30' = App (Const "P4" dummyPos) (App (Var "p" dummyPos) (Const "P" dummyPos))
exp30 = App (Const "P4" dummyPos) (App (App (App (Var "qa1" dummyPos) (App (App (App (Const "F" dummyPos) (Const "Z" dummyPos)) (Const "X5" dummyPos)) (App (Const "S" dummyPos) (Const "Y6" dummyPos)))) (Const "X5" dummyPos)) (Const "Y6" dummyPos))

test11 = map disp $ runMatch exp29 exp30
test11' = map disp $ runMatch exp29' exp30'
exp31 = Imply (App (Var "p7" dummyPos) exp29) (App (Var "p7" dummyPos) (App (App (App (Const "F" dummyPos) (Const "Z" dummyPos)) (App (Const "S" dummyPos) (Var "x8" dummyPos))) (Var "y9" dummyPos)))

exp32 = Imply (App (Const "P4" dummyPos) exp30) (App (Const "P4" dummyPos) (App (App (App (Const "F" dummyPos) (Const "Z" dummyPos)) (App (Const "S" dummyPos) (Const "X5" dummyPos))) (Const "Y6" dummyPos)))

test12 = map disp $ runMatch exp31 exp32
  -- can't match p7# (G (F Z x8# (S y9#)) (F x8# y9# (S (S Z))))
  --             ->
  --               p7# (F Z (S x8#) y9#)
  -- against [p4#] (qa1# (F Z [x5#] (S [y6#])) [x5#] [y6#])
  --         ->
  --           [p4#] (F Z (S [x5#]) [y6#])
  --   when applying k : forall p x y .
  --                       p (G (F Z x (S y)) (F x y (S (S Z)))) -> p (F Z (S x) y)
  --   current expression: k
  --   current mixed proof term
  --     g1 @(\ x1# . x1#) @qa1# @qb2# @F


