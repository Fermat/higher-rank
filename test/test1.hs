-- import Test.QuickCheck
{-#LANGUAGE RankNTypes, KindSignatures, GADTs#-}

g1 0 y | y >= 0 = y
g1 x 0 | x >= 0 = x
g1 x y | x > 0 && y > 0 = g1 x (y-1) + g1 (x-1) y
g1 x y | otherwise = -1

g2 0 y | y >= 0 = y
g2 x y | x > 0 && y >= 0 = f y x g2 + g2 (x-1) y
g2 x y | otherwise = -1

type Pair a b =  forall x . (a -> b -> x) -> x

pair :: forall a b . a -> b -> Pair a b
pair x y = \ f -> f x y

test :: Pair Int Int
test = pair 1 1

fst' :: forall a b . Pair a b -> a
fst' = \ p -> p (\ a b -> a)

type Nat = forall x . (x -> x) -> x -> x

zero :: Nat
zero = \ s z -> z

succ' :: Nat -> Nat
succ' n = \ s z -> s (n s z)

-- add :: Nat -> Nat -> Nat
-- add n m = n succ' m


f 0 x u = 1
f y x u | y > 0 = u x (y-1)

prop x y = g1 x y == g2 x y 

data PTerm :: * -> * where
  PVar :: forall a . a -> PTerm a
  PApp :: forall a . PTerm a -> PTerm a -> PTerm a
  PAbs :: forall a . (a -> PTerm a) -> PTerm a

pid :: forall a . PTerm a
pid = PAbs PVar


numVars :: PTerm () -> Int
numVars (PVar x) = 1
numVars (PApp e1 e2) =  (numVars e1) + (numVars e2)
numVars (PAbs e') = numVars (e' ())

numVars' :: (forall a . PTerm a) -> Int
numVars' e = numVars e

type PTerm1 = forall a . a -> PTerm a

subst :: forall a . PTerm (PTerm a) -> PTerm a
subst (PVar e) = e
subst (PApp e1 e2) = PApp (subst e1) (subst e2)
subst (PAbs e) = PAbs (\ x -> subst (e (PVar x)))

subst' :: PTerm1 -> (forall a . PTerm a) -> (forall a . PTerm a)
subst' e1 e2 = subst (e1 e2)
