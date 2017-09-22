-- import Test.QuickCheck
{-#LANGUAGE RankNTypes#-}

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

add :: Nat -> Nat -> Nat
add n m = n succ' m


f 0 x u = 1
f y x u | y > 0 = u x (y-1)

prop x y = g1 x y == g2 x y 
