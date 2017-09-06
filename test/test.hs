{-# LANGUAGE KindSignatures, RankNTypes, GADTs #-}
data F :: * -> *
data Void :: *  
l :: forall x . F x -> F x  
l = undefined 

what :: (forall x . F x) -> Void
what = what



fix :: forall a . (a -> a) -> a
fix f = f (fix f)

l'' :: (forall x . F x) -> forall x . F x
l'' = l''

l' :: Void
l' = let y :: forall x . F x
         y = fix l
     in what y
u :: forall x . F x
u = u -- fix l''

v :: forall x . F (F x)
v = u

type Nat = forall x . (x -> x) -> x -> x

f :: forall x . F x -> forall x . F x
f = f
a :: F Void
a = a

test1 :: F Void
test1 = f a 

omegaHalf :: (forall a . a) -> forall a . a
omegaHalf x = x x x x 
-- zero :: Nat 
-- zero = \ s z -> z

-- app :: forall a . [a] -> [a] -> [a]
app = fix $ \ r f l -> case l of
                           [] -> []
                           x:xs -> f x : (r f xs)
  
-- suc :: Nat -> Nat
-- suc n = \ s z -> s (n s z)

-- add :: Nat -> Nat -> Nat
-- add n m = n suc m

-- test :: Void
-- test = what (fix l'')

data Term :: * -> * where
     Var :: forall a . a -> Term a
     App :: forall a . Term a -> Term a -> Term a
     Lam :: forall a . Term (Incr a) -> Term a

data Incr :: * -> * where
  Zero :: forall a . Incr a
  Succ :: forall a . a -> Incr a

mapI :: forall a b . (a -> b) -> Incr a -> Incr b
mapI f Zero = Zero
mapI f (Succ x) = Succ (f x)

-- mapT' :: forall a b. (a -> b) -> Term a -> Term b
data Nested a where
  NN :: forall a . Nested a
  NCons :: forall a . a -> Nested [a] -> Nested a

len :: forall a . Nested a -> Int
len NN = 0
len (NCons x xs) = 1 + len xs

fixN :: ((forall a . Nested a -> Int) -> forall a . Nested a -> Int) -> forall a . Nested a -> Int
fixN f = f (fixN f)

len' :: forall a . Nested a -> Int
len' = fixN $ \ r n -> case n of
                        NN -> 0
                        NCons x xs -> 1 + r xs

