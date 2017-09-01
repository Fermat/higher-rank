{-# LANGUAGE KindSignatures, RankNTypes #-}
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

-- zero :: Nat 
-- zero = \ s z -> z

-- suc :: Nat -> Nat
-- suc n = \ s z -> s (n s z)

-- add :: Nat -> Nat -> Nat
-- add n m = n suc m

-- test :: Void
-- test = what (fix l'')

