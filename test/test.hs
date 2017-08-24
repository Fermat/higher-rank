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

type Nat = forall x . (x -> x) -> x -> x

zero :: Nat 
zero = \ s z -> z

suc :: Nat -> Nat
suc n = \ s z -> s (n s z)

add :: Nat -> Nat -> Nat
add n m = n suc m

-- test :: Void
-- test = what (fix l'')

