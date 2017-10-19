module Nested

data Pair' : Type -> Type where
  MkP : a -> a -> Pair' a

data Nested : Type -> Type where
  N : Nested a
  C : a -> Nested (Pair' a) -> Nested a
  
f : (n : Nat) -> Type -> Type
f Z a = a
f (S n) a = Pair' (f n a)

th1 : (n : Nat) -> Pair' (f n a) = f n (Pair' a)
th1 Z = Refl
th1 (S n) = cong (th1 n)

-- helper : (n : Nat) -> f n (Pair' a) -> f (S n) a
-- helper Z p = p
-- helper (S n) p = helper n p

fold : b -> ((n : Nat) -> f n a -> b -> b) -> Nested a -> b
fold e g N = e
fold e g (C a as) = g Z a (fold e ((\ n, p, b => g (S n) (?helper n p) b)) as)

 
