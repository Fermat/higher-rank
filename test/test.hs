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

-- test :: Void
-- test = what (fix l'')

