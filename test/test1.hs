import Test.QuickCheck


g1 0 y | y >= 0 = y
g1 x 0 | x >= 0 = x
g1 x y | x > 0 && y > 0 = g1 x (y-1) + g1 (x-1) y
g1 x y | otherwise = -1

g2 0 y | y >= 0 = y
g2 x y | x > 0 && y >= 0 = f y x g2 + g2 (x-1) y
g2 x y | otherwise = -1


f 0 x u = 1
f y x u | y > 0 = u x (y-1)

prop x y = g1 x y == g2 x y 
