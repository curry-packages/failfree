------------------------------------------------------------------------------
-- Non-failure conditions for Prelude operations.

solve'nonfail :: Bool -> Bool
solve'nonfail x = x

doSolve'nonfail :: Bool -> Bool
doSolve'nonfail x = x

head'nonfail :: [a] -> Bool
head'nonfail xs = not (null xs)

tail'nonfail :: [a] -> Bool
tail'nonfail xs = not (null xs)

foldr1'nonfail :: (a -> a -> a) -> [a] -> Bool
foldr1'nonfail _ xs = not (null xs)

foldl1'nonfail :: (a -> a -> a) -> [a] -> Bool
foldl1'nonfail _ xs = not (null xs)

anyOf'nonfail :: [a] -> Bool
anyOf'nonfail xs = not (null xs)

-- Non-failure condition for `&>`.
op_x263E'nonfail :: Bool -> a -> Bool
op_x263E'nonfail x _ = x

-- Non-failure condition for `!!`.
op_x2121'nonfail :: [a] -> Int -> Bool
op_x2121'nonfail xs n = n >= 0 && length (take (n+1) xs) == n+1

------------------------------------------------------------------------------
-- External operations:

-- Non-failure condition for `=:=`.
op_x3D3A3D'nonfail :: a -> a -> Bool
op_x3D3A3D'nonfail _ _ = False

-- Non-failure condition for `=:<=`.
op_x3D3A3C3D'nonfail :: a -> a -> Bool
op_x3D3A3C3D'nonfail _ _ = False

-- Non-failure condition for `=:<<=`.
op_x3D3A3C3C3D'nonfail :: a -> a -> Bool
op_x3D3A3C3C3D'nonfail _ _ = False

-- Non-failure condition for `&`.
op_x26'nonfail :: Bool -> Bool -> Bool
op_x26'nonfail x y = x && y

chr'nonfail :: Int -> Bool
chr'nonfail n = n>=0

div'nonfail :: Int -> Int -> Bool
div'nonfail x y = y/=0

mod'nonfail :: Int -> Int -> Bool
mod'nonfail x y = y/=0

divMod'nonfail :: Int -> Int -> Bool
divMod'nonfail x y = y/=0

quot'nonfail :: Int -> Int -> Bool
quot'nonfail x y = y/=0

rem'nonfail :: Int -> Int -> Bool
rem'nonfail x y = y/=0

quotRem'nonfail :: Int -> Int -> Bool
quotRem'nonfail x y = y/=0

------------------------------------------------------------------------------

