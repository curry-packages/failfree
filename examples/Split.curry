-- {-# OPTIONS_CYMAKE -F --pgmF=currypp --optF=contracts #-}

-- non-failure could be verified with contracts, i.e., with option '-c':
split :: (a -> Bool) -> [a] -> [[a]]
split _ []                 = [[]]
split p (x:xs) | p x       = [] : split p xs
               | otherwise = --let (ys:yss) = split p xs in (x:ys):yss
                             -- TODO: improve let reasoning in tool...
                             (x : head (split p xs)) : tail (split p xs)

split'post p xs ys = not (null ys)
