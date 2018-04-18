nth :: [a] -> Int -> a
nth (x:xs) n | n==0 = x
             | n>0  = nth xs (n-1)
             
nth'nonfail :: [a] -> Int -> Bool
nth'nonfail xs n = n >= 0 && length (take (n+1) xs) == n+1
