--- Computes the first element of a list.
head'nonfail xs = not (null xs)

head            :: [a] -> a
head (x:_)      = x

main = head "12"
