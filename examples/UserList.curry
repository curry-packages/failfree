--- Test for verification with user-defined polymorphic lists.

data MyList a = Nil | Cons a (MyList a)

--- Defining head on these lists:
head :: MyList a -> a
head (Cons x _) = x

head'nonfail xs = xs/=Nil

main = head (Cons 1 Nil)
