failfree: A tool for verifying fail-free Curry programs
=======================================================

Basic idea of the tool:
-----------------------

The objective is this tool is to verify that all operations are non-failing,
i.e., their evaluation does not result in a failure, if they are called with
the correct arguments which satisfy the non-failing precondition of
the operation.

Example:

    -- The operation `head` does not fail if this precondition is satisfied:
    head_nonfail xs = not (null xs)
    
    head (x:xs) = x

Note that the non-failing precondition is not a precondition for `head`,
i.e., it is still allowed to use `head` in a logical setting.
However, it can be used to verify that the following operation
is non-failing:

    readCommand = do
      putStr "Input a command:"
      s <- getLine
      let ws = words s
      if null ws then readCommand
                 else processCommand (head ws) (tail ws)

The following techniques to verify non-failing properties are used:

1. Test whether the operation is pattern-completely defined
   (i.e., branches on all patterns in all or-branches)
   for all inputs satisfying the non-failing precondition.
   If this is not the case, the operation is possibly failing.

2. Test whether the operations called in the right-hand side
   are used with satisfied non-failing preconditions
   for all inputs satisfying the non-failing precondition.
    
3. Test whether a call to `Prelude.fail` is unreachable, e.g., in
    
     abs x = if x>=0 then x else if x<0 then (0 - x) else fail

   Note that this might be the result translating the following definition:

     abs x | x>=0 = x
           | x<0  = 0 - x

   This requires SMT solving...


Depending on the state of the operation `error`,
this could also avoid the occurrence of run-time errors:

    readLine :- do
      putStr "Input a non-empty string:"
      s <- getLine
      if null s then error "Empty input!"
                else do putStr "First char: "
                        putStrLn (head s)

If `error` is considered as an always failing operation,
`readLine` cannot be verified as non-failing.
However, this requires also a careful analysis
of all external operations (like `readFile`)
which might raise exceptions.

---------------------------------------------------------------------------

Current restrictions:
---------------------

- The nonfail specification should be a Boolean formula, i.e.,
  not a function with pattern matching or local definitions.
  Furthermore, it should be a first-order equation, i.e.,
  in eta-expanded form.
  

---------------------------------------------------------------------------

Notes:
------

- Contracts and nonfail specifications can also be stored in a separate
  file. When checking a module `m`, if there is a Curry module `m_SPEC`
  in the load path, the contents of `m_SPEC` is added to `m` before
  it is checked.

- nonfail specifications for operators can be also specified by
  operations named by `op_xh1...hn'`, where
  each `hi` is a two digit hexadecimal number, into the name
  of corresponding to the ord values of `h1...hn`.
  For instance, the nonfail specification for `&>` can be named
  `op_x263E'nonfail`.

- Operations defining contracts and properties are not verified.

---------------------------------------------------------------------------

Directories of the package:
---------------------------

* examples: some examples (and test suite)

* include: an include file for the SMT solver and non-fail conditions
  for various system modules

* src: source code of the implementation

---------------------------------------------------------------------------

