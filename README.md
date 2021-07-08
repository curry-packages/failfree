failfree: A tool for verifying fail-free Curry programs
=======================================================

Basic idea of the tool:
-----------------------

The objective is this tool is to verify that all operations are non-failing,
i.e., their evaluation does not result in a failure, if they are called
with arguments satisfying the non-failing precondition of the operation.

Example:

    -- The operation `head` does not fail if this condition is satisfied:
    head'nonfail xs = not (null xs)
    
    head (x:xs) = x

Note that the non-failing precondition is not a precondition for `head`
in the sense of contract-based programming, i.e.,
it is still allowed to use `head` in a logical setting.
However, it can be used to verify that the following operation
is non-failing:

    readCommand = do
      putStr "Input a command:"
      s <- getLine
      let ws = words s
      if null ws then readCommand
                 else processCommand (head ws) (tail ws)

A detailed description can be found in the
[PPDP 2018 paper](https://doi.org/10.1145/3236950.3236957).
Basically, the following techniques are used to verify non-failing properties:

1. Test whether the operation is pattern-completely defined
   (i.e., branches on all patterns in all or-branches)
   for all inputs satisfying the non-failing precondition.
   If this is not the case, the operation is possibly failing.

2. Test whether the operations called in the right-hand side
   are used with satisfied non-failing preconditions
   for all inputs satisfying the non-failing precondition.
    
3. Test whether a call to `Prelude.failed` is unreachable, e.g., in

       abs x = if x>=0 then x
                       else if x<0 then (0 - x)
                                   else failed

   Note that this might be the result translating the following definition:

       abs x | x>=0 = x
             | x<0  = 0 - x

   This requires reasoning on integer arithmetic, as supported by SMT solvers.


Depending on the state of the operation `error`,
this could also verify the absence of run-time errors:

    readLine = do
      putStr "Input a non-empty string:"
      s <- getLine
      if null s then error "Empty input!"
                else do putStr "First char: "
                        putStrLn (head s)

If `error` is considered as an always failing operation
(which is done if the option `--error` is set),
`readLine` cannot be verified as non-failing.
However, this requires also a careful analysis
of all external operations (like `readFile`)
which might raise exceptions.

---------------------------------------------------------------------------

Current restrictions:
---------------------

- The non-fail condition should be a Boolean formula, i.e.,
  not a function with pattern matching or local definitions.
  Furthermore, it should be a first-order equation, i.e.,
  in eta-expanded form.
  

---------------------------------------------------------------------------

Notes:
------

- The current implementation uses the
  [Z3 theorem prover](https://github.com/Z3Prover), i.e.,
  the executable `z3` must be in the path when using the tool.

- Contracts and non-fail conditions can also be stored in separate
  files. When checking a module `m`, if there is a Curry module `m_SPEC`
  in the load path for module `m` or in the package directory `include`,
  the contents of `m_SPEC` is added to `m` before it is checked.

- Non-fail conditions for operators can also be specified by
  operations named by `op_xh1...hn'`, where each
  `hi` is a two digit hexadecimal number and the name
  of the operator corresponds to the ord values of `h1...hn`.
  For instance, the non-fail condition for `&>` can be named
  `op_x263E'nonfail`. To generate such names automatically,
  one can use the option `--name` of the tool.

- Operations defining contracts and properties are not verified.

---------------------------------------------------------------------------

Directories of the package:
---------------------------

* examples: some examples (and test suite)

* include: an include file for the SMT solver and non-fail conditions
  for various system modules

* src: source code of the implementation

---------------------------------------------------------------------------

