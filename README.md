nonfailing
==========


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
