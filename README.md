# ats2-hrecord

__Work in progress...__

This is an implementation of heterogeneous datatypes
for ATS2.

- `hlist_vt` - heterogeneous linked list implementation
- `hrecord` - flat, heterogeneous records

Both collections may contain viewtypes.

It's important to understand a few of the tradeoffs for heterogeneous types:
- No tail-call optimization
- Binary sizes may be larger; the generated functions are highly specialized.  Inlining
  should mostly take care of this, but perhaps not in all cases.
- You either need to know the types at compile time or have some record of them 
  in the type system -- in many cases, if you already have this information, you
  could just use "traditional" types like records or tuples.

They can, in some cases, be convenient for control-flow or resource management. I find them
useful for eDSLs and language design.

## TODO
- Limit the number of assertions
- Further testing
- Make hrecords easier to use.

License: MIT
