# ats2-hrecord

__Work in progress...__

This is an implementation of heterogeneous datatypes
in ATS2.

a) `hlist_vt` - heterogeneous linked list implementation
b) `hrecord` - flat, heterogeneous records

Both collections may contain viewtypes.

It's important to understand a few of the tradeoffs
of heterogeneous types:
- No tail-call optimization
- Binary sizes may be larger; the generated functions are highly specialized.  Inlining
  should mostly take care of this.
- You either need to know the types at compile time or have some record of them 
  in the type system -- in many cases, if you already have this information, you
  could just use normal types.

In many cases, heterogeneous datatypes do not offer much in advantage
over others.  They can, in some cases, be convenient for control-flow
or resource management. 

 Licence: MIT
