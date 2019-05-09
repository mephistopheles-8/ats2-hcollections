#ifndef _HCOLLECTIONS
#define _HCOLLECTIONS

staload "./SATS/tlist.sats"
staload _ = "./DATS/tlist.dats"

staload "./SATS/hlist_vt.sats"
staload _ = "./DATS/hlist_vt.dats"

staload "./SATS/hrecord.sats"
staload _ = "./DATS/hrecord.dats"

#ifndef NO_TLIST_INFIX
#include "./HATS/tlist_infix.hats"
#endif

#endif
