(* 
 ** Project : hcollections
 ** Author  : Mark Bellaire
 ** Year    : 2019
 ** License : MIT
*)
#include "./../HATS/project.hats"

staload "./tlist.sats"
#include "./../HATS/tlist_infix.hats"

datavtype hlist_vt( tlist, int ) =
  | hlist_nil (tnil,0) 
  | {n:nat}{a:vt@ype+}{tl:tlist}
    hlist_cons (a ::: tl, n + 1) of (a, hlist_vt(tl,n )) 

fun {a:vt@ype+}
  hlist_vt_free$clear( x: &a >> a? ) : void

fun {tl:tlist} 
  hlist_vt_free{n:nat}( hs : hlist_vt( tl, n ) ) 
  : void

fun {a:vt@ype+}{env:vt@ype+}
hlist_foreach_env$fwork( &a >> _, &env >> _ )
  : void

fun {a:vt@ype+}
    {env:vt@ype+}
    hlist_foreach_env$cont(  &a, &env ) : bool

fun {env:vt@ype+}{tl:tlist} 
hlist_foreach_env{n:nat}( hl: !hlist_vt(tl,n), env: &env >> _ )
  : [m:nat | m <= n] size_t m 
