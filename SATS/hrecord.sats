(* 
 ** Project : hcollections
 ** Author  : Mark Bellaire
 ** Year    : 2019
 ** License : MIT
*)

#include "./../HATS/project.hats"

staload "./tlist.sats"
staload "./hlist_vt.sats"

#include "./../HATS/tlist_infix.hats"

absvtype hrecord( tl:tlist, len: int, sz: int, l:addr ) = ptr
vtypedef hrecord0(tl:tlist, len:int) = [sz:nat][l:addr] hrecord(tl,len,sz,l)

castfn 
hrecord_ptrcast{tl:tlist}{len,sz:nat}{l:addr} ( 
    !hrecord(tl,len,sz,l)
  ) : ptr l

fun {} 
  hrecord_nil{sz:nat}( sz: size_t sz ) 
  : [l:addr] hrecord(tnil,0,sz,l) 

fun {tl:tlist}
  hrecord_create_hlist{n:nat}( h: hlist_vt(tl,n) ) 
  : [l:addr] hrecord(tl,n,0,l)

fun {a:vt@ype+}{tl:tlist}
  hrecord_push{sz:nat | sz >= sizeof(a)}{len:nat}{l:addr}( 
    hr: !hrecord(tl,len,sz,l) >> hrecord(a ::: tl,len + 1,sz - sizeof(a),l), x: a 
  ): void 

fun {a:vt@ype+}{tl:tlist}
  hrecord_pop{sz:nat}{len:pos}{l:addr}( 
    hr: !hrecord(a ::: tl,len,sz,l) >> hrecord(tl,len - 1,sz + sizeof(a),l)  
  ): a 


fun {a:vt@ype+}{tl:tlist}
  hrecord_exch{ind,len:nat | ind < len}(
    pf : TLISTIND(ind,tl,a) 
  | hr: !hrecord0(tl,len)
  , ind: size_t ind
  , x: a 
  ): a 


fun {a,env:vt@ype+}{tl:tlist}
  hrecord_with_env{ind,len:nat | ind < len}(
    pf : TLISTIND(ind,tl,a) 
  | hr: !hrecord0(tl,len)
  , ind: size_t ind
  , x: (&a >> _, &env >> _) -> void
  , env: &env >> _ 
  ): void 


fun {a:vt@ype+}
    {env:vt@ype+}
    hrecord_foreach$fwork(  &a >> _, &env >> _ ) : void
(*
extern
fun {a:vt@ype+}
    {env:vt@ype+}
    hrecord_foreach$cont(  &a, &env ) : bool
*)

fun {env: vt@ype+}{tl:tlist}
  hrecord_foreach_env{n:nat}( h: !hrecord0(tl,n), env: &env >> _ ) 
  : void//[m:nat | m <= n] size_t m

fun {a:vt@ype+}
    hrecord_clear$clear(  &a >> a? ) : void

fun {tl:tlist}
  hrecord_clear{len,sz:nat}{l:addr}( h: !hrecord(tl,len,sz,l) >> hrecord(tnil,0,sz+sz1,l)) 
  : #[sz1:nat] size_t sz1

fun {tl:tlist}
  hrecord_free{len:nat}( h: hrecord0(tl,len) ) 
  : void

(** Create an hrecord from static array **)

absview hrecord_static( x:int, l:addr )

castfn 
hrecord_create_b0ytes{n:nat}{l:addr}( 
    pb: b0ytes(n) @ l
  | buf: ptr l
): ( hrecord_static(n,l) | hrecord(tnil,0,n,l) )


(** use hrecord_clear or hrecord_pop, then claim to get proof of b0ytes back **)
castfn 
hrecord_claim_b0ytes{n:nat}{l:addr}( 
    pv: hrecord_static(n,l)
  | hr: hrecord(tnil,0,n,l)
  ): ( b0ytes(n) @ l | ptr l )
 

