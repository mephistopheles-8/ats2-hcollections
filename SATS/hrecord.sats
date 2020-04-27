(* 
 ** Project : hcollections
 ** Author  : Mark Bellaire
 ** Year    : 2019
 ** License : MIT
*)

#include "./../HATS/project.hats"

staload "./tlist.sats"

#include "./../HATS/tlist_infix.hats"
 
absvtype hrecord( tli:tlist, tlo:tlist, len: int, l:addr ) = ptr
absvtype hrecordout( tli:tlist, tlo:tlist, len: int, l:addr ) = ptr

vtypedef hrecord0(tli:tlist, tlo:tlist, len:int) = [l:addr] hrecord(tli,tlo,len,l)

castfn hrecord_arrayptr{tlo:tlist}{sz:nat}{l:addr}( 
    TLISTSZ(sz,tlo) | arrayptr(byte?,l,sz) 
  ) : hrecord(tnil,tlo,0,l) 

castfn arrayptr_hrecord{tlo:tlist}{l:addr}( 
     hrecord(tnil,tlo,0,l) 
  ) : [sz:nat] arrayptr(byte?,l,sz) 


(** Create an hrecord from static array **)

absview hrecord_static( x:int, l:addr )

castfn 
hrecord_create_b0ytes{sz:nat}{tlo:tlist}{l:addr}( 
    TLISTSZ(sz,tlo), pb: b0ytes(sz) @ l
  | buf: ptr l
): ( hrecord_static(sz,l) | hrecord(tnil,tlo,0,l) )

castfn 
hrecord_claim_b0ytes{sz:nat}{tlo:tlist}{l:addr}( 
    pv: hrecord_static(sz,l)
  | hr: hrecord(tnil,tlo,0,l)
  ): ( b0ytes(sz) @ l | ptr l )


praxi hrecord_is_empty{tlo:tlist}{len:nat}{l:addr}(
     !hrecord(tnil,tlo,len,l)
  ) : [len == 0] void 

praxi hrecord_isnot_empty{a:vt@ype+}{tli,tlo:tlist}{len:nat}{l:addr}(
     !hrecord(a ::: tli,tlo,len,l)
  ) : [len > 0] void 


castfn hrecord_takeout_push{a:vt@ype+}{tli,tlo:tlist}{sz,len:nat}{l:addr}( 
    TLISTSZ(sz,tli) | !hrecord(tli,a ::: tlo,len, l ) >> hrecordout(tli,a:::tlo,len,l)
  ) : ( a? @ l + sz | ptr l ) 

praxi hrecord_addback_push{a:vt@ype+}{tli,tlo:tlist}{sz,len:nat}{l:addr}( 
    TLISTSZ(sz,tli), a @ l + sz | !hrecordout(tli,a ::: tlo,len, l ) >> hrecord(a ::: tli,tlo,len + 1,l)
  ) : void

castfn hrecord_takeout_pop{a:vt@ype+}{tli,tlo:tlist}{sz,len:nat | len > 0}{l:addr}( 
    TLISTSZ(sz,tli) | !hrecord(a ::: tli,tlo,len, l ) >> hrecordout(a ::: tli,tlo,len,l)
  ) : ( a @ l + sz | ptr l ) 

praxi hrecord_addback_pop0{a:vt@ype+}{tli,tlo:tlist}{sz,len:nat | len > 0}{l:addr}( 
    TLISTSZ(sz,tli), a? @ l + sz | !hrecordout(a ::: tli,tlo,len, l ) >> hrecord(tli,a ::: tlo,len - 1,l)
  ) : void

praxi hrecord_addback_pop1{a:vt@ype+}{tli,tlo:tlist}{sz,len:nat | len > 0}{l:addr}( 
    TLISTSZ(sz,tli), a @ l + sz | !hrecordout(a ::: tli,tlo,len, l ) >> hrecord(a ::: tli,tlo,len,l)
  ) : void

castfn hrecord_uncons{a:vt@ype+}{tli,tlo:tlist}{len:pos}{l:addr}( 
      !hrecord(a ::: tli,tlo,len, l ) >> hrecordout(a ::: tli,tlo,len,l)
  ) : hrecord(tli,tnil,len-1,l) 

praxi hrecord_cons{a:vt@ype+}{tli,tlo:tlist}{len:pos}{l:addr}( 
      !hrecordout(a ::: tli,tlo,len, l ) >> hrecord(a ::: tli,tlo,len,l), hrecord(tli,tnil,len-1,l)
  ) : void 

fun {tlo:tlist}
  hrecord_create() 
  : [l:addr] hrecord(tnil,tlo,0,l)

fun {a:vt@ype+}{tli:tlist} 
  hrecord_push{tlo:tlist}{len:nat}{l:addr}( 
    hr: !hrecord(tli,a ::: tlo,len,l) >> hrecord(a ::: tli,tlo,len+1,l), x: a 
  ) : void 

fun {a:vt@ype+}{tli:tlist} 
  hrecord_push1{tlo:tlist}{len:nat}{l:addr}( 
    hr: hrecord(tli,a ::: tlo,len,l), x: a 
  ) : hrecord(a ::: tli, tlo,len+1,l)

fun {a:vt@ype+}{tli:tlist} 
  hrecord_pop{tlo:tlist}{len:pos}{l:addr}( 
    hr: !hrecord(a ::: tli,tlo,len,l) >> hrecord(tli,a ::: tlo,len-1,l) 
  ) : a

fun {a:vt@ype+}
  hrecord_free$clear( a ) : void

fun {tli:tlist}
  hrecord_free{tlo:tlist}{len:nat}{l:addr}( hrecord(tli,tlo,len,l) ) : void

(** foreach: traverse the record in the order in which the items were added; **)
fun {a:vt@ype+}{env:vt@ype+}
  hrecord_foreach$fwork( size_t, &a >> _, &env >> _ ) : void

fun {tli:tlist}{env:vt@ype+}
  hrecord_foreach{tlo:tlist}{len:nat}{l:addr}( !hrecord(tli,tlo,len,l), &env >> _ ) : size_t len

(** Consume items in the hrec, in the order that they were added **)

fun {a:vt@ype+}{env:vt@ype+}
  hrecord_consume$fwork( size_t, &a >> a?, &env >> _ ) : void

fun {tli:tlist}{env:vt@ype+}
  hrecord_consume{tlo:tlist}{len:nat}{l:addr}( 
    !hrecord(tli,tlo,len,l) >> hrecord(tnil,tlo1,0,l)
   , &env >> _ 
  ) : #[tlo1:tlist] size_t len

