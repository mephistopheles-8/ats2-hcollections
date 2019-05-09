(* 
 ** Project : hcollections
 ** Author  : Mark Bellaire
 ** Year    : 2019
 ** License : MIT
*)

#include "./../HATS/project.hats"

datasort tlist =
  | tlist_nil of () | tlist_cons of (vt@ype+, tlist)

#include "./../HATS/tlist_infix.hats"

dataprop TLISTLEN (int,tlist) =
  | TLISTLENnil (0, tnil)
  | {n:pos}{a:vt@ype+}{tl:tlist}
    TLISTLENcons (n, a ::: tl ) of TLISTLEN( n - 1, tl )

dataprop TLISTSZ (int,tlist) =
  | TLISTSZnil (0, tnil)
  | {n:nat}{a:vt@ype+}{tl:tlist}
    TLISTSZcons (n + sizeof(a), a ::: tl ) of TLISTSZ( n, tl )

(** Associate indicies with a type **)
dataprop TLISTIND( int , tlist, vt@ype+ ) =
  | {a:vt@ype+}{tl:tlist} 
    TLISTINDbas (0, a ::: tl, a)
  | {n:pos}{a,b:vt@ype+}{tl:tlist} 
    TLISTINDcas (n, b ::: tl, a)
      of TLISTIND(n-1, tl, a)

dataprop TLISTOFFS( i:int,sz: int , tl:tlist ) =
  | {tl:tlist} 
    TLISTOFFSbas (0,0,tl)
  | {n:pos}{a:vt@ype+}{sz:nat | sz >= sizeof(a)}{tl:tlist} 
    TLISTOFFScas (n,sz,a ::: tl)
      of TLISTOFFS(n-1,sz - sizeof(a),tl)


(** Ultimately, I'd like to do more of this sort of thing in the statics **)
fun 
  {tl:tlist}
  tlist_length() 
  : [n:nat] (TLISTLEN(n,tl) | size_t n)

fun 
  {tl:tlist}
  tlist_size() 
  : [n:nat] (TLISTSZ(n,tl) | size_t n)

fun 
  {tl:tlist}
  tlist_offset{ind,len:nat | ind < len; len > 0}
  ( pf: TLISTLEN(len,tl) | i: size_t ind ) 
  : [sz:nat] (TLISTOFFS(ind,sz,tl) | size_t sz)

fun
  {tl:tlist}
  {a0:vt@ype+} 
  tlist_ind_of{ind,len:nat | ind < len; len > 0}
  ( pf: TLISTLEN(len,tl) | i: size_t ind ) 
  : [b:bool] (option_v(TLISTIND(ind,tl,a0), b) | bool b)
