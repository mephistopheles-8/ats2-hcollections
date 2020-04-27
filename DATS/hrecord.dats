(* 
 ** Project : hcollections
 ** Author  : Mark Bellaire
 ** Year    : 2019
 ** License : MIT
*)
#include "./../HATS/project.hats"
#include "share/atspre_staload.hats"

staload "./../SATS/tlist.sats"
staload "./../SATS/hrecord.sats"

#include "./../HATS/tlist_infix.hats"

implement {tlo}
hrecord_create()
  = let
        val (pfsz | sz) = tlist_size<tlo>()
     in hrecord_arrayptr( pfsz | arrayptr_make_uninitized<byte>( sz ) )
    end

implement {a}{tli}
hrecord_push(hr,x) =
  let
      val (pfsz | sz) = tlist_size<tli>()
      val ( pf | p ) = hrecord_takeout_push( pfsz | hr )
      val () = ptr_set<a>( pf | add_ptr_bsz(p,sz), x )
      prval () = hrecord_addback_push( pfsz, pf | hr )
   in
  end 

implement {a}{tli}
hrecord_push1(hr,x) =
  let
      val (pfsz | sz) = tlist_size<tli>()
      val ( pf | p ) = hrecord_takeout_push( pfsz | hr )
      val () = ptr_set<a>( pf | add_ptr_bsz(p,sz), x )
      prval () = hrecord_addback_push( pfsz, pf | hr )
   in hr
  end 

implement {a}{tli}
hrecord_pop(hr) =
  let
      val (pfsz | sz) = tlist_size<tli>()
      val ( pf | p ) = hrecord_takeout_pop( pfsz | hr )
      val x = ptr_get<a>( pf | add_ptr_bsz(p,sz) )
      prval () = hrecord_addback_pop0( pfsz, pf | hr )
   in x
  end 

implement (a:t@ype+)
hrecord_free$clear<a>( x ) = ()

implement
hrecord_free<tlist_nil()>( hr ) = free( arrayptr_hrecord( hr ) ) where {
    prval () = hrecord_is_empty(hr)
  }

implement (a:vt@ype+,xs)
hrecord_free<a ::: xs>( hr ) = {
    prval () = hrecord_isnot_empty(hr)
    val x = hrecord_pop<a><xs>( hr )
    val () = hrecord_free<xs>( hr )
    (** Avoid TCO **) 
    val () = hrecord_free$clear<a>( x ) 
  }


(** foreach: traverse the record in the order in which the items were added; **)

implement (env:vt@ype+) 
hrecord_foreach<tlist_nil()><env>( hr, env ) = i2sz(0)  where {
      prval () = hrecord_is_empty(hr)
    }

implement (a:vt@ype+,xs0,env:vt@ype+) 
hrecord_foreach<a ::: xs0><env>( hr, env ) = 
  let
      prval () = hrecord_isnot_empty(hr)
      val hr0 = hrecord_uncons( hr )    
      val ind = hrecord_foreach<xs0>( hr0, env )
      prval () = hrecord_cons( hr, hr0 )
      
      (** Avoid TCO **)
      val (pfsz | sz) = tlist_size<xs0>()
      val ( pf | p ) = hrecord_takeout_pop( pfsz | hr )
      val p0 = add_ptr_bsz( p, sz )
      val () = hrecord_foreach$fwork<a>( ind, !p0, env )
      prval () = hrecord_addback_pop1( pfsz, pf | hr )
   in ind + 1
  end

(** Consume items in the hrec, in the order that they were added **)

implement (env:vt@ype+) 
hrecord_consume<tlist_nil()><env>( hr, env ) = i2sz(0)  where {
      prval () = hrecord_is_empty(hr)
    }

implement (a:vt@ype+,xs0,env:vt@ype+) 
hrecord_consume<a ::: xs0><env>( hr, env ) = 
  let
      prval () = hrecord_isnot_empty(hr)
      val (pfsz | sz) = tlist_size<xs0>()
      val ( pf | p ) = hrecord_takeout_pop( pfsz | hr )
      val p0 = add_ptr_bsz( p, sz )
      var x : a = !p0
      prval () = hrecord_addback_pop0( pfsz, pf | hr )

      val ind = hrecord_consume<xs0>( hr, env )
      
      (** Avoid TCO **)
      val () = hrecord_consume$fwork<a>( ind, x, env )
   in ind + 1
  end
