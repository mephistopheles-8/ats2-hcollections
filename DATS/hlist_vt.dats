(* 
 ** Project : hcollections
 ** Author  : Mark Bellaire
 ** Year    : 2019
 ** License : MIT
*)
#include "./../HATS/project.hats"
#include "share/atspre_staload.hats"

staload "./../SATS/tlist.sats"
staload "./../SATS/hlist_vt.sats"

#include "./../HATS/tlist_infix.hats"


implement(a:t0p)
hlist_vt_free$clear<a>( a ) = () where { prval () = topize( a ) }

implement(a:vt0p)
hlist_vt_free$clear<a>( a ) = gclear_ref<a>( a )

implement hlist_vt_free<tnil>( hs ) = 
  case+ hs of
  | ~hlist_nil() => ()

// emulating prelude for list_vt
implement (a:vt@ype+, tl:tlist) 
  hlist_vt_free<a ::: tl>( hs ) = 
  case+ hs of
  | @hlist_cons( x, hs0 ) =>
      let 
        val () =  hlist_vt_free$clear<a>(x)
        val hs0 = hs0 
        val () = free@{0}{a}(hs)
        val () = hlist_vt_free<tl>(hs0);
        (** Break tail recursion **)
        val () = ignoret( 5 )   
       in end


(** Something like this could use a base implementation **)
implement {a}{env}
hlist_foreach_env$fwork( a, env ) = ()

implement {a}{env}
hlist_foreach_env$cont( a, env ) = true

implement(env)
hlist_foreach_env<env><tlist_nil()>( hl, env ) = i2sz(0)

implement(env,a,tl0)
hlist_foreach_env<env><tlist_cons(a,tl0)>{n1}( hl, env ) = 
  let
    val-@hlist_cons(x,xs) = hl
    val sz = ( 
      if hlist_foreach_env$cont<a><env>(x,env)
      then 
        let
          val () = hlist_foreach_env$fwork<a><env>(x,env)
          val sz = hlist_foreach_env<env><tl0>(xs, env );
         in sz + 1
        end
      else i2sz(0)
    ) : [m:nat | m <= n1] size_t m
    prval () = fold@hl
  in sz
  end
