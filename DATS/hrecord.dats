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
staload "./../SATS/hrecord.sats"

#include "./../HATS/tlist_infix.hats"

implement {}
hrecord_nil{sz}( sz ) =
  $UNSAFE.castvwtp0{ [l:addr] hrecord(tnil,0,sz,l) }( 
    arrayptr_make_elt<byte>( sz, i2byte(0)) 
  )

implement {a}{tl}
hrecord_push{sz}{len}{l}( hr, x ) =
  let
    val p  = hrecord_ptrcast( hr )

    val (pf | sz) = tlist_size<tl>() 
    val p0 = ptr_add<byte>(p,sz)
 
    val () = assertloc(p0 > the_null_ptr) 

    val () = 
      $UNSAFE.ptr1_set<a>( p0, x ) 
    
   extern
    prfn 
    __assert{a:vt@ype+}{tl:tlist}{len,sz:nat}{l:addr}( 
        hr:  !hrecord(tl,len,sz,l) >> hrecord(a ::: tl,len + 1,sz - sizeof(a),l) 
    ) : void 

    prval () = __assert{a}{tl}{len,sz}{l}( hr )
  in 
  end

implement {a}{tl}
hrecord_pop{sz}{len}{l}( hr ) =
  let
    val p  = hrecord_ptrcast( hr )

    val (pf | sz) = tlist_size<tl>() 
    val p0 = ptr_add<byte>(p,sz)
 
    val () = assertloc(p0 > the_null_ptr) 

    val x = 
      $UNSAFE.ptr1_get<a>( p0 ) 
    
   extern
    prfn 
    __assert{a:vt@ype+}{tl:tlist}{len,sz:nat}{l:addr}( 
        hr:  !hrecord(a ::: tl,len,sz,l) >> hrecord(tl,len - 1,sz + sizeof(a),l) 
    ) : void 

    prval () = __assert{a}{tl}{len,sz}{l}( hr )

  in x 
  end

implement {tl:tlist}
hrecord_create_hlist{n}( hl ) =
  let
    val (pf | sz) = tlist_size<tl>()

    val hr = hrecord_nil<>( sz ) 
    val p  = hrecord_ptrcast( hr )

    extern fun {tl:tlist}
    loop {l:addr}{n:nat}{len:nat}(p: ptr l, sz: size_t n, hlist_vt(tl,len) ) : void
    
    implement
    loop<tlist_nil()>(p,sz,hl) = 
      let
        val ~hlist_nil() = hl
      in
      end

    implement (a,tl0)
    loop<tlist_cons(a,tl0)>(p,sz,hl) =
      let

        val () = assertloc( sz >=  sizeof<a> )
        val p0 = ptr_add<byte>(p,sz - sizeof<a>)
        val () = assertloc(p0 > the_null_ptr)
           
        val ~hlist_cons(x,xs) = hl
        val () = 
          $UNSAFE.ptr1_set<a>( p0, x ) 
    
        val () = loop<tl0>(p,sz - sizeof<a>, xs)
      in ignoret(5)
      end

    val () = loop<tl>( p, sz, hl )

    val hr1 = $UNSAFE.castvwtp0{[l:addr] hrecord(tl,n,0,l) }(hr)

  in hr1
  end

implement {a}{tl}
hrecord_exch{ind,len}( pf | hr, ind, x ) =
  let
    val p  = hrecord_ptrcast( hr )
    (** Perhaps some of these should be arguments **)
    (** This is weird because data is stored earliest --> latest **)
    val (pfs | sz) = tlist_size<tl>()
    val (pfl | len) = tlist_length<tl>()

    val () = assertloc( ind < len )

    val (pfo | offs) = tlist_offset<tl>(pfl | ind)

    val () = assertloc( sz > (offs + sizeof<a>) )
 
    val p0 = ptr_add<byte>(p,sz - (offs + sizeof<a>))

    val () = assertloc(p0 > the_null_ptr)
 
    val x0 = 
      $UNSAFE.ptr1_get<a>( p0 ) 
    val () = 
      $UNSAFE.ptr1_set<a>( p0, x )
    
  in x0 
  end

implement {a,env}{tl}
hrecord_with_env{ind,len}( pf | hr, ind, f, env ) =
  let
    val p  = hrecord_ptrcast( hr )
    (** Perhaps some of these should be arguments **)
    (** This is weird because data is stored earliest --> latest **)
    val (pfs | sz) = tlist_size<tl>()
    val (pfl | len) = tlist_length<tl>()

    val () = assertloc( ind < len )

    val (pfo | offs) = tlist_offset<tl>(pfl | ind)

    val () = assertloc( sz > (offs + sizeof<a>) )
 
    val p0 = ptr_add<byte>(p,sz - (offs + sizeof<a>))

    val () = assertloc(p0 > the_null_ptr)

    val (pf,plf | p0) = $UNSAFE.ptr1_vtake{a}( p0 )

    val () = f( !p0, env )

    prval () = plf(pf) 
  in  
  end



implement {a}{env}
hrecord_foreach$fwork( a, env ) = ()
implement {a}{env}
hrecord_foreach$cont( a, env ) = true



implement {env}{tl}
hrecord_foreach_env{n0}( hr,  env ) =
  let
    val p  = hrecord_ptrcast( hr )
    (** Perhaps some of these should be arguments **)
    (** This is weird because data is stored earliest --> latest **)
    val (pfs | sz) = tlist_size<tl>()


    extern fun {tl:tlist}
    loop{len:nat}{l:addr}{n:nat}(p: ptr l, sz: size_t n, env : &env >> _ ) 
    : [m:nat | m <= len] size_t m
    
    implement
    loop<tlist_nil()>(p,sz,env) = i2sz(0)

    implement (a,tl0)
    loop<tlist_cons(a,tl0)>{n1}(p,sz,env) =
      let

        prval () = $UNSAFE.prop_assert{n1 > 0}()
 
        val () = assertloc( sz >  sizeof<a> )
        val p0 = ptr_add<byte>(p,sz - sizeof<a>)

        val () = assertloc(p0 > the_null_ptr)
        val (pf,plf | p0) = $UNSAFE.ptr1_vtake{a}( p0 )

        val sz = 
          (if hrecord_foreach$cont<a><env>( !p0, env )
          then 
            let
              val () = hrecord_foreach$fwork<a><env>( !p0, env )
              val sz = loop<tl0>{n1-1}(p,sz - sizeof<a>, env)
             in sz + 1 
            end 
          else i2sz(0)
        ): [m:nat | m <= n1] size_t m

        prval () = plf(pf) 
        val () = ignoret(5)
      in sz
      end

    val sz = loop<tl>{n0}(p, sz,env)
  in sz
  end

implement(a:t0p)
hrecord_clear$clear<a>( a ) = () where { prval () = topize(a) }

implement(a:vt0p)
hrecord_clear$clear<a>( a ) = gclear_ref<a>(a)

implement {tl}
hrecord_clear( hr  ) =
  let
    val p  = hrecord_ptrcast( hr )
    (** Perhaps some of these should be arguments **)
    (** This is weird because data is stored earliest --> latest **)
    val (pfs | sz) = tlist_size<tl>()


    extern fun {tl:tlist}
    loop {l:addr}{n:nat}(p: ptr l, sz: size_t n ) : void
    
    implement
    loop<tlist_nil()>(p,sz) = ()

    implement (a,tl0)
    loop<tlist_cons(a,tl0)>(p,sz) =
      let

        val () = assertloc( sz >=  sizeof<a> )
        val p0 = ptr_add<byte>(p,sz - sizeof<a>)

        val () = assertloc(p0 > the_null_ptr)
        val (pf,plf | p0) = $UNSAFE.ptr1_vtake{a}( p0 )
        
        val () = hrecord_clear$clear<a>( !p0 )
      
        (** FIXME **) 
        extern
        prfn __assert{a:vt@ype+}( &a? >> a ) : void 
        prval () = __assert{a}( !p0 )
        prval () = plf( pf ) 
        (*** ***)
 
        val () = loop<tl0>(p,sz - sizeof<a>)
      in ignoret(5)
      end

    val () = loop<tl>( p, sz )

    extern
    prfn {tl:tlist}
      __assert{len,sz:nat}{sz1:nat}{l:addr}( h: !hrecord(tl,len,sz,l) >> hrecord(tnil,0,sz+sz1,l), size_t sz1) 
      : void

    prval () = __assert( hr, sz )

  in sz
  end

implement {tl}
hrecord_free{len}( h ) = 
  let
   val _ = hrecord_clear<tl>( h ) 
   val ar = $UNSAFE.castvwtp0{arrayptr(byte,len)}( h )
     
  in free( ar )
  end
