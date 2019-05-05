
#include "share/atspre_staload.hats"

datasort tlist =
  | tlist_nil of () | tlist_cons of (vt@ype+, tlist)

infixr :::
#define ::: tlist_cons
#define tnil tlist_nil

absvtype hrecord(tl:tlist,l:addr) = ptr

dataprop TLISTLEN (int,tlist) =
  | TLISTLENnil (0, tnil)
  | {n:pos}{a:vt@ype+}{tl:tlist}
    TLISTLENcons (n, a ::: tl ) of TLISTLEN( n - 1, tl )

dataprop TLISTSZ (int,tlist) =
  | TLISTSZnil (0, tnil)
  | {n:nat}{a:vt@ype+}{tl:tlist}
    TLISTSZcons (n + sizeof(a), a ::: tl ) of TLISTSZ( n, tl )

extern
praxi size_is_nat{a:vt@ype+}() : [sizeof(a) >= 0] void

fun 
  {tl:tlist}
  tlist_length() 
  : [n:nat] (TLISTLEN(n,tl) | size_t n) =
  let
    extern
    fun { a: vt@ype+  }
        { tl: tlist  }
        loop(  )
        : [n:nat] (TLISTLEN(n,a ::: tl) | size_t n) 
    
    extern
    fun { tl: tlist  }
        run_loop( )
        : [n:nat] (TLISTLEN(n,tl) | size_t n ) 

    implement (a)
    loop<a><tlist_nil()>() = ( TLISTLENcons( TLISTLENnil() ) |  i2sz(1) )
    
    implement (a,b,tl)
    loop<a><tlist_cons(b,tl)>() = 
      let   
        val (pf | sz0) =  loop<b><tl>( )
        (** Break tail recursion **)
        val () = ignoret(5)
       in (TLISTLENcons( pf ) | sz0 + 1 )
      end

    implement
    run_loop<tlist_nil()>() = (TLISTLENnil() |  i2sz(0))
    
    implement (a,tl)
    run_loop<tlist_cons(a,tl)>() = loop<a><tl>()

  in run_loop<tl>()
  end 

fun 
  {tl:tlist}
  tlist_size() 
  : [n:nat] (TLISTSZ(n,tl) | size_t n) =
  let
    extern
    fun { a: vt@ype+  }
        { tl: tlist  }
        loop(  )
        : [n:nat] (TLISTSZ(n,a ::: tl) | size_t n) 
    
    extern
    fun { tl: tlist  }
        run_loop( )
        : [n:nat] (TLISTSZ(n,tl) | size_t n ) 

    implement (a)
    loop<a><tlist_nil()>() = ( TLISTSZcons( TLISTSZnil() ) |  sizeof<a> )
      where {
        prval () = size_is_nat{a}()
      }

    implement (a,b,tl)
    loop<a><tlist_cons(b,tl)>() = 
      let   
        val (pf | sz0) =  loop<b><tl>( )
        (** This is mostly to break tail recursion **)
        val () = assertloc( sizeof<a> >= 0 )
       in (TLISTSZcons( pf ) | sz0 + sizeof<a> )
      end

    implement
    run_loop<tlist_nil()>() = (TLISTSZnil() |  i2sz(0))
    
    implement (a,tl)
    run_loop<tlist_cons(a,tl)>() = loop<a><tl>()

  in run_loop<tl>()
  end 

datavtype hlist_vt( tlist, int ) =
  | hlist_nil (tnil,0) 
  | {n:nat}{a:vt@ype+}{tl:tlist}
    hlist_cons (a ::: tl, n + 1) of (a, hlist_vt(tl,n )) 

extern
fun {a:vt@ype+}
  hlist_vt_free$clear( x: &a >> a? ) : void

implement(a:t0p)
hlist_vt_free$clear<a>( a ) = () where { prval () = topize( a ) }

implement(a:vt0p)
hlist_vt_free$clear<a>( a ) = gclear_ref<a>( a )

extern
fun {tl:tlist} 
  hlist_vt_free{n:nat}( hs : hlist_vt( tl, n ) ) 
  : void

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


absview hinit( tl:tlist, l:addr )
absvtype hrecord( tl:tlist, l:addr )
absvtype hrecordinit( tl:tlist, l:addr )

extern
fun {tl:tlist} 
  hrecordinit_create( ) 
  : [l:addr] (hinit( tl, l) | hrecordinit(tl,l) ) 

extern
fun {a:vt@ype+}{tl0,tl1:tlist} 
  hrecordinit_set{l:addr}
  ( !hinit( a ::: tl0, l) >> hinit(tl0,l) | !hrecordinit(tl1,l) ) 
  : void 

extern
castfn hrecord_finalize{tl:tlist}{l:addr}
  ( hinit(tnil, l) | hrecordinit(tl,l) ) 
  : hrecord( tl, l)


(**
  Heterogenous records with O(1) storage and retrieval
  are the goal here.
  Initialization can come in a few forms:

  hlist to hrecord -- intuitive, but comes with the overhead of
    constructing a list.  This should be possible, but perhaps
    not the main way to construct an hrecord

  template per instantiation --
     less overhead, but makes it difficult to bring in external
     values. Setting and retrieval are easier; maybe this
     is a good way to initialize.  Also, template implementations
     may get tedious.
     The perk here, however, is that you can manage
     large hrecords automatically.

  convenience functions with tuples
    I guess I could have these anyway.  There
    would be an upper bound of 6 items, which
    I'm not terribly excited about.

  fixed size, gradual instantiation
    All records start with tnil and a size
    Items are pushed to the end of the list 
    This would probably provide the best 
    interface 
**)




implement main0 () 
  = println!("Hello [harray]")
  where {
        
    val () = println!( sizeof<int64> )
    val (pf | sz )   = tlist_size<int ::: int32 ::: int64 ::: tnil>() 
    val (pf1 | len ) = tlist_length<int ::: int32 ::: int64 ::: tnil>() 
    val () = println!(sz) 
    val () = println!(len) 
    val x : int = 5
    val y : bool = true
    val tl0 = hlist_cons( y, hlist_cons( x, hlist_nil() ))
    val () = hlist_vt_free<bool ::: int ::: tnil>( tl0 )

  }
