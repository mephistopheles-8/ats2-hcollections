
#include "share/atspre_staload.hats"

datasort tlist =
  | tlist_nil of () | tlist_cons of (vt@ype+, tlist)

infixr :::
#define ::: tlist_cons
#define tnil tlist_nil

absvtype hrecord(tl:tlist,l:addr) = ptr

dataprop TLISTLEN (int,tlist)=
  | TLISTLENnil (0, tnil)
  | {n:pos}{a:vt@ype+}{tl:tlist}
    TLISTLENcons (n, a ::: tl ) of TLISTLEN( n - 1, tl )

dataprop TLISTSZ (int,tlist)=
  | TLISTSZnil (0, tnil)
  | {n:nat}{a:vt@ype+}{tl:tlist}
    TLISTSZcons (n + sizeof(a), a ::: tl ) of TLISTSZ( n, tl )

extern
praxi size_is_nat{a:vt@ype+}() : [sizeof(a) >= 0] void

extern
praxi TLISTSZ_elim{tl:tlist}{n:int}( TLISTSZ(n,tl)  ) : void

extern
praxi TLISTLEN_elim{tl:tlist}{n:int}( TLISTLEN(n,tl)  ) : void

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


implement main0 () 
  = println!("Hello [harray]")
  where {
    val () = println!( sizeof<int64> )
  //  val () = println!(tlist_size<int ::: int32 ::: int64 ::: tnil>()  )


  }
