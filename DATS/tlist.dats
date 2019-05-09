(* 
 ** Project : hcollections
 ** Author  : Mark Bellaire
 ** Year    : 2019
 ** License : MIT
*)
#include "./../HATS/project.hats"
#include "share/atspre_staload.hats"

staload "./../SATS/tlist.sats"
#include "./../HATS/tlist_infix.hats"

extern
praxi size_is_nat{a:vt@ype+}() : [sizeof(a) >= 0] void

implement {tl}
tlist_length() =
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

implement {tl}
tlist_size() =
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

implement{tl}
tlist_offset( pf | i ) =
  let
    extern
    fun { a: vt@ype+  }
        { tl: tlist  }
        loop{ind:nat}( size_t ind  )
        : [sz:nat] (TLISTOFFS(ind,sz,a ::: tl) | size_t sz ) 
    
    extern
    fun { tl: tlist  }
        run_loop{ind:nat} ( size_t ind )
        : [sz:nat] (TLISTOFFS(ind,sz, tl) | size_t sz ) 

    implement (a)
    loop<a><tlist_nil()> (i) =
      let
        val () = assertloc( i = 0 )
      in ( TLISTOFFSbas() | i2sz(0) ) 
      end
    
    implement (a,b,tl)
    loop<a><tlist_cons(b,tl)> (i) =
      case+ sz2i(i) of
       | 0 => (TLISTOFFSbas() | i2sz(0) )
       | _ =>>  
          let   
            val (pf | sz0) =  loop<b><tl>( i - 1 )
            (** This is mostly to break tail recursion **)
            val () = assertloc( sizeof<a> >= 0 )
           in (TLISTOFFScas( pf ) | sz0 + sizeof<a> )
          end

    implement (a,tl)
    run_loop<tlist_cons(a,tl)>(i) = loop<a><tl>(i)

  in run_loop<tl>( i )
  end 

implement{tl}{a0}
tlist_ind_of( pf | i ) =
  let
    extern
    fun { a: vt@ype+  }
        { tl: tlist  }
        loop{ind:nat}( size_t ind  )
        : [b:bool] (option_v(TLISTIND(ind,a ::: tl,a0), b) | bool b)
    
    extern
    fun { tl: tlist  }
        run_loop{ind:nat} ( size_t ind )
        : [b:bool] (option_v(TLISTIND(ind,tl,a0), b) | bool b)

    implement (a)
    loop<a><tlist_nil()> (i) =
      let
        val () = assertloc( i = 0 )
      in ( None_v() | false ) 
      end
   
    implement
    loop<a0><tlist_nil()>(i) =
      let
        val () = assertloc( i = 0 )
      in ( Some_v(TLISTINDbas()) | true ) 
      end

 
    implement (a,b,tl)
    loop<a><tlist_cons(b,tl)> (i) =
      case+ sz2i(i) of
       | 0 => (None_v() | false )
       | _ =>>  
          let   
            val (pf | sz0) =  loop<b><tl>( i - 1 )
            val () = ignoret(5)
           in if sz0 
              then 
                let
                  prval Some_v(pf) = pf
                in ( Some_v( TLISTINDcas( pf ) ) | true )
                end 
              else 
                let
                  prval None_v () = pf
                in ( None_v() | false )
                end 
          end
    
    implement (b,tl)
    loop<a0><tlist_cons(b,tl)> (i) =
      case+ sz2i(i) of
       | 0 => (Some_v(TLISTINDbas()) | true )
       | _ =>>  
          let   
            val (pf | sz0) =  loop<b><tl>( i - 1 )
            val () = ignoret(5)
           in if sz0 
              then 
                let
                  prval Some_v(pf) = pf
                in ( Some_v( TLISTINDcas( pf ) ) | true )
                end 
              else 
                let
                  prval None_v () = pf
                in ( None_v() | false )
                end 
          end

    implement (a,tl)
    run_loop<tlist_cons(a,tl)>(i) = loop<a><tl>(i)

  in run_loop<tl>( i )
  end 







