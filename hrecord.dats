
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

extern
praxi size_is_nat{a:vt@ype+}() : [sizeof(a) >= 0] void

(** This is useless...**)
extern prfun
lemma_tlist_len_exists{tl:tlist} ()
  : [len:nat] ( TLISTLEN(len,tl) | size_t len )

primplmnt
lemma_tlist_len_exists{tl}()
  = scase tl of
    | tlist_nil() => ( TLISTLENnil() | i2sz(0) )
    | tlist_cons(a,tl0) =>
      let
        prval (pf | len) = lemma_tlist_len_exists{tl0}()
      in ( TLISTLENcons(pf) | len + 1 )
      end


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
  tlist_offset{ind,len:nat | ind < len; len > 0}
  ( pf: TLISTLEN(len,tl) | i: size_t ind ) 
  : [sz:nat] (TLISTOFFS(ind,sz,tl) | size_t sz) =
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

fun
  {tl:tlist}
  {a0:vt@ype+} 
  tlist_ind_of{ind,len:nat | ind < len; len > 0}
  ( pf: TLISTLEN(len,tl) | i: size_t ind ) 
  : [b:bool] (option_v(TLISTIND(ind,tl,a0), b) | bool b) =
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


absvtype hrecord( tl:tlist, len: int, sz: int, l:addr )
vtypedef hrecord0(tl:tlist, len:int) = [sz:nat][l:addr] hrecord(tl,len,sz,l)
(** Creates an intermediary until the 
    user finishes initializing **)
extern
fun {} 
  hrecord_nil{sz:nat}( sz: size_t sz ) 
  : [l:addr] hrecord(tnil,0,sz,l) 

implement {}
hrecord_nil{sz}( sz ) =
  $UNSAFE.castvwtp0{ [l:addr] hrecord(tnil,0,sz,l) }( 
    arrayptr_make_elt<byte>( sz, i2byte(0)) 
  )




extern
fun {tl:tlist}
  hrecord_create_hlist{n:nat}( h: hlist_vt(tl,n) ) 
  : [l:addr][sz:nat] hrecord(tl,n,sz,l)
 
extern
fun {a:vt@ype+}{tl:tlist}
  hrecord_push{sz:nat | sz >= sizeof(a)}{len:nat}{l:addr}( 
    hr: !hrecord(tl,len,sz,l) >> hrecord(a ::: tl,len + 1,sz - sizeof(a),l), x: a 
  ): void 

extern
fun {a:vt@ype+}{tl:tlist}
  hrecord_pop{sz:nat}{len:pos}{l:addr}( 
    hr: !hrecord(a ::: tl,len,sz,l) >> hrecord(tl,len - 1,sz + sizeof(a),l)  
  ): a 

extern
fun {a:vt@ype+}{tl:tlist}
  hrecord_exch{ind,len:nat | ind < len}(
    pf : TLISTIND(ind,tl,a) 
  | hr: !hrecord0(tl,len)
  , ind: size_t ind
  , x: a 
  ): a 

extern
fun {a,env:vt@ype+}{tl:tlist}
  hrecord_with_env{ind,len:nat | ind < len}(
    pf : TLISTIND(ind,tl,a) 
  | hr: !hrecord0(tl,len)
  , ind: size_t ind
  , x: (&a >> _, &env >> _) -> void
  , env: &env >> _ 
  ): void 


extern
fun {a:vt@ype+}
    {env:vt@ype+}
    hrecord_foreach$fwork{n:nat}( i : size_t n,  &a >> _, &env >> _ ) : void

extern
fun {a:vt@ype+}
    {env:vt@ype+}
    hrecord_foreach$cont{n:nat}(i: size_t n, &a, &env ) : bool

extern
fun {tl:tlist}{env: vt@ype+}
  hrecord_foreach_env{n:nat}( h: !hrecord0(tl,n), env: &env >> _ ) 
  : [m:nat | m <= n] size_t m
 


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
(** Create an hrecord from static array **)
extern
fun {tl:tlist} 
hrecord_create_b0ytes{n:nat}{l:addr}( 
    pb: b0ytes(n) @ l
  , psz: TLISTSZ(n,tl)
  | buf: ptr l
  , sz: size_t n
): hrecord(tnil,0,n,l)



implement main0 () 
  = println!("Hello [harray]")
  where {
        
    val () = println!( sizeof<int64> )
    val (pf | sz )   = tlist_size<int ::: int32 ::: int64 ::: tnil>() 
    val (pf1 | len ) = tlist_length<int ::: int32 ::: int64 ::: tnil>()

    val () = assertloc( len = 3 )

    val () = println!("Size: ", sz) 
    val () = println!("Len:", len) 
    val (pf2 | offs ) = tlist_offset<int ::: int32 ::: int64 ::: tnil>(pf1 | i2sz(0))
    val () = println!("Offs 0:", offs) 
    val (pf2 | offs ) = tlist_offset<int ::: int32 ::: int64 ::: tnil>(pf1 | i2sz(1))
    val () = println!("Offs 1:", offs) 
    val (pf2 | offs ) = tlist_offset<int ::: int32 ::: int64 ::: tnil>(pf1 | i2sz(2))
    val () = println!("Offs 2:", offs) 
    
    val (pf3 | isind ) = tlist_ind_of<int ::: int32 ::: int64 ::: tnil><int>(pf1 | i2sz(0))
    val () = println!("Ind 0 is int:", isind)
    val () = assertloc ( isind ) 
    prval Some_v(_) = pf3
    
    val (pf3 | isind ) = tlist_ind_of<int ::: int32 ::: int64 ::: tnil><bool>(pf1 | i2sz(0))
    val () = println!("Ind 0 is bool:", isind)
    val () = assertloc ( ~isind ) 
    prval None_v() = pf3
 
    val x : int = 5
    val y : bool = true
    val tl0 = hlist_cons( y, hlist_cons( x, hlist_nil() ))
    val () = hlist_vt_free<bool ::: int ::: tnil>( tl0 )

  }
