#include "share/atspre_staload.hats"
#include "./../mylibies.hats"


implement main0 () 
  = println!("Hello [test01]")
  where {
        
    stadef tl0 = int ::: int32 ::: int64 ::: tnil

    val (pf | sz )   = tlist_size<tl0>() 
    val (pf1 | len ) = tlist_length<tl0>()

    val () = assertloc( len = 3 )

    val () = println!("Size: ", sz) 
    val () = println!("Len:", len)

 
    val (pf2 | offs ) = tlist_offset<tl0>(pf1 | i2sz(0))
    val () = println!("Offs 0:", offs) 
    val (pf2 | offs ) = tlist_offset<tl0>(pf1 | i2sz(1))
    val () = println!("Offs 1:", offs) 
    val (pf2 | offs ) = tlist_offset<tl0>(pf1 | i2sz(2))
    val () = println!("Offs 2:", offs) 
    
    val (pf3 | isind ) = tlist_ind_of<tl0><int>(pf1 | i2sz(0))
    val () = println!("Ind 0 is int:", isind)
    val () = assertloc ( isind ) 
    prval Some_v(_) = pf3
    
    val (pf3 | isind ) = tlist_ind_of<tl0><bool>(pf1 | i2sz(0))
    val () = println!("Ind 0 is bool:", isind)
    val () = assertloc ( ~isind ) 
    prval None_v() = pf3

    var e : int = 0 
    val x : int = 5
    val y : bool = true
    val tl0 = hlist_cons( y, hlist_cons( x, hlist_nil() ))

    stadef tl = bool ::: int ::: tnil

    implement(a)
    hlist_foreach$fwork<a><int>(x,env) =
      (println!(env, ": hlist_foreach_env$fwork"); env := env + 1)

    val sz = hlist_foreach_env<int><tl>(tl0, e)
    val () = assertloc( sz = 2 )

    val () = hlist_vt_free<tl>( tl0 )

  }
