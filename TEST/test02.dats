(* 
 ** Project : hcollections
 ** Author  : Mark Bellaire
 ** Year    : 2019
 ** License : MIT
*)
#include "share/atspre_staload.hats"
#include "./../mylibies.hats"

infixl <<<
overload <<< with hrecord_push1

implement main0 () = println!("Hello [test04]") where {
    var env : void = ()
    val hr = hrecord_create<int ::: size_t ::: string ::: tnil>()

    val hr = hr <<<  30 <<< i2sz(30) <<< "Hello World"

    val _ = hrecord_foreach( hr, env ) where {
        implement (env:vt@ype+) 
        hrecord_foreach$fwork<int><env>( sz, x, env ) = println!(sz,": ",x)
        implement (env:vt@ype+) 
        hrecord_foreach$fwork<size_t><env>( sz, x, env ) = println!(sz,": ",x)
        implement (env:vt@ype+)
        hrecord_foreach$fwork<string><env>( sz, x, env ) = println!(sz,": ",x)
      }


    val () = hrecord_free( hr )
  }





