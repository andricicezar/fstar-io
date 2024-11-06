module MSTReifyReflect

open MST
open MST.Tot

let fixed_wp #a : st_wp a =
  fun p h0 -> forall r h1. p r h1

let linkT
  (pt:((int -> _mst int fixed_wp) -> _mst int fixed_wp))
  (ct:(int -> _mst int fixed_wp)) :
  (unit -> _mst int fixed_wp)
  =
  fun () -> pt ct

let linkS
  (ps:((int -> STATEwp int fixed_wp) -> STATEwp int fixed_wp))
  (cs:(int -> STATEwp int fixed_wp)) :
  (unit -> STATEwp int fixed_wp)
  =
  fun () -> ps cs
  
let behT (f:(unit -> _mst int fixed_wp)) : st_wp int =
  theta (f ())

let behS (f:(unit -> STATEwp int fixed_wp)) : st_wp int =
  theta (reify (f ()))

val compile :
  ((int -> STATEwp int fixed_wp) -> STATEwp int fixed_wp) ->
  ((int -> _mst int fixed_wp) -> _mst int fixed_wp)

open FStar.Tactics

let compile ps ct : _mst int fixed_wp =
  let cs : (int -> STATEwp int fixed_wp) = (fun x -> STATEwp?.reflect (ct x)) in
  reify (ps cs)

val backtranslate : 
  (int -> _mst int fixed_wp) ->
  (int -> STATEwp int fixed_wp)
let backtranslate ct x =
  STATEwp?.reflect (ct x)

type sc
  (ps:((int -> STATEwp int fixed_wp) -> STATEwp int fixed_wp))
  (ct:(int -> _mst int fixed_wp))
  =
  behS (linkS ps (backtranslate ct)) == behT (linkT (compile ps) ct) (* syntactic equality between behaviors *)

let lemma_sc ps ct : Lemma (sc ps ct) by (
  norm [delta_only [`%sc;`%behS;`%behT;`%compile;`%backtranslate;`%linkS;`%linkT];zeta;iota]
)= 
  ()
