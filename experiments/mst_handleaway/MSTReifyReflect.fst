module MSTReifyReflect

open FStar.Tactics
open FStar.Tactics.Typeclasses

open MST
open MST.Tot

class lang_effect (t:Type) = { [@@@no_method] _empty : unit }

instance lang_effect_int : lang_effect int = { _empty = () }

instance lang_effect_pair (t1:Type) {| lang_effect t1 |} (t2:Type) {| lang_effect t2 |} : lang_effect (t1 * t2) = { _empty = () }

instance lang_effect_arrow
  (t1:Type) {| lang_effect t1 |}
  (t2:t1 -> Type) {| (x:t1) -> lang_effect (t2 x) |}
  (wp:(x:t1) -> st_wp (t2 x)) : 
  lang_effect (x:t1 -> STATEwp (t2 x) (wp x)) = { _empty = () }

class lang_repr (t:Type) = { [@@@no_method] _empty : unit }

instance lang_repr_int : lang_repr int = { _empty = () }

instance lang_repr_pair (t1:Type) {| lang_repr t1 |} (t2:Type) {| lang_repr t2 |} : lang_repr (t1 * t2) = { _empty = () }

instance lang_repr_arrow
  (t1:Type) {| lang_repr t1 |}
  (t2:t1 -> Type) {| (x:t1) -> lang_repr (t2 x) |}
  (wp:(x:t1) -> st_wp (t2 x)) : 
  lang_repr (x:t1 -> mheap (t2 x) (wp x)) = { _empty = () }

class my_reflectable (t:Type u#a) = {
  [@@@no_method]
  t_tc : lang_repr t;
  [@@@no_method]
  s : Type u#b;
  [@@@no_method]
  s_tc : lang_effect s;

  my_reflect : t -> s;
}

class my_reifiable (s:Type u#a) = {
  [@@@no_method]
  s_tc : lang_effect s;

  [@@@no_method]
  t : Type u#b;
  [@@@no_method]
  t_tc : lang_repr t;

  my_reify : s -> t;
}

instance my_reflectable_int : my_reflectable int = {
  t_tc = lang_repr_int;
  s = int;
  s_tc = lang_effect_int;
  my_reflect = (fun x -> x);
}

instance my_reflectable_pair (t1:Type) {| c1:my_reflectable t1 |} (t2:Type) {| c2:my_reflectable t2 |} : my_reflectable (t1 * t2) = {
  t_tc = lang_repr_pair t1 #c1.t_tc t2 #c2.t_tc;
  s = c1.s * c2.s;
  s_tc = lang_effect_pair c1.s #c1.s_tc c2.s #c2.s_tc;
  my_reflect = (fun (x, y) -> (c1.my_reflect x, c2.my_reflect y));
}
// TODO: check that this is polymorphic in two universes

instance my_reflectable_arrow 
  (s1:Type) {| c1:my_reifiable s1 |}
  (t2:c1.t -> Type) {| c2:(x:c1.t -> my_reflectable (t2 x)) |}
  (wp:(x:c1.t -> st_wp (t2 x))) 
  : my_reflectable (x:c1.t -> mheap (t2 x) (wp x)) = {
  t_tc = lang_repr_arrow c1.t #c1.t_tc t2 #(fun x -> (c2 x).t_tc) wp;
  s = x:s1 -> STATEwp (c2 (c1.my_reify x)).s (fun p -> wp (c1.my_reify x) (fun (r:t2 (c1.my_reify x)) -> p ((c2 (c1.my_reify x)).my_reflect r)));
  s_tc = lang_effect_arrow s1 #c1.s_tc (fun (x:s1) -> (c2 (c1.my_reify x)).s) #(fun (x:s1) -> (c2 (c1.my_reify x)).s_tc) _;
  my_reflect = (fun (f:(x:c1.t -> mheap (t2 x) (wp x))) ->
    let f' (x:s1) : mheap (c2 (c1.my_reify x)).s (fun p -> wp (c1.my_reify x) (fun (r:t2 (c1.my_reify x)) -> p ((c2 (c1.my_reify x)).my_reflect r))) = begin 
      let x' : c1.t = c1.my_reify x in
      let comp : mheap (t2 x') (wp x') = f x' in
      ((mheap_bind _ _ _ _ comp (fun r -> mheap_return _ ((c2 x').my_reflect r))))
    end in
    let f'' (x:s1) : STATEwp (c2 (c1.my_reify x)).s (fun p -> wp (c1.my_reify x) (fun (r:t2 (c1.my_reify x)) -> p ((c2 (c1.my_reify x)).my_reflect r))) = begin
      STATEwp?.reflect (f' x)
    end in
    f'');
}

instance my_reifiable_int : my_reifiable int = {
  s_tc = lang_effect_int;
  t = int;
  t_tc = lang_repr_int;
  my_reify = (fun x -> x);
}

instance my_reifiable_pair (s1:Type) {| c1:my_reifiable s1 |} (s2:Type) {| c2:my_reifiable s2 |} : my_reifiable (s1 * s2) = {
  s_tc = lang_effect_pair s1 #c1.s_tc s2 #c2.s_tc;
  t = c1.t * c2.t;
  t_tc = lang_repr_pair c1.t #c1.t_tc c2.t #c2.t_tc;
  my_reify = (fun (x, y) -> (c1.my_reify x, c2.my_reify y));
}

instance my_reifiable_arrow 
  (t1:Type) {| c1:my_reflectable t1 |}
  (s2:c1.s -> Type) {| c2:(x:c1.s -> my_reifiable (s2 x)) |}
  (wp:(x:c1.s -> st_wp (s2 x))) 
  : my_reifiable (x:c1.s -> STATEwp (s2 x) (wp x)) = {
  s_tc = lang_effect_arrow c1.s #c1.s_tc s2 #(fun x -> (c2 x).s_tc) wp;
  t = x:t1 -> mheap (c2 (c1.my_reflect x)).t (fun p -> wp (c1.my_reflect x) (fun (r:s2 (c1.my_reflect x)) -> p ((c2 (c1.my_reflect x)).my_reify r)));
  t_tc = lang_repr_arrow t1 #c1.t_tc (fun (x:t1) -> (c2 (c1.my_reflect x)).t) #(fun (x:t1) -> (c2 (c1.my_reflect x)).t_tc) _;
  my_reify = (fun (f:(x:c1.s -> STATEwp (s2 x) (wp x))) ->
    let f' (x:t1) : STATEwp (c2 (c1.my_reflect x)).t (fun p -> wp (c1.my_reflect x) (fun (r:s2 (c1.my_reflect x)) -> p ((c2 (c1.my_reflect x)).my_reify r))) = begin
      let x' : c1.s = c1.my_reflect x in
      let r : (s2 x') = f x' in
      let r' : (c2 x').t = (c2 x').my_reify r in
      admit ();
      r'
    end in
    let f'' (x:t1) : mheap (c2 (c1.my_reflect x)).t (fun p -> wp (c1.my_reflect x) (fun (r:s2 (c1.my_reflect x)) -> p ((c2 (c1.my_reflect x)).my_reify r))) = begin
      reify (f' x)
    end in
    f'');
}

let fixed_wp #a : st_wp a =
  fun p h0 -> forall r h1. p r h1

let linkT
  (pt:((int -> mheap int fixed_wp) -> mheap int fixed_wp))
  (ct:(int -> mheap int fixed_wp)) :
  (unit -> mheap int fixed_wp)
  =
  fun () -> pt ct

let linkS
  (ps:((int -> STATEwp int fixed_wp) -> STATEwp int fixed_wp))
  (cs:(int -> STATEwp int fixed_wp)) :
  (unit -> STATEwp int fixed_wp)
  =
  fun () -> ps cs
  
let behT (f:(unit -> mheap int fixed_wp)) : st_wp int =
  theta (f ())

let behS (f:(unit -> STATEwp int fixed_wp)) : st_wp int =
  theta (reify (f ()))

val compile :
  ((int -> STATEwp int fixed_wp) -> STATEwp int fixed_wp) ->
  ((int -> mheap int fixed_wp) -> mheap int fixed_wp)

let compile ps = 
  (my_reifiable_arrow
    (int -> mheap int fixed_wp)
    #(my_reflectable_arrow int #my_reifiable_int (fun _ -> int) (fun _ -> fixed_wp))
    (fun _ -> int) 
    #(solve)
    (fun _ -> fixed_wp)).my_reify ps

val backtranslate : 
  (int -> mheap int fixed_wp) ->
  (int -> STATEwp int fixed_wp)
let backtranslate ct =
  (my_reflectable_arrow 
    int #my_reifiable_int 
    (fun _ -> int) 
    (fun _ -> fixed_wp)).my_reflect ct

type sc
  (ps:((int -> STATEwp int fixed_wp) -> STATEwp int fixed_wp))
  (ct:(int -> mheap int fixed_wp))
  =
  behS (linkS ps (backtranslate ct)) == behT (linkT (compile ps) ct) (* syntactic equality between behaviors *)

open FStar.Tactics.V2

let lemma_sc ps ct : Lemma (sc ps ct) by (
  norm [delta_only [`%sc;`%behS;`%behT;`%compile;`%backtranslate;`%linkS;`%linkT;`%my_reflectable_arrow;`%my_reifiable_arrow;
   `%lang_repr_arrow;`%lang_effect_arrow;`%my_reflectable_int;`%my_reifiable_int;`%lang_repr_int;`%lang_effect_int;
   `%Mkmy_reflectable?.my_reflect;
   `%Mkmy_reflectable?.s;
   `%Mkmy_reifiable?.my_reify;
   `%Mkmy_reifiable?.t;
  ];zeta;delta;iota];
  norm [iota];
 // tadmit (); (** looks the same, weird it fails, maybe because the previous admit? **)
  dump "H"
)= 
  ()
