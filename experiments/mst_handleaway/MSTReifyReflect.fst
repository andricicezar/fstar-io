module MSTReifyReflect

open FStar.Tactics
open FStar.Tactics.Typeclasses

open MST
open MST.Tot

unfold
let eq_wp wp1 wp2 = wp1 ⊑ wp2 /\ wp2 ⊑ wp1

unfold
let eq_wp_f (f:'a -> 'b) (wp1:st_wp 'a) (wp2:st_wp 'b) =
  st_bind_wp _ _ _ wp1 (fun r -> st_return _ _ (f r)) `eq_wp` wp2

let lemma_eq_wp_f #a #b (w:st_wp a) (f:a -> b) :
  Lemma
    (ensures (w `eq_wp_f f` (st_bind_wp _ _ _ w (fun x -> st_return _ _ (f x))))) = () (** REFL **)

let rec lemma_theta_bind_pure (m:mheap 'a 'w) (f:'a -> 'b) :
  Lemma (ensures (theta m `eq_wp_f f` theta (mheap_bind _ _ _ _ m (fun x -> mheap_return _ (f x))))) (decreases m) = admit ()

let lemma_theta_bind_id (m:mheap 'a 'w) :
  Lemma (eq_wp 
    (theta (mheap_bind 'a 'a 'w (fun x -> st_return _ 'a x) m (fun x -> mheap_return 'a x)))
    (theta m)) = 
  lemma_theta_bind_pure m id

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
  s = x:s1 -> STATEwp (c2 (c1.my_reify x)).s (fun (p:st_post (c2 (c1.my_reify x)).s) -> wp (c1.my_reify x) (fun (r:t2 (c1.my_reify x)) -> p ((c2 (c1.my_reify x)).my_reflect r)));
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

let helper_reifiable_arrow_wp 
  (s1:Type)
  (s2:s1 -> Type) {| c2:(x:s1 -> my_reifiable (s2 x)) |}
  (wp:(x:s1 -> st_wp (s2 x)))
  (x' : s1)
  : st_wp (c2 x').t =
  (fun (p:(st_post (c2 x').t)) -> wp x' (fun (r:s2 x') -> p ((c2 x').my_reify r)))

let helper_reifiable_arrow
  (s1:Type)
  (s2:s1 -> Type) {| c2:(x:s1 -> my_reifiable (s2 x)) |}
  (wp:(x:s1 -> st_wp (s2 x))) 
  (f:(x:s1 -> STATEwp (s2 x) (wp x)))
  (x':s1)
  : STATEwp (c2 x').t (helper_reifiable_arrow_wp s1 s2 #c2 wp x') =
  (c2 x').my_reify (f x')

let helper_reifiable_arrow'
  (t1:Type) {| c1:my_reflectable t1 |}
  (s2:c1.s -> Type) {| c2:(x:c1.s -> my_reifiable (s2 x)) |}
  (wp:(x:c1.s -> st_wp (s2 x))) 
  (f:(x:c1.s -> STATEwp (s2 x) (wp x)))
  (x:t1)
  : STATEwp (c2 (c1.my_reflect x)).t (helper_reifiable_arrow_wp c1.s s2 #c2 wp (c1.my_reflect x)) =
  helper_reifiable_arrow c1.s s2 #c2 wp f (c1.my_reflect x)

instance my_reifiable_arrow 
  (t1:Type) {| c1:my_reflectable t1 |}
  (s2:c1.s -> Type) {| c2:(x:c1.s -> my_reifiable (s2 x)) |}
  (wp:(x:c1.s -> st_wp (s2 x))) 
  : my_reifiable (x:c1.s -> STATEwp (s2 x) (wp x)) = {
  s_tc = lang_effect_arrow c1.s #c1.s_tc s2 #(fun (x:c1.s) -> (c2 x).s_tc) wp;
  t = x:t1 -> mheap (c2 (c1.my_reflect x)).t (fun (p:st_post (c2 (c1.my_reflect x)).t) -> wp (c1.my_reflect x) (fun (r:s2 (c1.my_reflect x)) -> p ((c2 (c1.my_reflect x)).my_reify r)));
  t_tc = lang_repr_arrow t1 #c1.t_tc (fun (x:t1) -> (c2 (c1.my_reflect x)).t) #(fun (x:t1) -> (c2 (c1.my_reflect x)).t_tc) _;
  my_reify = (fun (f:(x:c1.s -> STATEwp (s2 x) (wp x))) (x:t1) ->
    reify (helper_reifiable_arrow' t1 #c1 s2 #c2 wp f x));
}

(** TODO: Why does this work? **)
let reify_lemma (#a:Type) (#b:Type) (#wp:a -> st_wp b) (f:(x:a -> STATEwp b (wp x))) (x:a) : 
  Lemma (
    (theta (reify (let y = f x in y))) `eq_wp`
    (theta (reify (f x)))) = ()

let lemma_reify_reflect (f:mheap int 'w) :
  Lemma (theta (reify (STATEwp?.reflect f)) `eq_wp` theta f) = admit ()

open BeyondCriteria
open FStar.FunctionalExtensionality


let fixed_wp #a : st_wp a = (** TODO: probably this can be generalized *)
  fun p h0 -> forall r h1. p r h1

noeq
type src_interface1 = {
  ct : Type;
  ct_reflectable : my_reflectable ct;

  prog_wp : ct_reflectable.s -> st_wp int;
}
  
type ctx_src1 (i:src_interface1)  = i.ct_reflectable.s
type prog_src1 (i:src_interface1) = i.ct_reflectable.s -> STATEwp int fixed_wp
type whole_src1 = unit -> STATEwp int fixed_wp

let link_src1 (#i:src_interface1) (p:prog_src1 i) (c:ctx_src1 i) : whole_src1 =
  fun () -> p c


val beh_src1 : whole_src1 ^-> st_mwp_h heap_state.t int
let beh_src1 = on_domain whole_src1 (fun ws -> theta (reify (ws ())))

let src_language1 : language (st_wp int) = {
  interface = src_interface1;
  ctx = ctx_src1; pprog = prog_src1; whole = whole_src1;
  link = link_src1;
  beh = beh_src1;
}

noeq
type tgt_interface1 = {
  ct : Type;
}

type ctx_tgt1 (i:tgt_interface1) = i.ct
type prog_tgt1 (i:tgt_interface1) = i.ct -> mheap int fixed_wp
type whole_tgt1 = (unit -> mheap int fixed_wp)

let link_tgt1 (#i:tgt_interface1) (p:prog_tgt1 i) (c:ctx_tgt1 i) : whole_tgt1 =
  fun () -> p c 

val beh_tgt1 : whole_tgt1 ^-> st_mwp_h heap_state.t int
let beh_tgt1 = on_domain whole_tgt1 (fun wt -> theta (wt ()))

let tgt_language1 : language (st_wp int) = {
  interface = tgt_interface1;
  ctx = ctx_tgt1; pprog = prog_tgt1; whole = whole_tgt1;
  link = link_tgt1;
  beh = beh_tgt1;
}

let comp_int_src_tgt1 (i:src_interface1) : tgt_interface1 = {
  ct = i.ct;
}

val backtranslate1 : (#i:src_interface1) -> ctx_tgt1 (comp_int_src_tgt1 i) -> src_language1.ctx i
let backtranslate1 #i ct = i.ct_reflectable.my_reflect ct

val compile_pprog1 : (#i:src_interface1) -> prog_src1 i -> prog_tgt1 (comp_int_src_tgt1 i)
let compile_pprog1 #i ps =
  (my_reifiable_arrow i.ct #i.ct_reflectable (fun _ -> int) (fun _ -> fixed_wp)).my_reify ps

let comp1 : compiler = {
  src_sem = st_wp int;
  tgt_sem = st_wp int;
  source = src_language1;
  target = tgt_language1;

  comp_int = comp_int_src_tgt1;

  compile_pprog = compile_pprog1;

  rel_sem = eq_wp;
}

val comp1_rrhc : unit -> Lemma (rrhc comp1)
let comp1_rrhc () : Lemma (rrhc comp1) =
  assert (rrhc comp1) by (
    norm [delta_only [`%rrhc]]; 
    let i = forall_intro () in
    let ct = forall_intro () in
    FStar.Tactics.witness (`(backtranslate1 #(`#i) (`#ct)));
    compute ())

let exempe1 : src_interface1 = {
  ct = int -> mheap int fixed_wp;
  ct_reflectable = my_reflectable_arrow int #my_reifiable_int (fun _ -> int) (fun _ -> fixed_wp);
}

(** ** The other setting **)
noeq
type src_interface2 = {
  pt : Type;
  pt_reifiable : my_reifiable pt;
}
  
type ctx_src2 (i:src_interface2)  = i.pt -> STATEwp int fixed_wp
type prog_src2 (i:src_interface2) = i.pt
type whole_src2 = unit -> STATEwp int fixed_wp

let link_src2 (#i:src_interface2) (p:prog_src2 i) (c:ctx_src2 i) : whole_src2 =
  fun () -> c p


val beh_src2 : whole_src2 ^-> st_mwp_h heap_state.t int
let beh_src2 = on_domain whole_src2 (fun ws -> theta (reify (ws ())))

let src_language2 : language (st_wp int) = {
  interface = src_interface2;
  ctx = ctx_src2; pprog = prog_src2; whole = whole_src2;
  link = link_src2;
  beh = beh_src2;
}

noeq
type tgt_interface2 = {
  pt : Type;
}

type ctx_tgt2 (i:tgt_interface2) = i.pt -> mheap int fixed_wp
type prog_tgt2 (i:tgt_interface2) = i.pt
type whole_tgt2 = (unit -> mheap int fixed_wp)

let link_tgt2 (#i:tgt_interface2) (p:prog_tgt2 i) (c:ctx_tgt2 i) : whole_tgt2 =
  fun () -> c p

val beh_tgt2 : whole_tgt2 ^-> st_mwp_h heap_state.t int
let beh_tgt2 = on_domain whole_tgt2 (fun wt -> theta (wt ()))

let tgt_language2 : language (st_wp int) = {
  interface = tgt_interface2;
  ctx = ctx_tgt2; pprog = prog_tgt2; whole = whole_tgt2;
  link = link_tgt2;
  beh = beh_tgt2;
}

let comp_int_src_tgt2 (i:src_interface2) : tgt_interface2 = {
  pt = i.pt_reifiable.t;
}

val backtranslate2 : (#i:src_interface2) -> ctx_tgt2 (comp_int_src_tgt2 i) -> src_language2.ctx i
let backtranslate2 #i ct = 
  (my_reflectable_arrow i.pt #i.pt_reifiable (fun _ -> int) (fun _ -> fixed_wp)).my_reflect ct

val compile_pprog2 : (#i:src_interface2) -> prog_src2 i -> prog_tgt2 (comp_int_src_tgt2 i)
let compile_pprog2 #i ps =
  i.pt_reifiable.my_reify ps

let comp2 : compiler = {
  src_sem = st_wp int;
  tgt_sem = st_wp int;
  source = src_language2;
  target = tgt_language2;

  comp_int = comp_int_src_tgt2;

  compile_pprog = compile_pprog2;

  rel_sem = eq_wp;
}

let exemple2 : src_interface2 = {
  pt = int -> STATEwp int fixed_wp;
  pt_reifiable = my_reifiable_arrow int #my_reflectable_int (fun _ -> int) (fun _ -> fixed_wp);
}

(** ** RrHC **)

let comp2_rrhc0 i ct ps : Lemma (
  comp2.rel_sem 
    (comp2.source.beh (comp2.source.link #i ps (backtranslate2 ct)))
    (comp2.target.beh (comp2.target.link #(comp_int_src_tgt2 i) (comp2.compile_pprog ps) ct))) =
  calc (eq_wp) {
    beh_src2 (link_src2 #i ps (backtranslate2 ct));
    `eq_wp` { _ by (compute ()) } 
    theta (reify (STATEwp?.reflect (mheap_bind int int fixed_wp (fun r -> st_return heap_state.t int r)
                      (ct (i.pt_reifiable.my_reify ps))
                      (fun r -> mheap_return int r))));
    `eq_wp` {
      lemma_reify_reflect #fixed_wp (mheap_bind int int fixed_wp (fun r -> st_return heap_state.t int r)
                      (ct (i.pt_reifiable.my_reify ps))
                      (fun r -> mheap_return int r))
    }
    theta (mheap_bind int int fixed_wp (fun r -> st_return heap_state.t int r)
                      (ct (i.pt_reifiable.my_reify ps))
                      (fun r -> mheap_return int r));
    `eq_wp` { lemma_theta_bind_id (ct (i.pt_reifiable.my_reify ps)) }
    theta (ct (i.pt_reifiable.my_reify ps));
    `eq_wp` { _ by (compute ()) } 
    beh_tgt2 (link_tgt2 #(comp_int_src_tgt2 i) (compile_pprog2 #i ps) ct);
  }

val comp2_rrhc : unit -> Lemma (rrhc comp2)
let comp2_rrhc () : Lemma (rrhc comp2) =
  assert (rrhc comp2) by (
    norm [delta_only [`%rrhc]]; 
    let i = forall_intro () in
    let ct = forall_intro () in
    FStar.Tactics.witness (`(backtranslate2 #(`#i) (`#ct)));
    let ps = forall_intro () in
    mapply (`comp2_rrhc0))
