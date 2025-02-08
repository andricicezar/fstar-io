module Compiler

open MST.Repr
open MST.Tot
open SharedRefs
open TargetLang
open BeyondCriteria

let default_spec : targetlang_pspec = (
    (fun h -> 
        trans_shared_contains h /\
        h `contains` map_shared /\ 
        ~(is_shared (map_shared) h) /\
        (forall p. p >= next_addr h ==> ~(sel h map_shared p))),
    (fun #a #rel (r:mref a rel) -> witnessed (contains_pred r) /\ witnessed (is_shared r)),
    (fun h0 h1 -> modifies_only_shared h0 h1 /\ gets_shared Set.empty h0 h1)
)

noeq
type src_interface1 = {
  ct : Type;
  ct_targetlang : targetlang default_spec ct;
}

type ctx_src1 (i:src_interface1)  = i.ct
type prog_src1 (i:src_interface1) = i.ct -> SST int (fun h0 -> True) (fun h0 _ h1 -> True)
type whole_src1 = unit -> SST int (fun h0 -> True) (fun h0 _ h1 -> True)

let link_src1 (#i:src_interface1) (p:prog_src1 i) (c:ctx_src1 i) : whole_src1 =
  fun () -> p c

open FStar.FunctionalExtensionality

val beh_src1 : whole_src1 ^-> st_mwp_h heap int
let beh_src1 = on_domain whole_src1 (fun ws -> theta (reify (ws ()))) (** what happens with the pre-condition? **)

let src_language1 : language (st_wp int) = {
  interface = src_interface1;
  ctx = ctx_src1; pprog = prog_src1; whole = whole_src1;
  link = link_src1;
  beh = beh_src1;
}

noeq
type tgt_interface1 = {
  ct : inv : (heap -> Type0) -> prref: mref_pred -> hrel : FStar.Preorder.preorder heap -> Type u#a;
  ct_targetlang : targetlang default_spec (ct (Mktuple3?._1 default_spec) (Mktuple3?._2 default_spec) (Mktuple3?._3 default_spec));
}

type ctx_tgt1 (i:tgt_interface1) = 
  inv  : (heap -> Type0) -> 
  prref: mref_pred ->
  (** ^ if this predicate would be also over heaps, then the contexts needs witness&recall in HO settings **)
  hrel : FStar.Preorder.preorder heap ->
  read :  ((#t:shareable_typ) -> r:ref (to_Type t) -> 
            ST (to_Type t) 
              (requires (fun h0 -> inv h0 /\ prref r))
              (ensures  (fun h0 v h1 -> h0 `hrel` h1 /\ inv h1 /\ forall_refs prref v))) -> 
  write : ((#t:shareable_typ) -> r:ref (to_Type t) -> v:(to_Type t) -> 
            ST unit
              (requires (fun h0 -> inv h0 /\ prref r /\ forall_refs prref v))
              (ensures  (fun h0 _ h1 -> h0 `hrel` h1 /\ inv h1))) ->
  alloc : ((#t:shareable_typ) -> init:(to_Type t) -> 
            ST (ref (to_Type t)) 
              (requires (fun h0 -> inv h0 /\ forall_refs prref init))
              (ensures  (fun h0 r h1 -> h0 `hrel` h1 /\ inv h1 /\ prref r))) ->
  i.ct inv prref hrel
  
type prog_tgt1 (i:tgt_interface1) = i.ct (Mktuple3?._1 default_spec) (Mktuple3?._2 default_spec) (Mktuple3?._3 default_spec) -> SST int (fun _ -> True) (fun _ _ _ -> True)
type whole_tgt1 = (unit -> SST int (fun _ -> True) (fun _ _ _ -> True))



#push-options "--split_queries always"
val instantiate_ctx_tgt1 : (#i:tgt_interface1) -> ctx_tgt1 i -> i.ct (Mktuple3?._1 default_spec) (Mktuple3?._2 default_spec) (Mktuple3?._3 default_spec)
let instantiate_ctx_tgt1 c =
  let c' = c (Mktuple3?._1 default_spec) (Mktuple3?._2 default_spec) (Mktuple3?._3 default_spec) in
  let c'' = c' (fun #t r -> (* READ *)
      let h0 = get_heap () in
      recall (contains_pred r); 
      recall (is_shared r);
      let v = read r in
      assert (forall_refs_heap contains_pred h0 v);
      assert (forall_refs_heap is_shared h0 v);
      lemma_forall_refs_heap_forall_refs_witnessed v contains_pred;
      lemma_forall_refs_heap_forall_refs_witnessed v is_shared;
      lemma_forall_refs_join v (fun r -> witnessed (contains_pred r)) (fun r -> witnessed (is_shared r));
      v) 
    (fun #t r v -> (* WRITE *)
      recall (contains_pred r);
      recall (is_shared r);
      let h0 = get_heap () in
      lemma_forall_refs_split v (fun r -> witnessed (contains_pred r)) (fun r -> witnessed (is_shared r));
      lemma_forall_refs_witnessed_forall_refs_heap v contains_pred;
      lemma_forall_refs_witnessed_forall_refs_heap v is_shared;
      sst_write r v;
      let h1 = get_heap () in
      assert (modifies_only_shared h0 h1 /\ gets_shared Set.empty h0 h1);

      assert (trans_shared_contains h1);
      assert (h1 `contains` map_shared);
      assert (~(is_shared (map_shared) h1));
      assert ((forall p. p >= next_addr h1 ==> ~(sel h1 map_shared p)))
      )
    (fun #t init -> (* ALLOC *)
      assert (forall_refs (fun r' -> witnessed (contains_pred r') /\ witnessed (is_shared r')) init);
      lemma_forall_refs_split init (fun r -> witnessed (contains_pred r)) (fun r -> witnessed (is_shared r));
      lemma_forall_refs_witnessed_forall_refs_heap init contains_pred;
      lemma_forall_refs_witnessed_forall_refs_heap init is_shared;
      let r = sst_alloc_shared init in 
      witness (contains_pred r); witness (is_shared r);
      r) in
  c''
#pop-options

val link_tgt1 : #i:tgt_interface1 -> prog_tgt1 i -> ctx_tgt1 i -> whole_tgt1
let link_tgt1 p c =
  fun () -> p (instantiate_ctx_tgt1 c)

val beh_tgt1 : whole_tgt1 ^-> st_mwp_h heap int
let beh_tgt1 = on_domain whole_tgt1 (fun wt -> theta (reify (wt ())))

let tgt_language1 : language (st_wp int) = {
  interface = tgt_interface1;
  ctx = ctx_tgt1; pprog = prog_tgt1; whole = whole_tgt1;
  link = link_tgt1;
  beh = beh_tgt1;
}

let comp_int_src_tgt1 (i:src_interface1) : tgt_interface1 = {
  ct = (fun _ _ _ -> i.ct);
  ct_targetlang = i.ct_targetlang;
}

val backtranslate_ctx1 : (#i:src_interface1) -> ctx_tgt1 (comp_int_src_tgt1 i) -> src_language1.ctx i
let backtranslate_ctx1 ct = instantiate_ctx_tgt1 ct

val compile_pprog1 : (#i:src_interface1) -> prog_src1 i -> prog_tgt1 (comp_int_src_tgt1 i)
let compile_pprog1 #i ps = ps

unfold
let eq_wp wp1 wp2 = wp1 ⊑ wp2 /\ wp2 ⊑ wp1

let comp1 : compiler = {
  src_sem = st_wp int;
  tgt_sem = st_wp int;
  source = src_language1;
  target = tgt_language1;

  comp_int = comp_int_src_tgt1;

  compile_pprog = compile_pprog1;

  rel_sem = eq_wp;
}

open FStar.Tactics

val comp1_rrhc : unit -> Lemma (rrhc comp1)
let comp1_rrhc () : Lemma (rrhc comp1) =
  assert (rrhc comp1) by (
    norm [delta_only [`%rrhc]]; 
    let i = forall_intro () in
    let ct = forall_intro () in
    FStar.Tactics.witness (`(backtranslate_ctx1 #(`#i) (`#ct)));
    compute ())
