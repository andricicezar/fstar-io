module TC.Instrumentable.IIOwp

open FStar.List.Tot
open FStar.Tactics
open FStar.Tactics.Typeclasses

open IO.Sig
open Common
open TC.ML
open TC.ML.HO
open TC.Export
open TC.Monitorable.Hist
open DM.IIO

let extract_local_trace (h':trace) (pi:monitorable_prop) :
  IIO trace
    (requires (fun h -> h' `suffix_of` h))
    (ensures (fun h lt' lt ->
      lt == [] /\
      enforced_locally pi h lt /\
      h == (apply_changes h' lt'))) =
  let h = get_trace () in
  suffix_of_length h' h;
  let n : nat = (List.length h) - (List.length h') in
  let (lt', ht) = List.Tot.Base.splitAt n h in
  lemma_splitAt_equal n h;
  lemma_splitAt_suffix h h';
  List.Tot.Properties.rev_involutive lt';
  assert (h == apply_changes h' (List.rev lt'));
  List.rev lt'

let enforce_post
  (#t1 #t2:Type)
  (pi:monitorable_prop)
  (pre:t1 -> trace -> Type0)
  (post:t1 -> trace -> (r:maybe t2) -> trace -> Type0)
  {| post_c:monitorable_post pre post pi |}
  (f:t1 -> IIOpi (maybe t2) pi)
  (x:t1) :
  IIO (maybe t2) (pre x) (post x) =
  let h = get_trace () in
  let r : maybe t2 = f x in
  Classical.forall_intro (lemma_suffixOf_append h);
  let lt = extract_local_trace h pi in
  Classical.forall_intro_2 (Classical.move_requires_2 (lemma_append_rev_inv_tail h));
  if post_c.result_check x h r lt then r
  else Inr Contract_failure

instance instrumentable_IIO 
  (#t1:Type) (#t2:Type) {| d1:mlfo t1 |} {| d2:mlfo t2 |}
  (pre : t1 -> trace -> Type0)
  (** it must be `maybe t2` because needs the ability to fail **)
  (post : t1 -> trace -> (r:maybe t2) -> trace -> Type0)
  (pi : monitorable_prop) {| post_c:monitorable_post pre post pi |} : 
  instrumentable ((x:t1) -> IIO (maybe t2) (pre x) (post x)) =
  { inst_type = t1 -> IIOpi (maybe t2) pi;
    cinst_type = ml_instrumented_iio t1 (maybe t2) #(ML_FO d1) #(ML_FO (mlfo_maybe t2)) pi;
    strengthen = (fun (f:(t1 -> IIOpi (maybe t2) pi)) ->
      enforce_post #t1 #t2 pi pre post #post_c f)
  }
