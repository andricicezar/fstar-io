module TC.Instrumentable.IIOwp

open FStar.List.Tot
open FStar.Tactics
open FStar.Tactics.Typeclasses

open IO.Sig
open Common
open TC.Export
open TC.Monitorable.Hist
open TC.MLify
include TC.Instrumentable
open DM.IIO

let iio_post
  (#a:Type)
  (pi : monitorable_prop)
  (h:trace)
  (result:a)
  (local_trace:trace) :
  Tot bool =
  enforced_locally pi h local_trace

effect IIOpi
  (a:Type)
  (pi : monitorable_prop)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  IIOwp a
    (fun p h ->
      pre h /\
      (forall r lt. (iio_post pi h r lt /\ post h r lt) ==> p lt r))

let extract_local_trace (h':trace) (pi:monitorable_prop) :
  IIOpi trace pi
    (requires (fun h -> h' `suffix_of` h))
    (ensures (fun h lt' lt ->
      lt == [] /\
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
  (post:t1 -> trace -> (r:maybe t2) -> trace -> (b:Type0{r == Inr Contract_failure ==> b}))
  {| post_c:monitorable_post pre post pi |}
  (f:t1 -> IIOpi (maybe t2) pi (fun _ -> True) (fun _ _ _ -> True))
  (x:t1) :
  IIOpi (maybe t2) pi (pre x) (post x) =
  let h = get_trace () in
  let r : maybe t2 = f x in
  Classical.forall_intro (lemma_suffixOf_append h);
  let lt = extract_local_trace h pi in
  Classical.forall_intro_2 (Classical.move_requires_2 (lemma_append_rev_inv_tail h));
  if post_c.result_check x h r lt then begin
    r
  end else Inr Contract_failure

instance instrumentable_IIO 
  (#t1:Type) (#t2:Type) {| d1:ml t1 |} {| d2:ml t2 |}
  (pre : t1 -> trace -> Type0)
  (** it must be `maybe t2` because needs the ability to fail **)
  (post : t1 -> trace -> (r:maybe t2) -> trace -> (b:Type0{r == Inr Contract_failure ==> b}))
  (pi : monitorable_prop) {| post_c:monitorable_post pre post pi |} : 
  instrumentable ((x:t1) -> IIOpi (maybe t2) pi (pre x) (post x)) =
  { a = t1; b = t2; a_c = d1; b_c = d2;
    start_type = t1 -> Tot (maybe t2);
    start_type_c = ml_arrow_tot_1 t1 (maybe t2);
    instrument = (fun (f:t1 -> Tot (maybe t2)) ->
      (** automatic lift from Pure to IIO. 
        The explicit (fun x -> f x) is necessary for the lift to be added by F*.
        we can say that f respects pi because a Pure computation has an empty trace. **)
      let f' : t1 -> IIOpi (maybe t2) pi (fun _ -> True) (fun _ _ _ -> True) = (fun x -> f x) in 
      enforce_post #t1 #t2 pi pre post #post_c f')
  }
