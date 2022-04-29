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

(** TODO: add importable/exportable types here **)

instance instrumentable_IIO 
  (#t1:Type) (#t2:Type) {| d1:mlfo t1 |} {| d2:mlfo t2 |}
  (pre : t1 -> trace -> Type0)
  (** it must be `maybe t2` because needs the ability to fail **)
  (post : t1 -> trace -> (r:maybe t2) -> trace -> Type0)
  (pi : monitorable_prop) {| post_c:monitorable_post pre post pi |} : 
  instrumentable ((x:t1) -> IIO (maybe t2) (pre x) (post x)) =
  { inst_type = t1 -> IIOpi (maybe t2) pi;
    cinst_type = ml_instrumented_iio t1 (maybe t2) #(ML_FO d1) #(ML_FO (mlfo_maybe t2 #(ML_FO d2))) pi;
    strengthen = (fun (f:(t1 -> IIOpi (maybe t2) pi)) ->
      enforce_post #t1 #t2 pi pre post #post_c f)
  }

(** ** Higher order **)

(** 
Be the following example:
  type ftype = a -> IO b fpre fpost
  val prog: (ctx: (f:ftype -> IO c cpre cpost) -> IO d ppre ppost.
For ctx to be instrumentable, the post of f should also respect pi. 
The post-condition of the ctx must respect pi, but because f is not instrumented, it can break this guarantee. Therefore, f can be mlifyied if its post implies the pi. **)
class mlifyable_guarded (a b:Type) pre post pi =
  { cmlifyable : mlifyable ((x:a) -> IIO b (pre x) (post x));
    cpi : squash (forall (x:a) h lt r. pre x h /\ post x h r lt ==> enforced_locally pi h lt) }

(** 
this instance should let us mlify example 1.
the problems here are the following:
1. c is a ml type.
2. enforce_post appears here in a kind of weird position **)

let import_out t1 t2 {| d0:importable (maybe t2) |} (pi:monitorable_prop) 
  (f:t1 -> IIOpi d0.itype pi) 
  (x:t1) : 
  IIOpi (maybe t2) pi =
  match import (f x) with
  | Some x' -> x'
  | None -> Inr Contract_failure

instance instrumentable_HO
  fin fout fpre fpost 
  cout cpre cpost 
  pi 
  {| d0:importable (maybe cout) |}
  {| d1:mlifyable_guarded fin fout fpre fpost pi |}
  {| d2:monitorable_post (fun x -> cpre) (fun x -> cpost) pi |} : 
  instrumentable ((x:fin -> IIO fout (fpre x) (fpost x)) -> DM.IIO.IIO (maybe cout) cpre cpost) =
  {
    inst_type = d1.cmlifyable.matype -> IIOpi d0.itype pi;
    cinst_type = ml_instrumented_iio d1.cmlifyable.matype d0.itype #(ML_ARROW d1.cmlifyable.cmatype) #(ML_FO d0.citype) pi;
    strengthen = (fun (ctx:(d1.cmlifyable.matype -> IIOpi d0.itype pi)) -> 
      (fun (f:(x:fin -> IIO fout (fpre x) (fpost x))) -> 
        (** TODO: import the result **)
        (let ctx' = import_out d1.cmlifyable.matype cout #d0 pi ctx in
        enforce_post pi (fun x -> cpre) (fun x -> cpost) #d2 ctx' (d1.cmlifyable.mlify f)) <: IIO (maybe cout) cpre cpost))
  }

let strengthen_out t1 t2 {| d0:instrumentable t2 |} (pi:monitorable_prop) 
  (f:t1 -> IIOpi (maybe d0.inst_type) pi) 
  (x:t1) : 
  IIOpi (maybe t2) pi =
  match (f x) with
  | Inl g -> Inl (d0.strengthen g)
  | Inr err -> Inr err

instance instrumentable_HO_2
  fin fout fpre fpost 
  cout cpre cpost 
  pi 
  {| d0:instrumentable cout |}
  {| d1:mlifyable_guarded fin fout fpre fpost pi |}
  {| d2:monitorable_post (fun x -> cpre) (fun x -> cpost) pi |} : 
  instrumentable ((x:fin -> IIO fout (fpre x) (fpost x)) -> DM.IIO.IIO (maybe cout) cpre cpost) =
  {
    inst_type = d1.cmlifyable.matype -> IIOpi (maybe d0.inst_type) pi;
    cinst_type = ml_instrumented_iio d1.cmlifyable.matype (maybe d0.inst_type) #(ML_ARROW d1.cmlifyable.cmatype) #(ML_FO (mlfo_maybe d0.inst_type #(ML_INST d0.cinst_type))) pi;
    strengthen = (fun (ctx:(d1.cmlifyable.matype -> IIOpi (maybe d0.inst_type) pi)) -> 
      (fun (f:(x:fin -> IIO fout (fpre x) (fpost x))) -> 
        (** TODO: import the result **)
        (let ctx' = strengthen_out d1.cmlifyable.matype _ #d0 pi ctx in 
        enforce_post pi (fun x -> cpre) (fun x -> cpost) #d2 ctx' (d1.cmlifyable.mlify f)) <: IIO (maybe cout) cpre cpost))
  }
