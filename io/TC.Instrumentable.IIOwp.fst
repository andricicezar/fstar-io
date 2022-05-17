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
  {| post_c:checkable_hist_post pre post pi |}
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
  (pi : monitorable_prop) {| post_c:checkable_hist_post pre post pi |} : 
  instrumentable ((x:t1) -> IIO (maybe t2) (pre x) (post x)) pi =
  { inst_type = t1 -> IIOpi (maybe t2) pi;
    cinst_type = ml_instrumented_iio t1 #(ML_FO d1) (maybe t2) #(ML_FO (mlfo_maybe t2 #(ML_FO d2))) pi;
    strengthen = (fun f ->
      enforce_post #t1 #t2 pi pre post #post_c f)
  }
  
instance instrumentable_IIO_strengthen
  (t1:Type) {| d1:exportable t1 |}
  (t2:Type) {| d2:importable t2 |}
  (pre : t1 -> trace -> Type0)
  (** it must be `maybe t2` because needs the ability to fail **)
  (post : t1 -> trace -> (r:maybe t2) -> trace -> Type0)
  (pi : monitorable_prop) {| post_c:checkable_hist_post pre post pi |} : 
  instrumentable ((x:t1) -> IIO (maybe t2) (pre x) (post x)) pi =
  { inst_type = d1.etype -> IIOpi (maybe d2.itype) pi;
    cinst_type = ml_instrumented_iio d1.etype #(ML_FO d1.cetype) (maybe d2.itype) #(ML_FO (mlfo_maybe d2.itype #(ML_FO d2.citype))) pi;
    strengthen = (fun f ->
      let f' : t1 -> IIOpi (maybe t2) pi = (fun (x:t1) -> 
        match f (export x) with 
        | Inl x' -> (match import x' with | Some x' -> Inl x' | None -> Inr Contract_failure)
        | Inr err -> Inr err) in
      enforce_post #t1 #t2 pi pre post #post_c f')
  }
  
instance instrumentable_IIO_strengthen_inst
  (t1:Type) {| d1:exportable t1 |}
  (t2:Type)
  (pre : t1 -> trace -> Type0)
  (** it must be `maybe t2` because needs the ability to fail **)
  (post : t1 -> trace -> (r:maybe t2) -> trace -> Type0)
  (pi : monitorable_prop) {| post_c:checkable_hist_post pre post pi |}
  {| d2:instrumentable t2 pi |} :
  instrumentable ((x:t1) -> IIO (maybe t2) (pre x) (post x)) pi =
  { inst_type = d1.etype -> IIOpi (maybe d2.inst_type) pi;
    cinst_type = ml_instrumented_iio d1.etype #(ML_FO d1.cetype) (maybe d2.inst_type) #(ML_FO (mlfo_maybe d2.inst_type #(ML_ARROW d2.cinst_type))) pi;
    strengthen = (fun f ->
      let f' : t1 -> IIOpi (maybe t2) pi = (fun (x:t1) -> 
        match f (export x) with 
        | Inr err -> Inr err
        | Inl r -> Inl (d2.strengthen r)) in
      enforce_post #t1 #t2 pi pre post #post_c f')
  }

(** ** Higher order **)

(** 
Be the following example:
  type ftype = a -> IO b fpre fpost
  val prog: (ctx: (f:ftype -> IO c cpre cpost) -> IO d ppre ppost.
For ctx to be instrumentable, the post of f should also respect pi. 
The post-condition of the ctx must respect pi, but because f is not instrumented, it can break this guarantee. Therefore, f can be mlifyied if its post implies the pi. **)
class mlifyable_in_arr0 (a b:Type) pre post pi =
  { cmlifyable0 : mlifyable (a -> IIO (maybe b) pre post) pi;
    ca0: instrumentable a pi;
  //  cpi0 : squash (forall h lt r. pre h /\ post h r lt ==> enforced_locally pi h lt)
  }

class mlifyable_in_arr1 (a b:Type) (pre:a -> trace -> Type0) (post:a -> trace -> maybe b -> trace -> Type0) pi =
  { cmlifyable1 : mlifyable ((x:a) -> IIO (maybe b) (pre x) (post x)) pi;
    ca1: importable a;
 //   cpi1 : squash (forall (x:a) h lt r. pre x h /\ post x h r lt ==> enforced_locally pi h lt) 
 }

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

instance instrumentable_HO_arr0_out_importable
  fin fout fpre fpost 
  cout cpre cpost 
  pi 
  {| d0:importable (maybe cout) |}
  {| d1:mlifyable_in_arr0 fin fout fpre fpost pi |}
  {| d2:checkable_hist_post #d1.cmlifyable0.matype #cout (fun x -> cpre) (fun x -> cpost) pi |} : 
  instrumentable ((fin -> IIO (maybe fout) fpre fpost) -> DM.IIO.IIO (maybe cout) cpre cpost) pi =
  {
    inst_type = d1.cmlifyable0.matype -> IIOpi d0.itype pi;
    cinst_type = ml_instrumented_iio d1.cmlifyable0.matype #(ML_ARROW d1.cmlifyable0.cmatype) d0.itype #(ML_FO d0.citype) pi;
    strengthen = (fun (ctx:(d1.cmlifyable0.matype -> IIOpi d0.itype pi)) -> 
      (fun (f:(fin -> IIO (maybe fout) fpre fpost)) -> 
        (
        let f' = d1.cmlifyable0.mlify f in
        let ctx' = import_out d1.cmlifyable0.matype cout #d0 pi ctx in
        enforce_post pi (fun x -> cpre) (fun x -> cpost) #d2 ctx' f') <: IIO (maybe cout) cpre cpost))
  }

instance instrumentable_HO_arr1_out_importable
  fin fout fpre fpost 
  cout cpre cpost 
  pi 
  {| d0:importable (maybe cout) |}
  {| d1:mlifyable_in_arr1 fin fout fpre fpost pi |}
  {| d2:checkable_hist_post #d1.cmlifyable1.matype #cout (fun x -> cpre) (fun x -> cpost) pi |} : 
  instrumentable ((x:fin -> IIO (maybe fout) (fpre x) (fpost x)) -> DM.IIO.IIO (maybe cout) cpre cpost) pi =
  {
    inst_type = d1.cmlifyable1.matype -> IIOpi d0.itype pi;
    cinst_type = ml_instrumented_iio d1.cmlifyable1.matype #(ML_ARROW d1.cmlifyable1.cmatype) d0.itype #(ML_FO d0.citype) pi;
    strengthen = (fun (ctx:(d1.cmlifyable1.matype -> IIOpi d0.itype pi)) -> 
      (fun (f:(x:fin -> IIO (maybe fout) (fpre x) (fpost x))) -> 
        (
        let f' = d1.cmlifyable1.mlify f in
        let ctx' = import_out d1.cmlifyable1.matype cout #d0 pi ctx in
        enforce_post pi (fun x -> cpre) (fun x -> cpost) #d2 ctx' f') <: IIO (maybe cout) cpre cpost))
  }

let strengthen_out t1 t2 (pi:monitorable_prop) {| d0:instrumentable t2 pi |}
  (f:t1 -> IIOpi (maybe d0.inst_type) pi) 
  (x:t1) : 
  IIOpi (maybe t2) pi =
  match (f x) with
  | Inl g -> Inl (d0.strengthen g)
  | Inr err -> Inr err

instance instrumentable_HO_arr0_out_instrumentable
  fin fout fpre fpost 
  cout cpre cpost 
  pi 
  {| d0:instrumentable cout pi |}
  {| d1:mlifyable_in_arr0 fin fout fpre fpost pi |}
  {| d2:checkable_hist_post (fun x -> cpre) (fun x -> cpost) pi |} : 
  instrumentable ((fin -> IIO (maybe fout) fpre fpost) -> DM.IIO.IIO (maybe cout) cpre cpost) pi =
  {
    inst_type = d1.cmlifyable0.matype -> IIOpi (maybe d0.inst_type) pi;
    cinst_type = ml_instrumented_iio d1.cmlifyable0.matype #(ML_ARROW d1.cmlifyable0.cmatype) (maybe d0.inst_type) #(ML_FO (mlfo_maybe d0.inst_type #(ML_ARROW d0.cinst_type))) pi;
    strengthen = (fun (ctx:(d1.cmlifyable0.matype -> IIOpi (maybe d0.inst_type) pi)) -> 
      (fun (f:(fin -> IIO (maybe fout) fpre fpost)) -> 
        (** TODO: import the result **)
        (let ctx' = strengthen_out d1.cmlifyable0.matype _ pi #d0 ctx in 
        enforce_post pi (fun x -> cpre) (fun x -> cpost) #d2 ctx' (d1.cmlifyable0.mlify f)) <: IIO (maybe cout) cpre cpost))
  }

instance instrumentable_HO_arr1_out_instrumentable
  fin fout fpre fpost 
  cout cpre cpost 
  pi 
  {| d0:instrumentable cout pi |}
  {| d1:mlifyable_in_arr1 fin fout fpre fpost pi |}
  {| d2:checkable_hist_post (fun x -> cpre) (fun x -> cpost) pi |} : 
  instrumentable ((x:fin -> IIO (maybe fout) (fpre x) (fpost x)) -> DM.IIO.IIO (maybe cout) cpre cpost) pi =
  {
    inst_type = d1.cmlifyable1.matype -> IIOpi (maybe d0.inst_type) pi;
    cinst_type = ml_instrumented_iio d1.cmlifyable1.matype #(ML_ARROW d1.cmlifyable1.cmatype) (maybe d0.inst_type) #(ML_FO (mlfo_maybe d0.inst_type #(ML_ARROW d0.cinst_type))) pi;
    strengthen = (fun (ctx:(d1.cmlifyable1.matype -> IIOpi (maybe d0.inst_type) pi)) -> 
      (fun (f:(x:fin -> IIO (maybe fout) (fpre x) (fpost x))) -> 
        (** TODO: import the result **)
        (let ctx' = strengthen_out d1.cmlifyable1.matype _ pi #d0 ctx in 
        enforce_post pi (fun x -> cpre) (fun x -> cpost) #d2 ctx' (d1.cmlifyable1.mlify f)) <: IIO (maybe cout) cpre cpost))
  }
