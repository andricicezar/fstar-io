module TC.Weaken.IIOwp

(** we do not need this file, and we do not use it in our development, 
but I did tried to write it to have a more complex example on how the
weaken transformation functions works. This file is still in progress **)

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open Free.IO
open DM.IIO
open TC.Export
open TC.Trivialize.IIOwp
include TC.Weaken

instance weak_IIOwp
  t1 t2 
  (pre:t1 -> trace -> Type0)
  (post:t1 -> trace -> t2 -> trace -> Type0) 
  {| ml t1 |} {| ml t2 |} : 
  weak ((x:t1) -> IIOwp t2 (pre_post_as_wp (pre x) (post x))) =
  { mldummy = () }

let new_post
  t1 t2 {| d1:importable t1 |} {| d2: exportable t2 |}
  (post:t1 -> trace -> t2 -> trace -> Type0) :
  Tot (d1.itype -> trace -> maybe d2.etype -> trace -> Type0) =
    fun x h r lt -> 
      match import x with
      | Some x' -> Inl? r /\ post x' h (safe_import #_ #(safe_importable_exportable _ #d2) (Inl?.v r)) lt
      | None -> r == (Inr Contract_failure) /\ lt == []

instance weakable_IIOwp
  t1 t2 {| d1:importable t1 |} {| d2: exportable t2 |}
  (post : t1 -> trace -> t2 -> trace -> Type0) :
  Tot (weakable ((x:t1) -> IIOwp t2 (post_as_wp (post x)))) by ( 
    unfold_def(`pre_post_as_wp);
    l_to_r [`List.Tot.Properties.append_l_nil; `List.Tot.Properties.append_nil_l];
    explode (); 
    bump_nth 8; 
    let _, lm = destruct_and (ExtraTactics.get_binder 17) in
    let z = ExtraTactics.get_binder 20 in
    let z':term = ExtraTactics.get_binder 21 in
    let lm' = ExtraTactics.instantiate_multiple_foralls lm [(`(Inl (export (`#z)))); z'] in
    mapply lm';
    unfold_def(`new_post);
    norm [iota;delta];
    tadmit ();
    dump "h") =
  let post' = new_post t1 t2 post in
  mk_weakable 
    ((x:d1.itype) -> IIOwp (maybe d2.etype) (pre_post_as_wp (fun _ -> True) (post' x)))
    #(trivial_IIOwp t1 t2 post)
    #(weak_IIOwp d1.itype (maybe d2.etype) (fun _ _ -> True) post')
    (fun (f:(x:t1) -> IIOwp t2 (post_as_wp (post x))) (x:d1.itype) ->
      match import x with
      | Some x' -> Inl (export (f x')) 
      | None -> Inr Contract_failure)
