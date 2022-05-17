module TC.Weaken.IIOwp

(** we do not need this file, and we do not use it in our development, 
but I did tried to write it to have a more complex example on how the
weaken transformation functions works. This file is still in progress **)

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open IO.Sig
open DM.IIO
open TC.ML
open TC.ML.HO
open TC.Export
open TC.Trivialize.IIOwp
include TC.Weaken

instance weak_IIOwp
  t1 t2 
  (pre:t1 -> trace -> Type0)
  (post:t1 -> trace -> t2 -> trace -> Type0) 
  {| mlfo t1 |} {| mlfo t2 |} : 
  weak ((x:t1) -> IIOwp t2 (to_hist (pre x) (post x))) =
  { mldummy = () }

let weaken_new_post
  t1 t2 {| d1:importable t1 |} {| d2: exportable t2 |}
  (post:t1 -> trace -> t2 -> trace -> Type0) :
  Tot (d1.itype -> trace -> maybe d2.etype -> trace -> Type0) =
    fun x h r lt -> True
    (**
    fun x h r lt -> 
      match import x with
      | Some x' -> Inl? r /\ post x' h (safe_import #_ #(safe_importable_exportable _ #d2) (Inl?.v r)) lt
      | None -> r == (Inr Contract_failure) /\ lt == []
      **)
      
instance weakable_IIOwp
  t1 t2 {| d1:importable t1 |} {| d2: exportable t2 |}
  (post : t1 -> trace -> t2 -> trace -> Type0) :
  Tot (weakable ((x:t1) -> IIOwp t2 (post_as_hist (post x)))) =
  let post' = weaken_new_post t1 t2 post in
  mk_weakable 
    ((x:d1.itype) -> IIOwp (maybe d2.etype) (to_hist (fun _ -> True) (post' x)))
    #(trivial_IIOwp t1 t2 post)
    #(weak_IIOwp d1.itype (maybe d2.etype) (fun _ _ -> True) post' #d1.citype #(mlfo_maybe d2.etype #(ML_FO d2.cetype)))
    (fun (f:(x:t1) -> IIOwp t2 (post_as_hist (post x))) (x:d1.itype) ->
      match import x with
      | Some x' -> Inl (export (f x')) 
      | None -> Inr Contract_failure)

let weaken_new_post_maybe
  #t1 #t2 {| d1:importable t1 |} {| d2: exportable t2 |}
  (post:t1 -> trace -> maybe t2 -> trace -> Type0) :
  Tot (d1.itype -> trace -> maybe d2.etype -> trace -> Type0) =
  fun (x:d1.itype) h (r:maybe d2.etype) lt -> 
    match import x with
    | None -> r == Inr Contract_failure /\ lt == [] 
    | Some x' -> (
        match r with
        | Inl r' -> exists (r'':t2). export r'' == r' /\ post x' h (Inl r'') lt
        | Inr err -> post x' h (Inr err) lt)

instance weakable_IIOwp_maybe
  t1 t2 {| d1:importable t1 |} {| d2: exportable t2 |}
  (post : t1 -> trace -> (maybe t2) -> trace -> Type0) :
  Tot (weakable ((x:t1) -> IIOwp (maybe t2) (post_as_hist (post x)))) by (
    explode ();
  
    bump_nth 12;
    binder_retype (nth_binder 18);
      norm [delta_only [`%post_as_hist; `%to_hist; `%weaken_new_post_maybe]; iota];
    trefl ();
    ignore (destruct_and (nth_binder 17));
//    l_to_r [`List.Tot.Properties.append_nil_l];
//    let x = ExtraTactics.instantiate_multiple_foralls (nth_binder (-1)) [(`[]); binder_to_term (nth_binder (-4))] in
//    mapply x;
 //   rewrite_eqs_from_context ();

    bump_nth 12;
    let x = instantiate (nth_binder (-5)) (nth_binder (-1)) in
    mapply x;
    rewrite (nth_binder (-3));
    norm [iota];
    let t = implies_intro () in
    norm [delta_only [`%hist_return]];
    l_to_r [`List.Tot.Properties.append_nil_l;`List.Tot.Properties.append_l_nil];
    binder_retype (nth_binder 18);
      norm [delta_only [`%weaken_new_post_maybe;`%post_as_hist;`%to_hist]];
    trefl ();
    ignore (destruct_and (nth_binder 17));
 //   let x = ExtraTactics.instantiate_multiple_foralls (nth_binder (-1)) [binder_to_term (nth_binder 20); binder_to_term (nth_binder (-5))] in
//    mapply x;

    bump_nth 12;
    let x = instantiate (nth_binder (-4)) (nth_binder (-1)) in
    mapply x;
    rewrite (nth_binder (-3));
    norm [iota];
    let t = implies_intro () in
    norm [delta_only [`%hist_return]];
    l_to_r [`List.Tot.Properties.append_nil_l;`List.Tot.Properties.append_l_nil];
    binder_retype (nth_binder 18);
      norm [delta_only [`%weaken_new_post_maybe;`%post_as_hist;`%to_hist]];
    trefl ();
    ignore (destruct_and (nth_binder 17))

 //   dump "H"
  )=
  mk_weakable 
    ((x:d1.itype) -> IIOwp (maybe d2.etype) (post_as_hist ((weaken_new_post_maybe post) x)))
    #(trivial_IIOwp t1 (maybe t2) post)
    #(weak_IIOwp d1.itype (maybe d2.etype) (fun _ _ -> True) (weaken_new_post_maybe post) #d1.citype #(mlfo_maybe d2.etype #(ML_FO d2.cetype)))
    (fun (f:(x:t1) -> IIOwp (maybe t2) (post_as_hist (post x))) (x:d1.itype) ->
      match import x with
      | Some x' -> begin
        match f x' with
        | Inl x'' -> Inl (export x'')
        | Inr err -> Inr err
      end
      | None -> Inr Contract_failure)
