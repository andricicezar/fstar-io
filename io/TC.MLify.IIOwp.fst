module TC.MLify.IIOwp

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.All
open FStar.Classical.Sugar

open Common
open TC.ML
open TC.ML.HO
open TC.Checkable
open TC.Export
open TC.Weaken.IIOwp
open TC.Trivialize.IIOwp
open TC.Monitorable.Hist

open Free
open IO.Sig
open DM.IIO

exception Something_went_really_bad

(** *** Base case **)

instance mlifyable_iiowp_post
  t1 {| ml t1 |}
  t2 {| ml t2 |} 
  post:
  Tot (mlifyable ((x:t1) -> IIOwp t2 (post_as_hist (post x))) (trivial_pi ())) =
  mk_mlifyable
    #((x:t1) -> IIOwp t2 (post_as_hist (post x)))
    (t1 -> MIIO t2)
    (fun f x -> f x)

instance mlifyable_iiowp_post_2
  t1 {| d1:ml t1 |}
  t2 {| d2:ml t2 |} 
  post 
  pi {| d3:monitorable_hist (fun _ _ -> True) post pi |} :
  Tot (mlifyable ((x:t1) -> IIOwp (maybe t2) (post_as_hist (post x))) pi) by (
    explode (); bump_nth 7; 
    l_to_r [`List.Tot.Properties.append_nil_l];
    mapply (ExtraTactics.instantiate_multiple_foralls (nth_binder (-6)) [binder_to_term (nth_binder (-2)); binder_to_term (nth_binder (-3))]);
    let x = nth_binder 19 in
    let x  = ExtraTactics.instantiate_multiple_foralls x [binder_to_term (nth_binder 14); binder_to_term (nth_binder 15); binder_to_term  (nth_binder (-4))] in
    binder_retype (nth_binder (-3)); 
      l_to_r [`List.Tot.Properties.append_nil_l];
    trefl ();
    tadmit (); // really close
    //ignore (ExtraTactics.apply_in (nth_binder (-1)) x);
    dump "H")=
  mk_mlifyable
    #((x:t1) -> IIOwp (maybe t2) (post_as_hist (post x)))
    (t1 -> IIOpi (maybe t2) pi)
    #(ml_instrumented_iio t1 #d1 (maybe t2) #(ML_FO (mlfo_maybe t2 #d2)) pi)
    (fun f x -> 
      let _ = d3.c1post in
      f x)

(** *** Arrows with base types as input/output **)

let weaken_new_post 
  #t1 {| d1:importable t1 |}
  #t2 {| d2: exportable t2 |}
  (pi:monitorable_prop)
  (post:t1 -> trace -> maybe t2 -> trace -> Type0)
  (d: squash (forall x h lt. enforced_locally pi h lt ==> (exists r. post x h r lt))) :
  squash (forall x h lt. enforced_locally pi h lt ==> (exists r. (weaken_new_post_maybe #t1 #t2 #d1 #d2 post) x h r lt)) = 
  introduce forall (x:d1.itype) h lt. (enforced_locally pi h lt ==> (exists r. (weaken_new_post_maybe #t1 #t2 #d1 #d2 post) x h r lt)) with begin
    introduce enforced_locally pi h lt ==> (exists r. (weaken_new_post_maybe #t1 #t2 #d1 #d2 post) x h r lt) with _. begin
      let post' = weaken_new_post_maybe #t1 #t2 #d1 #d2 post in

      match lt, import x with
      | [], None -> assert (post' x h (Inr Contract_failure) [])
      | _, None -> admit () //assert (False)
      | _, Some x' -> begin
         assert (enforced_locally pi h lt ==> (exists r. post x' h r lt)) by (
         ignore (ExtraTactics.instantiate_multiple_foralls (nth_binder 6) [binder_to_term (nth_binder (-2))]));
         assert (enforced_locally pi h lt);
         eliminate exists (r:maybe t2). post x' h r lt 
           returns exists (r:maybe t2). post' x h (match r with | Inl r -> Inl (export r) | Inr err -> Inr err) lt 
              with _. ()
      end
    end
  end

let convert
  #t1 {| d1:importable t1 |}
  #t2 {| d2: exportable t2 |}
  (pi:monitorable_prop)
  (post:t1 -> trace -> maybe t2 -> trace -> Type0)
  (x:monitorable_hist (fun _ _ -> True) post pi) : 
  monitorable_hist (fun _ _ -> True) (weaken_new_post_maybe #t1 #t2 #d1 #d2 post) pi = {
    c1post = weaken_new_post pi post x.c1post 
  }

instance mlifyable_iiowp_weaken_post
  t1 {| d1:importable t1 |}
  t2 {| d2:exportable t2 |}
  post
  pi {| d3:monitorable_hist (fun _ _ -> True) post pi |} :
  Tot (mlifyable ((x:t1) -> IIOwp (maybe t2) (post_as_hist (post x))) pi) =
  mk_mlifyable
    #((x:t1) -> IIOwp (maybe t2) (post_as_hist (post x)))
    (d1.itype -> IIOpi (maybe d2.etype) pi)
    #(ml_instrumented_iio d1.itype #(ML_FO d1.citype) (maybe d2.etype) #(ML_FO (mlfo_maybe d2.etype #(ML_FO d2.cetype))) pi)
    (fun f -> 
      mlify 
        #_ #_
        #(mlifyable_iiowp_post_2 
            d1.itype
            #(ML_FO d1.citype)
            d2.etype
            #(ML_FO d2.cetype)
            (weaken_new_post_maybe post)
            pi
            #(convert pi post d3))
        (weaken f))


let convert222
  #t1
  #t2
  pre {| d3: checkable2 pre |}
  (post:t1 -> trace -> maybe t2 -> trace -> Type0) 
  pi
  (x:squash (forall (x:t1) (h lt:trace). pre x h /\ enforced_locally pi h lt ==> (exists r. post x h r lt))) :
  squash (forall x h lt. enforced_locally pi h lt ==> (exists r. (trivialize_new_post_maybe d3.check2 post) x h r lt)) = 
  introduce forall (x:t1) (h lt:trace). enforced_locally pi h lt ==> (exists r. (trivialize_new_post_maybe d3.check2 post) x h r lt) with begin
    introduce enforced_locally pi h lt ==> (exists r. (trivialize_new_post_maybe d3.check2 post) x h r lt) with _. begin
      assert (pre x h /\ enforced_locally pi h lt ==> (exists r. post x h r lt)) by (
        ignore (ExtraTactics.instantiate_multiple_foralls (nth_binder 6) [binder_to_term (nth_binder 7)]));
      assert (enforced_locally pi h lt);
      assert (pre x h ==> (exists r. post x h r lt));
      admit ()
    end
  end

let convert2
  #t1
  #t2
  pre {| d3: checkable2 pre |}
  (post:t1 -> trace -> maybe t2 -> trace -> Type0) 
  pi (x:monitorable_hist pre post pi) :
  monitorable_hist (fun _ _ ->True) (trivialize_new_post_maybe d3.check2 post) pi = {
    c1post = convert222 pre post pi x.c1post 
  }

instance mlifyable_iiowp_trivialize_weaken_post
  t1 {| d1:importable t1 |}
  t2 {| d2:exportable t2 |}
  pre {| d3: checkable2 pre |}
  post 
  pi {| d4:monitorable_hist pre post pi |} :
  Tot (mlifyable ((x:t1) -> IIO (maybe t2) (pre x) (post x)) pi) =
  mk_mlifyable
    #((x:t1) -> IIO (maybe t2) (pre x) (post x))
    (d1.itype -> IIOpi (maybe d2.etype) pi)
    #(ml_instrumented_iio d1.itype #(ML_FO d1.citype) (maybe d2.etype) #(ML_FO (mlfo_maybe d2.etype #(ML_FO d2.cetype))) pi)
    (fun f -> 
      mlify 
        #_ #_ 
        #(mlifyable_iiowp_weaken_post 
          t1
          t2
          (trivialize_new_post_maybe d3.check2 post)
          pi
          #(convert2 pre post pi d4))
        (trivialize f))

let monitorable_hist_trivial_pi 
  t1
  t2
  post : monitorable_hist (fun _ _ -> True) post (trivial_pi ()) = admit ()

instance mlifyable_iiowp_trivialize_weaken_post'
  t1 {| d1:importable t1 |}
  t2 {| d2:exportable t2 |}
  pre {| d3: checkable2 pre |}
  post :
  Tot (mlifyable ((x:t1) -> IIO (maybe t2) (pre x) (post x)) (trivial_pi ())) =
  mk_mlifyable
    #((x:t1) -> IIO (maybe t2) (pre x) (post x))
    (d1.itype -> MIIO (maybe d2.etype))
    #(ml_arrow_miio d1.itype #(ML_FO d1.citype) (maybe d2.etype) #(ML_FO (mlfo_maybe d2.etype #(ML_FO d2.cetype))))
    (fun f -> 
      mlify
        #_ #_
        #(mlifyable_iiowp_trivialize_weaken_post
          t1 t2
          (fun _ _ -> True) #({ check2 = fun _ _ -> true })
          (trivialize_new_post_maybe d3.check2 post)
          (trivial_pi ())
          #(monitorable_hist_trivial_pi t1 t2 (trivialize_new_post_maybe d3.check2 post)))
        (trivialize f))

(** *** Arrows with other arrows as input and base types as output **)

instance mlifyable_inst_iiowp_weaken'
  (#pi:monitorable_prop)
  t1 {| d1:instrumentable t1 pi |} 
  t2 {| d2:exportable t2 |} 
  post 
  {| monitorable_hist #t1 (fun _ _ -> True) (fun _ -> post) pi |} :
  Tot (mlifyable (t1 -> IIO (maybe t2) (fun _ -> True) post) pi) =
  admit (); (** similar with mlifyable_iiowp_post_2 **)
  mk_mlifyable
    #(t1 -> IIO (maybe t2) (fun _ -> True) post)
    (d1.inst_type -> IIOpi (maybe d2.etype) pi)
    #(ml_instrumented_iio 
        d1.inst_type #(ML_ARROW d1.cinst_type)
        (maybe d2.etype) #(ML_FO (mlfo_maybe d2.etype #(ML_FO d2.cetype))) pi)
    (fun p (ct:d1.inst_type) ->
      match p (d1.strengthen ct) with
      | Inl x -> Inl (export x)
      | Inr err -> Inr err)


let monitorable_hist_trivial_pi'
  t1
  t2
  pi
  post : monitorable_hist #t1 #t2 (fun _ _ -> True) (fun _ -> post) pi = admit ()

#set-options "--print_implicits --print_bound_var_types"
(** TODO: there can be two pi's where the one for instrumentable is stricter **)
instance mlifyable_inst_iiowp_trivialize_weaken'
  (#pi:monitorable_prop)
  t1 {| d1:instrumentable t1 pi |}
  t2 {| d2:exportable t2 |} 
  pre {| d3:checkable pre |}
  post 
  {| monitorable_hist #t1 #t2 (fun _ -> pre) (fun _ -> post) pi |} :
  Tot (mlifyable (t1 -> IIO (maybe t2) pre post) pi) =
  mk_mlifyable
    #(t1 -> IIO (maybe t2) pre post)
    (d1.inst_type -> IIOpi (maybe d2.etype) pi)
    #(ml_instrumented_iio d1.inst_type #(ML_ARROW d1.cinst_type) (maybe d2.etype) #(ML_FO (mlfo_maybe d2.etype #(ML_FO d2.cetype))) pi)
    (fun p -> 
      mlify
        #_ #_
        #(mlifyable_inst_iiowp_weaken'
          t1 
          t2 
          (trivialize_new_post_maybe' d3.check post)
          #(monitorable_hist_trivial_pi' t1 t2 pi (trivialize_new_post_maybe' d3.check post)))
        (trivialize p))

instance mlifyable_inst_iiowp_weaken
  (#pi:monitorable_prop)
  t1 {| d1:instrumentable t1 pi |} 
  t2 {| d2:exportable t2 |} 
  post :
  Tot (mlifyable (t1 -> IIO t2 (fun _ -> True) post) (trivial_pi ())) =
  mk_mlifyable
    #(t1 -> IIO t2 (fun _ -> True) post)
    (d1.inst_type -> MIIO d2.etype)
    #(ml_arrow_miio d1.inst_type #(ML_ARROW d1.cinst_type) d2.etype #(ML_FO d2.cetype))
    (fun p (ct:d1.inst_type) ->
      export (p (d1.strengthen ct)))

instance mlifyable_inst_iiowp_trivialize_weaken
  (#pi:monitorable_prop)
  t1 {| d1:instrumentable t1 pi |}
  t2 {| d2:exportable t2 |} 
  pre {| d3:checkable pre |}
  post :
  Tot (mlifyable (t1 -> IIO (maybe t2) pre post) (trivial_pi ())) =
  mk_mlifyable
    #(t1 -> IIO (maybe t2) pre post)
    (d1.inst_type -> MIIO (maybe d2.etype))
    #(ml_arrow_miio d1.inst_type #(ML_ARROW d1.cinst_type) (maybe d2.etype) #(ML_FO (mlfo_maybe d2.etype #(ML_FO d2.cetype))))
    (fun p -> mlify #_ #_ #(mlifyable_inst_iiowp_weaken t1 (maybe t2) (trivialize_new_post_maybe' d3.check post)) (trivialize p))
