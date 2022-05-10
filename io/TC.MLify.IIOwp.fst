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

instance mlifyable_iiowp
  t1 t2 {| ml t1 |} {| ml t2 |} :
  Tot (mlifyable (t1 -> IIOwp t2 (trivial_hist ()))) =
  mk_mlifyable
    #(t1 -> IIOwp t2 (trivial_hist ()))
    (t1 -> MIIO t2)
    (fun f x -> f x)

instance mlifyable_iiowp_2
  t1 t2 {| d1:ml t1 |} {| d2:ml t2 |} pre {| d3: checkable2 pre |} post :
  Tot (mlifyable ((x:t1) -> IIO t2 (pre x) (post x))) =
  mk_mlifyable
    #((x:t1) -> IIO t2 (pre x) (post x))
    (t1 -> MIIO (maybe t2))
    #(ml_arrow_miio t1 (maybe t2) #d1 #(ML_FO (mlfo_maybe t2 #d2)))
    (fun f -> 
      let f' : (x:t1) -> IIOwp (maybe t2) (post_as_hist (new_post d3.check2 post x)) = trivialize f in
      (** erase post **)
      let f'' : (x:t1) -> IIOwp (maybe t2) (trivial_hist ()) = f' in
      mlify #_ #(mlifyable_iiowp t1 (maybe t2) #d1 #(ML_FO (mlfo_maybe t2 #d2))) f'')

instance mlifyable_iiowp_3
  t1 t2 {| d1:importable t1 |} {| d2:exportable t2 |} pre {| d3: checkable2 pre |} post :
  Tot (mlifyable ((x:t1) -> IIO t2 (pre x) (post x))) =
  mk_mlifyable
    #((x:t1) -> IIO t2 (pre x) (post x))
    (d1.itype -> MIIO (maybe d2.etype))
    #(ml_arrow_miio d1.itype (maybe d2.etype) #(ML_FO d1.citype) #(ML_FO (mlfo_maybe d2.etype #(ML_FO d2.cetype))))
    (fun f -> 
      let f' : (x:t1) -> IIOwp (maybe t2) (post_as_hist (new_post d3.check2 post x)) = trivialize f in
      (** weaken **)
      let f'' : d1.itype -> IIOwp (maybe d2.etype) (trivial_hist ()) = weaken f' in
      mlify #_ #(mlifyable_iiowp d1.itype (maybe d2.etype) #(ML_FO d1.citype) #(ML_FO (mlfo_maybe d2.etype #(ML_FO d2.cetype)))) f'')

instance mlifyable_inst_iiowp
  t1 t2
  {| d1:instrumentable t1 |} {| d2:ml t2 |} :
  Tot (mlifyable (t1 -> IIOwp t2 (trivial_hist ()))) =
  mk_mlifyable
    #_
    (d1.inst_type -> MIIO t2)
    #(ml_arrow_miio d1.inst_type t2 #(ML_INST d1.cinst_type) #d2)
    (fun (p:t1 -> IIOwp t2 (trivial_hist ())) (ct:d1.inst_type) ->
      p (d1.strengthen ct))

instance mlifyable_inst_iiowp_post
  t1 t2 post
  {| d1:instrumentable t1 |} {| d2:ml t2 |} :
  Tot (mlifyable (t1 -> IIO t2 (fun _ -> True) post)) =
  mk_mlifyable
    #_
    (d1.inst_type -> MIIO t2)
    #(ml_arrow_miio d1.inst_type t2 #(ML_INST d1.cinst_type) #d2)
    (fun (p:t1 -> IIO t2 (fun _ -> True) post) (ct:d1.inst_type) ->
      p (d1.strengthen ct))

instance mlifyable_inst_iiowp_post_2
  t1 t2 post
  {| d1:instrumentable t1 |} {| d2:exportable t2 |} :
  Tot (mlifyable (t1 -> IIO t2 (fun _ -> True) post)) =
  mk_mlifyable
    #_
    (d1.inst_type -> MIIO d2.etype)
    #(ml_arrow_miio d1.inst_type d2.etype #(ML_INST d1.cinst_type) #(ML_FO d2.cetype))
    (fun (p:t1 -> IIO t2 (fun _ -> True) post) (ct:d1.inst_type) ->
      export (p (d1.strengthen ct)))
