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

instance mlifyable_iiowp_post
  t1 {| ml t1 |}
  t2 {| ml t2 |} 
  post:
  Tot (mlifyable ((x:t1) -> IIOwp t2 (post_as_hist (post x)))) =
  mk_mlifyable
    #((x:t1) -> IIOwp t2 (post_as_hist (post x)))
    (t1 -> MIIO t2)
    (fun f x -> f x)

instance mlifyable_iiowp_weaken_post
  t1 {| d1:importable t1 |}
  t2 {| d2:exportable t2 |}
  post :
  Tot (mlifyable ((x:t1) -> IIOwp (maybe t2) (post_as_hist (post x)))) =
  mk_mlifyable
    #((x:t1) -> IIOwp (maybe t2) (post_as_hist (post x)))
    (d1.itype -> MIIO (maybe d2.etype))
    #(ml_arrow_miio d1.itype (maybe d2.etype) #(ML_FO d1.citype) #(ML_FO (mlfo_maybe d2.etype #(ML_FO d2.cetype))))
    (fun f -> 
      mlify 
        #_ 
        #(mlifyable_iiowp_post 
            d1.itype
            #(ML_FO d1.citype)
            (maybe d2.etype)
            #(ML_FO (mlfo_maybe d2.etype #(ML_FO d2.cetype)))
            (weaken_new_post_maybe post))
        (weaken f))

instance mlifyable_iiowp_trivialize_weaken_post
  t1 {| d1:importable t1 |}
  t2 {| d2:exportable t2 |}
  pre {| d3: checkable2 pre |}
  post :
  Tot (mlifyable ((x:t1) -> IIO (maybe t2) (pre x) (post x))) =
  mk_mlifyable
    #((x:t1) -> IIO (maybe t2) (pre x) (post x))
    (d1.itype -> MIIO (maybe d2.etype))
    #(ml_arrow_miio d1.itype (maybe d2.etype) #(ML_FO d1.citype) #(ML_FO (mlfo_maybe d2.etype #(ML_FO d2.cetype))))
    (fun f -> 
      mlify #_ #(mlifyable_iiowp_weaken_post t1 t2 (trivialize_new_post_maybe d3.check2 post)) (trivialize f))

instance mlifyable_inst_iiowp_weaken
  t1 {| d1:instrumentable t1 |} 
  t2 {| d2:exportable t2 |} 
  post :
  Tot (mlifyable (t1 -> IIO t2 (fun _ -> True) post)) =
  mk_mlifyable
    #(t1 -> IIO t2 (fun _ -> True) post)
    (d1.inst_type -> MIIO d2.etype)
    #(ml_arrow_miio d1.inst_type d2.etype #(ML_INST d1.cinst_type) #(ML_FO d2.cetype))
    (fun p (ct:d1.inst_type) ->
      export (p (d1.strengthen ct)))

instance mlifyable_inst_iiowp_trivialize_weaken
  t1 {| d1:instrumentable t1 |}
  t2 {| d2:exportable t2 |} 
  pre {| d3:checkable pre |}
  post :
  Tot (mlifyable (t1 -> IIO (maybe t2) pre post)) =
  mk_mlifyable
    #(t1 -> IIO (maybe t2) pre post)
    (d1.inst_type -> MIIO (maybe d2.etype))
    #(ml_arrow_miio d1.inst_type (maybe d2.etype) #(ML_INST d1.cinst_type) #(ML_FO (mlfo_maybe d2.etype #(ML_FO d2.cetype))))
    (fun p -> mlify #_ #(mlifyable_inst_iiowp_weaken t1 (maybe t2) (trivialize_new_post_maybe' d3.check post)) (trivialize p))
