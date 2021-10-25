module TC.Weaken.MIIO

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open TC.Checkable
open TC.Export
open TC.Weaken
open TC.Trivialize.MIIO
open DM.MIIO

instance weak_miio t1 t2 {| ml t1 |} {| ml t2 |} : weak (t1 -> MIIO t2) =
  { mldummy = () }

instance weakable_miio
  t1 t2 {| d1:importable t1 |} {| d2:exportable t2 |} :
  Tot (weakable (t1 -> MIIO t2))  =
  mk_weakable (d1.itype -> MIIO (maybe d2.etype))
    (fun (f:(t1 -> MIIO t2)) ->
      (fun (x:d1.itype) ->
        match import x with
        | Some x' -> Inl (export (f x')) <: MIIO (maybe d2.etype)
        | None -> Inr Contract_failure <: MIIO (maybe d2.etype)))
