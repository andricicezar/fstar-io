module TC.Weaken.MIIO

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open TC.Checkable
open TC.Export
include TC.Weaken
open TC.Trivialize.MIIO
open DM.IIO
open DM.MIIO

instance weak_miio t1 t2 {| ml t1 |} {| ml t2 |} : weak (t1 -> MIIO t2) =
  { mldummy = () }

(** TODO: is this really a weak arrow? Is type (t1 -> IIO t2 pi .. ..) weak? 
We need this for extracting higher order MIIO computations. Is pi weak? **)
instance weak_iio_miio t1 t2 t3 pi {| ml t1 |} {| ml t2 |} {| ml t3 |} : 
  weak ((t1 -> IIO t2 pi (fun _ -> True) (fun _ _ _ -> True)) -> MIIO t3) =
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
