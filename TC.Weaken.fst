module TC.Weaken

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open TC.ML
open TC.Checkable
open TC.Export
open TC.Trivialize

(** Principles for `weak`:
1. A function should be labeled with `weak`, if the input and output types 
   of the function are `ml`.
2. We need to be really careful with what we label with `weak` since
   there are no restrictions.
**)
class weak (t:Type) = { mldummy: unit }

(** Principles for weakable/weaken: 
1. it does not change the effect of the argument.
2. The pre-condition must be trivial. Use `trivialize` first if the function has a 
   non-trivial pre-condition.
3. The output type usually changes to accept the possiblity of failure.
4. The post should be rewritten to accept the possibility of a failure, but should still
   guarantee the old post if the pre-condition is met.
   Erasing or weakeaning the post-condition even further can be done through sub-typing, 
   therefore we try to give the best post-condition we can do after weakeaning.
**)

class weakable (t : Type) =
  { wtype : Type; weaken : t -> wtype; trivial_t: trivial t; weak_wtype : weak wtype }
  
let mk_weakable (#t1 t2 : Type) {| trivial t1 |} {| weak t2 |} (exp : t1 -> t2) : weakable t1 =
  { wtype = t2; weaken = exp; trivial_t = solve; weak_wtype = solve }

(**
instance weak_totarrow t1 t2 {| mlfo t1 |} {| mlfo t2 |} : weak (t1 -> Tot t2) =
  { mldummy = () }

instance weak_purearrow 
  t1 t2 {| mlfo t1 |} {| mlfo t2 |}
  (pre:t1 -> Type0)
  (post:t1 -> t2 -> Type0) : 
  weak ((x:t1) -> Pure t2 (pre x) (post x)) =
  { mldummy = () }

instance weakable_arrow
  t1 t2 {| d1:importable t1 |} {| d2:exportable t2 |} :
  Tot (weakable (t1 -> Tot t2)) =
  mk_weakable (d1.itype -> Tot (maybe d2.etype))
    (fun (f:(t1 -> Tot t2)) (x:d1.itype) ->
        match import x with
        | Some x' -> Inl (export (f x'))
        | None -> Inr Contract_failure)**)

(** The post-condition does not respect principle 4.
  The post-condition should look something like this: 
    match import x with
    | Some x' -> Inl? r /\ post x' (safe_import (Inl?.v r))
    | None -> r == Inr Contract_failure
**)

(**
instance weakable_purearrow
  t1 t2 {| d1:importable t1 |} {| d2:exportable t2 |}
  (post : t1 -> t2 -> Type0) :
  Tot (weakable ((x:t1) -> Pure t2 True (post x))) =
  mk_weakable (x:d1.itype -> Pure (maybe d2.etype) True (fun _ -> True))
    (fun (f:(x:t1 -> Pure t2 True (post x))) ->
      (fun (x:d1.itype) ->
        match import x with
        | Some x' -> Inl (export (f x'))
        | None -> Inr Contract_failure))

(**
instance exportable_IOwp
  (t1:Type) {| d1:importable t1 |}
  (t2:Type) {| d2:exportable t2 |}
  (pre:t1 -> trace -> Type0) {| d3:checkable2 pre |}
  (post:t1 -> trace -> (m:maybe t2) -> trace -> (r:Type0{Inr? m ==> r})) :
  Tot (exportable (x:t1 ->
    IOwp t2 (fun h p ->
      pre x h /\ (forall r lt. post x h r lt ==>  p r lt)))) =
  mk_exportable
    (d1.itype -> MIIO (maybe d2.etype))
    (fun (f:(x:t1 -> IOwp t2 (fun h p ->
      pre x h /\ (forall r lt. post x h r lt ==>  p r lt)))) ->
      (fun x ->
        match import x with
        | Some x' -> Inl (export (_IIOwp_as_MIIO d3.check2 post f x'))
        | None -> Inr Contract_failure))
**)

(** TODO: write strengthen_iio from the thesis **)
