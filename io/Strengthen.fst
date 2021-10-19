module Strengthen

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open Export
open Checkable
open DM

(** Discussion: maybe it will be better to define as "weak functions":
functions that have trivial pre-conditions. I don't think it's right 
that while trying to weaken the types of a function, we also affect the specification. We should take care of the specification before weaking 
the type. **)

(** Principles for strengthen/weaken: 
1. they do not change the effect of the argument.
2. The pre-condition must be converted to a runtime check because the argument is 
   imported at runtime, therefore the pre-condition must be checked at runtime.
3. The output type usually changes to accept the possiblity of failure.
4. The post should be rewritten to accept the possibility of a failure, but should still
   guarantee the old post if the pre-condition is met.
   Erasing or weakeaning the post-condition even further can be done through sub-typing, 
   therefore we try to give the best post-condition we can do after weakeaning.
5. We need to be really careful with what we say it is `weak` since
   there are no restrictions.
**)

class weak (t:Type) = { mldummy: unit }

instance weak_totarrow t1 t2 {| ml t1 |} {| ml t2 |} : weak (t1 -> Tot t2) =
  { mldummy = () }

instance weak_purearrow 
  t1 t2 {| ml t1 |} {| ml t2 |}
  (pre:t1 -> Type0)
  (post:t1 -> t2 -> Type0) : 
  weak ((x:t1) -> Pure t2 (pre x) (post x)) =
  { mldummy = () }

instance weak_miioarrow (t1:Type u#a) (t2:Type u#b) {| ml t1 |} {| ml t2 |} : 
  weak (t1 -> MIIO t2) =
  { mldummy = () }

class weakable (t : Type) =
  { wtype : Type; weaken : t -> wtype; weak_wtype : weak wtype }
class strengthneable (t : Type) =
  { stype: Type; strengthen : stype -> t; weak_stype : weak stype }
  
let mk_weakable (#t1 t2 : Type) {| weak t2 |} (exp : t1 -> t2) : weakable t1 =
  { wtype = t2; weaken = exp;  weak_wtype = solve }

instance weakable_arrow
  t1 t2 {| d1:importable t1 |} {| d2:exportable t2 |} :
  Tot (weakable (t1 -> Tot t2))  =
  mk_weakable (d1.itype -> Tot (maybe d2.etype))
    (fun (f:(t1 -> t2)) ->
      (fun (x:d1.itype) ->
        match import x with
        | Some x' -> Inl (export (f x')) <: Tot (maybe d2.etype)
        | None -> Inr Contract_failure <: Tot (maybe d2.etype)))

let adapt_post #t1 #t2 {| d1:importable t1 |} {| d2:exportable t2 |} 
  (pre:t1 -> Type0)
  (post:t1 -> t2 -> Type0) :
  (d1.itype -> (maybe d2.etype) -> Type0) =
  fun xi re ->
    match import xi with
    | Some x -> 
      (((pre x) ==> Inl? re /\ (post x (safe_import #_ #(safe_importable_exportable t2 #d2) (Inl?.v re)))) /\
       (~(pre x) ==> re == (Inr Contract_failure)))
    | _ -> re == (Inr Contract_failure)

(** The post-condition does not respect principle 4. **)
instance weakable_purearrow
  t1 t2 {| d1:importable t1 |} {| d2:exportable t2 |}
  (pre : t1 -> Type0) {| d3:checkable pre |}
  (post : t1 -> t2 -> Type0) :
  Tot (weakable ((x:t1) -> Pure t2 (pre x) (post x))) =
  mk_weakable (x:d1.itype -> Pure (maybe d2.etype) True (fun _ -> True))
    (fun (f:(x:t1 -> Pure t2 (pre x) (post x))) ->
      (fun (x:d1.itype) ->
        match import x with
        | Some x' ->
          if check #t1 #pre x' then Inl (export (f x'))
          else Inr Contract_failure
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
