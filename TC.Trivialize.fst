module TC.Trivialize

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open TC.Checkable

(** By trivial functions, we understand functions that have the pre-condition True. 
We must be careful with what we label with `trivial` since an effect can hide pre-conditions.

For exemple, we can define a synonym effect:
  effect PureExtraPre a pre post = Pure a (5 == 7 /\ pre) post

Any function with the PureExtraPre effect is not a trivial function.
**)

class trivial (t:Type) = { mldummy: unit }

instance trivial_totarrow t1 t2 : trivial (t1 -> Tot t2) =
  { mldummy = () }

instance trivial_purearrow 
  t1 t2 (post:t1 -> t2 -> Type0) : trivial ((x:t1) -> Pure t2 True (post x)) =
  { mldummy = () }

(**
Trivialize wraps the function in a new function that checks the 
pre-condition dynamically. Not all effects support dynamic verification
of the pre-condition. Also, because the pre-condition is checked dynamically
it means that the check may fail, therefore, the new output of the function
may be different.

Principles for trivialize:
1. does not change the effect of the computation.
2. does preserver the post-condition as much as possible.
**)

class trivializeable (t : Type) =
  { ttype : Type; trivialize : t -> ttype; trivial_ttype : trivial ttype }
  
let mk_trivializeable (#t1 t2 : Type) {| trivial t2 |} (exp : t1 -> t2) : trivializeable t1 =
  { ttype = t2; trivialize = exp;  trivial_ttype = solve }

(** The new post-condition of the function may be look weird. 
Like, why is it `check x ==> post x r` and not `pre x ==> post x r`? Well, because `pre`
is checkable (check x ==> pre x), not decideable (check x <==> pre x). Therefore,
therere may be x for which `check x` is false and `pre x` is true. **)
instance trivializeable_purearrow
  t1 t2
  (pre : t1 -> Type0) {| d3:checkable pre |}
  (post : t1 -> t2 -> Type0) :
  Tot (trivializeable ((x:t1) -> Pure t2 (pre x) (post x))) =
  mk_trivializeable (x:t1 -> Pure (maybe t2) True (fun (r:maybe t2) -> (
    (check #t1 #pre x ==> Inl? r /\ post x (Inl?.v r)))))
    (fun (f:(x:t1 -> Pure t2 (pre x) (post x))) ->
      (fun (x:t1) ->
        if check #t1 #pre x then Inl (f x)
        else Inr Contract_failure))

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
