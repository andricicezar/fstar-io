module TC.Trivialize.IIOwp

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open Free.IO
open DM.IIO
open TC.Checkable
include TC.Trivialize

let post_as_wp post = (fun h p -> forall r lt. post h r lt ==> p r lt)
let pre_post_as_wp pre post = (fun h p -> pre h /\ (forall r lt. post h r lt ==> p r lt))

(** functions in the IIO effect can not be trivial since they hide a pre-condition.
Check TC.Trivialize for more details. **)

instance trivial_IIOwp
  t1 t2 (post:t1 -> trace -> t2 -> trace -> Type0) : 
  trivial ((x:t1) -> IIOwp t2 (post_as_wp (post x))) =
  { mldummy = () }

instance trivial_IIOwp_2
  t1 t2 t3 (post:t1 -> t2 -> trace -> t3 -> trace -> Type0) : 
  trivial ((x:t1) -> (y:t2) -> IIOwp t3 (post_as_wp (post x y))) =
  { mldummy = () }

instance trivial_IIOwp_3
  t1 t2 t3 t4 (post:t1 -> t2 -> t3 -> trace -> t4 -> trace -> Type0) : 
  trivial ((x:t1) -> (y:t2) -> (z:t3) -> IIOwp t4 (post_as_wp (post x y z))) =
  { mldummy = () }

let new_post
  (pre:'a -> trace -> bool)
  (post:'a -> trace -> 'b -> trace -> Type0) :
  Tot ('a -> trace -> maybe 'b -> trace -> Type0) =
    fun x h r lt -> 
      (~(pre x h) ==> r == (Inr Contract_failure) /\ lt == []) /\
      (pre x h ==> Inl? r /\ post x h (Inl?.v r) lt)

instance trivializeable_IIOwp
  t1 t2
  (pre : t1 -> trace -> Type0) {| d:checkable2 pre |}
  (post : t1 -> trace -> t2 -> trace -> Type0) :
  Tot (trivializeable ((x:t1) -> IIOwp t2 (pre_post_as_wp (pre x) (post x)))) =
  mk_trivializeable 
    #((x:t1) -> IIOwp t2 (pre_post_as_wp (pre x) (post x)))
    ((x:t1) -> IIOwp (maybe t2) (post_as_wp (new_post d.check2 post x)))
    (fun f x ->
        let h = get_trace () in
        if d.check2 x h then Inl (f x)
        else Inr Contract_failure)
  
let new_post_2
  (pre:'a -> 'b -> trace -> bool)
  (post:'a -> 'b -> trace -> 'c -> trace -> Type0) :
  Tot ('a -> 'b -> trace -> maybe 'c -> trace -> Type0) =
    fun x y h r lt -> 
      (~(pre x y h) ==> r == (Inr Contract_failure) /\ lt == []) /\
      (pre x y h ==> Inl? r /\ post x y h (Inl?.v r) lt)

instance trivializeable_IIOwp_2
  t1 t2 t3
  (pre : t1 -> t2 -> trace -> Type0) {| d:checkable3 pre |}
  (post : t1 -> t2 -> trace -> t3 -> trace -> Type0) :
  Tot (trivializeable ((x:t1) -> (y:t2) -> IIOwp t3 (pre_post_as_wp (pre x y) (post x y)))) =
  mk_trivializeable 
    #((x:t1) -> (y:t2) -> IIOwp t3 (pre_post_as_wp (pre x y) (post x y)))
    ((x:t1) -> (y:t2) -> IIOwp (maybe t3) (post_as_wp (new_post_2 d.check3 post x y)))
    (fun f x y ->
        let h = get_trace () in
        if d.check3 x y h then Inl (f x y)
        else Inr Contract_failure)
  
let new_post_3
  (pre:'a -> 'b -> 'c -> trace -> bool)
  (post:'a -> 'b -> 'c -> trace -> 'd -> trace -> Type0) :
  Tot ('a -> 'b -> 'c -> trace -> maybe 'd -> trace -> Type0) =
    fun x y z h r lt -> 
      (~(pre x y z h) ==> r == (Inr Contract_failure) /\ lt == []) /\
      (pre x y z h ==> Inl? r /\ post x y z h (Inl?.v r) lt)

instance trivializeable_IIOwp_3
  t1 t2 t3 t4
  (pre : t1 -> t2 -> t3 -> trace -> Type0) {| d:checkable4 pre |}
  (post : t1 -> t2 -> t3 -> trace -> t4 -> trace -> Type0) :
  Tot (trivializeable ((x:t1) -> (y:t2) -> (z:t3) -> IIOwp t4 (pre_post_as_wp (pre x y z) (post x y z)))) =
  mk_trivializeable 
    #((x:t1) -> (y:t2) -> (z:t3) -> IIOwp t4 (pre_post_as_wp (pre x y z) (post x y z)))
    ((x:t1) -> (y:t2) -> (z:t3) -> IIOwp (maybe t4) (post_as_wp (new_post_3 d.check4 post x y z)))
    (fun f x y z ->
        let h = get_trace () in
        if d.check4 x y z h then Inl (f x y z)
        else Inr Contract_failure)
