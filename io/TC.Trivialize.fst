module TC.Trivialize

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open TC.Checkable
open IO.Sig
open IO
open IIO

class trivial (t:Type) = { 
  [@@@no_method] mldummy: unit }

instance trivial_IIOwp
  t1 t2 (post:t1 -> trace -> t2 -> trace -> Type0) : 
  trivial ((x:t1) -> IIOwp t2 (post_as_hist (post x))) =
  { mldummy = () }

instance trivial_IIOwp_2
  t1 t2 t3 (post:t1 -> t2 -> trace -> t3 -> trace -> Type0) : 
  trivial ((x:t1) -> (y:t2) -> IIOwp t3 (post_as_hist (post x y))) =
  { mldummy = () }

instance trivial_IIOwp_3
  t1 t2 t3 t4 (post:t1 -> t2 -> t3 -> trace -> t4 -> trace -> Type0) : 
  trivial ((x:t1) -> (y:t2) -> (z:t3) -> IIOwp t4 (post_as_hist (post x y z))) =
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

class trivializeable (t : Type) = { 
  [@@@no_method]
  ttype : Type; 
  trivialize : t -> ttype; 
  [@@@no_method]
  trivial_ttype : trivial ttype 
}
  
let mk_trivializeable (#t1 t2 : Type) {| trivial t2 |} (exp : t1 -> t2) : trivializeable t1 =
  { ttype = t2; trivialize = exp;  trivial_ttype = solve }

(** The new post-condition of the function may be look weird. 
Like, why is it `check x ==> post x r` and not `pre x ==> post x r`? Well, because `pre`
is checkable (check x ==> pre x), not decideable (check x <==> pre x). Therefore,
therere may be x for which `check x` is false and `pre x` is true. **)

let new_post
  (pre:'a -> trace -> bool)
  (post:'a -> trace -> 'b -> trace -> Type0) :
  Tot ('a -> trace -> resexn 'b -> trace -> Type0) =
    fun x h r lt -> 
      (~(pre x h) ==> r == (Inr Contract_failure) /\ lt == []) /\
      (pre x h ==> Inl? r /\ post x h (Inl?.v r) lt)

instance trivializeable_IIOwp
  t1 t2
  (pre : t1 -> trace -> Type0) {| d:checkable2 pre |}
  (post : t1 -> trace -> t2 -> trace -> Type0) :
  Tot (trivializeable ((x:t1) -> IIOwp t2 (to_hist (pre x) (post x)))) =
  mk_trivializeable 
    #((x:t1) -> IIOwp t2 (to_hist (pre x) (post x)))
    ((x:t1) -> IIOwp (resexn t2) (post_as_hist (new_post d.check2 post x)))
    (fun f x ->
        let h = get_trace () in
        if d.check2 x h then Inl (f x)
        else Inr Contract_failure)

instance trivializeable_IOwp
  t1 t2
  (pre : t1 -> trace -> Type0) {| d:checkable2 pre |}
  (post : t1 -> trace -> t2 -> trace -> Type0) :
  Tot (trivializeable ((x:t1) -> IOwp t2 (to_hist (pre x) (post x)))) =
  mk_trivializeable 
    #((x:t1) -> IOwp t2 (to_hist (pre x) (post x)))
    ((x:t1) -> IIOwp (resexn t2) (post_as_hist (new_post d.check2 post x)))
    (fun f -> 
      let f' : (x:t1) -> IIOwp t2 (to_hist (pre x) (post x)) = fun x -> f x in
      trivialize f' )

let trivialize_new_post_resexn
  (pre:'a -> trace -> bool)
  (post:'a -> trace -> resexn 'b -> trace -> Type0) :
  Tot ('a -> trace -> resexn 'b -> trace -> Type0) =
    fun x h r lt -> 
      (~(pre x h) ==> r == (Inr Contract_failure) /\ lt == []) /\
      (pre x h ==> post x h r lt) 

let trivialize_new_post_resexn'
  (pre:trace -> bool)
  (post:trace -> resexn 'b -> trace -> Type0) :
  Tot (trace -> resexn 'b -> trace -> Type0) =
    fun h r lt -> 
      (~(pre h) ==> r == (Inr Contract_failure)) /\
      (pre h ==> post h r lt) 

instance trivializeable_1_IIOwp_resexn
  t1 t2
  (pre : trace -> Type0) {| d:checkable pre |}
  (post : trace -> (resexn t2) -> trace -> Type0) :
  Tot (trivializeable (t1 -> IIOwp (resexn t2) (to_hist pre post))) =
  mk_trivializeable 
    #(t1 -> IIOwp (resexn t2) (to_hist pre post))
    (t1 -> IIOwp (resexn t2) (post_as_hist (trivialize_new_post_resexn' d.check post)))
    (fun f x ->
        let h = get_trace () in
        if d.check h then f x
        else Inr Contract_failure)

instance trivializeable_IIOwp_resexn
  t1 t2
  (pre : t1 -> trace -> Type0) {| d:checkable2 pre |}
  (post : t1 -> trace -> (resexn t2) -> trace -> Type0) :
  Tot (trivializeable ((x:t1) -> IIOwp (resexn t2) (to_hist (pre x) (post x)))) =
  mk_trivializeable 
    #((x:t1) -> IIOwp (resexn t2) (to_hist (pre x) (post x)))
    ((x:t1) -> IIOwp (resexn t2) (post_as_hist (trivialize_new_post_resexn d.check2 post x)))
    (fun f x ->
        let h = get_trace () in
        if d.check2 x h then f x
        else Inr Contract_failure)

instance trivializeable_IOwp_resexn
  t1 t2
  (pre : t1 -> trace -> Type0) {| d:checkable2 pre |}
  (post : t1 -> trace -> (resexn t2) -> trace -> Type0) :
  Tot (trivializeable ((x:t1) -> IO (resexn t2) (pre x) (post x))) =
  mk_trivializeable 
    #((x:t1) -> IO (resexn t2) (pre x) (post x))
    ((x:t1) -> IIOwp (resexn t2) (post_as_hist (trivialize_new_post_resexn d.check2 post x)))
    (fun f ->
      let f' : (x:t1) -> IIOwp (resexn t2) (to_hist (pre x) (post x)) = fun x -> f x in
      trivialize f')
  
let new_post_2
  (pre:'a -> 'b -> trace -> bool)
  (post:'a -> 'b -> trace -> 'c -> trace -> Type0) :
  Tot ('a -> 'b -> trace -> resexn 'c -> trace -> Type0) =
    fun x y h r lt -> 
      (~(pre x y h) ==> r == (Inr Contract_failure) /\ lt == []) /\
      (pre x y h ==> Inl? r /\ post x y h (Inl?.v r) lt)

instance trivializeable_IIOwp_2
  t1 t2 t3
  (pre : t1 -> t2 -> trace -> Type0) {| d:checkable3 pre |}
  (post : t1 -> t2 -> trace -> t3 -> trace -> Type0) :
  Tot (trivializeable ((x:t1) -> (y:t2) -> IIOwp t3 (to_hist (pre x y) (post x y)))) =
  mk_trivializeable 
    #((x:t1) -> (y:t2) -> IIOwp t3 (to_hist (pre x y) (post x y)))
    ((x:t1) -> (y:t2) -> IIOwp (resexn t3) (post_as_hist (new_post_2 d.check3 post x y)))
    (fun f x y ->
        let h = get_trace () in
        if d.check3 x y h then Inl (f x y)
        else Inr Contract_failure)
  
let new_post_3
  (pre:'a -> 'b -> 'c -> trace -> bool)
  (post:'a -> 'b -> 'c -> trace -> 'd -> trace -> Type0) :
  Tot ('a -> 'b -> 'c -> trace -> resexn 'd -> trace -> Type0) =
    fun x y z h r lt -> 
      (~(pre x y z h) ==> r == (Inr Contract_failure) /\ lt == []) /\
      (pre x y z h ==> Inl? r /\ post x y z h (Inl?.v r) lt)

instance trivializeable_IIOwp_3
  t1 t2 t3 t4
  (pre : t1 -> t2 -> t3 -> trace -> Type0) {| d:checkable4 pre |}
  (post : t1 -> t2 -> t3 -> trace -> t4 -> trace -> Type0) :
  Tot (trivializeable ((x:t1) -> (y:t2) -> (z:t3) -> IIOwp t4 (to_hist (pre x y z) (post x y z)))) =
  mk_trivializeable 
    #((x:t1) -> (y:t2) -> (z:t3) -> IIOwp t4 (to_hist (pre x y z) (post x y z)))
    ((x:t1) -> (y:t2) -> (z:t3) -> IIOwp (resexn t4) (post_as_hist (new_post_3 d.check4 post x y z)))
    (fun f x y z ->
        let h = get_trace () in
        if d.check4 x y z h then Inl (f x y z)
        else Inr Contract_failure)
