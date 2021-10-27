module TC.MLify

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.All

open Common
open TC.Weaken
open TC.Trivialize
open TC.Export

class ml_arrow (t:Type) = { mldummy : unit }
instance ml_arrow_1 t1 t2 {| ml t1 |} {| ml t2 |} : ml_arrow (t1 -> ML t2) = { mldummy = () }

(** TODO: Is this really a ML arrow? 
This is just a hack to be able to extract higher-order functions in the MIIO effect **)
instance ml_tot_arrow_1 t1 t2 t3 {| ml t1 |} {| ml t2 |} {| ml t3 |} : ml_arrow ((t1 -> Tot t2) -> ML t3) = { mldummy = () }

class mlifyable (t : Type) =
  { mtype : Type; 
    trivial_t: trivial t;
    weak_t: weak t;
    mlify : t -> mtype; 
    ml_arrow_mtype : ml_arrow mtype }

let mk_mlifyable
  (#t1:Type) {| trivial t1 |} {| weak t1 |}
  (t2:Type) {| ml_arrow t2 |} 
  (exp : t1 -> t2) : 
  mlifyable t1 =
  { mtype = t2; 
    trivial_t = solve;
    weak_t = solve;
    mlify = exp;
    ml_arrow_mtype = solve }

instance mlifyable_tot 
  t1 t2 {| ml t1 |} {| ml t2 |} :
  Tot (mlifyable (t1 -> Tot t2)) =
  mk_mlifyable (t1 -> ML t2)
    (fun f x -> f x <: ML t2)

instance mlifyable_pure
  t1 t2 {| ml t1 |} {| ml t2 |} 
  (post: t1->t2->Type0):
  Tot (mlifyable ((x:t1) -> Pure t2 True (post x))) =
  mk_mlifyable
    #((x:t1) -> Pure t2 True (post x))
    (t1 -> ML t2)
    (fun f x -> f x <: ML t2)
