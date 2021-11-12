module TC.Monitorable

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Free.IO

class monitorable_post (#t1:Type) (#t2:Type) 
  (pre : t1 -> trace -> Type0)
  (post : t1 -> trace -> t2 -> trace -> Type0)
  (pi : monitorable_prop) = {
  result_check : t1 -> trace -> t2 -> trace -> bool;
  (** this condition makes sure that all trace properties enforced by post are instrumented by pi **)
  c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> (exists r. post x h r lt));
  (** this one makes sure that the post at the end is enough **)
  c2post: squash (forall x h r lt. pre x h /\ enforced_locally pi h lt /\ result_check x h r lt ==> post x h r lt)
}
