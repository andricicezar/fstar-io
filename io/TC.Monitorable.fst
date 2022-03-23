module TC.Monitorable

open FStar.Tactics
open FStar.Tactics.Typeclasses

open IO.Sig 

type action_type = (cmd : io_cmds) & (io_sig.args cmd)
type monitorable_prop = (history:trace) -> (action:action_type) -> Tot bool

let convert_event_to_action (e:event) : action_type =
  match e with
  | EOpenfile arg _ -> (| Openfile, arg |)
  | ERead arg _ -> (| Read, arg |)
  | EClose arg _ -> (| Close, arg |)

let rec enforced_locally
  (check : monitorable_prop)
  (h l: trace) :
  Tot bool (decreases l) =
  match l with
  | [] -> true
  | hd  ::  t ->
    let action = convert_event_to_action hd in
    if check h action then enforced_locally (check) (hd::h) t
    else false

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
