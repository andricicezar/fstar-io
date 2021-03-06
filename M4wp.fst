module M4wp

open Common
open IOStHist

let m4wp_invariant_pre (pi_check : monitorable_prop) (s0:events_trace) : Type0 =
  enforced_globally default_check s0 &&
  enforced_globally pi_check s0

let m4wp_invariant_post
  (#a:Type)
  (pi_check : monitorable_prop)
  (s0:events_trace)
  (result:maybe (events_trace * a))
  (local_trace:events_trace) :
  Tot Type0 =
  enforced_globally (default_check) (apply_changes s0 local_trace) /\
  enforced_globally (pi_check) (apply_changes s0 local_trace) /\
  (match result with
  | Inl v -> let (s1, r) = v in s1 == (apply_changes s0 local_trace)
  | Inr _ -> True)

effect M4wp
  (a:Type)
  (pi_check : monitorable_prop) 
  (post : events_trace -> maybe (events_trace * a) -> events_trace -> Type0) =
  IOStHist a
    (requires (m4wp_invariant_pre pi_check))
    (ensures (fun h r le -> m4wp_invariant_post pi_check h r le /\ post h r le))
