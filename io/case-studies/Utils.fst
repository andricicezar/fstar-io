module Utils

open FStar.List

open DM
open IO.Sig.Call

let lemma_append_enforced_locally pi :
  Lemma (forall h lt1 lt2.
    enforced_locally pi h lt1 /\
    enforced_locally pi (apply_changes h lt1) lt2 ==> 
    enforced_locally pi h (lt1 @ lt2)) = admit () 

open FStar.Tactics

let static_cmd
  (cmd : io_cmds)
  (pi : monitorable_prop)
  (arg : io_sig.args cmd) :
  IO (io_resm cmd)
    (requires (fun h -> pi cmd arg h /\ io_pre cmd arg h))
    (ensures (fun h (r:io_sig.res cmd arg) lt ->
        lt == [convert_call_to_event cmd arg r] /\
        enforced_locally pi h lt)) =
  admit ();
  static_cmd cmd arg

let io_post
  (#a:Type)
  (pi : monitorable_prop)
  (h:trace)
  (result:a)
  (local_trace:trace) :
  Tot bool =
  enforced_locally pi h local_trace

effect IOpi
  (a:Type)
  (pi : monitorable_prop)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  IOwp a
    (fun p h ->
      pre h /\
      (forall r lt. (io_post pi h r lt /\ post h r lt) ==> p lt r))

let _IIOwp_as_MIIO
  (pre:'a -> trace -> bool)
  (post:'a -> trace -> (m:'b) -> trace -> Type0)
  (f:(x:'a ->
    IIOwp 'b (fun p h -> pre x h /\ (forall r lt. post x h r lt ==> p lt r))))
  (x:'a) :
  IIOwp (Common.maybe 'b) (trivial_hist ()) =
  (trivialize 
    #_ 
    #(trivializeable_IIOwp _ _ (fun x h -> pre x h) post) f) x

let _IIOwp_as_MIIO_2
  (pre:'a -> 'b -> trace -> bool)
  (post:'a -> 'b -> trace -> (m:'c) -> trace -> Type0)
  (f:(x:'a -> y:'b ->
    IIOwp 'c (fun p h -> pre x y h /\ (forall r lt. post x y h r lt ==> p lt r))))
  (x:'a) (y:'b):
  IIOwp (Common.maybe 'c) (trivial_hist ()) =
  (trivialize 
    #_ 
    #(trivializeable_IIOwp_2 _ _ _ (fun x y h -> pre x y h) post) f) x y
