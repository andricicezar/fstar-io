module IO

(** we only have bools in STLC right now **)
open Trace

noeq
type io (a:Type u#a) : Type u#a =
| Call : o:io_ops -> args:io_args o -> (io_res o args -> io a) -> io a
//| PartialCall : (pre:pure_pre) -> cont:((squash pre) -> io u#a a) -> io a
| Return : a -> io a

let io_return (#a:Type) (x:a) : io a =
  Return x

let rec io_bind
  (#a:Type u#a)
  (#b:Type u#b)
  (l : io a)
  (k : a -> io b) :
  io b =
  match l with
  | Return x -> k x
  | Call o args fnc ->
      Call o args (fun i ->
        io_bind #a #b (fnc i) k)

let read () : io (resexn bool) =
  Call ORead () Return

let write (x:bool) : io (resexn unit) =
  Call OWrite x Return

let op_wp (o:io_ops) (args:io_args o) : hist (io_res o args) =
  to_hist
    (fun h -> io_pre h o args)
    (fun h res lt -> io_post h o args res /\ lt == [op_to_ev o args res])

let rec theta #a (m:io a) : hist a =
  match m with
  | Return x -> hist_return x
  | Call o args k -> hist_bind (op_wp o args) (fun r -> theta (k r))

let io_bind_equivalence (#a #b:Type) (k k':a -> io b) (m:io a) :
  Lemma (requires forall x. k x == k' x)
        (ensures theta (io_bind m k) `hist_equiv` theta (io_bind m k')) = admit ()
        
let lem_theta_return (#a:Type) (x:a) (h:history) (lt:local_trace h) :
  Lemma (requires lt == [])
        (ensures wp2p (theta (return x)) h lt x) =
  introduce forall p. theta (return x) h p ==> p lt x with begin
    introduce theta (return x) h p ==> p lt x with _. begin
      assert (return x == Return x);
      assert (theta (return x) h p == p [] x)
    end
  end

let lem_theta_bind #a #b (m:io a) (h:history) (lt2:local_trace h) (fs_r_m:a) (k:a -> io b) (lt3:local_trace (h++lt2)) (fs_r:b) (lt:local_trace h) :
  Lemma (requires wp2p (theta m) h lt2 fs_r_m /\
                  wp2p (theta (k fs_r_m)) (h++lt2) lt3 fs_r /\
                  (lt == lt2 @ lt3))
        (ensures wp2p (theta (io_bind m k)) h lt fs_r) = admit ()

let theta_history_independence #a (m:io a) (h h':history) (lt:local_trace h) (lt':local_trace h') (fs_r:a) :
  Lemma (requires wp2p (theta m) h lt fs_r) 
        (ensures wp2p (theta m) h' lt' fs_r) = admit ()
