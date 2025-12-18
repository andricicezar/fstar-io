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

let lem_theta_return (#a:Type) (x:a) (h:history) (lt:local_trace h) :
  Lemma (requires lt == [])
        (ensures wp2p (theta (return x)) h lt x) =
  introduce forall p. theta (return x) h p ==> p lt x with begin
    introduce theta (return x) h p ==> p lt x with _. begin
      assert (return x == Return x);
      assert (theta (return x) h p == p [] x)
    end
  end

let post_condition_independence (#a:Type) (#h:history) (p:hist_post h a) (x:a) :
  Lemma (requires p [] x)
        (ensures forall h' (p':hist_post h' a). p' [] x) = admit ()

(*let theta_hist_indep #a (m:io a) (h:history) (lt:local_trace h) (fs_r:a) (p:hist_post h a) :
  Lemma (requires theta m h p ==> p lt fs_r)
        (ensures forall (h':history). exists (p':hist_post h' a) (lt':local_trace h'). theta m h' p' ==> p' lt' fs_r /\ (lt' == lt) /\ (p == p')) = admit () *)

let theta_history_independence #a (m:io a) (h:history) (lt:local_trace h) (fs_r:a) (p:hist_post h a) :
  Lemma (requires theta m h p ==> p lt fs_r)
        (ensures forall h' (lt':local_trace h') p'. theta m h' p' ==> p' lt' fs_r) =
  introduce forall h' lt' p'. theta m h' p' ==> p' lt' fs_r with begin
    introduce theta m h' p' ==> p' lt' fs_r with _. begin
      let _ : hist0 a = theta m in
      let _ : h:history -> hist_post h a -> Type0 = theta m in
      let _ : hist_post h a = p in
      let _ : local_trace h -> a -> Type0 = p in
      match m with
      | Return x -> begin
        assert (theta m h p == (hist_return x) h p);
        assert (theta m h p == p [] x);
        assert (p [] x ==> p lt fs_r);
        assume (p' [] x ==> p' lt' fs_r);
        ()
        //admit ()
        end
      | Call o args k -> begin
        //hist_bind (op_wp o args) (fun r -> theta (k r))
        //fun h p -> (op_wp o args) h (hist_post_bind h (fun r -> theta (k r)) p)
        assume (theta m h p == (hist_bind (op_wp o args) (fun r -> theta (k r))) h p);
        assert (theta m h p == (op_wp o args) h (hist_post_bind h (fun r -> theta (k r)) p));
        assert (theta m h p == (op_wp o args) h (fun lt r -> (fun r -> theta (k r)) r (h++lt) (hist_post_shift h p lt)));
        assert (theta m h p == (op_wp o args) h (fun lt r -> (fun r -> theta (k r)) r (h++lt) (fun lt' r -> p (lt @ lt') r)));
        admit ()
        end
    end
  end
