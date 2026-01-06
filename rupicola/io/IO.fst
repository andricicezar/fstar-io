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

let theta_monad_morphism_ret x =
  assert (theta (return x) == hist_return x) by (FStar.Tactics.compute ())

let theta_monad_morphism_bind m k = admit ()

let wp2p_theta_bind m k =
  theta_monad_morphism_bind m k

let io_bind_equivalence (#a #b:Type) (k k':a -> io b) (m:io a) :
  Lemma (requires forall x. k x == k' x)
        (ensures theta (io_bind m k) `hist_equiv` theta (io_bind m k')) = admit ()

let lem_theta_read (x:io_res ORead ()) (h:history) (lt:local_trace h) :
  Lemma (requires lt == [EvRead () x])
        (ensures wp2p (theta (read ())) h lt x) =
  assert (theta (read ()) == (fun (h:history) (p:hist_post h (resexn bool)) -> (forall (lt:local_trace h) (r:resexn bool). lt == [EvRead () r] ==> p (lt @ []) r))) by (assert (lt @ []) == lt; FStar.Tactics.compute ())

let lem_theta_write (b:bool) (x:io_res OWrite b) (h:history) (lt:local_trace h) :
  Lemma (requires lt == [EvWrite b x])
        (ensures wp2p (theta (write b)) h lt x) =
  assert (theta (write b) == (fun (h:history) (p:hist_post h (resexn unit)) -> (forall (lt:local_trace h) (r:resexn unit). lt == [EvWrite b r] ==> p (lt @ []) r))) by (assert (lt @ []) == lt; FStar.Tactics.compute ())

(*let hist_independence #a (wp:hist0 a) (h:history) (p:hist_post h a) :
  Lemma (requires wp h p)
        (ensures forall h_. exists p_. wp h_ p_) = admit ()

let hist_post_independence #a #h (p:hist_post h a) (lt:local_trace h) (r:a) :
  Lemma (requires p lt r)
        (ensures forall (h_:history). exists (p_:hist_post h_ a). p_ lt r)*)

// steps e e' h' lt'
// indexed_irred e' (h'++lt')
// steps e e' h lt_
// indexed_irred e' (h++lt_)
// t in (h++lt_, fs_r, e')
// fs_beh fs_e h lt_ fs_r == wp2p (theta fs_r)

(*let test_lemma (e e':closed_exp) (h:history) (lt:local_trace h) (t:qType) (fs_e:fs_prod t) (fs_r:get_Type t) :
  Lemma (requires steps e e' h lt /\
                  indexed_irred e' (h++lt) /\
                  t ⪾ (h, fs_e, e) /\
                  t ∋ (h++lt, fs_r, e')) /\
                  (theta fs_e) == fs_r)
        (ensures wp2p (theta fs_e) h lt fs_r) =
  introduce forall p. (theta fs_e) h p ==> p lt fs_r with begin // we have no information about this p, since we don´t know how the ((theta fs_e) h p) predicate is calculated
    admit ()
  end*)

let theta_history_independence #a (m:io a) (h h':history) (lt:local_trace h) (lt':local_trace h') (fs_r:a) :
  Lemma (requires wp2p (theta m) h lt fs_r /\ lt == lt')
        (ensures wp2p (theta m) h' lt' fs_r) =
  match lt' with
  | [] -> begin
    match m with
    | Return x -> begin
      assert (m == (return x));
      lem_theta_return x h' lt';
      assert (wp2p (theta m) h' lt' x);
      admit ()
      end
    | _ -> admit ()//false_elim ()
    //admit ()
    end
  | ev :: tl -> admit ()
