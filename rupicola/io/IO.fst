module IO

(** we only have bools in STLC right now **)
open Trace
open STLC

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

(*//requires lt == []
//ensures wp2p (theta (return x))

assume val get_lt (h h':history) (lt:local_trace h) : (lt':local_trace h') // indution on lt

let hist_monotonic (wp:hist 'a) :
Lemma (forall h h' (p':hist_post h' 'a). (wp h' p' ==> wp h (fun lt res -> p' (get_lt h h' lt) res))) = admit ()

// equivalent up to renaming of local traces*)

let rec theta_monotonic_hist (m:io 'a) :
Lemma (forall h h' (p':hist_post h' 'a). (theta m h' p' ==> theta m h (fun lt res -> p' (get_lt h h' lt) res))) =
  match m with
  | Return x -> begin
    introduce forall h h' p'. theta m h' p' ==> theta m h (fun lt res -> p' (get_lt h h' lt) res) with begin
      introduce _ ==> _ with _. begin
        let lt' : local_trace h' = [] in
        let lt : local_trace h = [] in
        assert (theta m h' p' == p' lt' x);
        assert (theta m h (fun lt res -> p' (get_lt h h' lt) res) == (p' (get_lt h h' lt) x));
        assume (p' lt' x ==> p' (get_lt h h' lt) x)
        //assume (get_lt h h' lt == lt')
        //admit ()
      end
    end
    end
  | Call o args k -> begin
    introduce forall h h' p'. theta m h' p' ==> theta m h (fun lt res -> p' (get_lt h h' lt) res) with begin
      introduce _ ==> _ with _. begin
        assert (theta (Call o args k) == hist_bind (op_wp o args) (fun r -> theta (k r))) by (FStar.Tactics.compute ());
        assert (hist_bind (op_wp o args) (fun r -> theta (k r)) h' p' == (op_wp o args) h' (hist_post_bind h' (fun r -> theta (k r)) p')) by (FStar.Tactics.compute ());
        assert ((op_wp o args) h' (hist_post_bind h' (fun r -> theta (k r)) p') == forall r. theta (k r) (h'++[op_to_ev o args r]) (fun lt' r -> p' ([op_to_ev o args r] @ lt') r)) by (FStar.Tactics.compute ());
        introduce forall r. theta (k r) (h++[op_to_ev o args r]) (fun lt' r -> (p' (get_lt h h' ([op_to_ev o args r] @ lt')) r with begin
          theta_monotonic_hist (k r);
        end
        //assume (forall r. theta (k r) (h++[op_to_ev o args r]) (fun lt' r -> (p' (get_lt h h' ([op_to_ev o args r] @ lt')) r));
        //assume ((op_wp o args) h (fun lt r -> theta (k r) (h++lt) (fun lt' r -> p' (get_lt h h' (lt @ lt')) r)))
        //assert (theta m h (fun lt res -> p' (get_lt h h' lt) res) == (p' (get_lt h h' lt) x));
        //assume (p' lt' x ==> p' (get_lt h h' lt) x)
        //assume (get_lt h h' lt == lt')
        admit ()
      end
    end
    end

let theta_history_independence #a (m:io a) (h h':history) (lt:local_trace h) (lt':local_trace h') (fs_r:a) :
  Lemma (requires wp2p (theta m) h lt fs_r /\ lt == lt')
        (ensures wp2p (theta m) h' (get_lt h h' lt) fs_r) =
  match m with
  | Return x -> begin
    assert (wp2p (theta m) h lt fs_r);
    assert (forall p. (theta m) h p ==> p [] x);
    introduce forall (p':hist_post h' a). (theta m) h' p' ==> p' lt' fs_r with begin
      introduce (theta m) h' p' ==> p' lt' fs_r with _. begin
      
        let p : hist_post h a = fun lt res -> p' (get_lt h h' lt) res in
        eliminate forall p. (theta m) h p ==> p lt fs_r with p;
        assert ((theta m) h' p');
        hist_wp_monotonic' (theta m);
        assert (p lt fs_r);
        assert (p' (get_lt h h' lt) fs_r);
        assert ((get_lt h h' lt) == lt')
  
        //admit ()
        //assert ((theta m) h p ==> p lt fs_r);
        //admit ()
      end
    end
    //assume (forall p'. (theta m) h' p' ==> p' [] x);
    //assert (lt == []);
    //assert (fs_r == x);
    //assume (wp2p (theta m) h' [] x)
    //admit ()
    end
  | Call o args k -> admit ()
  (*introduce forall (p':hist_post h' a). (theta m) h' p' ==> p' lt' fs_r with begin
    introduce (theta m) h' p' ==> p' lt' fs_r with _. begin
      
      let p : hist_post h a = fun lt res -> p' (get_lt h h' lt) res in
      eliminate forall p. (theta m) h p ==> p lt fs_r with p;
      assert ((theta m) h' p');
      assert ((theta m) h p ==> p lt fs_r);
      admit ()
    end
  end*)







let theta_history_independence' #a (m:io a) (h h':history) (lt:local_trace h) (lt':local_trace h') (fs_r:a) :
  Lemma (requires wp2p (theta m) h lt fs_r /\ lt == lt')
        (ensures wp2p (theta m) h' lt' fs_r) =
  match m with
  | Return x -> begin
    assert (wp2p (theta m) h lt fs_r);
    assert (forall p. (theta m) h p ==> p [] x);
    introduce forall (p':hist_post h' a). (theta m) h' p' ==> p' lt' fs_r with begin
      introduce (theta m) h' p' ==> p' lt' fs_r with _. begin
      
        let p : hist_post h a = fun lt res -> p' (get_lt h h' lt) res in
        eliminate forall p. (theta m) h p ==> p lt fs_r with p;
        assert ((theta m) h' p');
        assert ((theta m) h p ==> p lt fs_r)
        //admit ()
      end
    end
    //assume (forall p'. (theta m) h' p' ==> p' [] x);
    //assert (lt == []);
    //assert (fs_r == x);
    //assume (wp2p (theta m) h' [] x)
    //admit ()
    end
  | Call o args k -> admit ()
  (*introduce forall (p':hist_post h' a). (theta m) h' p' ==> p' lt' fs_r with begin
    introduce (theta m) h' p' ==> p' lt' fs_r with _. begin
      
      let p : hist_post h a = fun lt res -> p' (get_lt h h' lt) res in
      eliminate forall p. (theta m) h p ==> p lt fs_r with p;
      assert ((theta m) h' p');
      assert ((theta m) h p ==> p lt fs_r);
      admit ()
    end
  end*)
  
