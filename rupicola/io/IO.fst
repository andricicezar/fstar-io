module IO

(** we only have bools in STLC right now **)
open Trace
open STLC

open FStar.Tactics

noeq
type io (a:Type u#a) : Type u#a =
| Call : o:io_ops -> args:io_args o -> (io_res o args -> io a) -> io a
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

let openfile (fnm:bool) : io (resexn file_descr) =
  Call OOpen fnm Return

let read (fd:file_descr) : io (resexn bool) =
  Call ORead fd Return

let write (x:file_descr * bool) : io (resexn unit) =
  Call OWrite x Return

let close (fd:file_descr) : io (resexn unit) =
  Call OClose fd Return

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

let theta_monad_morphism_bind m k =
  admit () (** Cezar: should be double. existing proof in sciostar/DMFree.fst **)

let io_bind_equivalence (#a #b:Type) (k k':a -> io b) (m:io a) :
  Lemma (requires forall x. k x == k' x)
        (ensures theta (io_bind m k) `hist_equiv` theta (io_bind m k')) =
  admit () (** Cezar: Is induction on m enough? **)

let wp2p_theta_bind m k =
  theta_monad_morphism_bind m k

let lem_theta_open arg res h =
  introduce forall (p:hist_post h (io_res OOpen arg)). (theta (openfile arg)) h p ==> p [EvOpen arg res] res with begin
    introduce _ ==> _ with _. begin
    match openfile arg with
    | Return x -> false_elim ()
    | Call OOpen arg k -> begin
      assert ((hist_bind (op_wp OOpen arg) (fun (r:io_res OOpen arg) -> theta (k r))) h p ==> (hist_bind (to_hist (fun h_ -> io_pre h_ OOpen arg) (fun h_ res_ lt_ -> io_post h_ OOpen arg res_ /\ lt_ == [op_to_ev OOpen arg res_])) (fun (r:io_res OOpen arg) -> theta (k r))) h p) by (compute ());
      eliminate forall (lt':local_trace h) (r':io_res OOpen arg). lt' == [EvOpen arg r'] ==> (theta (k r')) (h++lt') (fun (lt'':local_trace (h++lt')) (r'':io_res OOpen arg) -> p (lt' @ lt'') r'') with [EvOpen arg res] res
      end
    end
  end

let lem_theta_read arg res h =
  assert (thetaP (read arg) h [EvRead arg res] res) by (compute ())

let lem_theta_write arg res h =
  assert (thetaP (write arg) h [EvWrite arg res] res) by (compute ())

let lem_theta_close arg res h =
  assert (thetaP (close arg) h [EvClose arg res] res) by (compute ())

(**
let rec get_lt (h h':history) (lt:local_trace h) : Tot (local_trace h') (decreases lt) =
  match lt with
  | [] -> []
  | ev :: tl -> begin
    match ev with
    | EvRead args res -> begin
      // here we will need to check compatability of ev with h' and either return Inl or Inr of unit
      assume (test_event h' ev);
      assume (well_formed_local_trace (ev::h) tl);
      assume (forall (lt':local_trace (ev::h')). well_formed_local_trace h' (ev::lt'));
      ev :: (get_lt (ev::h) (ev::h') tl)
      end
    | EvWrite args res -> begin
      // here we will need to check compatability of ev with h' and either return Inl or Inr of unit
      assume (test_event h' ev);
      assume (well_formed_local_trace (ev::h) tl);
      assume (forall (lt':local_trace (ev::h')). well_formed_local_trace h' (ev::lt'));
      ev :: (get_lt (h++[ev]) (h'++[ev]) tl)
      end
    end
**)

// (lt == [] ==> (get_lt h h' []) == [])

(*
let get_lt_correct (h h':history) (lt:local_trace h) :
  Lemma ((lt == [] ==> (get_lt h h' []) == []) /\
         (forall (lt1:local_trace h) (lt2:local_trace (h++lt1)). lt == (lt1 @ lt2) ==> (get_lt h h' (lt1 @ lt2)) == (get_lt h h' lt1) @ (get_lt (h++lt1) (h'++lt1) lt2))) = admit ()
*)

// x ( lt1 @ lt2) == x lt1 @ x lt2

(*
let rec theta_monotonic_hist (m:io 'a) :
Lemma (forall h h' (p':hist_post h' 'a). (theta m h' p' ==> theta m h (fun lt res -> p' (get_lt h h' lt) res))) =
  match m with
  | Return x -> begin
    introduce forall h h' p'. theta m h' p' ==> theta m h (fun lt res -> p' (get_lt h h' lt) res) with begin
      introduce _ ==> _ with _. begin
        assert ((theta m h' p') == p' [] x);
        assert ((theta m h (fun lt res -> p' (get_lt h h' lt) res)) == p' (get_lt h h' []) x);
        get_lt_correct h h' []
      end
    end
    end
  | Call o args k -> begin
    introduce forall h h' p'. theta m h' p' ==> theta m h (fun lt res -> p' (get_lt h h' lt) res) with begin
      introduce theta m h' p' ==> theta m h (fun lt res -> p' (get_lt h h' lt) res) with _. begin
        assume ((theta m h' p') == (forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h'++lt) (fun (lt':local_trace (h'++lt)) r -> p' (lt @ lt') r)));
        assume ((theta m h (fun lt res -> p' (get_lt h h' lt) res)) == (forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h++lt) (fun (lt':local_trace (h++lt)) r -> p' (get_lt h h' (lt @ lt')) r)));
        introduce forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h++lt) (fun (lt':local_trace (h++lt)) r -> p' (get_lt h h' (lt @ lt')) r) with begin
          introduce lt == [op_to_ev o args r] ==> theta (k r) (h++lt) (fun (lt':local_trace (h++lt)) r -> p' (get_lt h h' (lt @ lt')) r) with _. begin
          // theta (k r) (h'++lt) (fun (lt':local_trace (h'++lt)) r -> p' (lt @ lt') r)
          // theta (k r) (h++lt) (fun (lt':local_trace (h++lt)) r -> p' (get_lt h h' (lt @ lt')) r)
            assert (theta (k r) (h'++lt) (fun (lt':local_trace (h'++lt)) r -> p' (lt @ lt') r));
            theta_monotonic_hist (k r);
            assert (forall h h' (p':hist_post h' 'a). (theta (k r) h' p' ==> theta (k r) h (fun lt res -> p' (get_lt h h' lt) res)));
            eliminate forall h h' (p':hist_post h' 'a). (theta (k r) h' p' ==> theta (k r) h (fun lt res -> p' (get_lt h h' lt) res)) with (h++lt) (h'++lt) (fun (lt':local_trace (h'++lt)) r -> p' (lt @ lt') r);
            assert (theta (k r) (h++lt) (fun lt_ res -> (fun (lt':local_trace (h'++lt)) r -> p' (lt @ lt') r) (get_lt (h++lt) (h'++lt) lt_) res));
            assert (theta (k r) (h++lt) (fun lt_ res -> p' (lt @ (get_lt (h++lt) (h'++lt) lt_)) res));
            introduce forall (lt':local_trace (h++lt)) r. (p' (get_lt h h' (lt @ lt')) r) ==  (p' (lt @ (get_lt (h++lt) (h'++lt) lt')) r) with begin
              get_lt_correct h h' (lt @ lt')
            end
          end
        end
      end
    end
    end
*)

(*
let theta_history_independence #a (m:io a) (h h':history) (lt:local_trace h) (fs_r:a) :
  Lemma (requires wp2p (theta m) h lt fs_r)
        (ensures wp2p (theta m) h' (get_lt h h' lt) fs_r) =
  introduce forall (p':hist_post h' a). theta m h' p' ==> p' (get_lt h h' lt) fs_r with begin
    introduce _ ==> _ with _. begin
      theta_monotonic_hist m;
      eliminate forall h h' p'. theta m h' p' ==> theta m h (fun lt res -> p' (get_lt h h' lt) res) with h h' p';
      assert (forall (p:hist_post h a). theta m h p ==> p lt fs_r);
      eliminate forall (p:hist_post h a). theta m h p ==> p lt fs_r with (fun lt res -> p' (get_lt h h' lt) res);
      assert (p' (get_lt h h' lt) fs_r)
    end
  end
*)

(* DEFINITION UNFOLDING
assert (theta m h' p' == theta (Call o args k) h' p');
        assert (theta m h (fun lt res -> p' (get_lt h h' lt) res) == theta (Call o args k) h (fun lt res -> p' (get_lt h h' lt) res));
        assert (theta (Call o args k) h' p' == hist_bind (op_wp o args) (fun r -> theta (k r)) h' p') by (FStar.Tactics.compute ());
        assert (theta (Call o args k) h (fun lt res -> p' (get_lt h h' lt) res) == hist_bind (op_wp o args) (fun r -> theta (k r)) h (fun lt res -> p' (get_lt h h' lt) res)) by (FStar.Tactics.compute ());
        assert (hist_bind (op_wp o args) (fun r -> theta (k r)) h' p' == (op_wp o args) h' (hist_post_bind h' (fun r -> theta (k r)) p')) by (FStar.Tactics.compute ());
        assert (hist_bind (op_wp o args) (fun r -> theta (k r)) h (fun lt res -> p' (get_lt h h' lt) res) == (op_wp o args) h (hist_post_bind h (fun r -> theta (k r)) (fun lt res -> p' (get_lt h h' lt) res))) by (FStar.Tactics.compute ());
        assert ((op_wp o args) h' (hist_post_bind h' (fun r -> theta (k r)) p') == to_hist (fun h -> io_pre h o args) (fun h res lt -> io_post h o args res /\ lt == [op_to_ev o args res]) h' (hist_post_bind h' (fun r -> theta (k r)) p')) by (FStar.Tactics.compute ());
        assert ((op_wp o args) h (hist_post_bind h (fun r -> theta (k r)) (fun lt res -> p' (get_lt h h' lt) res)) == to_hist (fun h -> io_pre h o args) (fun h res lt -> io_post h o args res /\ lt == [op_to_ev o args res]) h (hist_post_bind h (fun r -> theta (k r)) (fun lt res -> p' (get_lt h h' lt) res))) by (FStar.Tactics.compute ());
        assert ((to_hist (fun h -> io_pre h o args) (fun h res lt -> io_post h o args res /\ lt == [op_to_ev o args res])) == (fun h p -> io_pre h o args /\ (forall (lt:local_trace h) (r:io_res o args). (io_post h o args r /\ lt == [op_to_ev o args r]) ==> p lt r))) by (FStar.Tactics.compute ());
        assert ((to_hist (fun h -> io_pre h o args) (fun h res lt -> io_post h o args res /\ lt == [op_to_ev o args res]) h' (hist_post_bind h' (fun r -> theta (k r)) p')) == (fun h p -> io_pre h o args /\ (forall (lt:local_trace h) (r:io_res o args). (io_post h o args r /\ lt == [op_to_ev o args r]) ==> p lt r)) h' (hist_post_bind h' (fun r -> theta (k r)) p')) by (FStar.Tactics.compute ());
        assert ((to_hist (fun h -> io_pre h o args) (fun h res lt -> io_post h o args res /\ lt == [op_to_ev o args res]) h (hist_post_bind h (fun r -> theta (k r)) (fun lt res -> p' (get_lt h h' lt) res))) == (fun h p -> io_pre h o args /\ (forall (lt:local_trace h) (r:io_res o args). (io_post h o args r /\ lt == [op_to_ev o args r]) ==> p lt r)) h (hist_post_bind h (fun r -> theta (k r)) (fun lt res -> p' (get_lt h h' lt) res))) by (FStar.Tactics.compute ());
        assert ((fun h p -> io_pre h o args /\ (forall (lt:local_trace h) (r:io_res o args). (io_post h o args r /\ lt == [op_to_ev o args r]) ==> p lt r)) h' (hist_post_bind h' (fun r -> theta (k r)) p') == (io_pre h' o args /\ (forall lt (r:io_res o args). (io_post h' o args r /\ lt == [op_to_ev o args r]) ==> (hist_post_bind h' (fun r -> theta (k r)) p') lt r))) by (FStar.Tactics.compute ());
        assert ((fun h p -> io_pre h o args /\ (forall (lt:local_trace h) (r:io_res o args). (io_post h o args r /\ lt == [op_to_ev o args r]) ==> p lt r)) h (hist_post_bind h (fun r -> theta (k r)) (fun lt res -> p' (get_lt h h' lt) res)) == (io_pre h o args /\ (forall lt (r:io_res o args). (io_post h o args r /\ lt == [op_to_ev o args r]) ==> (hist_post_bind h (fun r -> theta (k r)) (fun lt res -> p' (get_lt h h' lt) res)) lt r))) by (FStar.Tactics.compute ());
        assert ((io_pre h o args /\ (forall lt (r:io_res o args). (io_post h o args r /\ lt == [op_to_ev o args r]) ==> (hist_post_bind h (fun r -> theta (k r)) (fun lt res -> p' (get_lt h h' lt) res)) lt r)) == (forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> (hist_post_bind h (fun r -> theta (k r)) (fun lt res -> p' (get_lt h h' lt) res)) lt r)) by (FStar.Tactics.compute ());
        assert ((io_pre h' o args /\ (forall lt (r:io_res o args). (io_post h' o args r /\ lt == [op_to_ev o args r]) ==> (hist_post_bind h' (fun r -> theta (k r)) p') lt r)) == (forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> (hist_post_bind h' (fun r -> theta (k r)) p') lt r)) by (FStar.Tactics.compute ());
        assert ((forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> (hist_post_bind h' (fun r -> theta (k r)) p') lt r) == (forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h'++lt) (hist_post_shift h' p' lt))) by (FStar.Tactics.compute ());
        assert ((forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> (hist_post_bind h (fun r -> theta (k r)) (fun lt res -> p' (get_lt h h' lt) res)) lt r) == (forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h++lt) (hist_post_shift h (fun lt res -> p' (get_lt h h' lt) res) lt))) by (FStar.Tactics.compute ());
        assert ((forall (lt:local_trace h'). (hist_post_shift h' p' lt) == (fun (lt':local_trace (h'++lt)) r -> p' (lt @ lt') r))) by (FStar.Tactics.compute ());
        assert ((forall (lt:local_trace h). (hist_post_shift h (fun lt res -> p' (get_lt h h' lt) res) lt) == (fun (lt':local_trace (h++lt)) r -> (p' (get_lt h h' (lt @ lt')) r)))) by (FStar.Tactics.compute ());
        assert ((forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h'++lt) (hist_post_shift h' p' lt)) == (forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h'++lt) (fun (lt':local_trace (h'++lt)) r -> p' (lt @ lt') r))) by (FStar.Tactics.compute ());
        assert ((forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h++lt) (hist_post_shift h (fun lt res -> p' (get_lt h h' lt) res) lt)) == (forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h++lt) (fun (lt':local_trace (h++lt)) r -> (p' (get_lt h h' (lt @ lt')) r)))) by (FStar.Tactics.compute ());
*)

(*let rec theta_monotonic_hist' (m:io 'a) :
Lemma (forall h h' (p':hist_post h' 'a). (theta m h' p' ==> theta m h (fun lt res -> p' (get_lt h h' lt) res))) =
  match m with
  | Return x -> () (*begin
    introduce forall h h' p'. theta m h' p' ==> theta m h (fun lt res -> p' (get_lt h h' lt) res) with begin
      introduce _ ==> _ with _. begin
        assert (theta m h' p' == p' [] x);
        assert (theta m h (fun lt res -> p' (get_lt h h' lt) res) == (p' [] x));
        //assume (p' lt' x ==> p' (get_lt h h' lt) x)
        //assume (get_lt h h' lt == lt')
        admit ()
      end
    end
    end*)
  | _ -> admit ()
  (*| Call o args k -> begin
    introduce forall h h' p'. theta m h' p' ==> theta m h (fun lt res -> p' (get_lt h h' lt) res) with begin
      introduce _ ==> _ with _. begin
        assert (theta (Call o args k) == hist_bind (op_wp o args) (fun r -> theta (k r))) by (FStar.Tactics.compute ());
        assert (hist_bind (op_wp o args) (fun r -> theta (k r)) h' p' == (op_wp o args) h' (hist_post_bind h' (fun r -> theta (k r)) p')) by (FStar.Tactics.compute ());
        //assert ((op_wp o args) h' (hist_post_bind h' (fun r -> theta (k r)) p') == forall r. theta (k r) (h'++[op_to_ev o args r]) (fun lt' r -> p' ([op_to_ev o args r] @ lt') r)) by (FStar.Tactics.compute ());
        //introduce forall r. theta (k r) (h++[op_to_ev o args r]) (fun lt' r -> (p' (get_lt h h' ([op_to_ev o args r] @ lt')) r with begin
        //  theta_monotonic_hist (k r);
        //end
        //assume (forall r. theta (k r) (h++[op_to_ev o args r]) (fun lt' r -> (p' (get_lt h h' ([op_to_ev o args r] @ lt')) r));
        //assume ((op_wp o args) h (fun lt r -> theta (k r) (h++lt) (fun lt' r -> p' (get_lt h h' (lt @ lt')) r)))
        //assert (theta m h (fun lt res -> p' (get_lt h h' lt) res) == (p' (get_lt h h' lt) x));
        //assume (p' lt' x ==> p' (get_lt h h' lt) x)
        //assume (get_lt h h' lt == lt')
        admit ()
      end
    end
  end*)

(*let theta_history_independence #a (m:io a) (h h':history) (lt:local_trace h) (lt':local_trace h') (fs_r:a) :
  Lemma (requires wp2p (theta m) h lt fs_r /\ lt == lt')
        (ensures wp2p (theta m) h' (get_lt h h' lt) fs_r) = admit ()*)
  (*match m with
  | Return x -> begin
    assert (wp2p (theta m) h lt fs_r);
    assert (forall p. (theta m) h p ==> p [] x);
    introduce forall (p':hist_post h' a). (theta m) h' p' ==> p' lt' fs_r with begin
      introduce (theta m) h' p' ==> p' lt' fs_r with _. begin

        let p : hist_post h a = fun lt res -> p' (get_lt h h' lt) res in
        eliminate forall p. (theta m) h p ==> p lt fs_r with p;
        assert ((theta m) h' p');
        theta_monotonic_hist m;
        //hist_wp_monotonic' (theta m);
        assert (p lt fs_r);
        assert (p' (get_lt h h' lt) fs_r);
        //assert ((get_lt h h' lt) == lt');

        admit ()
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
  end*)*)







(*let theta_history_independence' #a (m:io a) (h h':history) (lt:local_trace h) (fs_r:a) (st:steps e e' h lt) :
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
  end*)*)

let theta_monotonic_hist'' #a #e #e' #h #lt (m:io a) (st:steps e e' h lt) :
  Lemma (forall h h' (p':hist_post h' a). theta m h' p' ==> theta m h (fun lt res -> p' (construct_local_trace st h') res)) =
  match m with
  | Return x -> begin
    introduce forall h h' p'. theta m h' p' ==> theta m h (fun lt res -> p' (construct_local_trace st h') res) with begin
    introduce _ ==> _ with _. begin
      assert (theta m h' p' == p' [] x);
      assert (theta m h (fun lt res -> p' (construct_local_trace st h') res) == p' (construct_local_trace st h') x);
      assume (p' [] x ==> p' (construct_local_trace st h') x)
      end
    end
    end
  | Call o args k -> begin
    introduce forall h h' p'. theta m h' p' ==> theta m h (fun lt res -> p' (construct_local_trace st h') res) with begin
    introduce theta m h' p' ==> theta m h (fun lt res -> p' (construct_local_trace st h') res) with _. begin
      assert (theta (Call o args k) == hist_bind (op_wp o args) (fun r -> theta (k r))) by (FStar.Tactics.compute ());
      assert (hist_bind (op_wp o args) (fun r -> theta (k r)) h' p' == (op_wp o args) h' (hist_post_bind h' (fun r -> theta (k r)) p')) by (FStar.Tactics.compute ());
      assert ((op_wp o args) h' (hist_post_bind h' (fun r -> theta (k r)) p') == to_hist (fun h -> io_pre h o args) (fun h res lt -> io_post h o args res /\ lt == [op_to_ev o args res]) h' (hist_post_bind h' (fun r -> theta (k r)) p')) by (FStar.Tactics.compute ());
      assert ((to_hist (fun h -> io_pre h o args) (fun h res lt -> io_post h o args res /\ lt == [op_to_ev o args res])) == (fun h p -> io_pre h o args /\ (forall (lt:local_trace h) (r:io_res o args). (io_post h o args r /\ lt == [op_to_ev o args r]) ==> p lt r))) by (FStar.Tactics.compute ());
      assert ((to_hist (fun h -> io_pre h o args) (fun h res lt -> io_post h o args res /\ lt == [op_to_ev o args res]) h' (hist_post_bind h' (fun r -> theta (k r)) p')) == (fun h p -> io_pre h o args /\ (forall (lt:local_trace h) (r:io_res o args). (io_post h o args r /\ lt == [op_to_ev o args r]) ==> p lt r)) h' (hist_post_bind h' (fun r -> theta (k r)) p')) by (FStar.Tactics.compute ());
      assert ((fun h p -> io_pre h o args /\ (forall (lt:local_trace h) (r:io_res o args). (io_post h o args r /\ lt == [op_to_ev o args r]) ==> p lt r)) h' (hist_post_bind h' (fun r -> theta (k r)) p') == (io_pre h' o args /\ (forall lt (r:io_res o args). (io_post h' o args r /\ lt == [op_to_ev o args r]) ==> (hist_post_bind h' (fun r -> theta (k r)) p') lt r))) by (FStar.Tactics.compute ());
       assert ((io_pre h' o args /\ (forall lt (r:io_res o args). (io_post h' o args r /\ lt == [op_to_ev o args r]) ==> (hist_post_bind h' (fun r -> theta (k r)) p') lt r)) == (forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> (hist_post_bind h' (fun r -> theta (k r)) p') lt r)) by (FStar.Tactics.compute ());
       assert ((forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> (hist_post_bind h' (fun r -> theta (k r)) p') lt r) == (forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h'++lt) (hist_post_shift h' p' lt))) by (FStar.Tactics.compute ());
       assert ((forall (lt:local_trace h'). (hist_post_shift h' p' lt) == (fun (lt':local_trace (h'++lt)) r -> p' (lt @ lt') r))) by (FStar.Tactics.compute ());
       assert ((forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h'++lt) (hist_post_shift h' p' lt)) == (forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h'++lt) (fun (lt':local_trace (h'++lt)) r -> p' (lt @ lt') r))) by (FStar.Tactics.compute ());
       assume ((theta m h' p') == (forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h'++lt) (fun (lt':local_trace (h'++lt)) r -> p' (lt @ lt') r))); //by (FStar.Tactics.compute ());
       assume ((theta m h (fun lt res -> p' (construct_local_trace st h') res)) == (forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h++lt) (fun (lt':local_trace (h++lt)) r -> p' (construct_local_trace st h') r)));
       introduce forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h++lt) (fun (lt':local_trace (h++lt)) r -> p' (construct_local_trace st h') r) with begin
         introduce _ ==> _ with _. begin
           assert (lt == [op_to_ev o args r]);
           let _ : io a = (k r) in
           //let _ : steps e e' h lt = st in
           //theta_monotonic_hist #a #e #e'
           admit ()
         end
       end
       //assert ((forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h'++lt) (hist_post_shift h' p' lt)) == (forall lt (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h'++lt) (fun lt' (r:io_res o args) -> p' (lt @ lt') r))) by (FStar.Tactics.compute ());
      //admit ()
    end
    end
    end

let theta_history_independence' #a #e #e' (m:io a) (h h':history) (lt:local_trace h) (lt':local_trace h') (fs_r:a) (st':steps e e' h' lt') (st:steps e e' h lt) :
  Lemma (requires wp2p (theta m) h (construct_local_trace st' h) fs_r)
        (ensures wp2p (theta m) h' (construct_local_trace st h') fs_r) =
  introduce forall (p':hist_post h' a). theta m h' p' ==> p' (construct_local_trace st h') fs_r with begin
    introduce _ ==> _ with _. begin
      theta_monotonic_hist m st;
      eliminate forall h h' p'. theta m h' p' ==> theta m h (fun lt res -> p' (construct_local_trace st h') res) with h h' p';
      assert (forall (p:hist_post h a). theta m h p ==> p (construct_local_trace st' h) fs_r);
      eliminate forall (p:hist_post h a). theta m h p ==> p (construct_local_trace st' h) fs_r with (fun lt res -> p' (construct_local_trace st h') res);
      assert (p' (construct_local_trace st h') fs_r)
    end
  end*)
