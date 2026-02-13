module IO

(** we only have bools in STLC right now **)
open Trace

open FStar.Tactics.V1

noeq
type io (a:Type u#a) : Type u#a =
| Call : o:io_ops -> args:io_args o -> (io_res o args -> io a) -> io a
| Return : a -> io a

let io_return (#a:Type) (x:a) : io a =
  Return x

let extract_v_from_io_return (#a:Type) (m:(io a){exists x. m == io_return x}) : (x:a{io_return x == m}) = admit ()

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

let rec theta_monad_morphism_bind m k =
  match m with
  | Return _ -> ()
  | Call o arg m' -> 
    calc (hist_equiv) {
      theta (io_bind (Call o arg m') k);
      `hist_equiv` { _ by (compute ()) }
      theta (Call o arg (fun x -> io_bind (m' x) k));
      `hist_equiv` { _ by (norm [delta_once [`%theta]; iota]) }
      hist_bind (op_wp o arg) (fun r -> theta (io_bind (m' r) k));
      `hist_equiv` { 
        introduce forall r. theta (io_bind (m' r) k) `hist_equiv` hist_bind (theta (m' r)) (fun x -> theta (k x)) with begin
          theta_monad_morphism_bind (m' r) k
        end;
        lem_hist_bind_equiv (op_wp o arg) (op_wp o arg) (fun r -> theta (io_bind (m' r) k)) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k x)))
       }
      hist_bind (op_wp o arg) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k x)));
      `hist_equiv` { lemma_hist_bind_associativity (op_wp o arg) (fun r -> theta (m' r)) (fun x -> theta (k x)) }
      hist_bind (hist_bind (op_wp o arg) (fun r -> theta (m' r))) (fun x -> theta (k x));
      `hist_equiv` {
        assert (hist_equiv
          (hist_bind (theta (Call o arg m')) (fun x -> theta (k x))) 
          (hist_bind (hist_bind (op_wp o arg) (fun r -> theta (m' r))) (fun x -> theta (k x)))
        ) by (norm [delta_once [`%theta]; zeta; iota]; 
          apply_lemma (`lem_hist_equiv_reflexive)) }
      hist_bind (theta (Call o arg m')) (fun x -> theta (k x));
    }

let io_bind_equivalence (#a #b:Type) (k k':a -> io b) (m:io a) :
  Lemma (requires forall x. k x == k' x)
        (ensures theta (io_bind m k) `hist_equiv` theta (io_bind m k')) =
  match m with
  | Return _ -> ()
  | Call o arg m' ->
    calc (hist_equiv) {
      theta (io_bind (Call o arg m') k);
      `hist_equiv` { theta_monad_morphism_bind (Call o arg m') k }
      hist_bind (theta (Call o arg m')) (fun x -> theta (k x));
      `hist_equiv` { _ by (norm [delta_once [`%theta]; zeta;iota]) }
      hist_bind (hist_bind (op_wp o arg) (fun r -> theta (m' r))) (fun x -> theta (k x));
      `hist_equiv` { lemma_hist_bind_associativity (op_wp o arg) (fun r -> theta (m' r)) (fun x -> theta (k x)) }
      hist_bind (op_wp o arg) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k x)));
      `hist_equiv` {
        lem_hist_bind_equiv (op_wp o arg) (op_wp o arg) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k x))) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k' x)))
      }
      hist_bind (op_wp o arg) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k' x)));
      `hist_equiv` { lemma_hist_bind_associativity (op_wp o arg) (fun r -> theta (m' r)) (fun x -> theta (k' x)) }
      hist_bind (hist_bind (op_wp o arg) (fun r -> theta (m' r))) (fun x -> theta (k' x));
      `hist_equiv` {
        assert (hist_equiv
          (hist_bind (theta (Call o arg m')) (fun x -> theta (k' x))) 
          (hist_bind (hist_bind (op_wp o arg) (fun r -> theta (m' r))) (fun x -> theta (k' x)))
        ) by (norm [delta_once [`%theta]; zeta; iota]; 
          apply_lemma (`lem_hist_equiv_reflexive)) 
       }
      hist_bind (theta (Call o arg m')) (fun x -> theta (k' x));
      `hist_equiv` { theta_monad_morphism_bind m k' }
      theta (io_bind (Call o arg m') k');
    }

let wp2p_theta_bind m k =
  theta_monad_morphism_bind m k

let lem_theta_open arg res h =
  introduce forall (p:hist_post h (io_res OOpen arg)). (theta (openfile arg)) h p ==> p (ev_lt (EvOpen arg res)) res with begin
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
  assert (thetaP (read arg) h (ev_lt (EvRead arg res)) res) by (compute ())

let lem_theta_write arg res h =
  assert (thetaP (write arg) h (ev_lt (EvWrite arg res)) res) by (compute ())

let lem_theta_close arg res h =
  assert (thetaP (close arg) h (ev_lt (EvClose arg res)) res) by (compute ())

(*let rec destruct_fs_beh_m #t1 #t2 (m:io t1) (w:t1 -> hist t2) (h:history) (lt:local_trace h) (fs_r:t2) :
  Lemma (requires forall p. hist_bind (theta m) w h p ==> p lt fs_r)
        (ensures exists (lt1:local_trace h) (fs_m:t1). forall p. theta m h p ==> p lt1 fs_m) =
  match m with
  | Return x -> ()
  | Call o args k -> begin
    match lt with
    | [] -> admit ()
    | ev::tl -> begin
      let r : io_res o (magic ()) = magic () in

       destruct_fs_beh_m (k r) w (h++[ev]) tl fs_r;
       admit ()

   end
  end

let destruct_fs_beh_m #t1 #t2 (m:io t1) (k:t1 -> io t2) (h:history) (lt:local_trace h) (fs_r:t2) :
  Lemma (requires thetaP (io_bind m k) h lt fs_r)
        (ensures exists (lt1:local_trace h) (fs_m:t1). thetaP m h lt1 fs_m) =
  wp2p_theta_bind m k;
  assert (wp2p (hist_bind (theta m) (fun x -> theta (k x))) h lt fs_r);
  assert (forall p. hist_bind (theta m) (fun x -> theta (k x)) h p ==> p lt fs_r);
  assert (forall p. (theta m) h (fun lt r -> theta (k r) (fun lt' r' -> p (lt@lt') r')) ==> p lt fs_r);
  assert (theta m h (fun lt r -> True));
   introduce exists (lt1:local_trace h) (fs_m:t1). forall p. theta m h p ==> p lt1 fs_m with _ _
  //assert (forall p. (theta (io_bind m k)) h p ==> p lt fs_m);

#push-options "--split_queries always"
let rec destruct_fs_beh' #t1 #t2 (m:io t1) (k:t1 -> io t2) (h:history) (lt:local_trace h) (fs_r:t2) :
  //Pure ((lt1:local_trace h & local_trace (h++lt1)) * t1)
  Lemma
    (requires thetaP (io_bind m k) h lt fs_r)
    (*(ensures fun ((| lt1, lt2 |), fs_m) ->
      lt == (lt1@lt2) /\
      thetaP m h lt1 fs_m /\
      thetaP (k fs_m) (h++lt1) lt2 fs_r)*)
    (ensures exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m:t1).
      lt == (lt1@lt2) /\
      thetaP m h lt1 fs_m /\
      thetaP (k fs_m) (h++lt1) lt2 fs_r)
    (decreases m) =
  match m with
  | Return x -> begin
    admit ()
    end
  | Call o args fnc -> begin
    match lt with
    | [] -> admit ()
    | ev::tl -> begin
      match o with
      | ORead -> begin
        assert (thetaP (io_bind m k) h lt fs_r == wp2p (theta (io_bind m k)) h lt fs_r);
        assert (wp2p (theta (io_bind m k)) h lt fs_r <==> forall p. (theta (io_bind m k)) h p ==> p lt fs_r);
        assert (forall p. (theta (Call ORead args (fun i -> io_bind #t1 #t2 (fnc i) k)) h p ==> p (ev::tl) fs_r));
        assert (forall p. hist_bind (op_wp ORead args) (fun r -> theta (io_bind #t1 #t2 (fnc r) k)) h p ==> p (ev::tl) fs_r);
        let p : hist_post h t2 = fun lt res -> exists res' lt'. lt == ((EvRead args res')::lt') in
        assert (hist_bind (op_wp ORead args) (fun r -> theta (io_bind #t1 #t2 (fnc r) k)) h p ==> p (ev::tl) fs_r);
        assert (hist_bind (op_wp ORead args) (fun r -> theta (io_bind #t1 #t2 (fnc r) k)) h p == (op_wp ORead args) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (fnc r) k)) p)) by (FStar.Tactics.compute ());
        assert ((op_wp ORead args) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (fnc r) k)) p) == (to_hist (fun h -> io_pre h ORead args) (fun h res lt -> io_post h ORead args res /\ lt == [op_to_ev ORead args res])) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (fnc r) k)) p)) by (FStar.Tactics.compute ());
        //assert ((to_hist (fun h -> io_pre h ORead args) (fun h res lt -> io_post h ORead args res /\ lt == [op_to_ev ORead args res])) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (fnc r) k)) p) ==
        assert (io_pre h ORead args);
        //***assert (forall lt r. io_post h ORead args r /\ lt == [op_to_ev ORead args r] ==> (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (fnc r) k)) p) lt r);
        assume (forall lt r. io_post h ORead args r /\ lt == [op_to_ev ORead args r] ==> theta (io_bind #t1 #t2 (fnc r) k) (h++lt) (fun lt' r -> p (lt @ lt') r));
        assert (p (ev::tl) fs_r);
        //assert (lt == ([EvRead args fs_r]@lt2));
      //thetaP m h lt1 fs_m /\
      //thetaP (k fs_m) (h++lt1) lt2 fs_r
        admit ()
        end
      | OWrite -> admit ()
      | OOpen -> admit ()
      | OClose -> admit ()
      end
    end
#pop-options*)

(*let theta_lemma #t1 #t2 (args:io_args ORead) (cont_m:io_res ORead args -> io t1) (k:t1 -> io t2) (h:history) (p:hist_post h t2):
  Lemma
    (requires theta (io_bind (Call ORead args cont_m) k) h p)
    (ensures forall (lt':local_trace h) (r':io_res ORead args). io_pre h ORead args /\ (io_post h ORead args r' /\ lt' == [op_to_ev ORead args r']) ==> theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r'')) = admit ()*)// this is by definition

(*let test #t1 #t2 (args:io_args ORead) (res:io_res ORead args) (cont_m:io_res ORead args -> io t1) (k:t1 -> io t2) (h:history) (tl:local_trace (h++[EvRead args res])) (fs_r:t2) (p:hist_post h t2) :
  Lemma (requires (theta (io_bind (Call ORead args cont_m) k) h p ==> p ([EvRead args res]@tl) fs_r) /\ theta (io_bind (Call ORead args cont_m) k) h p)
        (ensures (theta (io_bind (cont_m res) k) (h++[EvRead args res]) (fun (lt'':local_trace (h++[EvRead args res])) (r'':t2) -> p ([EvRead args res] @ lt'') r'') ==> (fun lt'' r'' -> p ([EvRead args res] @ lt'') r'') tl fs_r)) = ()

let test2 #t1 #t2 (o:io_ops) (args:io_args o) (res:io_res o args) (cont_m:io_res o args -> io t1) (k:t1 -> io t2) (h:history) (tl:local_trace (h++[op_to_ev o args res])) (fs_r:t2) (p:hist_post h t2) :
  Lemma (requires (theta (io_bind (Call o args cont_m) k) h p) /\ p ([op_to_ev o args res]@tl) fs_r)
        (ensures (theta (io_bind (cont_m res) k) (h++[op_to_ev o args res]) (fun (lt'':local_trace (h++[op_to_ev o args res])) (r'':t2) -> p ([op_to_ev o args res] @ lt'') r'')) /\ (fun (lt'':local_trace (h++[op_to_ev o args res])) (r'':t2) -> p ([op_to_ev o args res] @ lt'') r'') tl fs_r) =
  assert (theta (io_bind (Call o args cont_m) k) h p);
  assert (theta (Call o args (fun (i:io_res o args) -> io_bind #t1 #t2 (cont_m i) k)) h p);
  assert (hist_bind (op_wp o args) (fun r -> theta ((fun i -> io_bind #t1 #t2 (cont_m i) k) r)) h p);
  assert (hist_bind (op_wp o args) (fun r -> theta (io_bind #t1 #t2 (cont_m r) k)) h p);
  assert ((op_wp o args) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (cont_m r) k)) p));
  assert ((op_wp o args) h (fun lt_ r_ -> theta (io_bind #t1 #t2 (cont_m r_) k) (h++lt_) (hist_post_shift h p lt_)));
  assert ((op_wp o args) h (fun lt_ r_ -> theta (io_bind #t1 #t2 (cont_m r_) k) (h++lt_) (fun lt_' r_' -> p (lt_ @ lt_') r_')));
  assert ((op_wp o args) == (to_hist (fun h -> io_pre h o args) (fun h res' lt' -> io_post h o args res' /\ lt' == [op_to_ev o args res']))) by (FStar.Tactics.compute ());
  assert ((to_hist (fun h -> io_pre h o args) (fun h res' lt' -> io_post h o args res' /\ lt' == [op_to_ev o args res'])) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (cont_m r) k)) p) <==> (io_pre h o args /\ (forall (lt':local_trace h) (r':io_res o args). (io_post h o args r' /\ lt' == [op_to_ev o args r']) ==> theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r''))));
  assume ((to_hist (fun h -> io_pre h o args) (fun h res' lt' -> io_post h o args res' /\ lt' == [op_to_ev o args res'])) h (fun lt_ r_ -> theta (io_bind #t1 #t2 (cont_m r_) k) (h++lt_) (fun lt_' r_' -> p (lt_ @ lt_') r_')));
  assert (io_pre h o args /\ (forall (lt':local_trace h) (r':io_res o args). (io_post h o args r' /\ lt' == [op_to_ev o args r']) ==> theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r'')));
  assert (io_pre h o args);
  eliminate forall (lt':local_trace h) (r':io_res o args). (io_post h o args r' /\ lt' == [op_to_ev o args r']) ==> theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r'') with [op_to_ev o args res] res;
  assert ((io_post h o args res /\ [op_to_ev o args res] == [op_to_ev o args res]) ==> theta (io_bind #t1 #t2 (cont_m res) k) (h++[op_to_ev o args res]) (fun lt'' r'' -> p ([op_to_ev o args res] @ lt'') r''));
  ()

let test2' #t1 #t2 (o:io_ops) (args:io_args o) (cont_m:io_res o args -> io t1) (k:t1 -> io t2) (h:history) (ev:event_h h) (tl:local_trace (h++[ev])) (lt:local_trace h{lt == (ev::tl)}) (fs_r:t2) (p:hist_post h t2) :
  Lemma (requires (theta (io_bind (Call o args cont_m) k) h p) /\ p (ev::tl) fs_r)
        (ensures forall (res:io_res o args). (theta (io_bind (cont_m res) k) (h++[ev]) (fun (lt'':local_trace (h++[ev])) (r'':t2) -> p ([ev] @ lt'') r'')) /\ (fun (lt'':local_trace (h++[ev])) (r'':t2) -> p ([ev] @ lt'') r'') tl fs_r) =
  assert (theta (io_bind (Call o args cont_m) k) h p);
  assert (theta (Call o args (fun (i:io_res o args) -> io_bind #t1 #t2 (cont_m i) k)) h p);
  assert (hist_bind (op_wp o args) (fun r -> theta ((fun i -> io_bind #t1 #t2 (cont_m i) k) r)) h p);
  assert (hist_bind (op_wp o args) (fun r -> theta (io_bind #t1 #t2 (cont_m r) k)) h p);
  assert ((op_wp o args) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (cont_m r) k)) p));
  assert ((op_wp o args) h (fun lt_ r_ -> theta (io_bind #t1 #t2 (cont_m r_) k) (h++lt_) (hist_post_shift h p lt_)));
  assert ((op_wp o args) h (fun lt_ r_ -> theta (io_bind #t1 #t2 (cont_m r_) k) (h++lt_) (fun lt_' r_' -> p (lt_ @ lt_') r_')));
  assert ((op_wp o args) == (to_hist (fun h -> io_pre h o args) (fun h res' lt' -> io_post h o args res' /\ lt' == [op_to_ev o args res']))) by (FStar.Tactics.compute ());
  assert ((to_hist (fun h -> io_pre h o args) (fun h res' lt' -> io_post h o args res' /\ lt' == [op_to_ev o args res'])) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (cont_m r) k)) p) <==> (io_pre h o args /\ (forall (lt':local_trace h) (r':io_res o args). (io_post h o args r' /\ lt' == [op_to_ev o args r']) ==> theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r''))));
  assume ((to_hist (fun h -> io_pre h o args) (fun h res' lt' -> io_post h o args res' /\ lt' == [op_to_ev o args res'])) h (fun lt_ r_ -> theta (io_bind #t1 #t2 (cont_m r_) k) (h++lt_) (fun lt_' r_' -> p (lt_ @ lt_') r_')));
  assert (io_pre h o args /\ (forall (lt':local_trace h) (r':io_res o args). (io_post h o args r' /\ lt' == [op_to_ev o args r']) ==> theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r'')));
  assert (io_pre h o args);
  introduce forall (res:io_res o args). (theta (io_bind (cont_m res) k) (h++[ev]) (fun (lt'':local_trace (h++[ev])) (r'':t2) -> p ([ev] @ lt'') r'')) /\ (fun (lt'':local_trace (h++[ev])) (r'':t2) -> p ([ev] @ lt'') r'') tl fs_r with begin
      eliminate forall (lt':local_trace h) (r':io_res o args). (io_post h o args r' /\ lt' == [op_to_ev o args r']) ==> theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r'') with [ev] res;
      //assert ((io_post h o args res /\ [ev] == [op_to_ev o args res]) <==> theta (io_bind #t1 #t2 (cont_m res) k) (h++[ev]) (fun lt'' r'' -> p ([ev] @ lt'') r''));
      assume ([ev] == [op_to_ev o args res]);
      ()
    end

let testing_something #t1 #t2 (m:io t1) (k:t1 -> io t2) (h:history) (lt:local_trace h) (fs_r:t2) (p:hist_post h t2) :
  Lemma (ensures (theta (io_bind m k) h p ==> p lt fs_r) <==> (theta (io_bind m k) h (hist_post_bind (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r')) (fun (lt':local_trace h) (r:t1) -> (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r'))) ==> (hist_post_bind (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r')) (fun (lt':local_trace h) (r:t1) -> (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r'))) lt fs_r)) = admit ()

let more_testing #t1 #t2 (m:io t1) (k:t1 -> io t2) (h:history) (p:hist_post h t1) (fs_r:t2) :
  Lemma (requires theta m h p) // p lta a /\ lta@ltb == lt /\ k_ lta a ltb b
        (ensures theta (io_bind m k) h (hist_post_bind p (fun (lt:local_trace h) (r:t1) -> (fun (lt':local_trace (h++lt)) (r':t2) -> r' == fs_r)))) = admit ()

let more_testing' #t1 #t2 (m:io t1) (k:t1 -> io t2) (h:history) (lt:local_trace h) (fs_r:t2) :
  Lemma (requires forall (p:hist_post h t2). theta m h (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r')) ==> p lt fs_r)
        (ensures forall (p:hist_post h t2). theta (io_bind m k) h (hist_post_bind (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r')) (fun (lt:local_trace h) (r:t1) -> (fun (lt':local_trace (h++lt)) (r':t2) -> r' == fs_r))) ==> (hist_post_bind (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r')) (fun (lt:local_trace h) (r:t1) -> (fun (lt':local_trace (h++lt)) (r':t2) -> r' == fs_r))) lt fs_r) = admit ()

let final_test #t1 #t2 (m:io t1) (k:t1 -> io t2) (h:history) (lt:local_trace h) (fs_r:t2) :
  Lemma (requires forall (p:hist_post h t2). theta (io_bind m k) h p ==> p lt fs_r)
        (ensures forall (p':hist_post h t1). theta m h p' ==> (exists (fs_r_m:t1) (lt1:local_trace h) (lt2:local_trace (h++lt1)). p' lt1 fs_r_m /\ (lt1@lt2 == lt))) =
  introduce forall p'. theta m h p' ==> (exists (fs_r_m:t1) (lt1:local_trace h) (lt2:local_trace (h++lt1)). p' lt1 fs_r_m /\ (lt1@lt2 == lt)) with begin
    introduce _ ==> _ with _. begin
      more_testing m k h p' fs_r;
      assert ((hist_post_bind p' (fun (lt:local_trace h) (r:t1) -> (fun (lt':local_trace (h++lt)) (r':t2) -> r' == fs_r))) lt fs_r);
      assert ((fun (lt:local_trace h) (r:t2) -> exists (fs_r_m:t1) (lt1:local_trace h) (lt2:local_trace (h++lt1)). p' lt1 fs_r_m /\ lt1@lt2 == lt /\ r == fs_r) lt fs_r);
      ()
    end
  end

let uniqueness_of_result #t1 (m:io t1) (h:history) (p:hist_post h t1) :
  Lemma (forall (lt lt':local_trace h) (r r':t1). (p lt r /\ p lt' r') ==> ((lt == lt') /\ (r' == r))) = admit ()

let most_testing #t1 (m:io t1) (h:history) (lt1':local_trace h) (fs_r_m':t1) :
  Lemma (requires forall (p':hist_post h t1). theta m h p' ==> (exists (fs_r_m:t1) (lt1:local_trace h) (lt2:local_trace (h++lt1)). p' lt1 fs_r_m))
        (ensures forall (p':hist_post h t1). theta m h p' ==> p' lt1' fs_r_m') =
 introduce forall (p':hist_post h t1). theta m h p' ==> p' lt1' fs_r_m' with begin
   introduce _ ==> _ with _. begin
     eliminate forall (p':hist_post h t1). theta m h p' ==> (exists (fs_r_m:t1) (lt1:local_trace h) (lt2:local_trace (h++lt1)). p' lt1 fs_r_m) with p';
     uniqueness_of_result m h p';
     admit ()
   end
 end

#push-options "--split_queries always"
let rec test_m #t1 #t2 (m:io t1) (k:t1 -> io t2) (h:history) (lt:local_trace h) (fs_r:t2) (p:hist_post h t2) :
  Pure (t1 * (lt1:local_trace h & local_trace (h++lt1)))
    (requires theta (io_bind m k) h p /\ p lt fs_r)
    (ensures fun (fs_r_m, (| lt1, lt2 |)) ->
      lt == (lt1@lt2) /\
      theta (k fs_r_m) (h++lt1) (fun (lt'':local_trace (h++lt1)) (r'':t2) -> p (lt1@lt'') r'') ==> (fun lt'' r'' -> p (lt1@lt'') r'') lt2 fs_r)
    (decreases m) =
    theta_monad_morphism_bind m k;
    assert (theta (io_bind m k) `hist_equiv` hist_bind (theta m) (fun x -> theta (k x)));
    assert ((theta (io_bind m k)) h p <==> (hist_bind (theta m) (fun x -> theta (k x))) h p);
    assert (theta (io_bind m k) h p);
    assert ((hist_bind (theta m) (fun x -> theta (k x))) h p);
    assert ((theta m) h (hist_post_bind' (fun x -> theta (k x)) p));
    assert ((theta m) h (fun lt' r -> theta (k r) (h++lt') (hist_post_shift h p lt')));
    assert ((theta m) h (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r')));
    assert (p lt fs_r);
    let _ : hist_post h t2 = p in
    let m_ : hist_post h t1 = (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r')) in
    let k_ : (lt:local_trace h -> t1 -> hist_post (h++lt) t2) = fun (lt':local_trace h) (r:t1) -> (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r') in
    let p1 : hist_post h t2 = hist_post_bind m_ k_ in
    assert (hist_post_bind m_ k_ == (fun (lt:local_trace h) (b:t2) -> exists (a:t1) (lta:local_trace h) (ltb:local_trace (h++lta)). m_ lta a /\ lta@ltb == lt /\ k_ lta a ltb b)) by (FStar.Tactics.compute ());
    introduce forall lt r. p1 lt r ==> p lt r with begin
      introduce _ ==> _ with _. begin
        ()
      end
    end;
    assert (p1 `hist_post_ord` p);
    assert (hist_wp_monotonic (theta (io_bind m k)));
    assert ((theta (io_bind m k)) h p1 ==> (theta (io_bind m k)) h p);
    //assert ((theta (io_bind m k)) h p1);
    (*assert (p1 lt fs_r);
    assert (exists (a:t1) (lta:local_trace h) (ltb:local_trace (h++lta)). m_ lta a /\ lta@ltb == lt /\ k_ lta a ltb fs_r);*)

    admit ()
#pop-options
    (*match m with
    | Return x -> (x, (| [], lt |))
    | Call o args cont_m -> begin
      assert (theta (io_bind m k) h p);
      match lt with
      | [] -> admit () // should be false_elim ()
      | (ev::tl) -> begin
        assert (theta (io_bind (Call o args cont_m) k) h p /\ p (ev::tl) fs_r);
        assume (well_formed_local_trace (h++[ev]) tl);
        test2' o args cont_m k h ev tl (ev::tl) fs_r p;
        //eliminate forall (res:io_res o args). (theta (io_bind (cont_m res) k) (h++[ev]) (fun (lt'':local_trace (h++[ev])) (r'':t2) -> p ([ev] @ lt'') r'')) /\ (fun (lt'':local_trace (h++[ev])) (r'':t2) -> p ([ev] @ lt'') r'') tl fs_r
        //let (fs_r_m', (| lt1', lt2' |)) = test_m (cont_m_ res_) k (h++[op_to_ev o_ args_ res_]) tl fs_r (fun (lt'':local_trace (h++[op_to_ev o_ args_ res_])) (r'':t2) -> p ([op_to_ev o_ args_ res_] @ lt'') r'') in
        //(fs_r_m', (| ([op_to_ev o_ args_ res_]@lt1'), lt2' |))
        admit ()
        end
      end*)

let destruct_fs_beh_small #t1 #t2 (args:io_args ORead) (res:io_res ORead args) (cont_m:io_res ORead args -> io t1) (k:t1 -> io t2) (h:history) (tl:local_trace (h++[EvRead args res])) (fs_r:t2) :
  Lemma (requires thetaP (io_bind (Call ORead args cont_m) k) h ([EvRead args res]@tl) fs_r)
        (ensures thetaP (io_bind (cont_m res) k) (h++[EvRead args res]) tl fs_r) =
  assert (forall (p:hist_post h t2). theta (io_bind (Call ORead args cont_m) k) h p ==> p ([EvRead args res]@tl) fs_r);
  assert (forall (p:hist_post h t2). theta (Call ORead args (fun (i:io_res ORead args) -> io_bind #t1 #t2 (cont_m i) k)) h p ==> p ([EvRead args res]@tl) fs_r);
  assert (forall (p:hist_post h t2). hist_bind (op_wp ORead args) (fun r -> theta ((fun i -> io_bind #t1 #t2 (cont_m i) k) r)) h p ==> p ([EvRead args res]@tl) fs_r);
  assert (forall (p:hist_post h t2). hist_bind (op_wp ORead args) (fun r -> theta (io_bind #t1 #t2 (cont_m r) k)) h p ==> p ([EvRead args res]@tl) fs_r);
  assert (forall (p:hist_post h t2). (op_wp ORead args) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (cont_m r) k)) p) ==> p ([EvRead args res]@tl) fs_r);
  assert (forall (p:hist_post h t2). (to_hist (fun h -> io_pre h ORead args) (fun h res lt -> io_post h ORead args res /\ lt == [op_to_ev ORead args res])) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (cont_m r) k)) p) ==> p ([EvRead args res]@tl) fs_r);
  assert (forall (p:hist_post h t2). (to_hist (fun h -> io_pre h ORead args) (fun h res lt -> io_post h ORead args res /\ lt == [op_to_ev ORead args res])) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (cont_m r) k)) p) <==> (io_pre h ORead args /\ (forall (lt':local_trace h) (r':io_res ORead args). (io_post h ORead args r' /\ lt' == [op_to_ev ORead args r']) ==> theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r''))));
  assert (forall (p:hist_post h t2). (io_pre h ORead args /\ (forall (lt':local_trace h) (r':io_res ORead args). (io_post h ORead args r' /\ lt' == [op_to_ev ORead args r']) ==> theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r''))) ==> p ([EvRead args res]@tl) fs_r);
  introduce forall (p':hist_post (h++[EvRead args res]) t2). theta (io_bind (cont_m res) k) (h++[EvRead args res]) p' ==> p' tl fs_r with begin
    introduce _ ==> _ with _. begin
      let p : hist_post h t2 = fun (lt'':local_trace h) (r'':t2) -> exists (tl:local_trace (h++[EvRead args res])). lt'' == [EvRead args res]@tl /\ p' tl r'' in
      eliminate forall (p:hist_post h t2). (io_pre h ORead args /\ (forall (lt':local_trace h) (r':io_res ORead args). (io_post h ORead args r' /\ lt' == [op_to_ev ORead args r']) ==> theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r''))) ==> p ([EvRead args res]@tl) fs_r with p;
      assert ((io_pre h ORead args /\ (forall (lt':local_trace h) (r':io_res ORead args). (io_post h ORead args r' /\ lt' == [op_to_ev ORead args r']) ==> theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r''))) ==> p ([EvRead args res]@tl) fs_r);
      assert (io_pre h ORead args);
      introduce forall (lt':local_trace h) (r':io_res ORead args). (lt' == [op_to_ev ORead args r']) ==> theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r'') with begin
        introduce _ ==> _ with _. begin
          assume (theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r''))
          //admit ()
        end
      end
    end
  end

let destruct_fs_beh_ #t1 #t2 (m:io t1) (k:t1 -> io t2) (h:history) (lt:local_trace h) (fs_r:t2) :
  Lemma (requires thetaP (io_bind m k) h lt fs_r)
        (ensures exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m:t1).
          lt == (lt1@lt2) /\
          thetaP m h lt1 fs_m /\
          thetaP (k fs_m) (h++lt1) lt2 fs_r)
        (decreases m) =
  let p : hist_post h t2 = fun (lt:local_trace h) (fs_r:t2) -> exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m:t1). lt == (lt1@lt2) /\ thetaP m h lt1 fs_m /\ thetaP (k fs_m) (h++lt1) lt2 fs_r in
  assert (forall (p:hist_post h t2). theta (io_bind m k) h p ==> p lt fs_r);
  theta_monad_morphism_bind m k;
  eliminate forall (p:hist_post h t2). theta m h (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r')) ==> p lt fs_r with p;
  let _ : hist_post h t1 = (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m:t1). (lt'@lt'') == (lt1@lt2) /\ thetaP m h lt1 fs_m /\ thetaP (k fs_m) (h++lt1) lt2 r')) in
  let p' = hist_post_bind (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m:t1). (lt'@lt'') == (lt1@lt2) /\ thetaP m h lt1 fs_m /\ thetaP (k fs_m) (h++lt1) lt2 r')) (fun (lt':local_trace h) (r:t1) -> (fun (lt'':local_trace (h++lt')) (r':t2) -> exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m:t1). (lt'@lt'') == (lt1@lt2) /\ thetaP m h lt1 fs_m /\ thetaP (k fs_m) (h++lt1) lt2 r')) in
  assert (p' == (fun (lt:local_trace h) (b:t2) -> exists (a:t1) (lta:local_trace h) (ltb:local_trace (h++lta)). theta (k a) (h++lta) (fun (lt'':local_trace (h++lta)) (r':t2) -> exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m:t1). (lta@lt'') == (lt1@lt2) /\ thetaP m h lt1 fs_m /\ thetaP (k fs_m) (h++lt1) lt2 r') /\ lta@ltb == lt /\ exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m:t1). (lta@ltb) == (lt1@lt2) /\ thetaP m h lt1 fs_m /\ thetaP (k fs_m) (h++lt1) lt2 b)) by (FStar.Tactics.compute ());
  admit ()
  //assume (theta m h (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m:t1). (lt'@lt'') == (lt1@lt2) /\ thetaP m h lt1 fs_m /\ thetaP (k fs_m) (h++lt1) lt2 r')))
  //admit ()
  //assume (theta m h (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r')))
  //admit ()
  (*assert (forall p. theta (io_bind m k) h p ==> p lt fs_r);
  theta_monad_morphism_bind m k;
  assert (forall p. theta m h (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r')) ==> p lt fs_r);
  more_testing' m k h lt fs_r;
  assert (forall (p:hist_post h t2). theta (io_bind m k) h (hist_post_bind (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r')) (fun (lt:local_trace h) (r:t1) -> (fun (lt':local_trace (h++lt)) (r':t2) -> r' == fs_r))) ==> (hist_post_bind (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r')) (fun (lt:local_trace h) (r:t1) -> (fun (lt':local_trace (h++lt)) (r':t2) -> r' == fs_r))) lt fs_r);*)

  //assert (forall p. theta (io_bind m k) h (hist_post_bind (fun (lt':local_trace h) (r:t1) -> theta (k r) (h++lt') (fun (lt'':local_trace (h++lt')) (r':t2) -> p (lt' @ lt'') r')) (fun (lt:local_trace h) (r:t1) -> (fun (lt':local_trace (h++lt)) (r':t2) -> r' == fs_r))) ==> p lt fs_r);
  //admit ()


  (*match m with
  | Return x -> admit ()
  | Call o args func -> begin
    match o with
    | ORead -> begin
    assert (thetaP (io_bind (Call o args func) k) h lt fs_r);
    assert (wp2p (theta (io_bind (Call o args func) k)) h lt fs_r);
    assert (wp2p (theta (Call o args (fun i -> io_bind #t1 #t2 (func i) k))) h lt fs_r);
    assert (forall p. (theta (io_bind m k)) h p ==> p lt fs_r);
    assert (forall (p:hist_post h t2). (theta (Call o args (fun (i:io_res o args) -> io_bind #t1 #t2 (func i) k))) h p ==> p lt fs_r);
    assert (forall p. hist_bind (op_wp o args) (fun r -> theta ((fun i -> io_bind #t1 #t2 (func i) k) r)) h p ==> p lt fs_r);
    assert (forall p. hist_bind (op_wp o args) (fun r -> theta (io_bind #t1 #t2 (func r) k)) h p ==> p lt fs_r);
    assert (forall p. (op_wp o args) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (func r) k)) p) ==> p lt fs_r);
    assert (forall p. (to_hist (fun h -> io_pre h o args) (fun h res lt -> io_post h o args res /\ lt == [op_to_ev o args res])) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (func r) k)) p) ==> p lt fs_r);
    assert (forall p. (to_hist (fun h -> io_pre h o args) (fun h res lt -> io_post h o args res /\ lt == [op_to_ev o args res])) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (func r) k)) p) <==> (io_pre h o args /\ (forall (lt':local_trace h) (r':io_res o args). (io_post h o args r' /\ lt' == [op_to_ev o args r']) ==> theta (io_bind #t1 #t2 (func r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r''))));
    assert (forall (p:hist_post h t2). (io_pre h o args /\ (forall (lt':local_trace h) (r':io_res o args). (io_post h o args r' /\ lt' == [op_to_ev o args r']) ==> theta (io_bind #t1 #t2 (func r') k) (h++lt') (fun (lt'':local_trace (h++lt')) (r'':t2) -> p (lt' @ lt'') r''))) ==> p lt fs_r);
    match lt with
    | [] -> begin
    assert (forall (p:hist_post h t2). (forall (lt':local_trace h) (r':io_res o args). (io_post h o args r' /\ lt' == [op_to_ev o args r']) ==> theta (io_bind #t1 #t2 (func r') k) (h++lt') (fun (lt'':local_trace (h++lt')) (r'':t2) -> p (lt' @ lt'') r'')) ==> p lt fs_r);
    let p : hist_post h t2 = fun (lt_:local_trace h) (fs_r_:t2) -> exists (lt':local_trace h) (lt'':local_trace (h++lt')) (r'':t2). (lt_ == (lt' @ lt'')) /\ (fs_r_ == r'') in
    assert (forall (r':io_res o args). (io_post h o args r' /\ [] == [op_to_ev o args r']) ==> theta (io_bind #t1 #t2 (func r') k) (h++[]) (fun (lt'':local_trace (h++[])) (r'':t2) -> p ([] @ lt'') r'') ==> p lt fs_r);
    admit ()
    end
    | ev::tl -> begin
    assert (forall (p:hist_post h t2). (forall (lt':local_trace h) (r':io_res o args). (io_post h o args r' /\ lt' == [op_to_ev o args r']) ==> theta (io_bind #t1 #t2 (func r') k) (h++lt') (fun (lt'':local_trace (h++lt')) (r'':t2) -> p (lt' @ lt'') r'')) ==> p lt fs_r);
    let p : hist_post h t2 = fun (lt_:local_trace h) (fs_r_:t2) -> exists (lt':local_trace h) (lt'':local_trace (h++lt')) (r'':t2). (lt_ == (lt' @ lt'')) /\ (fs_r_ == r'') in
    assert (theta (io_bind m k) h p ==> p lt fs_r);
    assume ((forall (lt':local_trace h) (r':io_res o args). (io_post h o args r' /\ lt' == [op_to_ev o args r']) ==> theta (io_bind #t1 #t2 (func r') k) (h++lt') (fun (lt'':local_trace (h++lt')) (r'':t2) -> p (lt' @ lt'') r'')) ==> p lt fs_r); //by (FStar.Tactics.compute ());
    introduce forall (lt':local_trace h) (r':io_res o args). (io_post h o args r' /\ lt' == [op_to_ev o args r']) ==> theta (io_bind #t1 #t2 (func r') k) (h++lt') (fun (lt'':local_trace (h++lt')) (r'':t2) -> p (lt' @ lt'') r'') with begin
      introduce _ ==> _ with _. begin
        assume (theta (io_bind #t1 #t2 (func r') k) (h++lt') (fun (lt'':local_trace (h++lt')) (r'':t2) -> p (lt' @ lt'') r''))
      end
    end;
    assert (p lt fs_r);
    let (| op_, a_, r_ |) = destruct_ev ev in

    admit ()
    end
    end
    | _ -> admit ()
    end


    theta_monad_morphism_bind m k;
    assert (forall (p:hist_post h t2). theta m h (fun (lt':local_trace h) (r':t1) -> theta (k r') (h++lt') (fun (lt'':local_trace (h++lt')) (r'':t2) -> p (lt' @ lt'') r'')) ==> p lt fs_r);


(*let theta_lemma #a #b (args:io_args ORead) (res:io_res ORead args) (func:io_res ORead args -> io a) (k:a -> io b) (h:history) (tl:local_trace ((EvRead args res)::h)) (fs_r:b) :
  Lemma
    (requires wp2p (theta (io_bind (Call ORead args func) k)) h ([EvRead args res]@tl) fs_r)
    (ensures wp2p (theta (k *)

let destruct_fs_beh_read #t1 #t2 (args:io_args ORead) (res:io_res ORead args) (cont_m:io_res ORead args -> io t1) (k:t1 -> io t2) (h:history) (tl:local_trace ((EvRead args res)::h)) (fs_r:t2) :
  Lemma (requires exists (p:hist_post h t2). theta (io_bind (Call ORead args cont_m) k) h p ==> p ([EvRead args res]@tl) fs_r)
        (ensures exists (p':hist_post ((EvRead args res)::h) t2). theta (io_bind (cont_m res) k) ((EvRead args res)::h) p' ==> p' tl fs_r) =
  eliminate exists (p:hist_post h t2). theta (io_bind (Call ORead args cont_m) k) h p ==> p ([EvRead args res]@tl) fs_r
  returns exists (p':hist_post ((EvRead args res)::h) t2). theta (io_bind (cont_m res) k) ((EvRead args res)::h) p' ==> p' tl fs_r with _. begin
    let p' : hist_post ((EvRead args res)::h) t2 = (fun (lt'':local_trace ((EvRead args res)::h)) (r'':t2) -> p ([EvRead args res]@lt'') r'') in
    assert (theta (io_bind (Call ORead args cont_m) k) h p ==> p ([EvRead args res]@tl) fs_r);
    assert (theta (Call ORead args (fun (i:io_res ORead args) -> io_bind #t1 #t2 (cont_m i) k)) h p ==> p ([EvRead args res]@tl) fs_r);
    assert (hist_bind (op_wp ORead args) (fun r -> theta ((fun i -> io_bind #t1 #t2 (cont_m i) k) r)) h p ==> p ([EvRead args res]@tl) fs_r);
    assert (hist_bind (op_wp ORead args) (fun r -> theta (io_bind #t1 #t2 (cont_m r) k)) h p ==> p ([EvRead args res]@tl) fs_r);
    assert ((op_wp ORead args) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (cont_m r) k)) p) ==> p ([EvRead args res]@tl) fs_r);
    assert ((to_hist (fun h -> io_pre h ORead args) (fun h res lt -> io_post h ORead args res /\ lt == [op_to_ev ORead args res])) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (cont_m r) k)) p) ==> p ([EvRead args res]@tl) fs_r);
    assert ((to_hist (fun h -> io_pre h ORead args) (fun h res lt -> io_post h ORead args res /\ lt == [op_to_ev ORead args res])) h (hist_post_bind' (fun r -> theta (io_bind #t1 #t2 (cont_m r) k)) p) <==> (io_pre h ORead args /\ (forall (lt':local_trace h) (r':io_res ORead args). (io_post h ORead args r' /\ lt' == [op_to_ev ORead args r']) ==> theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r''))));
      assert ((io_pre h ORead args /\ (forall (lt':local_trace h) (r':io_res ORead args). (io_post h ORead args r' /\ lt' == [op_to_ev ORead args r']) ==> theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r''))) ==> p ([EvRead args res]@tl) fs_r);
    assert (p' tl fs_r == p ([EvRead args res]@tl) fs_r);
    introduce theta (io_bind (cont_m res) k) ((EvRead args res)::h) p' ==> p' tl fs_r with _. begin
      introduce forall (lt':local_trace h) (r':io_res ORead args). (io_post h ORead args r' /\ lt' == [op_to_ev ORead args r']) ==> theta (io_bind #t1 #t2 (cont_m r') k) (h++lt') (fun lt'' r'' -> p (lt' @ lt'') r'') with begin
        introduce _ ==> _ with _. begin
          admit ()
        end
      end
    end
  end
*)*)

let thetaP_shift_op_lt #t (o:io_ops) (args:io_args o) (k:io_res o args -> io t) (r:io_res o args) (h:history) (lt:local_trace h) 
  : Lemma 
      (requires (lt == [op_to_ev o args r]))
      (ensures (forall (lt':local_trace (h++lt)) fs_r . thetaP (k r) (h ++ lt) lt' fs_r ==> thetaP (Call o args k) h (lt@lt') fs_r)) 
  =
  introduce forall (lt':local_trace (h++lt)) fs_r . thetaP (k r) (h ++ lt) lt' fs_r ==> thetaP (Call o args k) h (lt@lt') fs_r with begin
    introduce thetaP (k r) (h ++ lt) lt' fs_r ==> thetaP (Call o args k) h (lt@lt') fs_r with _. begin
      introduce forall (p:hist_post h t). theta (Call o args k) h p ==> p (lt@lt') fs_r with begin
        introduce theta (Call o args k) h p ==> p (lt@lt') fs_r with _. begin
          assert (hist_bind (op_wp o args) (fun r -> theta (k r)) h p);
          assert (forall (lt:local_trace h) (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h++lt) (hist_post_shift h p lt)) by (
            binder_retype (nth_binder (-1));
              norm [delta_only [`%hist_bind;`%op_wp;`%to_hist;`%io_post;`%io_pre;`%hist_post_bind'];iota];
            trefl ());
          eliminate forall (lt:local_trace h) (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h++lt) (hist_post_shift h p lt)
            with lt r;
          eliminate forall (p':hist_post (h++lt) t). theta (k r) (h++lt) p' ==> p' lt' fs_r
            with (hist_post_shift h p lt)
        end
      end
    end
  end

#push-options "--split_queries always"
let rec theta_thetaP_in_post #t (m:io t) (h:history) : Lemma (theta m h (fun lt fs_r -> thetaP m h lt fs_r)) =
  match m with
  | Return x -> ()
  | Call o args k ->
      introduce forall (lt:local_trace h) (r:io_res o args). (lt == [op_to_ev o args r]) ==> theta (k r) (h ++ lt) (fun lt' fs_r' -> thetaP m h (lt@lt') fs_r') with begin
        introduce _ ==> _ with _. begin
          theta_thetaP_in_post (k r) (h ++ lt);
          assert (theta (k r) (h ++ lt) (fun lt' fs_r' -> thetaP (k r) (h ++ lt) lt' fs_r'));
          thetaP_shift_op_lt o args k r h lt;
          assert (theta (k r) (h ++ lt) (fun lt' fs_r' -> thetaP m h (lt@lt') fs_r'))
        end
      end;
      assert ((op_wp o args) h (fun lt fs_r -> theta (k fs_r) (h ++ lt) (fun lt' fs_r' -> thetaP m h (lt@lt') fs_r')))
#pop-options

unfold
let theta_io_bind_exists_post #t1 #t2 (m:io t1) (f:t1 -> io t2) (h:history) (lt:local_trace h) (fs_r:t2) =
  exists fs_m lt1 lt2 .
      lt = lt1 @ lt2 /\
      thetaP m h lt1 fs_m /\
      thetaP (f fs_m) (h ++ lt1) lt2 fs_r

#push-options "--z3rlimit 10000"
let rec theta_io_bind_exists #t1 #t2 (m:io t1) (f:t1 -> io t2) (h:history) : Lemma (theta (io_bind m f) h (theta_io_bind_exists_post m f h)) =
  match m with
  | Return x ->
      theta_thetaP_in_post (f x) h;
      assert (theta (f x) h (fun lt fs_r -> thetaP (f x) h lt fs_r));
      calc (hist_post_ord) {
        (fun lt fs_r -> thetaP (f x) h lt fs_r);
        `hist_post_ord` {}
        (fun lt fs_r -> exists lt2. lt = []@lt2 /\ thetaP (f x) h lt2 fs_r);
        `hist_post_ord` {}
        (fun lt fs_r -> exists lt2. lt = []@lt2 /\ (forall (p:hist_post h t1). p [] x ==> p [] x) /\ thetaP (f x) h lt2 fs_r);
        `hist_post_ord` {}
        (fun lt fs_r -> exists fs_m lt1 lt2. lt = []@lt2 /\ (forall (p:hist_post h t1). p [] x ==> p lt1 fs_m) /\ thetaP (f x) h lt2 fs_r /\ lt1 == [] /\ fs_m == x);
        `hist_post_ord` {}
        (fun lt fs_r -> exists fs_m lt1 lt2. lt = lt1@lt2 /\ thetaP (Return x) h lt1 fs_m /\ thetaP (f fs_m) (h++lt1) lt2 fs_r /\ lt1 == [] /\ fs_m == x);
        `hist_post_ord` {}
        (fun lt fs_r -> exists fs_m lt1 lt2. lt = lt1@lt2 /\ thetaP (Return x) h lt1 fs_m /\ thetaP (f fs_m) (h++lt1) lt2 fs_r);
      };
      assert (theta (f x) h (theta_io_bind_exists_post m f h))
  | Call o args k ->     
      introduce forall lt r. lt == [op_to_ev o args r] ==> theta (io_bind (k r) f) (h ++ lt) (fun lt' fs_r' -> theta_io_bind_exists_post m f h (lt @ lt') fs_r') with begin
        introduce _ ==> _ with _. begin
          theta_io_bind_exists (k r) f (h ++ lt);
          assert (theta (io_bind (k r) f) (h ++ lt) (fun lt' fs_r' -> theta_io_bind_exists_post (k r) f (h ++ lt) lt' fs_r'));
          introduce forall (lt':local_trace (h ++ lt)) fs_r' . theta_io_bind_exists_post (k r) f (h ++ lt) lt' fs_r' ==> theta_io_bind_exists_post m f h (lt @ lt') fs_r' with begin
            introduce _ ==> _ with _. begin
              eliminate exists fs_m lt1 lt2 .
                            lt' = lt1 @ lt2 /\
                            thetaP (k r) (h ++ lt) lt1 fs_m /\
                            thetaP (f fs_m) (h ++ lt ++ lt1) lt2 fs_r'
              returns theta_io_bind_exists_post m f h (lt @ lt') fs_r'
              with _. begin
                trans_history h lt lt1;
                introduce exists fs_m' lt1' lt2' .
                              lt @ lt' = lt1' @ lt2' /\
                              thetaP m h lt1' fs_m /\
                              thetaP (f fs_m) (h ++ lt1') lt2' fs_r'
                with fs_m (lt @ lt1) lt2
                and begin
                  thetaP_shift_op_lt o args k r h lt
                end
              end
            end
          end;
          assert (forall lt' r' . theta_io_bind_exists_post (k r) f (h ++ lt) lt' r' ==> theta_io_bind_exists_post m f h (lt @ lt') r');
          assert (theta_io_bind_exists_post (k r) f (h ++ lt) `hist_post_ord` (fun lt' r' -> theta_io_bind_exists_post m f h (lt @ lt') r'));
          assert (theta (io_bind (k r) f) (h ++ lt) (fun lt' r' -> theta_io_bind_exists_post m f h (lt @ lt') r'))
        end
      end;
      
      assert ((op_wp o args) h (fun lt r -> theta (io_bind (k r) f) (h ++ lt) (fun lt' r' -> theta_io_bind_exists_post m f h (lt @ lt') r')));
      assert (hist_bind (op_wp o args) (fun r -> theta (io_bind (k r) f)) h (theta_io_bind_exists_post m f h));
      assert (theta (io_bind (Call o args k) f) h (theta_io_bind_exists_post m f h))
#pop-options

let destruct_fs_beh #t1 #t2 (m:io t1) (k:t1 -> io t2) (h:history) (lt:local_trace h) (fs_r:t2) :
  Lemma
    (requires thetaP (io_bind m k) h lt fs_r) // forall p. theta (io_bind m k) h p ==> p lt fs_r
    (ensures exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m:t1).
      lt == (lt1@lt2) /\
      thetaP m h lt1 fs_m /\ // forall p. theta m h p ==> p lt1 fs_m
      thetaP (k fs_m) (h++lt1) lt2 fs_r) (* forall p. theta (k fs_m) (h++lt1) p ==> p lt2 fs_r *) =
    theta_io_bind_exists m k h




(* Thoughts with Danel

forall p. theta (io_bind m k) h p ==> p lt fs_r
forall q. theta m h q ==> q lt1 fs_m

Instantiate p with: exists lt'. lt == (lt1@lt') /\ q lt1 fs_m
Prove: theta (io_bind m k) h p

However:
1. we don't know the values lt1 and fs_m ahead of time
2. still need to prove: theta (io_bind m k) h p
*)
