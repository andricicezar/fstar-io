module IO

(** we only have bools in STLC right now **)
open Trace

open FStar.Tactics.V1

let theta = theta_unf

let unfold_theta #a :
  Lemma (theta #a == theta_unf #a)
  by (norm [delta_only [`%theta]])
= ()

let theta_monad_morphism_ret x =
  assert (theta (return x) == hist_return x) by (FStar.Tactics.compute ())

val theta_monad_morphism_bind_ (m:io 'a) (k:'a -> io 'b) :
  Lemma (theta_unf (io_bind m k) `hist_equiv` hist_bind (theta_unf m) (fun x -> theta_unf (k x)))
let rec theta_monad_morphism_bind_ m k =
  match m with
  | Return _ -> ()
  | Call o arg m' ->
    calc (hist_equiv) {
      theta_unf (io_bind (Call o arg m') k);
      `hist_equiv` { _ by (compute ()) }
      theta_unf (Call o arg (fun x -> io_bind (m' x) k));
      `hist_equiv` { _ by (norm [delta_once [`%theta_unf]; iota]) }
      hist_bind (op_wp o arg) (fun r -> theta_unf (io_bind (m' r) k));
      `hist_equiv` {
        introduce forall r. theta_unf (io_bind (m' r) k) `hist_equiv` hist_bind (theta_unf (m' r)) (fun x -> theta_unf (k x)) with begin
          theta_monad_morphism_bind_ (m' r) k
        end;
        lem_hist_bind_equiv (op_wp o arg) (op_wp o arg) (fun r -> theta_unf (io_bind (m' r) k)) (fun r -> hist_bind (theta_unf (m' r)) (fun x -> theta_unf (k x)))
       }
      hist_bind (op_wp o arg) (fun r -> hist_bind (theta_unf (m' r)) (fun x -> theta_unf (k x)));
      `hist_equiv` { lemma_hist_bind_associativity (op_wp o arg) (fun r -> theta_unf (m' r)) (fun x -> theta_unf (k x)) }
      hist_bind (hist_bind (op_wp o arg) (fun r -> theta_unf (m' r))) (fun x -> theta_unf (k x));
      `hist_equiv` {
        assert (hist_equiv
          (hist_bind (theta_unf (Call o arg m')) (fun x -> theta_unf (k x)))
          (hist_bind (hist_bind (op_wp o arg) (fun r -> theta_unf (m' r))) (fun x -> theta_unf (k x)))
        ) by (norm [delta_once [`%theta_unf]; zeta; iota];
          apply_lemma (`lem_hist_equiv_reflexive)) }
      hist_bind (theta_unf (Call o arg m')) (fun x -> theta_unf (k x));
    }

let theta_monad_morphism_bind #a m k =
  unfold_theta #a ;
  theta_monad_morphism_bind_ m k

val io_bind_equivalence_ #a #b (k k':a -> io b) (m:io a) :
  Lemma (requires forall x. k x == k' x)
        (ensures theta_unf (io_bind m k) `hist_equiv` theta_unf (io_bind m k'))
let io_bind_equivalence_ (#a #b:Type) (k k':a -> io b) (m:io a) :
  Lemma (requires forall x. k x == k' x)
        (ensures theta_unf (io_bind m k) `hist_equiv` theta_unf (io_bind m k')) =
  match m with
  | Return _ -> ()
  | Call o arg m' ->
    calc (hist_equiv) {
      theta_unf (io_bind (Call o arg m') k);
      `hist_equiv` { theta_monad_morphism_bind_ (Call o arg m') k }
      hist_bind (theta_unf (Call o arg m')) (fun x -> theta_unf (k x));
      `hist_equiv` { _ by (norm [delta_once [`%theta_unf]; zeta;iota]) }
      hist_bind (hist_bind (op_wp o arg) (fun r -> theta_unf (m' r))) (fun x -> theta_unf (k x));
      `hist_equiv` { lemma_hist_bind_associativity (op_wp o arg) (fun r -> theta_unf (m' r)) (fun x -> theta_unf (k x)) }
      hist_bind (op_wp o arg) (fun r -> hist_bind (theta_unf (m' r)) (fun x -> theta_unf (k x)));
      `hist_equiv` {
        lem_hist_bind_equiv (op_wp o arg) (op_wp o arg) (fun r -> hist_bind (theta_unf (m' r)) (fun x -> theta_unf (k x))) (fun r -> hist_bind (theta_unf (m' r)) (fun x -> theta_unf (k' x)))
      }
      hist_bind (op_wp o arg) (fun r -> hist_bind (theta_unf (m' r)) (fun x -> theta_unf (k' x)));
      `hist_equiv` { lemma_hist_bind_associativity (op_wp o arg) (fun r -> theta_unf (m' r)) (fun x -> theta_unf (k' x)) }
      hist_bind (hist_bind (op_wp o arg) (fun r -> theta_unf (m' r))) (fun x -> theta_unf (k' x));
      `hist_equiv` {
        assert (hist_equiv
          (hist_bind (theta_unf (Call o arg m')) (fun x -> theta_unf (k' x)))
          (hist_bind (hist_bind (op_wp o arg) (fun r -> theta_unf (m' r))) (fun x -> theta_unf (k' x)))
        ) by (norm [delta_once [`%theta_unf]; zeta; iota];
          apply_lemma (`lem_hist_equiv_reflexive))
       }
      hist_bind (theta_unf (Call o arg m')) (fun x -> theta_unf (k' x));
      `hist_equiv` { theta_monad_morphism_bind_ m k' }
      theta_unf (io_bind (Call o arg m') k');
    }

let io_bind_equivalence (#a #b:Type) (k k':a -> io b) (m:io a) :
  Lemma (requires forall x. k x == k' x)
        (ensures theta (io_bind m k) `hist_equiv` theta (io_bind m k')) =
  unfold_theta #a ;
  io_bind_equivalence_ k k' m

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

let destruct_thetaP_open arg h lt fs_r =
  let p : hist_post h (io_res OOpen arg) = fun lt' r' ->
    (r' == Inl (fresh_fd h) /\ lt' == [EvOpen arg (Inl (fresh_fd h))]) \/
    (r' == Inr () /\ lt' == [EvOpen arg (Inr ())]) in
  match openfile arg with
  | Return _ -> false_elim ()
  | Call OOpen arg' k -> begin
    assert (theta (openfile arg) h p) by (compute ());
    assert (p lt fs_r)
    end

let lem_theta_read arg res h =
  assert (thetaP (read arg) h (ev_lt (EvRead arg res)) res) by (compute ())

let lem_theta_write arg res h =
  assert (thetaP (write arg) h (ev_lt (EvWrite arg res)) res) by (compute ())

let lem_theta_close arg res h =
  assert (thetaP (close arg) h (ev_lt (EvClose arg res)) res) by (compute ())

let destruct_thetaP_read arg h lt fs_r =
  let p : hist_post h (io_res ORead arg) = fun lt' r' -> lt' == [EvRead arg r'] in
  match read arg with
  | Return _ -> false_elim ()
  | Call ORead arg' k -> begin
    assert (theta (read arg) h p) by (compute ());
    assert (p lt fs_r)
    end

let destruct_thetaP_write arg h lt fs_r =
  let p : hist_post h (io_res OWrite arg) = fun lt' r' -> lt' == [EvWrite arg r'] in
  match write arg with
  | Return _ -> false_elim ()
  | Call OWrite arg' k -> begin
    assert (theta (write arg) h p) by (compute ());
    assert (p lt fs_r)
    end

let destruct_thetaP_close arg h lt fs_r =
  let p : hist_post h (io_res OClose arg) = fun lt' r' -> lt' == [EvClose arg r'] in
  match close arg with
  | Return _ -> false_elim ()
  | Call OClose arg' k -> begin
    assert (theta (close arg) h p) by (compute ());
    assert (p lt fs_r)
    end

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
      assert ((op_wp o args) h (fun lt fs_r -> theta_unf (k fs_r) (h ++ lt) (fun lt' fs_r' -> thetaP m h (lt@lt') fs_r')))
#pop-options

unfold
let theta_io_bind_exists_post #t1 #t2 (m:io t1) (f:t1 -> io t2) (h:history) (lt:local_trace h) (fs_r:t2) =
  exists fs_m lt1 lt2 .
      lt = lt1 @ lt2 /\
      thetaP m h lt1 fs_m /\
      thetaP (f fs_m) (h ++ lt1) lt2 fs_r

#push-options "--split_queries always"
let rec theta_io_bind_exists_ #t1 #t2 (m:io t1) (f:t1 -> io t2) (h:history) : Lemma (theta (io_bind m f) h (theta_io_bind_exists_post m f h)) =
  match m with
  | Return x ->
      theta_thetaP_in_post (f x) h;
      assert (theta_unf (f x) h (fun lt fs_r -> thetaP (f x) h lt fs_r));
      calc (hist_post_ord) {
        (fun lt fs_r -> thetaP (f x) h lt fs_r);
        `hist_post_ord` {}
        (fun lt fs_r -> exists lt2. lt = []@lt2 /\ thetaP (f x) h lt2 fs_r);
        `hist_post_ord` {}
        (fun lt fs_r -> exists fs_m lt1 lt2. lt = lt1@lt2 /\ thetaP (Return x) h lt1 fs_m /\ thetaP (f fs_m) (h++lt1) lt2 fs_r);
      };
      assert (theta_unf (f x) h (theta_io_bind_exists_post m f h))
  | Call o args k ->
      introduce forall lt r. lt == [op_to_ev o args r] ==> theta_unf (io_bind (k r) f) (h ++ lt) (fun lt' fs_r' -> theta_io_bind_exists_post m f h (lt @ lt') fs_r') with begin
        introduce _ ==> _ with _. begin
          theta_io_bind_exists_ (k r) f (h ++ lt);
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
          assert (theta_unf (io_bind (k r) f) (h ++ lt) (fun lt' r' -> theta_io_bind_exists_post m f h (lt @ lt') r'))
        end
      end;
      assert (hist_bind (op_wp o args) (fun r -> theta_unf (io_bind (k r) f)) h (theta_io_bind_exists_post m f h));
      assert (theta_unf (io_bind (Call o args k) f) h (theta_io_bind_exists_post m f h))
#pop-options

let theta_io_bind_exists #t1 #t2 (m:io t1) (f:t1 -> io t2) (h:history) : Lemma (theta (io_bind m f) h (theta_io_bind_exists_post m f h)) =
  unfold_theta #t1 ;
  theta_io_bind_exists_ m f h

let destruct_fs_beh #t1 #t2 (m:io t1) (k:t1 -> io t2) (h:history) (lt:local_trace h) (fs_r:t2) :
  Lemma
    (requires thetaP (io_bind m k) h lt fs_r) // forall p. theta (io_bind m k) h p ==> p lt fs_r
    (ensures exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m:t1).
      lt == (lt1@lt2) /\
      thetaP m h lt1 fs_m /\ // forall p. theta m h p ==> p lt1 fs_m
      thetaP (k fs_m) (h++lt1) lt2 fs_r) (* forall p. theta (k fs_m) (h++lt1) p ==> p lt2 fs_r *) =
    theta_io_bind_exists m k h
