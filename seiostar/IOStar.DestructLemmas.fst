module IOStar.DestructLemmas

open FStar.Tactics.V1
open IOStar


val destruct_thetaP_call (o:io_ops) (args:io_args o) (h:history) (lt:local_trace h) (fs_r:io_res o args) :
  Lemma (requires thetaP (io_call o args) h lt fs_r)
        (ensures lt == [op_to_ev o args fs_r] /\ io_post h o args fs_r)
let destruct_thetaP_call o args h lt fs_r =
  let p : hist_post h (io_res o args) = fun lt' r' -> lt' == [op_to_ev o args r'] /\ io_post h o args r' in
  assert (theta (io_call o args) h p) by (compute ());
  assert (p lt fs_r)

let thetaP_shift_op_lt #t (o:io_ops) (args:io_args o) (k:io_res o args -> io t) (r:io_res o args) (h:history) (lt:local_trace h)
  : Lemma
      (requires (lt == [op_to_ev o args r]))
      (ensures (forall (lt':local_trace (h++lt)) fs_r . thetaP (k r) (h ++ lt) lt' fs_r ==> thetaP (Call o args k) h (lt@lt') fs_r))
  =
  introduce forall (lt':local_trace (h++lt)) fs_r . thetaP (k r) (h ++ lt) lt' fs_r ==> thetaP (Call o args k) h (lt@lt') fs_r with begin
    introduce thetaP (k r) (h ++ lt) lt' fs_r ==> thetaP (Call o args k) h (lt@lt') fs_r with _. begin
      introduce forall (p:hist_post h t). theta (Call o args k) h p ==> p (lt@lt') fs_r with begin
        introduce theta (Call o args k) h p ==> p (lt@lt') fs_r with _. begin
          assert (hist_bind (hist_call o args) (fun r -> theta (k r)) h p);
          assert (forall (lt:local_trace h) (r:io_res o args). lt == [op_to_ev o args r] ==> theta (k r) (h++lt) (hist_post_shift h p lt)) by (
            binder_retype (nth_binder (-1));
              norm [delta_only [`%hist_bind;`%hist_call;`%to_hist;`%io_post;`%io_pre;`%hist_post_bind'];iota];
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
      assert ((hist_call o args) h (fun lt fs_r -> theta (k fs_r) (h ++ lt) (fun lt' fs_r' -> thetaP m h (lt@lt') fs_r')))
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
      assert (theta (f x) h (fun lt fs_r -> thetaP (f x) h lt fs_r));
      calc (hist_post_ord) {
        (fun lt fs_r -> thetaP (f x) h lt fs_r);
        `hist_post_ord` {}
        (fun lt fs_r -> exists lt2. lt = []@lt2 /\ thetaP (f x) h lt2 fs_r);
        `hist_post_ord` {}
        (fun lt fs_r -> exists fs_m lt1 lt2. lt = lt1@lt2 /\ thetaP (Return x) h lt1 fs_m /\ thetaP (f fs_m) (h++lt1) lt2 fs_r);
      };
      assert (theta (f x) h (theta_io_bind_exists_post m f h))
  | Call o args k ->
      introduce forall lt r. lt == [op_to_ev o args r] ==> theta (io_bind (k r) f) (h ++ lt) (fun lt' fs_r' -> theta_io_bind_exists_post m f h (lt @ lt') fs_r') with begin
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
          assert (theta (io_bind (k r) f) (h ++ lt) (fun lt' r' -> theta_io_bind_exists_post m f h (lt @ lt') r'))
        end
      end;
      assert (hist_bind (hist_call o args) (fun r -> theta (io_bind (k r) f)) h (theta_io_bind_exists_post m f h));
      assert (theta (io_bind (Call o args k) f) h (theta_io_bind_exists_post m f h))
#pop-options

let theta_io_bind_exists #t1 #t2 (m:io t1) (f:t1 -> io t2) (h:history) : Lemma (theta (io_bind m f) h (theta_io_bind_exists_post m f h)) =
  theta_io_bind_exists_ m f h

val destruct_fs_beh #t1 #t2 (m:io t1) (k:t1 -> io t2) (h:history) (lt:local_trace h) (fs_r:t2) :
  Lemma
    (requires thetaP (io_bind m k) h lt fs_r)
    (ensures exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m:t1).
      lt == (lt1@lt2) /\
      thetaP m h lt1 fs_m /\
      thetaP (k fs_m) (h++lt1) lt2 fs_r)
let destruct_fs_beh #t1 #t2 (m:io t1) (k:t1 -> io t2) (h:history) (lt:local_trace h) (fs_r:t2) :
  Lemma
    (requires thetaP (io_bind m k) h lt fs_r) // forall p. theta (io_bind m k) h p ==> p lt fs_r
    (ensures exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m:t1).
      lt == (lt1@lt2) /\
      thetaP m h lt1 fs_m /\ // forall p. theta m h p ==> p lt1 fs_m
      thetaP (k fs_m) (h++lt1) lt2 fs_r) (* forall p. theta (k fs_m) (h++lt1) p ==> p lt2 fs_r *) =
    theta_io_bind_exists m k h
