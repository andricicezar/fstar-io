module IOStar

open FStar.Tactics.V1

include BaseTypes
include Hist
include Trace

(** Computational Monad **)

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

let io_call (o:io_ops) (args:io_args o) : io (io_res o args) =
  Call o args Return

let return = io_return
let (let!@) = io_bind

let op_wp (o:io_ops) (args:io_args o) : hist (io_res o args) =
  to_hist
    (fun h -> io_pre h o args)
    (fun h res lt -> io_post h o args res /\ lt == [op_to_ev o args res])

let rec theta #a (m:io a) : hist a =
  match m with
  | Return x -> hist_return x
  | Call o args k -> hist_bind (op_wp o args) (fun r -> theta (k r))

val theta_monad_morphism_ret (x:'a) :
  Lemma (theta (return x) == hist_return x)
let theta_monad_morphism_ret x =
  assert (theta (return x) == hist_return x) by (FStar.Tactics.compute ())

val theta_monad_morphism_bind (m:io 'a) (k:'a -> io 'b) :
  Lemma (theta (io_bind m k) `hist_equiv` hist_bind (theta m) (fun x -> theta (k x)))
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

val io_bind_equivalence #a #b (k k':a -> io b) (m:io a) :
  Lemma (requires forall x. k x == k' x)
        (ensures theta (io_bind m k) `hist_equiv` theta (io_bind m k'))
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

let thetaP m = wp2p (theta m)

val wp2p_theta_bind (m:io 'a) (k:'a -> io 'b) :
  Lemma (forall h.
         wp2p (hist_bind (theta m) (fun x -> theta (k x))) h (** Kind of ugly. Can we use hist_post_bind? **)
         `hist_post_equiv`
         thetaP (io_bind m k) h)
let wp2p_theta_bind m k =
  theta_monad_morphism_bind m k

(** Trying to connect with hist_post_bind. Does not look like it holds.
let lem_thetaP_bind #a #b (m:io a) (k:a -> io b) :
  Lemma (forall h.
         wp2p (hist_bind (theta m) (fun x -> theta (k x))) h
        `hist_post_equiv`
         hist_post_bind (thetaP m h) (fun lt r -> thetaP (k r) (h++lt))) =
  assert (forall h.
         wp2p (hist_bind (theta m) (fun x -> theta (k x))) h
        `hist_post_equiv`
         hist_post_bind (thetaP m h) (fun lt r -> thetaP (k r) (h++lt))) by (
         norm [delta_only [`%hist_post_bind; `%thetaP; `%hist_bind; `%wp2p;
         `%hist_post_bind'; `%hist_post_shift;`%hist_post_equiv;`%hist_post_ord]; iota];
         let h = forall_intro () in
         split ();
         dump "H")
**)


let lem_thetaP_return #a (x:a) (h:history) :
  Lemma (thetaP (return x) h [] x) =
  theta_monad_morphism_ret x

#push-options "--split_queries always"
let lem_thetaP_bind #a #b (m:io a) (h:history) (lt1:local_trace h) (fs_r_m:a) (k:a -> io b) (lt2:local_trace (h++lt1)) (fs_r:b) :
  Lemma (requires thetaP m h lt1 fs_r_m /\
                  thetaP (k fs_r_m) (h++lt1) lt2 fs_r)
        (ensures thetaP (io_bind m k) h (lt1@lt2) fs_r)
        =
  wp2p_theta_bind m k;
  introduce forall (p:hist_post h b). hist_bind (theta m) (fun x -> theta (k x)) h p ==> p (lt1@lt2) fs_r with begin
    introduce _ ==> _ with _. begin
      assert (wp2p (theta (k fs_r_m)) (h++lt1) lt2 fs_r);
      assert (forall (p':hist_post (h++lt1) b). theta (k fs_r_m) (h++lt1) p' ==> p' lt2 fs_r);
      let p' : hist_post (h++lt1) b = fun lt r -> p (lt1@lt) r in
      assert (theta (k fs_r_m) (h++lt1) p' ==> p' lt2 fs_r);
      assert (p (lt1@lt2) fs_r)
    end
  end
#pop-options

#push-options "--split_queries always"
val lem_thetaP_call (o:io_ops) (args:io_args o) (res:io_res o args) (h:history) :
  Lemma (requires io_post h o args res)
        (ensures thetaP (io_call o args) h [op_to_ev o args res] res)
let lem_thetaP_call o args res h =
  introduce forall (p:hist_post h (io_res o args)). (theta (io_call o args)) h p ==> p [op_to_ev o args res] res with begin
    introduce (theta (io_call o args)) h p ==> p [op_to_ev o args res] res with _. begin
      assert ((hist_bind (op_wp o args) (fun (r:io_res o args) -> theta (Return r))) h p ==>
              (hist_bind (to_hist (fun h_ -> io_pre h_ o args) (fun h_ res_ lt_ -> io_post h_ o args res_ /\ lt_ == [op_to_ev o args res_])) (fun (r:io_res o args) -> theta (Return r))) h p) by (compute ());
      eliminate forall (lt':local_trace h) (r':io_res o args). lt' == [op_to_ev o args r'] ==>
        (theta (Return r')) (h++lt') (fun (lt'':local_trace (h++lt')) (r'':io_res o args) -> p (lt' @ lt'') r'')
        with [op_to_ev o args res] res
    end
  end
#pop-options