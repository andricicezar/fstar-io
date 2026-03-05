module IOStar

open FStar.Tactics.V1

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

(** Specification monad **)

(** The postcondition for an io computation is defined over the
result (type: a) and local trace (type: list event).
The local trace represents the events that happend during the
computation. Local trace is in chronological order.

We also have the history (type: list event) that represents the
events that happend until the beginning of the io computation.
The history is in reverse chronological order.

At the end of an io computation, the local trace is
reversed and appended to the history. **)

type hist_post (h:history) a = lt:local_trace h -> r:a -> Type0
type hist_pre = h:history -> Type0

type hist0 a =
  h:history -> hist_post h a -> Type0

unfold
let hist_post_ord (#h:history) (p1 p2:hist_post h 'a) = forall lt r. p1 lt r ==> p2 lt r

unfold
let hist_post_equiv (#h:history) (p1 p2:hist_post h 'a) =
  hist_post_ord p1 p2 /\ hist_post_ord p2 p1

unfold
let hist_post_bind #h (m:hist_post h 'a) (k:(lt:local_trace h -> 'a -> hist_post (h++lt) 'b)) : hist_post h 'b =
  fun lt b ->
    exists a lta ltb. m lta a /\ lta@ltb == lt /\ k lta a ltb b

unfold
let hist_wp_monotonic (wp:hist0 'a) =
  forall h (p1 p2:hist_post h 'a). (p1 `hist_post_ord` p2) ==>  (wp h p1 ==> wp h p2)

type hist a = wp:(hist0 a){hist_wp_monotonic wp}

let wp2p (wp:hist 'a) (h:history) : hist_post h 'a =
  fun lt res -> forall p. wp h p ==> p lt res

val hist_subcomp0 : #a:Type -> #p1:(a -> Type0) -> #p2:(a -> Type0) -> #_:unit{forall x. p1 x ==> p2 x} -> wp:hist (x:a{p1 x}) ->
  (hist (x:a{p2 x}))
let hist_subcomp0 #a #p1 #p2 #_ wp : (hist (x:a{p2 x})) =
  let wp' : hist0 (x:a{p2 x}) = wp in
  assert (forall h (post1:hist_post h (x:a{p2 x})) (post2:hist_post h (x:a{p2 x})). (hist_post_ord post1 post2 ==>  wp' h post1 ==> wp' h post2));
  assert (hist_wp_monotonic #(x:a{p2 x}) wp');
  wp'

val hist_subcomp : #a:Type -> #p1:(a -> Type0) -> #p2:(a -> Type0) -> wp:hist (x:a{p1 x}) ->
  Pure (hist (x:a{p2 x})) (requires (forall x. p1 x ==> p2 x)) (ensures (fun _ -> True))
let hist_subcomp #a #p1 #p2 wp = hist_subcomp0 #a #p1 #p2 #() wp


unfold
let hist_return0 (x:'a) : hist0 'a =
  fun _ p -> p [] x

unfold
let hist_return (x:'a) : hist 'a = hist_return0 x

unfold
let hist_post_shift (h:history) (p:hist_post h 'a) (lt:local_trace h) : hist_post (h++lt) 'a =
  fun lt' r -> p (lt @ lt') r

unfold
let hist_post_bind'
  (#a #b:Type)
  (#h:history)
  (kw : a -> hist b)
  (p:hist_post h b) :
  Tot (hist_post h a) =
  fun lt r ->
    kw r (h ++ lt) (hist_post_shift h p lt)

unfold
let hist_bind (#a #b:Type) (w : hist a) (kw : a -> hist b) : hist b =
  fun h p -> w h (hist_post_bind' kw p)

unfold
let to_hist (#op:io_ops) (#args:io_args op) (pre:hist_pre) (post:(h:history -> io_res op args -> local_trace h -> Type0)) : hist (io_res op args)  =
  fun h p -> pre h /\ (forall lt r. post h r lt ==> p lt r)

let hist_call (o:io_ops) (args:io_args o) : hist (io_res o args) =
  to_hist
    (fun h -> io_pre h o args)
    (fun h res lt -> io_post h o args res /\ lt == [op_to_ev o args res])

unfold
let wp_lift_pure_hist0 (#a:Type u#a) (w : pure_wp a) : hist0 a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall u#a ();
  fun _ p -> w (p [])

unfold
let wp_lift_pure_hist (#a:Type u#a) (w : pure_wp a) : hist a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall u#a ();
  wp_lift_pure_hist0 w

let lemma_wp_lift_pure_hist_implies_as_requires #a w :
  Lemma (forall h (p:hist_post h a). wp_lift_pure_hist w h p ==> as_requires w) =
    assert (forall h (p:hist_post h a) x. p [] x ==> True) ;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity w ;
    assert (forall h (p:hist_post h a). w (fun x -> p [] x) ==> w (fun _ -> True))

unfold
val (⊑) (#a : Type) : hist a -> hist a -> Type0
let (⊑) wp1 wp2 = forall h p. wp2 h p ==> wp1 h p

unfold
val hist_equiv (#a : Type) : hist a -> hist a -> Type0
let hist_equiv wp1 wp2 = forall h p. wp1 h p <==> wp2 h p

unfold
let hist_if_then_else (wp1 wp2:hist 'a) (b:bool) : hist 'a =
  fun h p -> (b ==> wp1 h p) /\ ((~b) ==> wp2 h p)

let lem_hist_bind_subset (#a #b:Type) (m m':hist a) (k k':a -> hist b) :
  Lemma
    (requires (m ⊑ m' /\ (forall x. k x ⊑ k' x)))
    (ensures (hist_bind m k ⊑ hist_bind m' k')) = ()

let lem_hist_bind_equiv (#a #b:Type) (m m':hist a) (k k':a -> hist b) :
  Lemma
    (requires (m `hist_equiv` m' /\ (forall x. k x `hist_equiv` k' x)))
    (ensures (hist_bind m k `hist_equiv` hist_bind m' k')) = ()

let lem_hist_equiv_reflexive #a (m:hist a) :
  Lemma (m `hist_equiv` m) = ()

let lem_hist_equiv_commutative #a (m m':hist a) :
  Lemma (m `hist_equiv` m' ==> m' `hist_equiv` m) = ()

module L = FStar.List.Tot

let __list_assoc_l #a (l1 l2 l3 : list a) : Lemma (L.append l1 (l2 `L.append` l3) == (l1 `L.append` l2) `L.append` l3) = List.Tot.Properties.append_assoc l1 l2 l3
let __helper #a (lt lt' : list a) : Lemma (L.rev_acc lt [] `L.append` L.rev_acc lt' [] == L.rev_acc (lt' `L.append` lt) []) = List.Tot.Properties.rev_append lt' lt
let __iff_refl a : Lemma (a <==> a) = ()

let lemma_hist_bind_associativity #a #b #c (w1:hist a) (w2:a -> hist b) (w3: b -> hist c) :
  Lemma (hist_bind w1 (fun r1 -> hist_bind (w2 r1) w3) `hist_equiv` hist_bind (hist_bind w1 w2) w3)
  =
  let lhs = hist_bind w1 (fun r1 -> hist_bind (w2 r1) w3) in
  let rhs = hist_bind (hist_bind w1 w2) w3 in
  let pw (h : history) (p : hist_post h c) : Lemma (lhs h p <==> rhs h p) =
    assert (lhs h p <==> rhs h p) by begin
      unfold_def (`hist_bind);
      norm [];
      l_to_r [`__list_assoc_l];
      l_to_r [`__helper];
      mapply (`__iff_refl)
    end
  in
  Classical.forall_intro_2 pw

(** Semantics of IOStar

  Connecting the computational monad to the specification monad using
  a monad morphism. **)
let rec theta #a (m:io a) : hist a =
  match m with
  | Return x -> hist_return x
  | Call o args k -> hist_bind (hist_call o args) (fun r -> theta (k r))

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
      hist_bind (hist_call o arg) (fun r -> theta (io_bind (m' r) k));
      `hist_equiv` {
        introduce forall r. theta (io_bind (m' r) k) `hist_equiv` hist_bind (theta (m' r)) (fun x -> theta (k x)) with begin
          theta_monad_morphism_bind (m' r) k
        end;
        lem_hist_bind_equiv (hist_call o arg) (hist_call o arg) (fun r -> theta (io_bind (m' r) k)) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k x)))
       }
      hist_bind (hist_call o arg) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k x)));
      `hist_equiv` { lemma_hist_bind_associativity (hist_call o arg) (fun r -> theta (m' r)) (fun x -> theta (k x)) }
      hist_bind (hist_bind (hist_call o arg) (fun r -> theta (m' r))) (fun x -> theta (k x));
      `hist_equiv` {
        assert (hist_equiv
          (hist_bind (theta (Call o arg m')) (fun x -> theta (k x)))
          (hist_bind (hist_bind (hist_call o arg) (fun r -> theta (m' r))) (fun x -> theta (k x)))
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
      hist_bind (hist_bind (hist_call o arg) (fun r -> theta (m' r))) (fun x -> theta (k x));
      `hist_equiv` { lemma_hist_bind_associativity (hist_call o arg) (fun r -> theta (m' r)) (fun x -> theta (k x)) }
      hist_bind (hist_call o arg) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k x)));
      `hist_equiv` {
        lem_hist_bind_equiv (hist_call o arg) (hist_call o arg) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k x))) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k' x)))
      }
      hist_bind (hist_call o arg) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k' x)));
      `hist_equiv` { lemma_hist_bind_associativity (hist_call o arg) (fun r -> theta (m' r)) (fun x -> theta (k' x)) }
      hist_bind (hist_bind (hist_call o arg) (fun r -> theta (m' r))) (fun x -> theta (k' x));
      `hist_equiv` {
        assert (hist_equiv
          (hist_bind (theta (Call o arg m')) (fun x -> theta (k' x)))
          (hist_bind (hist_bind (hist_call o arg) (fun r -> theta (m' r))) (fun x -> theta (k' x)))
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
      assert ((hist_bind (hist_call o args) (fun (r:io_res o args) -> theta (Return r))) h p ==>
              (hist_bind (to_hist (fun h_ -> io_pre h_ o args) (fun h_ res_ lt_ -> io_post h_ o args res_ /\ lt_ == [op_to_ev o args res_])) (fun (r:io_res o args) -> theta (Return r))) h p) by (compute ());
      eliminate forall (lt':local_trace h) (r':io_res o args). lt' == [op_to_ev o args r'] ==>
        (theta (Return r')) (h++lt') (fun (lt'':local_trace (h++lt')) (r'':io_res o args) -> p (lt' @ lt'') r'')
        with [op_to_ev o args res] res
    end
  end
#pop-options