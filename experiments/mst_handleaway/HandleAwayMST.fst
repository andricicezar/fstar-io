module HandleAwayMST

open FStar.Tactics
open FStar.Tactics.Typeclasses

open MST
open MST.Tot

unfold
let eq_wp wp1 wp2 = wp1 ⊑ wp2 /\ wp2 ⊑ wp1

unfold
let eq_wp_f (f:'a -> 'b) (wp1:st_wp 'a) (wp2:st_wp 'b) =
  st_bind_wp _ _ _ wp1 (fun r -> st_return _ _ (f r)) `eq_wp` wp2

unfold
let pure_wp_as_post (w:pure_wp 'a) : pure_post 'a =
  fun r -> forall p. w p ==> p r

unfold
let post_ord_f (#a:Type u#a) (#b:Type u#b) (rel:a -> b -> Type0) (p1:pure_post a) (p2:pure_post b) : Type0 =
  forall r1 r2. r1 `rel` r2 ==> (p1 r1 ==> p2 r2)

unfold
let eq_post_f (#a:Type u#a) (#b:Type u#b) (rel:a -> b -> Type0) (p1:pure_post a) (p2:pure_post b): Type0 =
  p1 `post_ord_f rel` p2 /\ p2 `post_ord_f (fun x y -> rel y x)` p1

let lemma_eq_wp_f #a #b (w:st_wp a) (f:a -> b) :
  Lemma
    (ensures (w `eq_wp_f f` (st_bind_wp _ _ _ w (fun x -> st_return _ _ (f x))))) = () (** REFL **)

let rec lemma_stheta_bind_pure (m:mheap 'a 'w) (f:'a -> 'b) :
  Lemma (ensures (theta m `eq_wp_f f` theta (mheap_bind _ _ _ _ m (fun x -> mheap_return _ (f x))))) (decreases m) =
  admit ()
  
class source (t:Type) = { [@@@no_method] _empty : unit }

instance source_int : source int = { _empty = () }

instance source_pair (t1:Type) {| source t1 |} (t2:Type) {| source t2 |} : source (t1 * t2) = { _empty = () }

instance source_arrow
  (t1:Type) {| source t1 |}
  (t2:t1 -> Type) {| (x:t1) -> source (t2 x) |}
  (wp:(x:t1) -> st_wp (t2 x)) : 
  source (x:t1 -> mheap (t2 x) (wp x)) = { _empty = () }

(** *** Source language has a fixed wp **)
let fixed_wp (#a:Type) : st_wp a = fun p h0 -> forall r h1. h0 `heap_state.rel` h1 ==> p r h1

(** *** Target monad : a Free Monad with less constructors **)
noeq
type tfree (a:Type u#a) : Type u#(max 1 a) = (* because of the heap *)
| GetT : cont:(heap_state.t -> tfree a) -> tfree a
| PutT : heap_state.t -> cont:(unit -> tfree a) -> tfree a
| ReturnT : a -> tfree a

let tfree_return (x:'a) : tfree 'a = ReturnT x

let rec tfree_bind (m:tfree 'a) (k:'a -> tfree 'b) : tfree 'b =
  match m with
  | ReturnT x -> k x
  | GetT cont -> GetT (fun x -> tfree_bind (cont x) k)
  | PutT h cont -> PutT h (fun x -> tfree_bind (cont ()) k)

let rec ttheta (m:tfree 'a) : st_wp 'a =
  match m with
  | ReturnT x -> st_return heap_state.t _ x
  | GetT k ->
      st_bind_wp heap_state.t heap_state.t 'a get_wp (fun r -> ttheta (k r))
  | PutT h1 k ->
      st_bind_wp heap_state.t _ _ (put_wp h1) (fun r -> ttheta (k r))

let rec lemma_ttheta_bind_pure (m:tfree 'a) (f:'a -> 'b) :
  Lemma (ensures (ttheta m `eq_wp_f f` ttheta (tfree_bind m (fun x -> tfree_return (f x)))))
        (decreases m) =
  match m with
  | ReturnT _ -> ()
  | GetT k ->
    introduce forall x. ttheta (k x) `eq_wp_f f` ttheta (tfree_bind (k x) (fun x -> tfree_return (f x))) with begin
      lemma_ttheta_bind_pure (k x) f
    end;
    assert (ttheta (GetT k) `eq_wp` (fun p h0 -> ttheta (k h0) p h0))
  | PutT h k -> 
    introduce forall x. ttheta (k x) `eq_wp_f f` ttheta (tfree_bind (k x) (fun x -> tfree_return (f x))) with begin
      lemma_ttheta_bind_pure (k x) f
    end;
    assert (ttheta (PutT h k) `eq_wp` (fun p h0 -> (h0 `heap_state.rel` h) /\ ttheta (k ()) p h))

class target (t:Type) = { [@@@no_method] _empty : unit }

instance target_int : target int = { _empty = () }

instance target_pair (t1:Type) {| target t1 |} (t2:Type) {| target t2 |} : target (t1 * t2) = { _empty = () }

instance target_arrow (t1:Type) {| target t1 |} (t2:Type) {| target t2 |} : target (x:t1 -> tfree t2) = { _empty = () }

(** *** Handlers: lift, erase **)
let rec lift_handler (m:tfree 'a) : mheap 'a fixed_wp =
  match m with
  | ReturnT x -> Return x
  | GetT k -> Get (fun x -> lift_handler (k x))
  | PutT h k -> Put h (fun x -> lift_handler (k x))

let rec erase_handler (m:dm 'a fixed_wp) : free 'a =
  match m with
  | Return x -> Ret x
  | Require pre k -> begin
    assert (stheta m (fun r -> True));
    assert (pre);
    erase_handler (k ())
  end
  | Op k -> Call (fun x -> erase_handler (k x))

let rec lemma_stheta_stronger_ttheta_erase (#a:Type0) (m:dm a fixed_wp) :
  Lemma (stheta m ⊑ ttheta (erase_handler m)) =
  match m with
  | Return x ->  ()
  | Require pre k -> begin
    assert (stheta m (fun r -> True));
    lemma_stheta_stronger_ttheta_erase (k ())
  end
  | Op k -> begin
    assert (stheta m == (fun p -> forall x. stheta (k x) p)) by (rewrite_eqs_from_context (); compute ());
    assert (ttheta (erase_handler m) == (fun p -> forall x. ttheta (erase_handler (k x)) p)) by (rewrite_eqs_from_context (); compute ());
    introduce forall x. stheta (k x) ⊑ ttheta (erase_handler (k x)) with begin
      lemma_stheta_stronger_ttheta_erase (k x)
    end
  end

let rec lemma_ttheta_erase_stronger_stheta (#a:Type0) (m:dm a fixed_wp) :
  Lemma (ttheta (erase_handler m) ⊑ stheta m) = 
  match m with
  | Return x ->  ()
  | Require pre k -> begin
    assert (stheta m (fun r -> True));
    lemma_ttheta_erase_stronger_stheta (k ())
  end
  | Op k -> begin
    assert (stheta m == (fun p -> forall x. stheta (k x) p)) by (rewrite_eqs_from_context (); compute ());
    assert (ttheta (erase_handler m) == (fun p -> forall x. ttheta (erase_handler (k x)) p)) by (rewrite_eqs_from_context (); compute ());
    introduce forall x. ttheta (erase_handler (k x)) ⊑ stheta (k x) with begin
      lemma_ttheta_erase_stronger_stheta (k x)
    end
  end

let rec lemma_ttheta_stronger_stheta_lift (#a:Type0) (m:free a) :
  Lemma (ttheta m ⊑ stheta (lift_handler m)) = 
  match m with
  | Ret x -> ()
  | Call k -> begin
    assert (ttheta m == (fun p -> forall x. ttheta (k x) p)) by (rewrite_eqs_from_context (); compute ());
    assert (stheta (lift_handler m) == (fun p -> forall x. stheta (lift_handler (k x)) p)) by (rewrite_eqs_from_context (); compute ());
    introduce forall x. ttheta (k x) ⊑ stheta (lift_handler (k x)) with begin
      lemma_ttheta_stronger_stheta_lift (k x)
    end
  end

let rec lemma_stheta_lift_stronger_ttheta (#a:Type0) (m:free a) :
  Lemma (stheta (lift_handler m) ⊑ ttheta m) =
  match m with
  | Ret x -> ()
  | Call k -> begin
    assert (ttheta m == (fun p -> forall x. ttheta (k x) p)) by (rewrite_eqs_from_context (); compute ());
    assert (stheta (lift_handler m) == (fun p -> forall x. stheta (lift_handler (k x)) p)) by (rewrite_eqs_from_context (); compute ());
    introduce forall x. stheta (lift_handler (k x)) ⊑ ttheta (k x)  with begin
      lemma_stheta_lift_stronger_ttheta (k x)
    end
  end

(** *** Semantics **)
type sem 'a = pure_wp 'a

let eq_beh (#a:Type u#a) (#b:Type u#b) (f:a -> b) (w1:sem a) (w2:sem b): Type0 =
  eq_wp_f f w1 w2

let behS (m:dm 'a 'wp) : sem 'a =
  stheta m
let behT (m:free 'a) : sem 'a = 
  ttheta m

let eq_beh_reflexivity (#a:Type u#a) (w:sem a) : 
  Lemma (w `eq_beh (id)` w) by (compute ()) = ()

let eq_beh_under_bind (#a:Type u#a) (#b:Type u#b) (m:sem a) (k:a -> sem b) (k':a -> sem b) : 
  Lemma 
    (requires (forall x. (k x) `eq_beh (id)` (k' x)))
    (ensures ((fun r -> exists x. k x r) `eq_beh (id)` (fun r' -> exists x'. k' x' r'))) = ()

open FStar.Calc

[@@expect_failure]
let rec lemma_erase_inverse_lift_syntactic (m:free 'a) :
  Lemma (erase_handler (lift_handler m) == m) =
  match m with
  | Ret x -> ()
  | Call k -> 

    calc (==) {
      erase_handler (lift_handler (Call k));
      == { _ by (norm [delta_only [`%lift_handler]; zeta; iota]) }
      erase_handler (Op (fun x -> lift_handler (k x)));
      == { _ by (norm [delta_only [`%erase_handler]; zeta; iota]) }
      Call (fun x -> erase_handler (lift_handler (k x)));
      == {
        introduce forall x. erase_handler (lift_handler (k x)) == k x with begin
          lemma_erase_inverse_lift_syntactic (k x)
        end
      }
      Call (fun x -> k x);
      == { (** function extensionality needed **) }
      Call k;
    }

let erase_preserves_beh (w:dm 'a fixed_wp) :
  Lemma (behS w `eq_beh id` behT (erase_handler w)) =
  lemma_ttheta_erase_stronger_stheta w;
  lemma_stheta_stronger_ttheta_erase w

let lift_preserves_beh (w:free 'a) :
  Lemma (behT w `eq_beh id` behS (lift_handler w)) =
  lemma_stheta_lift_stronger_ttheta w;
  lemma_ttheta_stronger_stheta_lift w

let lemma_erase_inverse_lift_semantic (m:free 'a) :
  Lemma (behT (erase_handler (lift_handler m)) `eq_beh id` behT m) =
  lift_preserves_beh m;
  erase_preserves_beh (lift_handler m)

let lemma_lift_inverse_erase_semantic (m:dm 'a fixed_wp) :
  Lemma (behS (lift_handler (erase_handler m)) `eq_beh id` behS m) =
  erase_preserves_beh m;
  lift_preserves_beh (erase_handler m)

(** *** Type class: Lift **)
class liftable (t:Type u#a) = {
  [@@@no_method]
  t_tc : target t;
  [@@@no_method]
  s : Type u#b;
  [@@@no_method]
  s_tc : source s;

  lift : t -> s;
}

class eraseable (s:Type u#a) = {
  [@@@no_method]
  s_tc : source s;

  [@@@no_method]
  t : Type u#b;
  [@@@no_method]
  t_tc : target t;

  erase : s -> t;
}

instance liftable_int : liftable int = {
  t_tc = solve;
  s = int;
  s_tc = solve;

  lift = (fun x -> x);
}

instance liftable_pair (t1 t2:Type) {| c1:liftable t1 |} {| c2:liftable t2 |} : liftable (t1 * t2) = {
  t_tc = target_pair t1 #c1.t_tc t2 #c2.t_tc; 
  s = c1.s * c2.s;
  s_tc = source_pair c1.s #c1.s_tc c2.s #c2.s_tc;

  lift = (fun (x, y) -> (c1.lift x, c2.lift y));
}

instance liftable_arrow (s1 t2:Type) {| c1:eraseable s1 |} {| c2:liftable t2 |} : liftable (c1.t -> free t2) = {
  t_tc = target_arrow c1.t #c1.t_tc t2 #c2.t_tc;
  s = s1 -> dm c2.s fixed_wp;
  s_tc = source_arrow s1 #c1.s_tc (fun _ -> c2.s) #(fun _ -> c2.s_tc) (fun x p -> forall r. p r);

  lift = (fun (f:c1.t -> free t2) (x:s1) -> 
    dm_subcomp #_ #_ #fixed_wp (dm_bind (lift_handler #t2 (f (c1.erase x))) (fun (r:t2) -> dm_return (c2.lift r)))
  );
}

instance eraseable_int : eraseable int = {
  t = int;
  t_tc = solve;
  s_tc = solve;

  erase = (fun x -> x);
}

instance eraseable_arrow (t1 s2:Type) {| c1:liftable t1 |} {| c2:eraseable s2 |} : eraseable (c1.s -> dm s2 fixed_wp) = {
  t_tc = target_arrow t1 #c1.t_tc c2.t #c2.t_tc;
  t = t1 -> free c2.t;
  s_tc = source_arrow c1.s #c1.s_tc (fun _ -> s2) #(fun _ -> c2.s_tc) (fun x p -> forall r. p r);

  erase = (fun f (x:t1) ->
    free_bind (erase_handler (f (c1.lift x))) (fun (r:s2) -> free_return (c2.erase r))
  )
}

let erase_result_preserves_beh (w:free 'a) (f:'a -> 'b) :
  Lemma (behT w `eq_beh f` behT (free_bind w (fun r -> free_return (f r)))) = 
  lemma_ttheta_bind_pure w f;
  let lhs = ttheta w in
  let rhs = ttheta (free_bind w (fun x -> free_return (f x))) in
  assert (lhs `eq_wp_f f` rhs);
  lemma_eq_wp_f lhs f

let lift_result_preserves_beh (w:dm 'a (fun p -> forall r. p r)) (f:'a -> 'b) :
  Lemma (behS w `eq_beh f` behS (dm_bind w (fun r -> dm_return (f r)))) =
  lemma_stheta_bind_pure w f;
  let lhs = stheta w in
  let rhs = stheta (dm_bind w (fun x -> dm_return (f x))) in
  assert (lhs `eq_wp_f f` rhs);
  lemma_eq_wp_f lhs f

let sem_transitivity (w1 w2:sem 'a) (w3:sem 'b) (f:'a -> 'b) :
  Lemma (requires (w1 `eq_beh id` w2 /\ w2 `eq_beh f` w3))
        (ensures (w1 `eq_beh f` w3)) = ()

let cc_whole (w:dm 'a fixed_wp) {| c1:eraseable 'a |} :
  Lemma (behS w `eq_beh c1.erase` behT (free_bind (erase_handler w) (fun r -> free_return (c1.erase r)))) =
  erase_preserves_beh w;
  erase_result_preserves_beh (erase_handler w) c1.erase;
  sem_transitivity #'a (behS w) (behT (erase_handler w)) (behT (free_bind (erase_handler w) (fun r -> free_return (c1.erase r)))) c1.erase
  
let sc (ps:(int -> dm int fixed_wp) -> dm int fixed_wp) (ct:int -> free int) : Type0 =
  behS (ps ((liftable_arrow int int).lift ct)) `eq_beh id` behT (((eraseable_arrow (int -> free int) _ #(liftable_arrow int int)).erase ps) ct)

open FStar.Tactics

let sc_proof ps ct : Lemma (sc ps ct) 
  by (
    norm [delta_only [`%Mkeraseable?.erase;`%eraseable_int]; zeta; iota];
    explode ();
    let x = nth_binder (-3) in
    let x = instantiate x (fresh_uvar None) in
    mapply x;
    norm [delta_only [`%sc;
      `%eraseable_arrow;`%target_arrow; `%source_arrow; 
      `%Mkeraseable?.erase;`%eraseable_int]; zeta; iota
    ];
    assumption ()
  )
  = cc_whole (ps ((liftable_arrow int int).lift ct)) #eraseable_int

let sc' (ct:(int -> free int) -> free int) (ps:int -> dm int fixed_wp) : Type0 =
  behT (ct ((eraseable_arrow int int).erase ps)) `eq_beh id`
  behS (((liftable_arrow (int -> dm int fixed_wp) int #(eraseable_arrow int int #liftable_int #eraseable_int)).lift ct) ps)

let btc_whole (w:free 'a) {| c1:liftable 'a |} :
  Lemma (behT w `eq_beh c1.lift` behS (dm_subcomp #_ #_ #fixed_wp (dm_bind (lift_handler w) (fun r -> dm_return (c1.lift r))))) =
  lift_preserves_beh w;
  lift_result_preserves_beh (lift_handler w) c1.lift;
  sem_transitivity #'a (behT w) (behS (lift_handler w)) (behS (dm_bind (lift_handler w) (fun r -> dm_return (c1.lift r)))) c1.lift

let sc_proof' ps ct : Lemma (sc' ct ps)
  by (
    norm [delta_only [`%Mkliftable?.lift;`%liftable_int]; zeta; iota];
    explode ();
    let x = nth_binder 3 in
    let x = instantiate x (fresh_uvar None) in
    mapply x;
    norm [delta_only [`%sc';
      `%liftable_arrow;`%target_arrow; `%source_arrow; 
      `%Mkliftable?.lift;`%liftable_int]; zeta; iota];
    assumption ()
  )
  = btc_whole (ct ((eraseable_arrow int int).erase ps)) #liftable_int
