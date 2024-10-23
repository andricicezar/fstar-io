module HandleAwayEff

open FStar.Monotonic.Pure

open FStar.Tactics
open FStar.Tactics.Typeclasses

assume type beta : Type u#0

let pure_wp (a: Type) = wp:pure_wp' a{pure_wp_monotonic0 a wp}

let pure_return (x:'a) : pure_wp 'a =
  pure_return 'a x

let pure_bind (m:pure_wp 'a) (k:'a -> pure_wp 'b) : pure_wp 'b =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  pure_bind_wp _ _ (as_pure_wp m) (fun x -> as_pure_wp (k x))

unfold
let pure_predicate_transformer (w:pure_wp 'a) : pure_post 'a =
  fun r -> forall p. w p ==> p r

unfold
let (⊑) wp1 wp2 = forall post. wp2 post ==> wp1 post

(** *** Source monad : a Dijkstra Monad **)
noeq
type free_req (a:Type u#a) : Type u#(a+1) = 
| Return : a -> free_req a
| Op : (beta -> free_req a) -> free_req a
| Require : (pre:pure_pre) -> cont:((squash pre) -> free_req a) -> free_req a

let free_req_return (x:'a) : free_req 'a = Return x

let rec free_req_bind (m:free_req 'a) (k:'a -> free_req 'b) : free_req 'b =
  match m with
  | Return x -> k x
  | Op cont -> Op (fun x -> free_req_bind (cont x) k)
  | Require pre cont -> Require pre (fun x -> free_req_bind (cont x) k)

let rec stheta (m:free_req 'a) : pure_wp 'a =
  match m with
  | Return x -> pure_return x
  | Op k ->
    pure_bind (fun p -> forall x. p x) (fun x -> stheta (k x))
  | Require pre k -> pure_bind (fun p -> pre /\ p (() <: squash pre)) (fun r -> stheta (k r))

let dm (a:Type) (wp:pure_wp a) =
  m:(free_req a){stheta m ⊑ wp}

let dm_return (x:'a) : dm 'a (pure_return x) = Return x

let dm_bind (#a:Type u#a) (#b:Type u#b) (#wp1:pure_wp a) (#wp2:a -> pure_wp b)
  (m:dm a wp1)
  (k:(x:a -> dm b (wp2 x))) :
  dm b (pure_bind wp1 wp2) =
  admit ();
  free_req_bind m k

let dm_subcomp (#a:Type u#a) (#wp1:pure_wp a) (#wp2:pure_wp a) (m:dm a wp1) : Pure (dm a wp2) (requires (forall p. wp2 p ==> wp1 p)) (ensures fun _ -> True) = m

class source (t:Type) = { [@@@no_method] _empty : unit }

instance source_int : source int = { _empty = () }

instance source_pair (t1:Type) {| source t1 |} (t2:Type) {| source t2 |} : source (t1 * t2) = { _empty = () }

instance source_arrow
  (t1:Type) {| source t1 |}
  (t2:t1 -> Type) {| (x:t1) -> source (t2 x) |}
  (wp:(x:t1) -> pure_wp (t2 x)) : 
  source (x:t1 -> dm (t2 x) (wp x)) = { _empty = () }

let test0 : source (x:int -> dm int (as_pure_wp (fun p -> x > 5 /\ (forall r. p r)))) =
  source_arrow int (fun _ -> int) (fun x -> (as_pure_wp (fun p -> x > 5 /\ (forall r. p r))))

let test1 : source (x:int -> dm (y:int -> dm int (fun p -> x == y /\ (forall r. p r))) (fun p -> x > 5 /\ (forall r. p r))) =
  source_arrow
    int _ #(fun x -> source_arrow int (fun _ -> int)
    (fun y -> as_pure_wp (fun p -> x == y /\ (forall r. p r))))
    (fun x -> as_pure_wp (fun p -> x > 5 /\ (forall r. p r)))

let test2 : source ((y:int -> dm int (fun p -> y > 2 /\ (forall r. p r))) -> dm int (fun p -> (forall r. p r))) =
  source_arrow
    _ #(source_arrow int (fun _ -> int) (fun y p -> y > 2 /\ (forall r. p r)))
    (fun _ -> int)
    (fun _ p -> (forall r. p r))

(** *** Source language has a fixed wp **)
let fixed_wp (#a:Type) : pure_wp a = fun p -> forall r. p r

(** *** Target monad : a Free Monad with less constructors **)
noeq
type free (a:Type u#a) : Type u#a =
| Call : (beta -> free a) -> free a
| Ret : a -> free a

let free_return (x:'a) : free 'a = Ret x

let rec free_bind (m:free 'a) (k:'a -> free 'b) : free 'b =
  match m with
  | Ret x -> k x
  | Call cont -> Call (fun b -> free_bind (cont b) k)

let rec ttheta (m:free 'a) : pure_wp 'a =
  match m with
  | Ret x -> pure_return x
  | Call k ->
    pure_bind (fun p -> forall x. p x) (fun x -> ttheta (k x))

class target (t:Type) = { [@@@no_method] _empty : unit }

instance target_int : target int = { _empty = () }

instance target_pair (t1:Type) {| target t1 |} (t2:Type) {| target t2 |} : target (t1 * t2) = { _empty = () }

instance target_arrow (t1:Type) {| target t1 |} (t2:Type) {| target t2 |} : target (x:t1 -> free t2) = { _empty = () }

(** *** Handlers: lift, erase **)
let rec lift_handler (m:free 'a) : dm 'a fixed_wp =
  match m with
  | Ret x -> Return x
  | Call k -> Op (fun x -> lift_handler (k x))

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
type sem 'a = 'a -> Type0

let eq_beh (#a:Type u#a) (#b:Type u#b) (rel:a -> b -> Type0) (w1:sem a) (w2:sem b): Type0 =
  forall r1 r2. r1 `rel` r2 ==> (w1 r1 <==> w2 r2)

let behS (m:dm 'a 'wp) : sem 'a =
  pure_predicate_transformer (stheta m)
let behT (m:free 'a) : sem 'a = 
  pure_predicate_transformer (ttheta m)

let eq_beh_reflexivity (#a:Type u#a) (w:sem a) : 
  Lemma (w `eq_beh (==)` w) by (norm [delta_only [`%eq_beh]]) = ()

let eq_beh_under_bind (#a:Type u#a) (#b:Type u#b) (m:sem a) (k:a -> sem b) (k':a -> sem b) : 
  Lemma 
    (requires (forall x. (k x) `eq_beh (==)` (k' x)))
    (ensures ((fun r -> exists x. k x r) `eq_beh (==)` (fun r' -> exists x'. k' x' r'))) = ()

let behS_pre (m:dm 'a (fun p -> forall r. p r)) (pre:Type0) (_:squash pre) :
  Lemma ( (fun r -> forall p. pre /\ stheta m p ==> p r)
          `eq_beh (==)`
          (fun r -> forall p. stheta m p ==> p r)) = ()

open FStar.Calc

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
        end;
        admit ()
      }
      Call (fun x -> k x);
      == {
        (** function extensionality **)
        admit ()
      }
      Call k;
    }

let erase_preserves_beh (w:dm 'a fixed_wp) :
  Lemma (behS w `eq_beh (==)` behT (erase_handler w)) =
  lemma_ttheta_erase_stronger_stheta w;
  lemma_stheta_stronger_ttheta_erase w

let lift_preserves_beh (w:free 'a) :
  Lemma (behT w `eq_beh (==)` behS (lift_handler w)) =
  lemma_stheta_lift_stronger_ttheta w;
  lemma_ttheta_stronger_stheta_lift w

let lemma_erase_inverse_lift_semantic (m:free 'a) :
  Lemma (behT (erase_handler (lift_handler m)) `eq_beh (==)` behT m) =
  lift_preserves_beh m;
  erase_preserves_beh (lift_handler m)

let lemma_lift_inverse_erase_semantic (m:dm 'a fixed_wp) :
  Lemma (behS (lift_handler (erase_handler m)) `eq_beh (==)` behS m) =
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

let erase_result_preserves_beh (w:free 'a) {| c1:eraseable 'a |} :
  Lemma (behT w `eq_beh (fun (x:'a) (y:c1.t) -> y == c1.erase x)` behT (free_bind w (fun r -> free_return (c1.erase r)))) = admit ()

let sem_transitivity (w1 w2:sem 'a) (w3:sem 'b) (f:'a -> 'b) :
  Lemma (requires (w1 `eq_beh (==)` w2 /\ w2 `eq_beh (fun x y -> y == f x)` w3))
        (ensures (w1 `eq_beh (fun x y -> y == f x)` w3)) = admit ()

let cc_whole (w:dm 'a fixed_wp) {| c1:eraseable 'a |} :
  Lemma (behS w `eq_beh (fun (x:'a) (y:c1.t) -> y == c1.erase x)` behT (free_bind (erase_handler w) (fun r -> free_return (c1.erase r)))) =
  erase_preserves_beh w;
  erase_result_preserves_beh (erase_handler w) #c1;
  sem_transitivity #'a (behS w) (behT (erase_handler w)) (behT (free_bind (erase_handler w) (fun r -> free_return (c1.erase r)))) c1.erase
  
let sc (ps:(int -> dm int fixed_wp) -> dm int fixed_wp) (ct:int -> free int) : Type0 =
  behS (ps ((liftable_arrow int int).lift ct)) `eq_beh (fun x y -> y == x)` behT (((eraseable_arrow (int -> free int) _ #(liftable_arrow int int)).erase ps) ct)

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
  behT (ct ((eraseable_arrow int int).erase ps)) `eq_beh (fun x y -> y == x)`
  behS (((liftable_arrow (int -> dm int fixed_wp) int #(eraseable_arrow int int #liftable_int #eraseable_int)).lift ct) ps)

let lift_result_preserves_beh (w:dm 'a (fun p -> forall r. p r)) {| c1:liftable 'a |} :
  Lemma (behS w `eq_beh (fun (x:'a) (y:c1.s) -> y == c1.lift x)` behS (dm_bind w (fun r -> dm_return (c1.lift r)))) = admit ()

let btc_whole (w:free 'a) {| c1:liftable 'a |} :
  Lemma (behT w `eq_beh (fun (x:'a) (y:c1.s) -> y == c1.lift x)` behS (dm_subcomp #_ #_ #fixed_wp (dm_bind (lift_handler w) (fun r -> dm_return (c1.lift r))))) =
  lift_preserves_beh w;
  lift_result_preserves_beh (lift_handler w) #c1;
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
