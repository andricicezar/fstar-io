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

let rec theta (m:free_req 'a) : pure_wp 'a =
  match m with
  | Return x -> pure_return x
  | Op k ->
    pure_bind (fun p -> forall x. p x) (fun x -> theta (k x))
  | Require pre k -> pure_bind (fun p -> pre /\ p (() <: squash pre)) (fun r -> theta (k r))

let dm (a:Type) (wp:pure_wp a) =
  m:(free_req a){forall p. wp p ==> theta m p}

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

let rec theta_free (m:free 'a) : pure_wp 'a =
  match m with
  | Ret x -> pure_return x
  | Call k ->
    pure_bind (fun p -> forall x. p x) (fun x -> theta_free (k x))

class target (t:Type) = { [@@@no_method] _empty : unit }

instance target_int : target int = { _empty = () }

instance target_pair (t1:Type) {| target t1 |} (t2:Type) {| target t2 |} : target (t1 * t2) = { _empty = () }

instance target_arrow (t1:Type) {| target t1 |} (t2:Type) {| target t2 |} : target (x:t1 -> free t2) = { _empty = () }

(** *** Semantics **)
type sem 'a = 'a -> Type0

let eq_beh (#a:Type u#a) (#b:Type u#b) (rel:a -> b -> Type0) (w1:sem a) (w2:sem b): Type0 =
  forall r1 r2. r1 `rel` r2 ==> (w1 r1 <==> w2 r2)

let test1234 #a #b (k k':b -> sem a) (r:a) :
  Lemma (requires (forall x. (k x r <==> k' x r)))
        (ensures ((forall x. k x r) <==> (forall x. k' x r))) = ()

let behS (m:dm 'a 'wp) : sem 'a = fun r -> forall p. theta m p ==> p r
let behT (m:free 'a) : sem 'a = fun r -> forall p. theta_free m p ==> p r
(** forall r. (forall x. behS (k x) r) <==> (forall x. behT (k x) r) **)

(**
CA: I tried this simpler definition, but in proving that handle preserves the behavior,
one has to prove:
  forall r. (forall x. behS (k x) r) <==> (exists x. behT (k x) r)
which I did not know how to prove.
let rec behT (m:free 'a) : sem 'a = 
  match m with
  | Ret x -> fun r -> r == x
  | Call k -> fun r -> (exists x. behT (k x) r)
**)

let eq_beh_reflexivity (#a:Type u#a) (w:sem a) : 
  Lemma (w `eq_beh (==)` w) by (norm [delta_only [`%eq_beh]]) = ()

let eq_beh_under_bind (#a:Type u#a) (#b:Type u#b) (m:sem a) (k:a -> sem b) (k':a -> sem b) : 
  Lemma 
    (requires (forall x. (k x) `eq_beh (==)` (k' x)))
    (ensures ((fun r -> exists x. k x r) `eq_beh (==)` (fun r' -> exists x'. k' x' r'))) = ()

let behS_pre (m:dm 'a (fun p -> forall r. p r)) (pre:Type0) (_:squash pre) :
  Lemma ( (fun r -> forall p. pre /\ theta m p ==> p r)
          `eq_beh (==)`
          (fun r -> forall p. theta m p ==> p r)) = ()

let eq_behs_under_bind (#a:Type u#a) (#b:Type u#b) (m:pure_wp a) (k:a -> pure_wp b) (k':a -> pure_wp b) : 
  Lemma 
    (requires (forall x. (fun r -> forall p. (k x) p ==> p r) `eq_beh (==)` (fun r -> forall p. (k' x) p ==> p r)))
    (ensures ((fun r -> forall p. pure_bind m k p ==> p r) `eq_beh (==)` (fun r -> forall p. pure_bind m k' p ==> p r)))  = 
  assert (forall r x. (forall p. (k x) p ==> p r) <==> (forall p. (k' x) p ==> p r)) by (
          binder_retype (nth_binder (-1)); norm [delta_only [`%eq_beh]; zeta;iota]; trefl ());
  introduce forall r1 r2. r1 == r2 ==> ((forall p. pure_bind m k p ==> p r1) <==> (forall p. pure_bind m k' p ==> p r2)) with begin
    introduce r1 == r2 ==> ((forall p. pure_bind m k p ==> p r1) <==> (forall p. pure_bind m k' p ==> p r2)) with _. begin
      let r = r1 in
      assert (forall x. (forall p. (k x) p ==> p r) <==> (forall p. (k' x) p ==> p r));
      introduce (forall p. pure_bind m k p ==> p r) ==> (forall p. pure_bind m k' p ==> p r) with _. begin
        introduce forall p. pure_bind m k' p ==> p r with begin
          assert (pure_bind m k p ==> p r);
          introduce pure_bind m k' p ==> p r with _. begin
            assert (pure_wp_monotonic0 _ m);
            let lhs : pure_post a = fun xx -> k' xx p in
            let rhs : pure_post a = fun xx -> k xx p in
            introduce forall xx. lhs xx ==> rhs xx with begin
              introduce lhs xx ==> rhs xx with _. begin
                assert (k' xx p);
                assert ((forall p. (k xx) p ==> p r) <==> (forall p. (k' xx) p ==> p r));
                assume (k xx p);
              end
            end;
            assert (pure_bind m k' p ==> pure_bind m k p);
            eliminate pure_bind m k p ==> p r with ()
          end
        end
      end;
      admit ()
    end
  end

let rec lift_m (m:free 'a) : dm 'a fixed_wp =
  match m with
  | Ret x -> Return x
  | Call k -> Op (fun x -> lift_m (k x))

let rec handle_m (m:dm 'a fixed_wp) : free 'a =
  match m with
  | Return x -> Ret x
  | Require pre k -> begin
    assert (theta m (fun r -> True));
    assert (pre);
    handle_m (k ())
  end
  | Op k -> Call (fun x -> handle_m (k x))

open FStar.Calc

let rec lemma_handle_inverse_lift_syntactic (m:free 'a) :
  Lemma (handle_m (lift_m m) == m) =
  match m with
  | Ret x -> ()
  | Call k -> 

    calc (==) {
      handle_m (lift_m (Call k));
      == { _ by (norm [delta_only [`%lift_m]; zeta; iota]) }
      handle_m (Op (fun x -> lift_m (k x)));
      == { _ by (norm [delta_only [`%handle_m]; zeta; iota]) }
      Call (fun x -> handle_m (lift_m (k x)));
      == {
        introduce forall x. handle_m (lift_m (k x)) == k x with begin
          lemma_handle_inverse_lift_syntactic (k x)
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

let rec handle_preserves_beh (w:dm 'a fixed_wp) :
  Lemma (behS w `eq_beh (==)` behT (handle_m w)) = 
  match w with 
  | Return x -> ()
  | Require pre k ->
    assert (theta w (fun r -> True));
    handle_preserves_beh (k ())
  | Op k ->
    introduce forall r1 r2. r1 == r2 ==> ((behS w r1) <==> (behT (handle_m w) r2)) with begin
      introduce r1 == r2 ==> ((behS w r1) <==> (behT (handle_m w) r2)) with _. begin
        let r = r1 in
        assert (behS #_ #fixed_wp (Op k) r <==> (forall p. (forall x. theta (k x) p) ==> p r));
        assert (behT (handle_m (Op k)) r <==> (forall p. (forall x. theta_free (handle_m (k x)) p) ==> p r)) by (
          norm [delta_only [`%behT;`%handle_m;`%theta_free];zeta;iota]);
        introduce forall x. behS #_ #fixed_wp (k x) r <==> behT (handle_m (k x)) r with begin
          handle_preserves_beh (k x);
          assert (behS #_ #fixed_wp (k x) `eq_beh (==)` behT (handle_m (k x)));
          assert (forall r1 r2. r1 == r2 ==> (behS #_ #fixed_wp (k x) r1 <==> behT (handle_m (k x)) r2)) by (
            binder_retype (nth_binder (-5)); norm [delta_only [`%eq_beh]; zeta;iota]; trefl ();
            assumption ()
          )
        end;
        // having:
        assert ((forall p x. (theta (k x) p ==> p r)) <==> (forall p x. theta_free (handle_m (k x)) p ==> p r));
        // needing: 
        assume ((forall p. (forall x. theta (k x) p) ==> p r) <==> (forall p. (forall x. theta_free (handle_m (k x)) p) ==> p r))
        (**introduce (forall p. (forall x. theta (k x) p) ==> p r) ==> (forall p. (forall x. theta_free (handle_m (k x)) p) ==> p r) with h1. begin
          introduce forall p. (forall x. theta_free (handle_m (k x)) p) ==> p r with begin
            eliminate forall p. (forall x. theta (k x) p) ==> p r with p;
            introduce (forall x. theta_free (handle_m (k x)) p) ==> p r with h2. begin
              test1234 #'a #beta (fun x -> behS #'a #fixed_wp (k x)) (fun x -> behT (handle_m (k x))) r;
              assert ((forall p x. (theta (k x) p ==> p r)) ==> (forall p x. theta_free (handle_m (k x)) p ==> p r));
              assert ((forall p x. theta_free (handle_m (k x)) p ==> p r) ==> (forall p x. (theta (k x) p ==> p r)));
              eliminate (forall x. theta (k x) p) ==> p r with begin
                introduce forall x. theta (k x) p with begin
                  assert (forall x. theta_free (handle_m (k x)) p);
 //                 assert (forall p. theta_free (handle_m (k x)) p ==> p r);
                  assume (theta (k x) p)
                end
              end
            end
          end
        end;**)
      end
    end
    
    

let lift_preserves_beh (w:free 'a) :
  Lemma (behT w `eq_beh (==)` behS (lift_m w)) = admit ()

let rec lemma_handle_inverse_lift_semantic (m:free 'a) :
  Lemma (behT (handle_m (lift_m m)) `eq_beh (==)` behT m) =
  match m with
  | Ret x -> assert (behT (handle_m (lift_m (Ret x))) `eq_beh (==)` behT (Ret x)) by (compute ())
  | Call k -> begin
    introduce forall x. (behT (handle_m (lift_m (k x))) `eq_beh (==)` behT (k x)) with begin
      lemma_handle_inverse_lift_semantic (k x)
    end;
    assert (behT (Call (fun x -> handle_m (lift_m (k x)))) `eq_beh (==)` behT (Call k)) by (
        norm [delta_only [`%behT;`%theta_free];zeta;iota];
        apply_lemma (`eq_behs_under_bind);
        norm [iota];
        assumption ()
    );
    assert (behT (handle_m (lift_m (Call k))) `eq_beh (==)` behT (Call (fun x -> handle_m (lift_m (k x))))) by (compute ())
  end

let rec lemma_lift_inverse_handle_semantic (m:dm 'a fixed_wp) :
  Lemma (behS (lift_m (handle_m m)) `eq_beh (==)` behS m) =
  match m with
  | Return x -> assert (behS (lift_m (handle_m m)) `eq_beh (==)` behS m) by (compute ())
  | Require pre k -> begin
    assert (theta m (fun r -> True));
    lemma_lift_inverse_handle_semantic (k ())
  end
  | Op k -> 
    introduce forall x. (behS (lift_m (handle_m (k x))) `eq_beh (==)` (behS #'a #fixed_wp (k x))) with begin
      lemma_lift_inverse_handle_semantic (k x)
    end;
    assert (behS #_ #fixed_wp (Op (fun x -> lift_m (handle_m (k x)))) `eq_beh (==)` behS #_ #(fun p -> forall r. p r) (Op k)) by (
        norm [delta_only [`%behS;`%theta];zeta;iota];
        apply_lemma (`eq_behs_under_bind);
        norm [iota];
        assumption ()
    );
    assert (behS (lift_m (handle_m (Op k))) `eq_beh (==)` behS #_ #fixed_wp (Op (fun x -> lift_m (handle_m (k x))))) by (compute ());
    ()

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

class handleable (s:Type u#a) = {
  [@@@no_method]
  s_tc : source s;

  [@@@no_method]
  t : Type u#b;
  [@@@no_method]
  t_tc : target t;

  handle : s -> t;
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

instance liftable_arrow (s1 t2:Type) {| c1:handleable s1 |} {| c2:liftable t2 |} : liftable (c1.t -> free t2) = {
  t_tc = target_arrow c1.t #c1.t_tc t2 #c2.t_tc;
  s = s1 -> dm c2.s fixed_wp;
  s_tc = source_arrow s1 #c1.s_tc (fun _ -> c2.s) #(fun _ -> c2.s_tc) (fun x p -> forall r. p r);

  lift = (fun (f:c1.t -> free t2) (x:s1) -> 
    dm_subcomp #_ #_ #fixed_wp (dm_bind (lift_m #t2 (f (c1.handle x))) (fun (r:t2) -> dm_return (c2.lift r)))
  );
}

instance handleable_int : handleable int = {
  t = int;
  t_tc = solve;
  s_tc = solve;

  handle = (fun x -> x);
}

instance handleable_arrow (t1 s2:Type) {| c1:liftable t1 |} {| c2:handleable s2 |} : handleable (c1.s -> dm s2 fixed_wp) = {
  t_tc = target_arrow t1 #c1.t_tc c2.t #c2.t_tc;
  t = t1 -> free c2.t;
  s_tc = source_arrow c1.s #c1.s_tc (fun _ -> s2) #(fun _ -> c2.s_tc) (fun x p -> forall r. p r);

  handle = (fun f (x:t1) ->
    free_bind (handle_m (f (c1.lift x))) (fun (r:s2) -> free_return (c2.handle r))
  )
}

let handle_result_preserves_beh (w:free 'a) {| c1:handleable 'a |} :
  Lemma (behT w `eq_beh (fun (x:'a) (y:c1.t) -> y == c1.handle x)` behT (free_bind w (fun r -> free_return (c1.handle r)))) = admit ()

let sem_transitivity (w1 w2:sem 'a) (w3:sem 'b) (f:'a -> 'b) :
  Lemma (requires (w1 `eq_beh (==)` w2 /\ w2 `eq_beh (fun x y -> y == f x)` w3))
        (ensures (w1 `eq_beh (fun x y -> y == f x)` w3)) = admit ()

let cc_whole (w:dm 'a fixed_wp) {| c1:handleable 'a |} :
  Lemma (behS w `eq_beh (fun (x:'a) (y:c1.t) -> y == c1.handle x)` behT (free_bind (handle_m w) (fun r -> free_return (c1.handle r)))) =
  handle_preserves_beh w;
  handle_result_preserves_beh (handle_m w) #c1;
  sem_transitivity #'a (behS w) (behT (handle_m w)) (behT (free_bind (handle_m w) (fun r -> free_return (c1.handle r)))) c1.handle
  
let sc (ps:(int -> dm int fixed_wp) -> dm int fixed_wp) (ct:int -> free int) : Type0 =
  behS (ps ((liftable_arrow int int).lift ct)) `eq_beh (fun x y -> y == x)` behT (((handleable_arrow (int -> free int) _ #(liftable_arrow int int)).handle ps) ct)

open FStar.Tactics

let sc_proof ps ct : Lemma (sc ps ct) 
  by (
    norm [delta_only [`%Mkhandleable?.handle;`%handleable_int]; zeta; iota];
    explode ();
    let x = nth_binder (-3) in
    let x = instantiate x (fresh_uvar None) in
    mapply x;
    norm [delta_only [`%sc;
      `%handleable_arrow;`%target_arrow; `%source_arrow; 
      `%Mkhandleable?.handle;`%handleable_int]; zeta; iota
    ];
    assumption ()
  )
  = cc_whole (ps ((liftable_arrow int int).lift ct)) #handleable_int

let sc' (ct:(int -> free int) -> free int) (ps:int -> dm int fixed_wp) : Type0 =
  behT (ct ((handleable_arrow int int).handle ps)) `eq_beh (fun x y -> y == x)`
  behS (((liftable_arrow (int -> dm int fixed_wp) int #(handleable_arrow int int #liftable_int #handleable_int)).lift ct) ps)

let lift_result_preserves_beh (w:dm 'a (fun p -> forall r. p r)) {| c1:liftable 'a |} :
  Lemma (behS w `eq_beh (fun (x:'a) (y:c1.s) -> y == c1.lift x)` behS (dm_bind w (fun r -> dm_return (c1.lift r)))) = admit ()

let btc_whole (w:free 'a) {| c1:liftable 'a |} :
  Lemma (behT w `eq_beh (fun (x:'a) (y:c1.s) -> y == c1.lift x)` behS (dm_subcomp #_ #_ #fixed_wp (dm_bind (lift_m w) (fun r -> dm_return (c1.lift r))))) =
  lift_preserves_beh w;
  lift_result_preserves_beh (lift_m w) #c1;
  sem_transitivity #'a (behT w) (behS (lift_m w)) (behS (dm_bind (lift_m w) (fun r -> dm_return (c1.lift r)))) c1.lift

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
  = btc_whole (ct ((handleable_arrow int int).handle ps)) #liftable_int
