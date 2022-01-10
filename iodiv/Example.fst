module Example

type unit : Type = unit

type repr (a:Type) (p:pure_pre) (q:pure_post a) = squash p -> v:a{q v}

unfold
let trivial_pre : pure_pre = True

unfold
let return_post (#a:Type) (x:a) : pure_post a = fun r -> r == x

let return (a:Type) (x:a) : repr a trivial_pre (return_post x) = fun _ -> x

unfold
let bind_pre (#a:Type) (p1:pure_pre) (p2:pure_post a) (q1:a -> pure_pre)
  : pure_pre
  = p1 /\ (forall x. q1 x ==> p2 x)

unfold
let bind_post (#a #b:Type) (q1:pure_post a) (q2:a -> pure_post b)
  : pure_post b
  = fun y -> exists x. q1 x /\ q2 x y

let bind (a b:Type)
  (p1:pure_pre) (q1:pure_post a)
  (p2:a -> pure_pre) (q2:a -> pure_post b)
  (f:repr a p1 q1) (g:(x:a -> repr b (p2 x) (q2 x)))
  : repr b (bind_pre p1 p2 q1) (bind_post q1 q2)
  = fun _ ->
    let x = f () in
    g x ()
let subcomp (a:Type) (p1 p2:pure_pre) (q1 q2:pure_post a)
  (f:repr a p1 q1)
  : Pure (repr a p2 q2) (requires (p2 ==> p1 /\ (forall x. q1 x ==> q2 x)))
                        (ensures fun _ -> True)
  = fun _ -> f ()


effect {
  M (a:Type) (p:pure_pre) (q:pure_post a)
  with { repr; return; bind; subcomp }
}

unfold
let lift_PURE_M (a:Type) (wp:pure_wp a) (f:unit -> PURE a wp)
  : repr a (as_requires wp) (as_ensures wp)
  = fun _ ->
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    f ()

sub_effect PURE ~> M = lift_PURE_M

assume val p : prop
assume val pure_lemma (_:unit) : Lemma p
assume val some_f (_:squash p) : M int True (fun _ -> True)

let test () : M int True (fun _ -> True) =
  pure_lemma ();
  some_f ()
