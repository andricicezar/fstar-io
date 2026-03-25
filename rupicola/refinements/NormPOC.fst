module NormPOC
(** Minimal PoC: the unifier won't delta-unfold a callee inside a
    definition's body when matching PURE-effect oexp type indices.

    [Pervasives.norm] forces full normalisation before the unifier
    sees the term, working around the limitation.  *)

(* ── oexp: function from empty env, with PURE effect and wp index ───── *)

let env0 = x:nat -> bool
let wp0 (a:Type) = env0 -> pure_wp a
type oexp (a:Type) (wp: wp0 a) = e:env0 -> PURE a (wp e)

unfold let lift (x:'a)
  (#wp: wp0 'a) (#_:squash (forall e. wp e `pure_stronger _` pure_return 'a x))
  : oexp 'a wp
  = fun _ -> x

noeq type witnessed (#a:Type) (#wp: wp0 a) : oexp a wp -> Type =
  | W : (f: oexp a wp) -> witnessed f

type closed #a (#wp: wp0 a) (x:a) =
  proof:squash (forall e. wp e `pure_stronger _` pure_return a x)
  -> witnessed (lift x #wp #proof)

let holds (a:Type) (x:a) =
  wp:(wp0 a) & closed #a #wp x

let mk #a #x (#wp: wp0 a)
  (thk: (proof:squash (forall e. wp e `pure_stronger _` pure_return a x)
     -> witnessed (lift x #wp #proof)))
  : holds a x = (| wp, thk |)

(* ── Tests ────────────────────────────────────────────────────────────── *)

let callee (_:bool) (y:bool) : bool = y
let caller (x:bool) : bool = callee x true

/// Self-contained: the unifier unfolds [callee] fine.
let test_callee ()
  : Tot (holds _ callee)
  = mk #_ #_ #(fun _ -> pure_return _ callee) (fun _ -> W (fun _ -> fun _ y -> y))

/// [caller] calls [callee]. The unifier can't fully reduce it.
[@expect_failure [189]]
let test_caller_fails ()
  : Tot (holds _ caller)
  = mk #_ #caller #(fun _ -> pure_return _ caller) (fun _ -> W (fun _ -> fun _ -> true))

/// Even with the "right" wp, without norm the oexp index match fails.
[@expect_failure [189]]
let test_caller_right_wp_no_norm ()
  : Tot (holds _ caller)
  = mk #_ #caller #(fun _ -> pure_return _ (fun (_:bool) -> true)) (fun _ -> W (fun _ -> fun _ -> true))

/// [Pervasives.norm []] fully reduces [caller] before unification.
let test_caller_norm ()
  : Tot (holds _ caller)
  = mk #_ #(Pervasives.norm [] caller) #(fun _ -> pure_return _ (fun (_:bool) -> true)) (fun _ -> W (fun _ -> fun _ -> true))
