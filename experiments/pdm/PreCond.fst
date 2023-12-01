module PreCond

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.Calc

open FStar.Tactics

let precond (a:Type) = pre:pure_pre & (squash pre -> a)

let ret_precond #a (x:a) : precond a =
  (| True, (fun _ -> x) |)

let pre_of #a (t : precond a) : pure_pre =
  let (| pre , f |) = t in pre

let val_of #a (t : precond a) : Pure a (requires pre_of t) (ensures fun _ -> True) =
  let (| pre, f |) = t in f ()

let bind_precond #a #b (m:precond a) (f:a -> precond b) : precond b =
  (| (pre_of m /\ (forall x. x == val_of m ==> pre_of (f x))), 
     (fun _ -> val_of (f (val_of m))) |)

let req_precond (pre:pure_pre) : precond (squash pre) =
  (| pre, (fun x -> x) |)

let theta_precond #a (m:precond a) : pure_wp a =
  let wp : pure_wp' a = fun p -> pre_of m /\ (forall x. x == val_of m ==> p x) in
  FStar.Monotonic.Pure.as_pure_wp wp

type pdm_pure (a:Type) (wp:pure_wp a) =
  m:precond a{forall p. wp p ==> theta_precond m p}

let ret_pdm_pure (a:Type) (x:a) : pdm_pure a (FStar.Pervasives.pure_return a x) = 
  ret_precond x

let bind_pdm_pure 
  (a b:Type)
  (lwp:pure_wp a)
  (kwp:a -> pure_wp b)
  (l:pdm_pure a lwp)
  (k:(x:a -> pdm_pure b (kwp x))) : 
  pdm_pure b (FStar.Pervasives.pure_bind_wp a b lwp kwp) =
  bind_precond l k

let subcomp_pdm_pure
  (a:Type)
  (wp1:pure_wp a)
  (wp2:pure_wp a)
  (l:pdm_pure a wp1) : 
  Pure (pdm_pure a wp2) (requires (forall p. wp2 p ==> wp1 p)) (ensures (fun _ -> True)) =
  (| pre_of l, (fun _ -> (val_of l)) |)

let w_req (p : Type0) : pure_wp (squash p) =
  FStar.Monotonic.Pure.as_pure_wp (fun post -> p /\ post (Squash.get_proof p))

let req_pdm_pure (pre:pure_pre) : pdm_pure (squash pre) (w_req pre) =
  req_precond pre

let if_then_else_pdm_pure
  (a:Type)
  (wp1:pure_wp a)
  (wp2:pure_wp a)
  (f:pdm_pure a wp1)
  (g:pdm_pure a wp2)
  (b:bool) :
  Type = 
  pdm_pure a (pure_if_then_else a b wp1 wp2)

let lemma_wp_implies_as_requires #a (wp:pure_wp a) :
  Lemma (forall (p:pure_post a). wp p ==> as_requires wp) =
    assert (forall (p:pure_post a) x. p x ==> True) ;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp ;
    assert (forall (p:pure_post a). wp (fun x -> p x) ==> wp (fun _ -> True))

total
reifiable
reflectable
effect {
  PreCOND (a:Type) (wp : pure_wp a) 
  with {
       repr       = pdm_pure
     ; return     = ret_pdm_pure
     ; bind       = bind_pdm_pure
     ; subcomp    = subcomp_pdm_pure
     ; if_then_else = if_then_else_pdm_pure
     }
}

let elim_pure #a #w (f : unit -> PURE a w) :
  Pure
    a
    (requires w (fun _ -> True))
    (ensures fun r -> forall post. w post ==> post r) =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall () ;
  f ()

let lift_pure_precond (a : Type) 
  (w : pure_wp a)
  (f:(eqtype_as_type unit -> Prims.PURE a w)) : 
  pdm_pure a w =
  let r = 
  bind_pdm_pure _ _ _ _
    (req_pdm_pure (as_requires w)) 
    (fun _ -> ret_pdm_pure a (elim_pure #a #w f)) in
  lemma_wp_implies_as_requires w;
  subcomp_pdm_pure _ _ _ r
  
sub_effect Prims.PURE ~> PreCOND = lift_pure_precond

(** [Pure] is a Hoare-style counterpart of [PURE]
    
    Note the type of post, which allows to assume the precondition
    for the well-formedness of the postcondition. c.f. #57 *)
unfold
let prepost_as_wp (a: Type) (pre: pure_pre) (post: pure_post' a pre) : pure_wp a =
  FStar.Monotonic.Pure.as_pure_wp (fun (p: pure_post a) -> pre /\ (forall (pure_result: a). post pure_result ==> p pure_result))

effect PreCond (a: Type) (pre: pure_pre) (post: pure_post' a pre) =
  PreCOND a (prepost_as_wp a pre post)

effect PreTot (a: Type) = PreCOND a (pure_null_wp a)

let test_sum (x y:int) : PreCond int (x == 7) (fun s -> s == x + y) =
  x + y

let test () : PreTot unit = 
  let _ = test_sum 7 10 in
  ()

let rec fibbonaci (n:int) : PreCond int (n >= 0) (fun r -> r >= 0) =
  if n = 0 then 0
  else (if n = 1 then 1
  else fibbonaci (n - 1) + fibbonaci (n - 2))

let test_assert p : PreCond unit (requires p) (ensures fun r -> True) =
  assert p

let partial_match (l : list nat) : PreCond unit (requires l <> []) (ensures fun r -> True) =
  match l with
  | x :: r -> ()

assume val p : Type0
assume val p' : Type0
assume val pure_lemma (_ : unit) : Lemma p
assume val some_f (_ : squash p) : PreCond unit (requires True) (ensures fun _ -> True)
assume val some_f' : unit -> PreCond unit (requires p) (ensures fun _ -> p')

let pure_lemma_test () : PreCond unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;
  some_f ()

let pure_lemma_test2 () : PreCond unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;
  some_f () ;
  some_f' () ;
  assert p'
