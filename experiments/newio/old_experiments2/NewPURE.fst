module NewPURE

open FStar.Tactics

(** Some notes:
  1. using this method does not seem to add any advantage related to lifts, because
     lifts anyway do not reify the Pure computation **)

let theta (a:Type) (m:a) : pure_wp a = FStar.Pervasives.pure_return a m

type value (a:Type) (wp:pure_wp a) = x:a{forall p. wp p ==> theta a x p}

let return_value (a:Type) (x:a) : value a (FStar.Pervasives.pure_return a x) = x

let return_of_value (#a:Type) (x:a) (#wp:pure_wp a) (m:value a wp) : Type0 = x == m
  
let bind_value
  (a b:Type)
  (lwp:pure_wp a)
  (kwp:a -> pure_wp b)
  (l:value a lwp)
  (k:(x:a{x `return_of_value` l} -> value b (kwp x))) : 
  value b  (FStar.Pervasives.pure_bind_wp a b lwp kwp) =
  k l

let subcomp_value (a:Type) (wp1:pure_wp a) (wp2:pure_wp a) (l:value a wp1) : 
  Pure (value a wp2) (requires (forall p. wp2 p ==> wp1 p)) (ensures (fun _ -> True)) =
  l

type pure (a:Type) (wp:pure_wp a) =
   pre:Type0 { forall p. wp p ==> pre } & (_:unit{pre} -> value a wp) 

let return_pure (a:Type) (x:a) : pure a (FStar.Pervasives.pure_return a x) = 
  (| True, (fun () -> return_value a x) |)

let get_pre #a #wp (t : pure a wp) : (r:Type0{forall p. wp p ==> r}) =
  let (| pre , f |) = t in pre

let get_fun #a #wp (t : pure a wp) (_:unit{get_pre t}) : value a wp =
  let (| pre, f |) = t in f ()

(** I think this return_of_pure refinement on bind is needed to be able to write
    other representations on top of pure **)
(**
let return_of_pure (a:Type) (x:a) (#wp:pure_wp a) (l:pure a wp) =
  let pre = get_pre l in
  assert (forall p. wp p ==> pre);
  assert (forall p. pre /\ wp p ==> theta a (get_fun l ()) p);
  return_of_value x (get_fun l ()) **)

let bind_pure 
  (a b:Type)
  (lwp:pure_wp a)
  (kwp:a -> pure_wp b)
  (l:pure a lwp)
  (k:(x:a -> pure b (kwp x))) : 
  pure b (FStar.Pervasives.pure_bind_wp a b lwp kwp) =
  (| (get_pre l /\ get_pre (k (get_fun l ()))), 
     (fun (_:unit{(get_pre l /\ get_pre (k (get_fun l ())))}) -> 
       bind_value a b lwp kwp (get_fun l ()) (fun x -> get_fun (k x) ())) |)

let subcomp_pure
  (a:Type)
  (wp1:pure_wp a)
  (wp2:pure_wp a)
  (l:pure a wp1) : 
  Pure (pure a wp2) (requires (forall p. wp2 p ==> wp1 p)) (ensures (fun _ -> True)) =
  (| get_pre l, (fun _ -> subcomp_value a wp1 wp2 (get_fun l ())) |)

let if_then_else_pure
  (a:Type)
  (wp1:pure_wp a)
  (wp2:pure_wp a)
  (f:pure a wp1)
  (g:pure a wp2)
  (b:bool) :
  Type = 
  pure a (pure_if_then_else a b wp1 wp2)

let lemma_wp_implies_as_requires #a (wp:pure_wp a) :
  Lemma (forall (p:pure_post a). wp p ==> as_requires wp) =
    assert (forall (p:pure_post a) x. p x ==> True) ;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp ;
    assert (forall (p:pure_post a). wp (fun x -> p x) ==> wp (fun _ -> True))

total
reifiable
reflectable
effect {
  NewPURE (a:Type) (wp : pure_wp a) 
  with {
       repr       = pure
     ; return     = return_pure
     ; bind       = bind_pure
     ; subcomp    = subcomp_pure
     ; if_then_else = if_then_else_pure
     }
}

let lift_pure_pure (a : Type) 
  (w : pure_wp a)
  (f:(eqtype_as_type unit -> Prims.PURE a w)) : 
  pure a w =
  lemma_wp_implies_as_requires w;
  (| as_requires w, (fun _ -> 
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    let r = f () in
    let r' = return_value _ r in
    subcomp_value _ _ _ r' ) |)
  
sub_effect Prims.PURE ~> NewPURE = lift_pure_pure

(** [Pure] is a Hoare-style counterpart of [PURE]
    
    Note the type of post, which allows to assume the precondition
    for the well-formedness of the postcondition. c.f. #57 *)
unfold
let prepost_as_wp (a: Type) (pre: pure_pre) (post: pure_post' a pre) : pure_wp a by (explode ())=
  fun (p: pure_post a) -> pre /\ (forall (pure_result: a). post pure_result ==> p pure_result)

effect NewPure (a: Type) (pre: pure_pre) (post: pure_post' a pre) =
  NewPURE a (prepost_as_wp a pre post)

effect NewTot (a: Type) = NewPURE a (pure_null_wp a)


let test_sum (x y:int) : NewPure int (x == 7) (fun s -> s == x + y) =
  x + y

let test () : NewTot unit = 
  let _ = test_sum 7 10 in
  ()

let rec fibbonaci (n:int) : NewPure int (n >= 0) (fun r -> r >= 0) =
  if n = 0 then 0
  else (if n = 1 then 1
  else fibbonaci (n - 1) + fibbonaci (n - 2))
