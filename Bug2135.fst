module Bug2135

open FStar.Exn

type maybe (a:Type) = either a exn 

let m4_post a = maybe a -> Type0
let m4_wpty a = m4_post a -> Type0
let w = m4_wpty

unfold
let m4_return_wp (a:Type) (x:a) : m4_wpty a = fun p -> p (Inl x) 

unfold
let compute_post (a b:Type) (kw : a -> m4_wpty b) (p:m4_post b)
  : m4_post a =
      (fun result -> 
        match result with
        | Inl v -> kw v (fun r' -> p r')
        | Inr err -> p (Inr err))

unfold
let m4_bind_wp (a b:Type) (w : m4_wpty a) (kw : a -> m4_wpty b) : m4_wpty b =
  fun p -> w (compute_post a b kw p)

type io (a:Type) = 
| Return : a -> io a

let m4_interpretation #a (m : io a) (p : m4_post a) : Type0 = True

let io_return (a:Type) (x: a) : io a = Return x

// REFINED COMPUTATION MONAD (repr)
let irepr (a:Type) (wp:m4_wpty a) =
  post:m4_post a ->
    Pure (io a)
      (requires (wp post))
      (ensures (fun (t:io a) -> m4_interpretation t post))

let ireturn (a : Type) (x : a) : irepr a (m4_return_wp a x) = fun _ -> io_return a x

unfold
val w_ord (#a : Type) : w a -> w a -> Type0
let w_ord wp1 wp2 = forall p. wp1 p ==> wp2 p

let io_bind (a:Type) (b:Type) (l:io a) (k:a -> io b) : io b =
  match l with
  | Return x -> k x

let ibind (a b : Type) (wp_v : w a) (wp_f: a -> w b) (v : irepr a wp_v)
  (f : (x:a -> irepr b (wp_f x))) : irepr b (m4_bind_wp _ _ wp_v wp_f) =
  fun p -> 
    let t = (io_bind a b
        (v (compute_post a b wp_f p))
        (fun x ->
          assume (wp_f x p);
           f x p)) in
    assume (m4_interpretation t p);
    t

unfold
let isubcomp (a:Type) (wp1 wp2: w a) (f : irepr a wp1) :
  Pure (irepr a wp2) (requires w_ord wp2 wp1) (ensures fun _ -> True) = f

unfold
let wp_if_then_else (#a:Type) (wp1 wp2:w a) (b:bool) : w a =
  fun p -> (b ==> wp1 p) /\ ((~b) ==> wp2 p)

unfold
let i_if_then_else (a : Type) (wp1 wp2 : w a) (f : irepr a wp1) (g : irepr a wp2) (b : bool) : Type =
  irepr a (wp_if_then_else wp1 wp2 b)

total
reifiable
reflectable
layered_effect {
  M4wp : a:Type -> wp : m4_wpty a -> Effect
  with
       repr       = irepr
     ; return     = ireturn
     ; bind       = ibind

     ; subcomp      = isubcomp
     ; if_then_else = i_if_then_else
}
  
let elim_pure #a #wp ($f : unit -> PURE a wp) p
 : Pure a (requires (wp p)) (ensures (fun r -> p r))
 //: PURE a (fun p' -> wp p /\ (forall r. p r ==> p' r))
 // ^ basically this, requires monotonicity
 = FStar.Monotonic.Pure.wp_monotonic_pure ();
   f ()

let lift_pure_m4wp (a:Type) (wp:pure_wp a) (f:(eqtype_as_type unit -> PURE a wp)) :
  Pure (irepr a (fun p -> wp (fun r -> p (Inl r)))) (requires True)
                    (ensures (fun _ -> True))
  = fun p -> let r = elim_pure f (fun r -> p (Inl r)) in io_return _ r

sub_effect PURE ~> M4wp = lift_pure_m4wp

open FStar.Tactics

let reify_reflect
  #t2
  (wp : m4_wpty t2)
  (f:irepr t2 wp) 
  (p:m4_post t2) : 
  Lemma (reify (M4wp?.reflect f) == f) = ()

let reify_reflect_2
  #t2
  (wp : m4_wpty t2)
  (f:irepr t2 wp) 
  (p:m4_post t2) : 
  Lemma
    (requires (wp p))
    (ensures (
    reify (M4wp?.reflect f <: M4wp t2 wp) p == f p)) by (
    explode ();
  
  dump "H") = ()

let iota_not_working 
  #t2
  (wp : m4_wpty t2)
  (f:irepr t2 wp) 
  (p:m4_post t2) : 
  Lemma (requires (wp p)) (ensures (true == true)) =
    calc (==) {
        reify ((M4wp?.reflect (f))) p;
        == { _ by (norm [iota]; dump "h") }
        f p;
    }

let iota_reify_reflect
  #t2
  (wp : m4_wpty t2)
  (f:irepr t2 wp) 
  (p:m4_post t2) : 
  Lemma (requires (wp p)) (ensures (true == true)) =
    calc (==) {
        reify ((M4wp?.reflect (f) <: M4wp t2 wp)) p;
        == { _ by (norm [iota]; dump "h") }
        f p;
    }

let wrapper
  #t1 #t2
  (wp : m4_wpty t2)
  (f:irepr t2 wp) : 
  Tot (option t1 -> M4wp t2 wp) =
  fun x ->
    match x with
    | Some x -> M4wp?.reflect f
    | None -> M4wp?.reflect f

// let lemma
//   #t1 #t2
//   (wp : m4_wpty t2)
//   (f:irepr t2 wp) :
//   Lemma (requires True) (ensures (true == true)) =
//     let ef = wrapper #int wp f in
//     calc (==) {
//       reify (ef (Some 5));
//       == {}
//       reify (
//         match (Some 5) with
//         | Some x -> M4wp?.reflect f <: M4wp t2 wp
//         | None -> M4wp?.reflect f <: M4wp t2 wp
//       );
//     }

let to_option #t1 (x:t1) : option t1 = Some x

let test (x:int) = lift_pure_m4wp (option int) (fun p -> p (to_option x)) (fun _ -> to_option x)

let lemma
  #t1 #t2
  (wp : m4_wpty t2)
  (f:irepr t2 wp)
  (p:m4_post (option t2)) : 
  Lemma (requires (forall p. wp p))
    (ensures (true == true)) =
    calc (==) {
      reify (to_option (M4wp?.reflect f) <: option t2);
      == { _ by (norm [reify_]; dump "h") }
      ibind t2 (option t2) wp (fun x -> m4_return_wp (option t2) (to_option x))
        (reify (M4wp?.reflect f))
        (fun x -> lift_pure_m4wp (option t2) (fun p -> p (to_option x)) (fun _ -> to_option x))
        ;
    }
