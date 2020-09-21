module UnfoldReify

open FStar.Exn
open FStar.Tactics

type maybe (a:Type) = either a exn 

type m4 (a:Type) = 
| Return : a -> m4 a

let m4_return (a:Type) (x: a) : m4 a = Return x

let m4_bind (a:Type) (b:Type) (l:m4 a) (k:a -> m4 b) : m4 b =
  match l with
  | Return x -> k x

let m4_post a = maybe a -> Type0
let m4_wpty a = m4_post a -> Type0

let m4_return_wp (a:Type) (x:a) : m4_wpty a = fun p -> p (Inl x) 

let compute_post (a b:Type) (km4_wpty : a -> m4_wpty b) (p:m4_post b) : m4_post a =
      (fun result -> 
        match result with
        | Inl v -> km4_wpty v (fun r' -> p r')
        | Inr err -> p (Inr err))

let m4_bind_wp (a b:Type) (w : m4_wpty a) (kw : a -> m4_wpty b) : m4_wpty b =
  fun p -> w (compute_post a b kw p)

let m4_interpretation #a (m : m4 a) (p : m4_post a) : Type0 = True

let irepr (a:Type) (wp:m4_wpty a) =
  post:m4_post a ->
    Pure (m4 a)
      (requires (wp post))
      (ensures (fun (t:m4 a) -> m4_interpretation t post))

let ireturn (a : Type) (x : a) : irepr a (m4_return_wp a x) = fun _ -> m4_return a x

val w_ord (#a : Type) : m4_wpty a -> m4_wpty a -> Type0
let w_ord wp1 wp2 = forall p. wp1 p ==> wp2 p

let ibind (a b : Type) (wp_v : m4_wpty a) (wp_f: a -> m4_wpty b) (v : irepr a wp_v)
  (f : (x:a -> irepr b (wp_f x))) : irepr b (m4_bind_wp _ _ wp_v wp_f) =
  fun p -> 
    let t = (m4_bind a b
        (v (compute_post a b wp_f p))
        (fun x ->
          assume (wp_f x p);
           f x p)) in
    assume (m4_interpretation t p);
    t

let isubcomp (a:Type) (wp1 wp2: m4_wpty a) (f : irepr a wp1) :
  Pure (irepr a wp2) (requires w_ord wp2 wp1) (ensures fun _ -> True) = f

let wp_if_then_else (#a:Type) (wp1 wp2:m4_wpty a) (b:bool) : m4_wpty a =
  fun p -> (b ==> wp1 p) /\ ((~b) ==> wp2 p)

let i_if_then_else (a : Type) (wp1 wp2 : m4_wpty a) (f : irepr a wp1) (g : irepr a wp2) (b : bool) : Type =
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
 = FStar.Monotonic.Pure.wp_monotonic_pure (); f ()

let lift_pure_m4wp (a:Type) (wp:pure_wp a) (f:(eqtype_as_type unit -> PURE a wp)) :
  Pure (irepr a (fun p -> wp (fun r -> p (Inl r)))) (requires True)
                    (ensures (fun _ -> True))
  = fun p -> let r = elim_pure f (fun r -> p (Inl r)) in m4_return _ r

sub_effect PURE ~> M4wp = lift_pure_m4wp


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
      == { admit () }
      ibind t2 (option t2) wp (fun x -> m4_return_wp (option t2) (to_option x))
        (reify (M4wp?.reflect f))
        (fun x -> lift_pure_m4wp (option t2) (fun p -> p (to_option x)) (fun _ -> to_option x))
        ;
    }
