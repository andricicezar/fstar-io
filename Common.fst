module Common

open FStar.Exn

exception GIO_default_check_failed
exception GIO_pi_failed

type maybe a = either a exn

type file_descr = int

let compose #a #b #c (g:b->c) (f:a->b) = fun x -> g (f x)

let id #a (x:a) = x

unfold let inl_app #a #b (f:a -> b) : maybe a -> maybe b =
  fun x -> 
    match x with
    | Inl x -> Inl (f x)
    | Inr err -> Inr err

  
let cdr #a (_, (x:a)) : a = x

let elim_pure #a #wp ($f : unit -> PURE a wp) p
 : Pure a (requires (wp p)) (ensures (fun r -> p r))
 //: PURE a (fun p' -> wp p /\ (forall r. p r ==> p' r))
 // ^ basically this, requires monotonicity
 = FStar.Monotonic.Pure.wp_monotonic_pure ();
   f ()
