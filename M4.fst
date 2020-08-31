module M4

open FStar.Tactics
// open ExtraTactics

open Common
open IO.Free
open IOHist
open IOStHist 

let m4_post a = maybe a -> Type0
let m4_wpty a = m4_post a -> Type0

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

let m4_interpretation #a (m : io a) (p : m4_post a) : Type0 = True

// REFINED COMPUTATION MONAD (repr)
let irepr (a:Type) (wp:m4_wpty a) =
  post:m4_post a ->
    Pure (io a)
      (requires (wp post))
      (ensures (fun (t:io a) -> m4_interpretation t post))

let ireturn (a : Type) (x : a) : irepr a (m4_return_wp a x) =
  fun _ -> io_return a x

let w = m4_wpty

unfold
val w_ord (#a : Type) : w a -> w a -> Type0
let w_ord wp1 wp2 = forall p. wp1 p ==> wp2 p

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
  
let lift_pure_m4wp (a:Type) (wp:pure_wp a) (f:(eqtype_as_type unit -> PURE a wp)) :
  Pure (irepr a (fun p -> wp (fun r -> p (Inl r)))) (requires True)
                    (ensures (fun _ -> True))
  = fun p -> let r = elim_pure f (fun r -> p (Inl r)) in io_return _ r

sub_effect PURE ~> M4wp = lift_pure_m4wp


effect M4
  (a:Type) =
  M4wp a (fun (p:m4_post a) -> forall res. p res)

let raise #a (e:exn) : M4wp a (fun p -> p (Inr e)) = 
  M4?.reflect (fun _ -> io_throw _ e)

let get_history () : M4wp events_trace (fun p -> p (Inl [])) = 
  M4?.reflect (fun _ -> io_return _ [])

let static_cmd
  (cmd : io_cmds)
  (argz : args cmd) :
  M4 (res cmd) = M4wp?.reflect(fun p -> ((io_all cmd argz)))
  
