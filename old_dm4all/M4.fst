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
let m4_bind_wp (_ : range) (a:Type) (b:Type) (w : m4_wpty a) (kw : a -> m4_wpty b) : m4_wpty b =
  fun p -> w 
      (fun result -> 
        match result with
        | Inl v -> kw v (fun r' -> p r')
        | Inr err -> p (Inr err))

let m4_interpretation #a (m : io a) (p : m4_post a) : Type0 = True

total
reifiable
reflectable
new_effect {
  M4wp : a:Type -> Effect
  with 
       repr       = io
     ; return     = io_return
     ; bind       = io_bind

     ; wp_type    = m4_wpty
     ; return_wp  = m4_return_wp
     ; bind_wp    = m4_bind_wp

     ; interp     = m4_interpretation
}
  
unfold let lift_PURE_M4 (a:Type) (wp:pure_wp a) (p:m4_post a) =
  wp (fun a -> p (Inl a))
sub_effect PURE~> M4wp = lift_PURE_M4

effect M4
  (a:Type) =
  M4wp a (fun (p:m4_post a) -> forall res. p res)

let raise #a (e:exn) : M4wp a (fun p -> p (Inr e)) = 
  M4?.reflect (io_throw _ e)

let get_history () : M4wp events_trace (fun p -> p (Inl [])) = 
  M4?.reflect (io_return _ [])
