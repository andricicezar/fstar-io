module IIO.Effect

open FStar.Tactics
open ExtraTactics

open Common
open IO.Free
open IO.Effect

let rec iio_interpretation #a
  (m : iio a) 
  (h : events_trace)
  (p : io_post a) : Type0 = 
  match m with
  | Return x -> p (Inl x) []
  | Throw err -> p (Inr err) []
  | Cont (Call GetTrace args fnc) -> (
      FStar.WellFounded.axiom1 fnc (Inl h);
      iio_interpretation (fnc (Inl h)) h p
  )
  | Cont (Call cmd args fnc) -> (
    forall res. (
      FStar.WellFounded.axiom1 fnc res;
      let event : io_event = convert_call_to_event cmd args res in
      iio_interpretation (fnc res) (event::h) (gen_post p event)))


// REFINED COMPUTATION MONAD (repr)
let irepr (a:Type) (wp:io_wpty a) =
  h:events_trace -> post:io_post a ->
    Pure (iio a)
      (requires (wp h post))
      (ensures (fun (t:iio a) -> iio_interpretation t h post))

let ireturn (a : Type) (x : a) : irepr a (io_return_wp a x) =
  fun _ _ -> iio_return a x

let w = io_wpty

unfold
val w_ord (#a : Type) : w a -> w a -> Type0
let w_ord wp1 wp2 = forall h p. wp1 h p ==> wp2 h p

let ibind (a b : Type) (wp_v : w a) (wp_f: a -> w b) (v : irepr a wp_v)
  (f : (x:a -> irepr b (wp_f x))) : irepr b (io_bind_wp _ _ wp_v wp_f) =
  fun h p -> 
    let t = (iio_bind a b 
        (v h (compute_post a b h wp_f p))
        (fun x ->
          assume (wp_f x h p);
           f x h p)) in
    assume (iio_interpretation t h p);
    t

unfold
let isubcomp (a:Type) (wp1 wp2: w a) (f : irepr a wp1) :
  Pure (irepr a wp2) (requires w_ord wp2 wp1) (ensures fun _ -> True) = f

unfold
let wp_if_then_else (#a:Type) (wp1 wp2:w a) (b:bool) : w a =
  fun h p -> (b ==> wp1 h p) /\ ((~b) ==> wp2 h p)

unfold
let i_if_then_else (a : Type) (wp1 wp2 : w a) (f : irepr a wp1) (g : irepr a wp2) (b : bool) : Type =
  irepr a (wp_if_then_else wp1 wp2 b)

total
reifiable
reflectable
layered_effect {
  IIOwp : a:Type -> wp : io_wpty a -> Effect
  with
       repr       = irepr
     ; return     = ireturn
     ; bind       = ibind

     ; subcomp      = isubcomp
     ; if_then_else = i_if_then_else
}

let lift_pure_iiowp (a:Type) (wp:pure_wp a) (f:(eqtype_as_type unit -> PURE a wp)) :
  Pure (irepr a (fun s0 p -> wp (fun r -> p (Inl r) []))) (requires True)
                    (ensures (fun _ -> True))
  = fun s0 p -> let r = elim_pure f (fun r -> p (Inl r) []) in iio_return _ r

sub_effect PURE ~> IOwp = lift_pure_iowp

let lift_iowp_iiowp (a:Type) (wp:io_wpty a) (f:IO.Effect.irepr a wp) :
  Pure (irepr a (fun s0 p -> wp s0 (fun r le -> p r le))) 
    (requires True)
    (ensures (fun _ -> True))
  // TODO: lift from IO.irepr to IIO.irepr
  = fun s0 p -> admit (); f s0 p

sub_effect IOwp ~> IIOwp = lift_iowp_iiowp
  
effect IIO
  (a:Type)
  (pre : events_trace -> Type0)
  (post : events_trace -> maybe a -> events_trace -> Type0) =
  IIOwp a (fun (h:events_trace) (p:io_post a) ->
    pre h /\ (forall res le. post h res le ==>  p res le))

let openfile = static_cmd Openfile
let read = static_cmd Read
let close = static_cmd Close

let testStat2 () : 
  IIO unit (fun h -> True) (fun h _ le -> enforced_locally default_check h le) =
  let fd = openfile "../Makefile" in
  let msg = read fd in
  close fd;
  ()

let get () : IIO events_trace (fun h -> True) 
  (fun h r le -> r == (Inl h)) by (
  let h = forall_intro () in
  let p = forall_intro () in
  norm [delta_only[`%iio_interpretation]];
  let _ = forall_intro () in
  let g = implies_intro () in
  let l1, l2 = Tactics.destruct_and g in
  dump "h") =
  IIOwp?.reflect (fun _ _ -> iio_all GetTrace ())

