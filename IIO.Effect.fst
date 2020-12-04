module IIO.Effect

open FStar.Tactics
open ExtraTactics
open FStar.Calc

open Common
open IO.Free
open IO.Effect

let rec iio_interpretation #a
  (m : iio a) 
  (h : trace)
  (p : io_post a) : Type0 = 
  match m with
  | Return x -> p (Inl x) []
  | Throw err -> p (Inr err) []
  (** silent actions / tau_cmds **)
  | Cont (Call GetTrace args fnc) -> (
    FStar.WellFounded.axiom1 fnc (Inl h);
    iio_interpretation (fnc (Inl h)) h p
  )
  (** observable actions / io_cmds **)
  | Cont (Call cmd args fnc) -> (
    forall res. (
      FStar.WellFounded.axiom1 fnc res;
      let e : event = convert_call_to_event cmd args res in
      iio_interpretation (fnc res) (e::h) (gen_post p e)))

// REFINED COMPUTATION MONAD (repr)
let iio_irepr (a:Type) (wp:io_wpty a) =
  h:trace -> post:io_post a ->
    Pure (iio a)
      (requires (wp h post))
      (ensures (fun (t:iio a) -> iio_interpretation t h post))

let iio_ireturn (a : Type) (x : a) : iio_irepr a (io_return_wp a x) =
  fun _ _ -> iio_return a x

let iio_ibind 
  (a b : Type) 
  (wp_v : io_wpty a) 
  (wp_f: a -> io_wpty b) 
  (v : iio_irepr a wp_v)
  (f : (x:a -> iio_irepr b (wp_f x))) : 
  Tot (iio_irepr b (io_bind_wp _ _ wp_v wp_f)) =
  fun h p -> 
    let t = (iio_bind a b 
        (v h (compute_post a b h wp_f p))
        (fun x ->
          assume (wp_f x h p);
           f x h p)) in
    assume (iio_interpretation t h p);
    t

unfold
let isubcomp (a:Type) (wp1 wp2: io_wpty a) (f : iio_irepr a wp1) :
  Pure (iio_irepr a wp2) (requires io_wpty_ord wp2 wp1) (ensures fun _ -> True) = f

unfold
let i_if_then_else (a : Type) (wp1 wp2 : io_wpty a) (f : iio_irepr a wp1) (g : iio_irepr a wp2) (b : bool) : Type =
  iio_irepr a (wp_if_then_else wp1 wp2 b)

total
reifiable
reflectable
layered_effect {
  IIOwp : a:Type -> wp : io_wpty a -> Effect
  with
       repr       = iio_irepr
     ; return     = iio_ireturn
     ; bind       = iio_ibind

     ; subcomp      = isubcomp
     ; if_then_else = i_if_then_else
}

let lift_pure_iiowp (a:Type) (wp:pure_wp a) (f:(eqtype_as_type unit -> PURE a wp)) :
  Tot (iio_irepr a (fun h p -> wp (fun r -> p (Inl r) [])))
  = fun h p -> let r = elim_pure f (fun r -> p (Inl r) []) in iio_return _ r

sub_effect PURE ~> IOwp = lift_pure_iowp

(** This is a identity function, and we need it because 
F* does not have depth subtyping on inductives. **)
let rec cast_io_iio #a (x:io a) : iio a =
  match x with
  | Return z -> Return z
  | Throw z -> Throw z
  | Cont (Call (cmd:io_cmds) args fnc) ->
     Cont (Call cmd args (fun res ->
       FStar.WellFounded.axiom1 fnc res;
       cast_io_iio (fnc res)))

let rec io_interp_to_iio_interp' (#a:Type u#a) 
  (cmd:io_cmds) (arg:io_args cmd) (fnc:(io_resm cmd -> io a)) 
  (h:trace) (p:io_post a) 
  (r:(io_resm cmd)) :
  Lemma
    (requires 
      (io_interpretation 
        (fnc r) 
        (gen_post p (convert_call_to_event cmd arg r))))
    (ensures (
      let e : event = convert_call_to_event cmd arg r in
      iio_interpretation 
        (cast_io_iio (fnc r)) 
        (e::h) 
        (gen_post p e))) 
    (decreases fnc) =
  let e : event = convert_call_to_event cmd arg r in
  FStar.WellFounded.axiom1 fnc r;
  match fnc r with
  | Cont (Call cmd' arg' fnc') ->
      Classical.forall_intro (Classical.move_requires (io_interp_to_iio_interp' cmd' arg' fnc' (e::h) (gen_post p e)))
  | _ -> ()

let io_interp_to_iio_interp (#a:Type u#a) (x:io a) (h:trace) (p:io_post a) : 
  Lemma
    (requires (io_interpretation x p))
    (ensures  (iio_interpretation (cast_io_iio x) h p)) =
  match x with
  | Cont (Call (cmd:io_cmds) arg fnc) -> 
      Classical.forall_intro (Classical.move_requires (io_interp_to_iio_interp' cmd arg fnc h p))
  | _ -> ()

let lift_iowp_iiowp (a:Type) (wp:io_wpty a) (f:io_irepr a wp) :
  Tot (iio_irepr a (fun h p -> wp h (fun r le -> p r le))) = 
  fun h p ->
    io_interp_to_iio_interp (f h p) h p;
    cast_io_iio (f h p)

sub_effect IOwp ~> IIOwp = lift_iowp_iiowp
  
effect IIOPrePost
  (a:Type)
  (pre : trace -> Type0)
  (post : trace -> maybe a -> trace -> Type0) =
  IIOwp a (fun (h:trace) (p:io_post a) ->
    pre h /\ (forall res le. post h res le ==>  p res le))

let get_trace () : IIOwp trace 
  (fun h p -> forall r le. r == (Inl h) /\ le == [] ==>  p r le) =
  IIOwp?.reflect (fun _ _ -> iio_call GetTrace ())

let throw (err:exn) : IIOwp trace (fun _ p -> p (Inr err) []) =
  IIOwp?.reflect(fun _ _ -> iio_throw _ err)

let pi_static_cmd
  (cmd : io_cmds)
  (pi : monitorable_prop)
  (arg : args cmd) :
  IIOPrePost (res cmd)
    (requires (fun h ->
      default_check h (| cmd, arg |) &&
      pi h (| cmd, arg |)))
    (ensures (fun h r le ->
      (match r with
      | Inr Contract_failure -> False
      | _ -> le == [convert_call_to_event cmd arg r])
      /\ enforced_locally default_check h le
      /\ enforced_locally pi h le)) =
  static_cmd cmd arg

let mixed_cmd
  (cmd : io_cmds)
  (pi : monitorable_prop)
  (arg : args cmd) :
  IIOPrePost (res cmd)
    (requires (fun h -> default_check h (| cmd, arg |)))
    (ensures (fun h r le ->
      (match r with
      | Inr Contract_failure -> le == []
      | _ -> le == [convert_call_to_event cmd arg r])
      /\ enforced_locally default_check h le
      /\ enforced_locally pi h le
      )) =
  let h = get_trace () in
  let action = (| cmd, arg |) in
  match pi h action with
  | true -> pi_static_cmd cmd pi arg
  | false -> throw Contract_failure 

let dynamic_cmd
  (cmd : io_cmds)
  (pi : monitorable_prop)
  (arg : args cmd) :
  IIOPrePost (res cmd) 
    (requires (fun h -> True))
    (ensures (fun h r le ->
      (match r with
      | Inr Contract_failure -> le == []
      | _ -> le == [convert_call_to_event cmd arg r])
      /\ enforced_locally default_check h le
      /\ enforced_locally pi h le
  )) =
  let h = get_trace () in
  let action = (| cmd, arg |) in
  match default_check h action with
  | true -> mixed_cmd cmd pi arg
  | false -> throw Contract_failure

let iio_pre (pi : monitorable_prop) (h:trace) : Type0 =
  enforced_globally default_check h &&
  enforced_globally pi h

let iio_post
  (#a:Type)
  (pi : monitorable_prop)
  (h:trace)
  (result:maybe a)
  (local_trace:trace) :
  Tot Type0 =
  enforced_globally (default_check) (apply_changes h local_trace) /\
  enforced_globally (pi) (apply_changes h local_trace)

effect IIO 
  (a:Type)
  (pi : monitorable_prop) 
  (post : trace -> maybe a -> trace -> Type0) =
  IIOPrePost a
    (requires (iio_pre pi))
    (ensures (fun h r le -> iio_post pi h r le /\ post h r le))
