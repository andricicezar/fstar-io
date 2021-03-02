module IIO.Effect

open FStar.Tactics
open ExtraTactics
open FStar.Calc

include Common
open IO.Free
open IO.Effect

let rec iio_interpretation #a
  (m : iio a)
  (h : trace)
  (p : io_post a) : Type0 =
  match m with
  | Return x -> p x []
  (** internal_cmds **)
  | Call GetTrace args fnc -> (
    iio_interpretation (fnc (Inl h)) h p
  )
  (** io_cmds **)
  | Call cmd args fnc -> (
    if _obs_cmds cmd then (
      forall res. (
        let e : event = convert_call_to_event cmd args res in
        iio_interpretation (fnc res) (e::h) (gen_post p cmd args res)))
    else (
      forall res. (
        iio_interpretation (fnc res) h p)
    ))

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
        (fun (x:a) ->
          assume (wp_f x h p);
           f x h p)) in
    assume (iio_interpretation t h p);
    t

unfold
let isubcomp (a:Type) (wp1 wp2: io_wpty a) (f : iio_irepr a wp1) :
  Pure (iio_irepr a wp2)
    (requires io_wpty_ord wp2 wp1)
    (ensures fun _ -> True) = f

unfold
let i_if_then_else
  (a : Type)
  (wp1 wp2 : io_wpty a)
  (f : iio_irepr a wp1)
  (g : iio_irepr a wp2)
  (b : bool) :
  Tot Type =
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

let lift_pure_iiowp
  (a:Type)
  (wp:pure_wp a)
  (f:(eqtype_as_type unit -> PURE a wp)) :
  Tot (iio_irepr a (fun h p -> wp (fun r -> p (Inl r) [])))
  = fun h p -> let r = elim_pure f (fun r -> p (Inl r) []) in iio_return _ r

sub_effect PURE ~> IOwp = lift_pure_iowp

(** This is a identity function, and we need it because
F* does not have depth subtyping on inductives. **)
let rec cast_io_iio #a (x:io a) : iio a =
  match x with
  | Return z -> Return z
  | Call (cmd:io_cmds) args fnc ->
     Call cmd args (fun res ->
       cast_io_iio (fnc res))

let rec io_interp_to_iio_interp' (#a:Type u#a)
  (cmd:io_cmds) (arg:io_args cmd) (fnc:(io_resm cmd -> io a))
  (h:trace) (p:io_post a)
  (r:(io_resm cmd)) :
  Lemma
    (requires
      (io_interpretation
        (fnc r)
        (gen_post p cmd arg r)))
    (ensures (
      iio_interpretation
        (cast_io_iio (fnc r))
        (if _obs_cmds cmd then (convert_call_to_event cmd arg r)::h
         else h)
        (gen_post p cmd arg r)))
    (decreases fnc) =
  admit (); (** after updating F* this is not checking anymore.
  Error: can not prove post condition **)
  match fnc r with
  | Call cmd' arg' fnc' ->
      assert (fnc' << fnc r);
      let e : event = convert_call_to_event cmd arg r in
      Classical.forall_intro (
        Classical.move_requires (
          io_interp_to_iio_interp' cmd' arg' fnc' (e::h) (gen_post p cmd arg r)))
  | _ -> ()

let io_interp_to_iio_interp (#a:Type u#a) (x:io a) (h:trace) (p:io_post a) :
  Lemma
    (requires (io_interpretation x p))
    (ensures  (iio_interpretation (cast_io_iio x) h p)) =
  match x with
  | Call (cmd:io_cmds) arg fnc ->
      Classical.forall_intro (
        Classical.move_requires (
          io_interp_to_iio_interp' cmd arg fnc h p))
  | _ -> ()

let lift_iowp_iiowp (a:Type) (wp:io_wpty a) (f:io_irepr a wp) :
  Tot (iio_irepr a (fun h p -> wp h (fun r lt -> p r lt))) =
  fun h p ->
    io_interp_to_iio_interp (f h p) h p;
    cast_io_iio (f h p)

sub_effect IOwp ~> IIOwp = lift_iowp_iiowp

let get_trace () : IIOwp trace
  (fun h p -> forall r lt. r == (Inl h) /\ lt == [] ==>  p r lt) =
  IIOwp?.reflect (fun _ _ -> iio_call GetTrace ())

let throw (#a:Type) (err:exn) : IIOwp a (fun _ p -> p (Inr err) []) =
  IIOwp?.reflect(fun _ _ -> iio_throw a err)


let iio_pre (pi : monitorable_prop) (h:trace) : Type0 =
  enforced_globally pi h

let iio_post
  (#a:Type)
  (pi : monitorable_prop)
  (h:trace)
  (result:maybe a)
  (local_trace:trace) :
  Tot Type0 =
  enforced_globally pi (apply_changes h local_trace)

effect IIO
  (a:Type)
  (pi : monitorable_prop)
  (pre : trace -> Type0)
  (post : trace -> maybe a -> trace -> Type0) =
  IIOwp a
    (fun h p ->
      pre h /\ iio_pre pi h /\
      (forall r lt. (iio_post pi h r lt /\ post h r lt) ==>  p r lt))

let dynamic_cmd
  (pi : monitorable_prop)
  (cmd : io_cmds)
  (arg : args cmd) :
  IIO (res cmd) pi
    (requires (fun _ -> True))
    (ensures (fun _ r lt ->
      (match r with
      | Inr Contract_failure -> lt == []
      | _ -> (_obs_cmds cmd ==> lt == [convert_call_to_event cmd arg r]) /\
            (_tau_cmds cmd ==> lt == [])))) =
  let h = get_trace () in
  let action = (| cmd, arg |) in
  match pi h action with
  | true -> static_cmd pi cmd arg
  | false -> throw Contract_failure

(** This tactic has the role to help F*/SMT to prove
larger function bodies in the IIO Effect. This is
needed for function bodies that contain a function
call to other IIO computations.

CA: I don't like that it explodes the goal. **)
let iio_tactic () : Tac unit =
    l_to_r [`List.append_l_nil; `List.append_nil_l];
    let lem = pose_lemma (`(rev_append_rev_append ())) in
    norm [delta_only [`%iio_post;`%apply_changes]];
    explode ()
