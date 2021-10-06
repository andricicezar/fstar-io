module DM.IIO

open FStar.Tactics
open ExtraTactics
open FStar.Calc

open Common
open Free.IO
open DM.IO
open Hist

let rec iio_interpretation #a
  (m : iio a)
  (h : trace)
  (p : hist_post a) : Type0 =
  match m with
  | Return x -> p x []
  (** internal_cmds **)
  | Call GetTrace args fnc ->
    iio_interpretation (fnc h) h p
  (** io_cmds **)
  | Call cmd args fnc -> (
    forall res. (
      let e : event = convert_call_to_event cmd args res in
      iio_interpretation (fnc res) (e::h) (gen_post p cmd args res)))

// REFINED COMPUTATION MONAD (repr)
let iio_irepr (a:Type) (wp:hist a) =
  h:trace -> post:hist_post a ->
    Pure (iio a)
      (requires (wp h post))
      (ensures (fun (t:iio a) -> iio_interpretation t h post))

let iio_ireturn (a : Type) (x : a) : iio_irepr a (hist_return a x) =
  fun _ _ -> iio_return a x

let iio_ibind
  (a b : Type)
  (wp_v : hist a)
  (wp_f: a -> hist b)
  (v : iio_irepr a wp_v)
  (f : (x:a -> iio_irepr b (wp_f x))) :
  Tot (iio_irepr b (hist_bind _ _ wp_v wp_f)) =
  fun h p ->
    let t = (iio_bind a b
        (v h (compute_post a b h wp_f p))
        (fun (x:a) ->
          assume (wp_f x h p);
           f x h p)) in
    assume (iio_interpretation t h p);
    t

unfold
let isubcomp (a:Type) (wp1 wp2: hist a) (f : iio_irepr a wp1) :
  Pure (iio_irepr a wp2)
    (requires hist_ord wp2 wp1)
    (ensures fun _ -> True) = f

unfold
let i_if_then_else
  (a : Type)
  (wp1 wp2 : hist a)
  (f : iio_irepr a wp1)
  (g : iio_irepr a wp2)
  (b : bool) :
  Tot Type =
  iio_irepr a (hist_if_then_else wp1 wp2 b)

total
reifiable
reflectable
layered_effect {
  IIOwp : a:Type -> wp : hist a -> Effect
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
  Tot (iio_irepr a (fun h p -> wp (fun r -> p r [])))
  = fun h p -> let r = elim_pure f (fun r -> p r []) in iio_return _ r

sub_effect PURE ~> IIOwp = lift_pure_iiowp

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
  (h:trace) (p:hist_post a)
  (r:(io_resm cmd)) :
  Lemma
    (requires
      (io_interpretation
        (fnc r)
        (gen_post p cmd arg r)))
    (ensures (
      iio_interpretation
        (cast_io_iio (fnc r))
        ((convert_call_to_event cmd arg r)::h)
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

let io_interp_to_iio_interp (#a:Type u#a) (x:io a) (h:trace) (p:hist_post a) :
  Lemma
    (requires (io_interpretation x p))
    (ensures  (iio_interpretation (cast_io_iio x) h p)) =
  match x with
  | Call (cmd:io_cmds) arg fnc ->
      Classical.forall_intro (
        Classical.move_requires (
          io_interp_to_iio_interp' cmd arg fnc h p))
  | _ -> ()

let lift_iowp_iiowp (a:Type) (wp:hist a) (f:io_irepr a wp) :
  Tot (iio_irepr a (fun h p -> wp h p)) =
  fun h p ->
    io_interp_to_iio_interp (f h p) h p;
    cast_io_iio (f h p)

sub_effect IOwp ~> IIOwp = lift_iowp_iiowp

let get_trace () : IIOwp trace
  (fun h p -> forall lt. lt == [] ==>  p h lt) =
  IIOwp?.reflect (fun _ _ -> iio_call GetTrace ())

let iio_pre (pi : monitorable_prop) (h:trace) : bool =
  enforced_globally pi h

let iio_post
  (#a:Type)
  (pi : monitorable_prop)
  (h:trace)
  (result:a)
  (local_trace:trace) :
  Tot bool =
  enforced_globally pi (apply_changes h local_trace)

effect IIO
  (a:Type)
  (pi : monitorable_prop)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  IIOwp a
    (fun h p ->
      pre h /\ iio_pre pi h /\
      (forall r lt. (iio_post pi h r lt /\ post h r lt) ==>  p r lt))

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

let _IIOwp_as_IIO
  (pre:'a -> trace -> bool)
  (post:'a -> trace -> (m:'b) -> trace -> Type0)
  (f:(x:'a ->
    IIOwp 'b (fun h p -> pre x h /\ (forall r lt. post x h r lt ==> p r lt))))
  (x:'a) :
  IIOwp (maybe 'b) (fun h p ->
    (~(pre x h) ==>  p (Inr Contract_failure) []) /\
    (pre x h ==>  (forall r lt. post x h r lt ==>  p (Inl r) lt)))
    by (iio_tactic ()) =
  let h = get_trace () in
  if pre x h then (Inl (f x))
  else (Inr Contract_failure)

let _IIOwp_as_IIO_2
  (pre:'a -> 'b -> trace -> bool)
  (post:'a -> 'b -> trace -> (m:'c) -> trace -> Type0)
  (f:(x:'a -> y:'b ->
    IIOwp 'c (fun h p -> pre x y h /\ (forall r lt. post x y h r lt ==> p r lt))))
  (x:'a) (y:'b) :
  IIOwp (maybe 'c) (fun h p ->
    (~(pre x y h) ==> p (Inr Contract_failure) []) /\
    (pre x y h ==> (forall r lt. post x y h r lt ==> p (Inl r) lt)))
    by (iio_tactic ()) =
  let h = get_trace () in
  if pre x y h then Inl (f x y)
  else Inr Contract_failure

let _IIOwp_as_IIO_3
  (pre:'a -> 'b -> 'c -> trace -> bool)
  (post:'a -> 'b -> 'c -> trace -> 'd -> trace -> Type0)
  (f:(x:'a -> y:'b -> z:'c ->
    IIOwp 'd (fun h p -> pre x y z h /\ (forall r lt. post x y z h r lt ==> p r lt))))
  (x:'a) (y:'b) (z:'c) :
  IIOwp (maybe 'd) (fun h p ->
    (~(pre x y z h) ==> p (Inr Contract_failure) []) /\
    (pre x y z h ==> (forall r lt. post x y z h r lt ==> p (Inl r) lt)))
    by (iio_tactic ()) =
  let h = get_trace () in
  if pre x y z h then Inl (f x y z)
  else Inr Contract_failure

val dynamic_cmd :
  (cmd : io_cmds) ->
  (pi : monitorable_prop) ->
  (arg : args cmd) ->
  IIOwp (maybe (io_resm cmd)) (fun h p ->
    (forall (r:maybe (io_resm cmd)) lt.
      ((match r with
      | Inr Contract_failure -> lt == []
      | Inl r' -> lt == [convert_call_to_event cmd arg r']
      | _ -> False) /\
      enforced_locally pi h lt) ==> p r lt))
let dynamic_cmd (cmd:io_cmds) = _IIOwp_as_IIO_2 #monitorable_prop #(args cmd)
  (fun pi (argz:args cmd) h -> pi h (| cmd, argz |))
  (fun pi (argz:args cmd) h r lt ->
      lt == [convert_call_to_event cmd argz r] /\
      enforced_locally pi h lt)
  (static_cmd cmd)
