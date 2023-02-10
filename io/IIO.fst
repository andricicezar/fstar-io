module IIO

open FStar.Tactics
open ExtraTactics
open FStar.Ghost

include IIO.Sig
open IIO.Sig.Call
open DMFree

(** The postcondition for an io computation is defined over the
result (type: a) and local trace (type: trace).
The local trace represents the events that happend during the
computation. Local trace is in chronological order.

We also have the history (type: trace) which represents the
events that happend until the beggining of the io computation.
The history is  in reverse chronology order.

At the end of an io computation, the local trace is appended
in reverse order to the history. **)
let dm_iio_theta #a = theta #a #iio_cmds #iio_sig #event iio_wps
  
type dm_iio = dm iio_cmds iio_sig event iio_wps
let dm_iio_return (a:Type) (x:a) : dm_iio a (hist_return x) =
  dm_return iio_cmds iio_sig event iio_wps a x

val dm_iio_bind  : 
  a: Type ->
  b: Type ->
  wp_v: hist a ->
  wp_f: (_: a -> hist b) ->
  v: dm_iio a wp_v ->
  f: (x: a -> dm_iio b (wp_f x)) ->
  Tot (dm_iio b (hist_bind wp_v wp_f))
let dm_iio_bind a b wp_v wp_f v f = dm_bind iio_cmds iio_sig event iio_wps a b wp_v wp_f v f

val dm_iio_subcomp : 
  a: Type ->
  wp1: hist a ->
  wp2: hist a ->
  f: dm_iio a wp1 ->
  Pure (dm_iio a wp2) (hist_ord wp2 wp1) (fun _ -> True)
let dm_iio_subcomp a wp1 wp2 f = dm_subcomp iio_cmds iio_sig event iio_wps a wp1 wp2 f

(** * The IIO effect indexed by actions **)

(** ** Types **)

(** **** Flag **)
noeq
type tflag = | NoActions | GetTraceActions | IOActions | AllActions

let rec satisfies (m:iio 'a) (flag:tflag) =
match flag, m with
| AllActions,   _                     -> True
| _,            Return x              -> True
| _,            PartialCall pre k     -> forall r. satisfies (k r) flag
| NoActions,    _                     -> False
| GetTraceActions, Call GetTrace arg k   -> forall r. satisfies (k r) flag
| GetTraceActions, Call cmd arg k        -> False
| IOActions,    Call GetTrace arg k   -> False
| IOActions,    Call cmd arg k        -> forall r. satisfies (k r) flag

let (+) (flag1:tflag) (flag2:tflag) = 
  match flag1, flag2 with
  | NoActions, NoActions -> NoActions
  | NoActions, fl -> fl
  | fl, NoActions -> fl
  | GetTraceActions, GetTraceActions -> GetTraceActions
  | IOActions, IOActions -> IOActions
  | _, _ -> AllActions

let (<=) (flag1:tflag) (flag2:tflag) =
  match flag1, flag2 with
  | NoActions, _ -> True
  | GetTraceActions, NoActions -> False
  | GetTraceActions, _ -> True
  | IOActions, NoActions -> False
  | IOActions, GetTraceActions -> False
  | IOActions, _ -> True
  | AllActions, AllActions -> True
  | AllActions, _ -> False

(** ** Defining F* Effect **)

type dm_giio (a:Type) (flag:erased tflag) (wp:hist a) = t:(dm_iio a wp){t `satisfies` flag} 

let dm_giio_theta #a = theta #a #iio_cmds #iio_sig #event iio_wps

let dm_giio_return (a:Type) (x:a) : dm_giio a NoActions (hist_return x) by (compute ()) =
  dm_iio_return a x

val dm_giio_bind  : 
  a: Type ->
  b: Type ->
  flag_v : erased tflag ->
  flag_f : erased tflag ->
  wp_v: Hist.hist a ->
  wp_f: (_: a -> Hist.hist b) ->
  v: dm_giio a flag_v wp_v ->
  f: (x: a -> dm_giio b flag_f (wp_f x)) ->
  Tot (dm_giio b (flag_v + flag_f) (hist_bind wp_v wp_f))
let dm_giio_bind a b flag_v flag_f wp_v wp_f v f : (dm_giio b (flag_v + flag_f) (hist_bind wp_v wp_f)) = 
  let r = dm_iio_bind a b wp_v wp_f v f in
  assume (v `satisfies` flag_v /\ (forall x. f x `satisfies` flag_f) ==> r `satisfies` (flag_v + flag_f));
  r

val dm_giio_subcomp : 
  a: Type ->
  flag1 : erased tflag ->
  flag2 : erased tflag ->
  wp1: hist a ->
  wp2: hist a ->
  f: dm_giio a flag1 wp1 ->
  Pure (dm_giio a flag2 wp2) ((flag1 <= flag2) /\ hist_ord wp2 wp1) (fun _ -> True)
let dm_giio_subcomp a flag1 flag2 wp1 wp2 f = 
  admit ();
  dm_iio_subcomp a wp1 wp2 f

let dm_giio_if_then_else (a : Type u#a) (fl1 fl2:erased tflag)
  (wp1 wp2: hist a) (f : dm_giio a fl1 wp1) (g : dm_giio a fl2 wp2) (b : bool) : Type =
  dm_giio a (fl1 + fl2) (hist_if_then_else wp1 wp2 b)

total
reflectable
effect {
  IIOwp (a:Type) (flag:erased tflag) (wp : hist #event a) 
  with {
       repr       = dm_giio
     ; return     = dm_giio_return
     ; bind       = dm_giio_bind 
     ; subcomp    = dm_giio_subcomp
     ; if_then_else = dm_giio_if_then_else
     }
}

let dm_giio_partial_return 
  (pre:pure_pre) : dm_giio (squash pre) NoActions (partial_call_wp pre) by (compute ()) =
  dm_partial_return iio_cmds iio_sig event iio_wps pre

val lift_pure_dm_giio :
  a: Type ->
  w: pure_wp a ->
  f: (eqtype_as_type unit -> PURE a w) ->
  Tot (dm_giio a NoActions (wp_lift_pure_hist w))
let lift_pure_dm_giio a w f = 
  lemma_wp_lift_pure_hist_implies_as_requires #a #event w;
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs : dm_giio _ NoActions _ = dm_giio_partial_return (as_requires w) in
  let rhs = (fun (pre:(squash (as_requires w))) -> dm_giio_return a (f pre)) in
  let m = dm_giio_bind _ _ NoActions NoActions _ _ lhs rhs in
  dm_giio_subcomp a NoActions NoActions _ _ m
  
sub_effect PURE ~> IIOwp = lift_pure_dm_giio

effect IIO
  (a:Type)
  (fl:erased tflag)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  IIOwp a fl (to_hist pre post) 
  
let static_cmd
  (cmd : io_cmds)
  (arg : io_sig.args cmd) :
  IIO (io_sig.res cmd arg) IOActions
    (requires (fun h -> io_pre cmd arg h))
    (ensures (fun h (r:io_sig.res cmd arg) lt ->
        lt == [convert_call_to_event cmd arg r])) =
  IIOwp?.reflect (iio_call cmd arg)

let get_trace () : IIOwp trace GetTraceActions
  (fun p h -> forall lt. lt == [] ==> p lt h) =
  IIOwp?.reflect (iio_call GetTrace ())

// There is no hope to prove anything about ctx without a meta-theorem about F* / without a formalization of F* & Ghost.
// val ctx_s : (fl:erased tflag) -> IIO unit fl (fun _ -> True) (fun _ _ _ -> True) 

private
let performance_test (#fl:tflag) : IIOwp unit (fl+IOActions) (fun p h -> forall lt. (List.length lt == 6) \/ (List.length lt == 7) ==> p lt ()) =
  let fd = static_cmd Openfile "../Makefile" in
  let fd = static_cmd Openfile "../Makefile" in
  let fd = static_cmd Openfile "../Makefile" in
  let fd = static_cmd Openfile "../Makefile" in
  let fd = static_cmd Openfile "../Makefile" in
  let fd = static_cmd Openfile "../Makefile" in
  if Inl? fd then let _ = static_cmd Close (Inl?.v fd) in () else 
  ()
