module MIO

open FStar.Tactics
open ExtraTactics
open FStar.Ghost

include MIO.Sig
//open MIO.Sig.Call
open DMFree

(** The postcondition for an io computation is defined over the
result (type: a) and local trace (type: trace).
The local trace represents the events that happened during the
computation. Local trace is in chronological order.

We also have the history (type: trace) which represents the
events that happend until the beggining of the io computation.
The history is in reverse chronology order.

At the end of an io computation, the local trace is appended
in reverse order to the history. **)
let dm_mio_theta #mst #a = theta #a #mio_cmds #(mio_sig mst) #event mio_wps
  
type dm_mio mst = dm mio_cmds (mio_sig mst) event mio_wps
let dm_mio_return (a:Type) (mst:mstate) (x:a) : dm_mio mst a (hist_return x) =
  dm_return mio_cmds (mio_sig mst) event mio_wps a x

val dm_mio_bind  : 
  a: Type ->
  b: Type ->
  mst : mstate ->
  wp_v: hist a ->
  wp_f: (_: a -> hist b) ->
  v: dm_mio mst a wp_v ->
  f: (x: a -> dm_mio mst b (wp_f x)) ->
  Tot (dm_mio mst b (hist_bind wp_v wp_f))
let dm_mio_bind a b mst wp_v wp_f v f = dm_bind mio_cmds (mio_sig mst) event mio_wps a b wp_v wp_f v f

val dm_mio_subcomp : 
  a: Type ->
  mst:mstate ->
  wp1: hist a ->
  wp2: hist a ->
  f: dm_mio mst a wp1 ->
  Pure (dm_mio mst a wp2) (hist_ord wp2 wp1) (fun _ -> True)
let dm_mio_subcomp a mst wp1 wp2 f = dm_subcomp mio_cmds (mio_sig mst) event mio_wps a wp1 wp2 f

(** * The MIO effect indexed by actions **)

(** ** Types **)

(** **** Flag **)
noeq
type tflag = | NoActions | GetTraceActions | IOActions | AllActions

let rec satisfies #mst (m:mio mst 'a) (flag:tflag) =
match flag, m with
| AllActions,   _                     -> True
| _,            Return x              -> True
| _,            PartialCall pre k     -> forall r. satisfies (k r) flag
| NoActions,    _                     -> False
| GetTraceActions, Call _ GetTrace arg k   -> forall r. satisfies (k r) flag
| GetTraceActions, Call _ GetST arg k   -> forall r. satisfies (k r) flag
| GetTraceActions, Call _ cmd arg k        -> False
| IOActions,    Call _ GetTrace arg k   -> False
| IOActions,    Call _ GetST    arg k   -> False
| IOActions,    Call _ cmd arg k        -> forall r. satisfies (k r) flag

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
  | GetTraceActions, IOActions -> False
  | GetTraceActions, _ -> True
  | IOActions, NoActions -> False
  | IOActions, GetTraceActions -> False
  | IOActions, _ -> True
  | AllActions, AllActions -> True
  | AllActions, _ -> False

let plus_compat_le (f1 f2 : tflag) : Lemma (f1 <= f1+f2) = ()
let plus_comm      (f1 f2 : tflag) : Lemma (f1+f2 == f2+f1) = ()

let rec sat_le #mst (f1:tflag) (f2:tflag{f1 <= f2}) (m : mio mst 'a) :
  Lemma (satisfies m f1 ==> satisfies m f2) =
  match m with
  | Return _ -> ()
  | PartialCall i o ->
    Classical.forall_intro
     ((fun r -> sat_le f1 f2 (o r)) <: r:_ -> Lemma (satisfies (o r) f1 ==> satisfies (o r) f2))
  | Call _ f i o ->
    Classical.forall_intro
     ((fun r -> sat_le f1 f2 (o r)) <: r:_ -> Lemma (satisfies (o r) f1 ==> satisfies (o r) f2))

let rec sat_bind #mst (fl:tflag) (v : mio mst 'a) (f : 'a -> mio mst 'b)
  : Lemma (v `satisfies` fl /\ (forall x. f x `satisfies` fl) ==> free_bind _ _ _ _ v f `satisfies` fl)
  =
  match v with
  | Return _ -> ()
  | PartialCall i o ->
  Classical.forall_intro
   ((fun r -> sat_bind fl (o r) f) <: r:_ -> Lemma ((o r) `satisfies` fl /\ (forall x. f x `satisfies` fl) ==> free_bind _ _ _ _ (o r) f `satisfies` fl))

  | Call _ _ i o ->
  Classical.forall_intro
   ((fun r -> sat_bind fl (o r) f) <: r:_ -> Lemma ((o r) `satisfies` fl /\ (forall x. f x `satisfies` fl) ==> free_bind _ _ _ _ (o r) f `satisfies` fl))

let dm_mio_bind_is_free_bind a b mst wp_v wp_f v f
: Lemma (dm_mio_bind a b mst wp_v wp_f v f == free_bind _ _ _ _ v f)
=
  let r = dm_mio_bind a b mst wp_v wp_f v f in
  assert (r == free_bind _ _ _ _ v f)

let sat_bind_add mst (fl_v fl_f:tflag) (v : mio mst 'a) (f : 'a -> mio mst 'b)
  : Lemma (v `satisfies` fl_v /\ (forall x. f x `satisfies` fl_f) ==> free_bind _ _ _ _ v f `satisfies` (fl_v + fl_f))
  =
  sat_le fl_v (fl_v + fl_f) v;
  let aux x : Lemma (f x `satisfies` fl_f ==> f x `satisfies` (fl_v + fl_f)) =
    sat_le fl_f (fl_v + fl_f) (f x)
  in
  Classical.forall_intro aux;
  sat_bind (fl_v + fl_f) v f

(** ** Defining F* Effect **)

type dm_gmio (a:Type) (mst:mstate) (flag:erased tflag) (wp:hist a) = t:(dm_mio mst a wp){t `satisfies` flag} 

let dm_gmio_theta #a #mst = theta #a #mio_cmds #(mio_sig mst) #event mio_wps

let dm_gmio_return (a:Type) (x:a) mst : dm_gmio a mst NoActions (hist_return x) by (compute ()) =
  dm_mio_return a mst x

val dm_gmio_bind  : 
  a: Type ->
  b: Type ->
  mst: mstate ->
  flag_v : erased tflag ->
  wp_v: Hist.hist a ->
  flag_f : erased tflag ->
  wp_f: (a -> Hist.hist b) ->
  v: dm_gmio a mst flag_v wp_v ->
  f: (x: a -> dm_gmio b mst flag_f (wp_f x)) ->
  Tot (dm_gmio b mst (flag_v + flag_f) (hist_bind wp_v wp_f))

let dm_gmio_bind a b mst flag_v wp_v flag_f wp_f v f : (dm_gmio b mst (flag_v + flag_f) (hist_bind wp_v wp_f)) =
  let r = dm_mio_bind a b mst wp_v wp_f v f in
  sat_bind_add mst flag_v flag_f v f;
  dm_mio_bind_is_free_bind a b mst wp_v wp_f v f;
  assert (free_bind _ _ _ _ v f `satisfies` (flag_v + flag_f));
  r

val dm_gmio_subcomp : 
  a: Type ->
  mst:mstate ->
  flag1 : erased tflag ->
  wp1: hist a ->
  flag2 : erased tflag ->
  wp2: hist a ->
  f: dm_gmio a mst flag1 wp1 ->
  Pure (dm_gmio a mst flag2 wp2) ((flag1 <= flag2) /\ hist_ord wp2 wp1) (fun _ -> True)
let dm_gmio_subcomp a mst flag1 wp1 flag2 wp2 f =
  sat_le flag1 flag2 f;
  dm_mio_subcomp a mst wp1 wp2 f

let dm_gmio_if_then_else (a : Type u#a) (mst:mstate)
  (fl1 : erased tflag) (wp1 : hist a)
  (fl2 : erased tflag) (wp2 : hist a)
  (f : dm_gmio a mst fl1 wp1) (g : dm_gmio a mst fl2 wp2) (b : bool) : Type =
  dm_gmio a mst (fl1 + fl2) (hist_if_then_else wp1 wp2 b)


(** TODO: Look into https://github.com/FStarLang/FStar/wiki/Indexed-effects to make
    * lift substitutive
    * use primitive_extraction **)

total
reifiable
reflectable
effect {
  MIOwp (a:Type) ([@@@effect_param] mst:mstate) (flag:erased tflag) (wp : hist #event a)
  with {
       repr       = dm_gmio
     ; return     = dm_gmio_return
     ; bind       = dm_gmio_bind
     ; subcomp    = dm_gmio_subcomp
     ; if_then_else = dm_gmio_if_then_else
     }
}

let dm_gmio_partial_return 
  mst (pre:pure_pre) : dm_gmio (squash pre) mst NoActions (partial_call_wp pre) by (compute ()) =
  dm_partial_return mio_cmds (mio_sig mst) event mio_wps pre

val lift_pure_dm_gmio :
  a: Type ->
  [@@@effect_param](mst: mstate)-> // syntax ok?
  w: pure_wp a ->
  f: (eqtype_as_type unit -> PURE a w) ->
  Tot (dm_gmio a mst NoActions (wp_lift_pure_hist w))
let lift_pure_dm_gmio a mst w f = 
  lemma_wp_lift_pure_hist_implies_as_requires #a #event w;
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs : dm_gmio _ mst NoActions _ = dm_gmio_partial_return mst (as_requires w) in
  let rhs = (fun (pre:(squash (as_requires w))) -> dm_gmio_return a (f pre) mst) in
  let m = dm_gmio_bind _ _ mst NoActions _ NoActions _ lhs rhs in
  dm_gmio_subcomp a mst NoActions _ NoActions _ m
  
sub_effect PURE ~> MIOwp = lift_pure_dm_gmio

effect MIO
  (a:Type)
  (fl:erased tflag)
  (mst:mstate)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  MIOwp a mst fl (to_hist pre post) 

let static_cmd
  (#mst:mstate)
  caller
  (cmd : io_cmds)
  (arg : io_sig.args cmd) :
  MIO (io_sig.res cmd arg) IOActions mst
    (requires (fun h -> io_pre cmd arg h))
    (ensures (fun h (r:io_sig.res cmd arg) lt ->
        io_post cmd arg r /\
        lt == [convert_call_to_event caller cmd arg r])) =
  MIOwp?.reflect (MIO.Sig.Call.mio_call caller cmd arg)

let get_trace #mst () : MIOwp (Ghost.erased trace) mst GetTraceActions
  (fun p h -> p [] (Ghost.hide h)) =
  MIOwp?.reflect (MIO.Sig.Call.mio_call Prog GetTrace ())
  
let get_state #mst () : MIOwp mst.typ mst GetTraceActions
  (fun p h -> forall s. s `mst.abstracts` h ==> p [] s) =
  MIOwp?.reflect (MIO.Sig.Call.mio_call Prog GetST ())

(**
#push-options "--compat_pre_core 1"
let performance_test (#fl:tflag) (#mst:mst) : MIOwp unit mst (fl+IOActions) (fun p h -> forall lt. (List.length lt == 6) \/ (List.length lt == 7) ==> p lt ())
  by (compute ())
=
  let fd = static_cmd #mst Prog Openfile "../Makefile" in
  let fd = static_cmd Prog Openfile "../Makefile" in
  let fd = static_cmd Prog Openfile "../Makefile" in
  let fd = static_cmd Prog Openfile "../Makefile" in
  let fd = static_cmd Prog Openfile "../Makefile" in
  let fd = static_cmd Prog Openfile "../Makefile" in
  if Inl? fd then let _ = static_cmd Prog Close (Inl?.v fd) in () else 
  ()
#pop-options
