module MIO.Sig

open FStar.List.Tot.Base

include Free
include Hist


type file_descr = int
exception Contract_failure
type resexn a = either a exn

unfold let no_cf (a:Type) = r:resexn a{~(r == Inr Contract_failure)}

(** IO commands (parameterize the free monad). *)
noeq
type io_cmds : Type0 -> Type0 =
| Openfile : string -> io_cmds (no_cf file_descr)
| Read     : file_descr -> io_cmds (no_cf string)
| Write    : file_descr -> string -> io_cmds (no_cf unit)
| Close    : file_descr -> io_cmds (no_cf unit)

(** IO events (parameterize the hist monad).
    Each event records the command, caller, and result. *)
noeq
type io_event =
  | EOpenfile : caller -> string -> no_cf file_descr -> io_event
  | ERead     : caller -> file_descr -> no_cf string -> io_event
  | EWrite    : caller -> file_descr -> string -> no_cf unit -> io_event
  | EClose    : caller -> file_descr -> no_cf unit -> io_event

type trace = list io_event

(** We only need GetTrace/GetST because we assume that our actions are
updating the trace for us. Therefore, at extraction, our actions
should be linked with wrapped primitives that initialize a
trace on the heap (?) and updates it with events.
GetTrace will be linked with a function that returns the reference
to the trace from the heap. **)

(* Monitoring state. *)
[@@erasable]
noeq
type mstate = {
  typ : Type0;
  abstracts : typ -> trace -> Type0;
}

type mst_updater (mst:mstate) : Type0 =
  s0:mst.typ -> e:io_event -> h : Ghost.erased trace ->
  Pure mst.typ
       (requires mst.abstracts s0 h)
       (ensures fun s1 -> mst.abstracts s1 (e::h))

noeq
type mst_impl (mst:mstate) = {
  init : (init : mst.typ{mst.abstracts init []});
  update : mst_updater mst;
}

(** Monitoring commands. *)
noeq
type m_cmds (mst:mstate) : Type0 -> Type0 =
| GetTrace : m_cmds mst (Ghost.erased trace)
| GetST    : m_cmds mst mst.typ

(** Combined MIO commands = io_cmds + m_cmds. *)
let mio_cmds (mst:mstate) : Type0 -> Type u#1 = cmd_sum io_cmds (m_cmds mst)

// THE MIO FREE MONAD
type mio (mst:mstate) (a:Type) = free (mio_cmds mst) a

let mio_return #mst (x:'a) : mio mst 'a =
  free_return x

let mio_bind #mst (#a:Type) (#b:Type) l k : mio mst b =
  free_bind l k

let convert_call_to_event
  (c:caller)
  (#r:Type0)
  (op:io_cmds r)
  (res:r) : io_event =
  match op with
  | Openfile arg -> EOpenfile c arg res
  | Read arg     -> ERead c arg res
  | Write fd s   -> EWrite c fd s res
  | Close arg    -> EClose c arg res

// OTHER TYPES & UTILS
unfold
let apply_changes (history local_events:trace) : Tot trace =
  (List.rev local_events) @ history

let destruct_event (e:io_event) : (caller & r:Type0 & io_cmds r & r) =
  match e with
  | EOpenfile c arg res -> (| c, no_cf file_descr, Openfile arg, res |)
  | ERead c arg res     -> (| c, no_cf string, Read arg, res |)
  | EWrite c fd s res   -> (| c, no_cf unit, Write fd s, res |)
  | EClose c arg res    -> (| c, no_cf unit, Close arg, res |)

let rec is_open (fd:file_descr) (h:trace) : bool =
  match h with
  | [] -> false
  | h :: tail -> match h with
               | EOpenfile _ _ (Inl fd') ->
                   if fd = fd' then true
                   else is_open fd tail
               | EClose _ fd' _ ->
                    if fd = fd' then false
                    else is_open fd tail
               | _ -> is_open fd tail

unfold let io_pre (#r:Type0) (op:io_cmds r) (h:trace) : Type0 =
  True

unfold let io_post (#r:Type0) (op:io_cmds r) (res:r) : Type0 =
  True

(** Command WP: maps each MIO command to a hist-based WP over io_events. *)
unfold let mio_cwp #mst (c:caller) (#r:Type0) (op:mio_cmds mst r) : hist #io_event r =
  fun (p : hist_post #io_event r) h ->
  match op with
  | CmdR GetTrace ->
    let p : hist_post (Ghost.erased trace) = p in
    p [] (Ghost.hide h)
  | CmdR GetST -> forall (s:mst.typ). s `mst.abstracts` h ==> p [] s
  | CmdL iocmd -> io_pre iocmd h /\ (forall (res:r). io_post iocmd res ==> p [convert_call_to_event c iocmd res] res)

open GuardedDMFree

(** Instantiation of the Dijkstra monad from DMFree with MIO commands/events **)

let mio_dm (mst:mstate) (a:Type) (wp:hist #io_event a) =
  gdm (mio_cmds mst) io_event mio_cwp a wp

let mio_dm_return (mst:mstate) #a (x:a) : mio_dm mst a (hist_return #a #io_event x) =
  gdm_return mio_cwp x

#push-options "--z3rlimit 40"
let mio_dm_bind (mst:mstate) #a #b
  (wp_v : hist #io_event a)
  (wp_f : a -> hist #io_event b)
  (v : mio_dm mst a wp_v)
  (f : (x:a -> mio_dm mst b (wp_f x))) :
  Tot (mio_dm mst b (hist_bind wp_v wp_f)) =
  gdm_bind mio_cwp wp_v wp_f v f
#pop-options

let mio_dm_subcomp (mst:mstate) #a (wp1 wp2 : hist #io_event a) (f : mio_dm mst a wp1) :
  Pure (mio_dm mst a wp2)
    (requires wp1 ⊑ wp2)
    (ensures fun _ -> True) =
  gdm_subcomp mio_cwp wp1 wp2 f

let mio_dm_if_then_else (mst:mstate) #a
  (wp1 wp2 : hist #io_event a) (f : mio_dm mst a wp1) (g : mio_dm mst a wp2) (b : bool) : Type =
  gdm_if_then_else mio_cwp wp1 wp2 f g b

let mio_dm_guard_return (mst:mstate)
  (pre:pure_pre) : mio_dm mst (squash pre) (guard_wp pre) =
  gdm_guard mio_cwp pre

let mio_dm_lift_pure (mst:mstate) #a
  (w : pure_wp a)
  (f : (eqtype_as_type unit -> PURE a w)) :
  mio_dm mst a (wp_lift_pure_hist w) =
  lift_pure_gdm mio_cwp w f
