module MIO.Sig

open FStar.List.Tot.Base

include CommonUtils
include Free
include Hist

unfold let no_cf (a:Type0) = r:resexn a{~(r == Inr Contract_failure)}

noeq
type io_cmds : Type0 -> Type0 =
| Openfile : string -> io_cmds (no_cf file_descr)
| Read     : file_descr -> io_cmds (no_cf string)
| Write    : file_descr -> string -> io_cmds (no_cf unit)
| Close    : file_descr -> io_cmds (no_cf unit)

type caller = Free.caller

noeq
type event =
  | EOpenfile : caller -> string -> no_cf file_descr -> event
  | ERead     : caller -> file_descr -> no_cf string -> event
  | EWrite    : caller -> file_descr -> string -> no_cf unit -> event
  | EClose    : caller -> file_descr -> no_cf unit -> event

type trace = list event

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
  s0:mst.typ -> e:event -> h : Ghost.erased trace ->
  Pure mst.typ
       (requires mst.abstracts s0 h)
       (ensures fun s1 -> mst.abstracts s1 (e::h))

noeq
type mst_impl (mst:mstate) = {
  init : (init : mst.typ{mst.abstracts init []});
  update : mst_updater mst;
}

noeq
type m_cmds (mst:mstate) : Type0 -> Type0 =
| GetTrace : m_cmds mst (Ghost.erased trace)
| GetST    : m_cmds mst mst.typ

let mio_cmds (mst:mstate) : Type0 -> Type u#1 = ev_sum io_cmds (m_cmds mst)

// THE MIO FREE MONAD
type mio (mst:mstate) (a:Type) = free (mio_cmds mst) a

let mio_return #mst (x:'a) : mio mst 'a =
  free_return x

let mio_bind #mst (#a:Type) (#b:Type) l k : mio mst b =
  free_bind l k

let convert_call_to_event
  (c:caller)
  (#r:Type0)
  (cmd:io_cmds r)
  (res:r) : event =
  match cmd with
  | Openfile arg -> EOpenfile c arg res
  | Read arg     -> ERead c arg res
  | Write fd s   -> EWrite c fd s res
  | Close arg    -> EClose c arg res

// OTHER TYPES & UTILS
unfold
let apply_changes (history local_events:trace) : Tot trace =
  (List.rev local_events) @ history

let destruct_event (e:event) : (caller & r:Type0 & io_cmds r & r) =
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

unfold let io_pre (#r:Type0) (cmd:io_cmds r) (h:trace) : Type0 =
  True

unfold let io_post (#r:Type0) (cmd:io_cmds r) (res:r) : Type0 =
  True

unfold let mio_wps #mst (c:caller) (#r:Type0) (cmd:mio_cmds mst r) : hist #event r =
  fun (p : hist_post #event r) h ->
  match cmd with
  | InEv2 GetTrace ->
    let p : hist_post (Ghost.erased trace) = p in
    p [] (Ghost.hide h)
  | InEv2 GetST -> forall (s:mst.typ). s `mst.abstracts` h ==> p [] s
  | InEv1 iocmd -> io_pre iocmd h /\ (forall (res:r). io_post iocmd res ==> p [convert_call_to_event c iocmd res] res)

open DMFree

(** Instantiation of the Dijkstra monad from DMFree with MIO events **)

let mio_dm (mst:mstate) (a:Type) (wp:hist #event a) =
  dm (mio_cmds mst) event mio_wps a wp

let mio_dm_return (mst:mstate) #a (x:a) : mio_dm mst a (hist_return #a #event x) =
  dm_return event mio_wps x

#push-options "--z3rlimit 40"
let mio_dm_bind (mst:mstate) #a #b
  (wp_v : hist #event a)
  (wp_f : a -> hist #event b)
  (v : mio_dm mst a wp_v)
  (f : (x:a -> mio_dm mst b (wp_f x))) :
  Tot (mio_dm mst b (hist_bind wp_v wp_f)) =
  dm_bind event mio_wps wp_v wp_f v f
#pop-options

let mio_dm_subcomp (mst:mstate) #a (wp1 wp2 : hist #event a) (f : mio_dm mst a wp1) :
  Pure (mio_dm mst a wp2)
    (requires wp1 ⊑ wp2)
    (ensures fun _ -> True) =
  dm_subcomp event mio_wps wp1 wp2 f

let mio_dm_if_then_else (mst:mstate) #a
  (wp1 wp2 : hist #event a) (f : mio_dm mst a wp1) (g : mio_dm mst a wp2) (b : bool) : Type =
  dm_if_then_else event mio_wps wp1 wp2 f g b

let mio_dm_partial_return (mst:mstate)
  (pre:pure_pre) : mio_dm mst (squash pre) (partial_call_wp pre) =
  dm_partial_return event mio_wps pre

#push-options "--z3rlimit 40"
let mio_dm_lift_pure (mst:mstate) #a
  (w : pure_wp a)
  (f : (eqtype_as_type unit -> PURE a w)) :
  mio_dm mst a (wp_lift_pure_hist w) =
  lift_pure_dm event mio_wps w f
#pop-options
