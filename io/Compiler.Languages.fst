module Compiler.Languages

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Ghost

open CommonUtils

include MIO

  
(** policy_spec is the type of the runtime check that is enforced when instrumenting.
    A policy_spec checks if the next operation with its arguments satisfy the property
    over the history. **)
type policy_spec = (history:trace) -> caller -> (cmd:io_cmds) -> (io_sig.args cmd) -> Type0

type policy (sgm:policy_spec) (mst:mstate) =
  s:mst.typ -> cmd:io_cmds -> arg:io_sig.args cmd -> r:bool{r ==> (forall h. s `mst.abstracts` h ==> sgm h Ctx cmd arg)}

unfold
let has_event_respected_sgm (e:event) (sgm:policy_spec) (h:trace) : Type0 =
  let (| caller, cmd, arg, _ |) = destruct_event e in
  sgm h caller cmd arg

(** `enforced_locally sgm` is a prefix-closed safety trace property. **)
let rec enforced_locally
  (sgm : policy_spec)
  (h l: trace) :
  Tot Type0 (decreases l) =
  match l with
  | [] -> True
  | e  ::  t ->
    has_event_respected_sgm e sgm h /\ enforced_locally sgm (e::h) t

unfold
let sgm_as_hist (#a:Type) (sgm:policy_spec) : hist a =
  (fun p h -> forall r lt. enforced_locally sgm h lt ==> p lt r)

effect MIOpi (a:Type) (fl:FStar.Ghost.erased tflag) (sgm : policy_spec) (mst:mstate) = 
  MIOwp a mst fl (sgm_as_hist #a sgm)


type io_lib (fl:erased tflag) (sgm:policy_spec) (mst:mstate) (c:caller) =
  (cmd : io_cmds) ->
  (arg : io_sig.args cmd) ->
  MIO (io_resm cmd arg) fl mst
    (requires (fun _ -> True))
    (ensures (fun h r lt ->
      enforced_locally sgm h lt /\
      (match r with
       | Inr Contract_failure -> lt == []
       | r' -> io_post cmd arg r' /\ lt == [convert_call_to_event c cmd arg r'])))

#push-options "--compat_pre_core 1" // fixme
val inst_io_cmds : #mst:mstate -> #sgm:policy_spec -> pi:policy sgm mst -> io_lib AllActions sgm mst Ctx
let inst_io_cmds pi cmd arg =
  let s0 = get_state () in
  if pi s0 cmd arg then (
    let r : io_resm' cmd arg = static_cmd Ctx cmd arg in
    r
  ) else Inr Contract_failure
#pop-options



class interm (t:Type u#a) (fl:erased tflag) (sgm:policy_spec) (mst:mstate) = { [@@@no_method] mldummy : unit }

instance interm_unit fl sgm mst : interm unit fl sgm mst = { mldummy = () }
instance interm_file_descr fl sgm mst : interm file_descr fl sgm mst = { mldummy = () }

instance interm_pair fl sgm mst t1 {| d1:interm t1 fl sgm mst |} t2 {| d2:interm t2 fl sgm mst |} : interm (t1 * t2) fl sgm mst = 
  { mldummy = () }
instance interm_either fl sgm mst t1 {| d1:interm t1 fl sgm mst |} t2 {| d2:interm t2 fl sgm mst |} : interm (either t1 t2) fl sgm mst =
  { mldummy = () }
instance interm_resexn fl sgm mst t1 {| d1:interm t1 fl sgm mst |} : interm (resexn t1) fl sgm mst =
  { mldummy = () }

type interm_arrow_typ fl sgm mst (t1 t2:Type) = t1 -> MIOpi t2 fl sgm mst

(** An weak arrow is a statically/dynamically verified arrow to respect sgm.
**)
instance interm_arrow fl sgm mst #t1 (d1:interm t1 fl sgm mst) #t2 (d2:interm t2 fl sgm mst) : interm (interm_arrow_typ fl sgm mst t1 t2) fl sgm mst =
  { mldummy = () }

instance interm_arrow3 fl sgm mst
  t1 {| d1:interm t1 fl sgm mst |}
  t2 {| d2:interm t2 fl sgm mst |}
  t3 {| d3:interm t3 fl sgm mst |}
  t4 {| d4:interm t4 fl sgm mst |}
  : interm (t1 -> t2 -> t3 -> MIOpi t4 fl sgm mst) fl sgm mst =
  { mldummy = () }

instance interm_bool fl sgm mst : interm bool fl sgm mst = { mldummy = () }
instance interm_int fl sgm mst : interm int fl sgm mst = { mldummy = () }
instance interm_option fl sgm mst t1 {| d1:interm t1 fl sgm mst |} : interm (option t1) fl sgm mst =
  { mldummy = () }
instance interm_bytes fl sgm mst : interm Bytes.bytes fl sgm mst = { mldummy = () }

(**instance weak_fo_uint8 : weak_fo UInt8.t = { fo_pred = () }
instance weak_fo_string : weak_fo string = { fo_pred = () }
instance weak_fo_open_flag : weak_fo open_flag = { fo_pred = () } 
instance weak_fo_socket_bool_option : weak_fo socket_bool_option = { fo_pred = () }
instance weak_fo_file_descr : weak_fo file_descr = { fo_pred = () }
instance weak_fo_zfile_perm : weak_fo zfile_perm = { fo_pred = () }
instance weak_fo_pair_2 t1 t2 t3 {| weak_fo t1 |} {| weak_fo t2 |} {| weak_fo t3 |} : weak_fo (t1 * t2 * t3) = { fo_pred = () }
instance weak_fo_pair_3 t1 t2 t3 t4 {| weak_fo t1 |} {| weak_fo t2 |} {| weak_fo t3 |} {| weak_fo t4 |} : weak_fo (t1 * t2 * t3 * t4) = { fo_pred = () }
instance weak_fo_option t1 {| weak_fo t1 |} : weak_fo (option t1) = { fo_pred = () }
instance weak_fo_list t1 {| weak_fo t1 |} : weak_fo (list t1) = { fo_pred = () } **)
