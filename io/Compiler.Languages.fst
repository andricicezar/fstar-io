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

type policy (mst:mst) (pi:policy_spec) =
  s:mst.cst -> cmd:io_cmds -> arg:io_sig.args cmd -> r:bool{r ==> (forall h. mst.models s h ==> pi h Ctx cmd arg)}

unfold
let has_event_respected_pi (e:event) (pi:policy_spec) (h:trace) : Type0 =
  match e with
  | EOpenfile caller arg _ -> pi h caller Openfile arg
  | ERead caller arg _ -> pi h caller Read arg
  | EWrite caller arg _ -> pi h caller Write arg
  | EClose caller arg _ -> pi h caller Close arg

(** `enforced_locally pi` is a prefix-closed safety trace property. **)
let rec enforced_locally
  (pi : policy_spec)
  (h l: trace) :
  Tot Type0 (decreases l) =
  match l with
  | [] -> True
  | e  ::  t ->
    has_event_respected_pi e pi h /\ enforced_locally pi (e::h) t

unfold
let pi_as_hist (#a:Type) (pi:policy_spec) : hist a =
  (fun p h -> forall r lt. enforced_locally pi h lt ==> p lt r)

effect MIOpi (a:Type) (fl:FStar.Ghost.erased tflag) (pi : policy_spec) (mst:mst) = 
  MIOwp a mst fl (pi_as_hist #a pi)

class interm (t:Type u#a) (fl:erased tflag) (pi:policy_spec) (mst:mst) = { [@@@no_method] mldummy : unit }

instance interm_unit fl pi mst : interm unit fl pi mst = { mldummy = () }
instance interm_file_descr fl pi mst : interm file_descr fl pi mst = { mldummy = () }

instance interm_pair fl pi mst t1 {| d1:interm t1 fl pi mst |} t2 {| d2:interm t2 fl pi mst |} : interm (t1 * t2) fl pi mst = 
  { mldummy = () }
instance interm_either fl pi mst t1 {| d1:interm t1 fl pi mst |} t2 {| d2:interm t2 fl pi mst |} : interm (either t1 t2) fl pi mst =
  { mldummy = () }
instance interm_resexn fl pi mst t1 {| d1:interm t1 fl pi mst |} : interm (resexn t1) fl pi mst =
  { mldummy = () }

type interm_arrow_typ fl pi mst (t1 t2:Type) = t1 -> MIOpi t2 fl pi mst

(** An weak arrow is a statically/dynamically verified arrow to respect pi.
**)
instance interm_arrow fl pi mst #t1 (d1:interm t1 fl pi mst) #t2 (d2:interm t2 fl pi mst) : interm (interm_arrow_typ fl pi mst t1 t2) fl pi mst =
  { mldummy = () }

instance interm_arrow3 fl pi mst
  t1 {| d1:interm t1 fl pi mst |}
  t2 {| d2:interm t2 fl pi mst |}
  t3 {| d3:interm t3 fl pi mst |}
  t4 {| d4:interm t4 fl pi mst |}
  : interm (t1 -> t2 -> t3 -> MIOpi t4 fl pi mst) fl pi mst =
  { mldummy = () }

instance interm_bool fl pi mst : interm bool fl pi mst = { mldummy = () }
instance interm_int fl pi mst : interm int fl pi mst = { mldummy = () }
instance interm_option fl pi mst t1 {| d1:interm t1 fl pi mst |} : interm (option t1) fl pi mst =
  { mldummy = () }
instance interm_bytes fl pi mst : interm Bytes.bytes fl pi mst = { mldummy = () }

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
