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

effect MIOpi (a:Type) (fl:FStar.Ghost.erased tflag) (pi : policy_spec) = 
  MIOwp a fl (pi_as_hist #a pi)

class interm (t:Type u#a) (fl:erased tflag) (pi:policy_spec) = { [@@@no_method] mldummy : unit }

instance interm_unit fl pi : interm unit fl pi = { mldummy = () }
instance interm_file_descr fl pi : interm file_descr fl pi = { mldummy = () }

instance interm_pair fl pi t1 {| d1:interm t1 fl pi |} t2 {| d2:interm t2 fl pi |} : interm (t1 * t2) fl pi = 
  { mldummy = () }
instance interm_either fl pi t1 {| d1:interm t1 fl pi |} t2 {| d2:interm t2 fl pi |} : interm (either t1 t2) fl pi =
  { mldummy = () }
instance interm_resexn fl pi t1 {| d1:interm t1 fl pi |} : interm (resexn t1) fl pi =
  { mldummy = () }

type interm_arrow_typ fl pi (t1 t2:Type) = t1 -> MIOpi t2 fl pi

(** An weak arrow is a statically/dynamically verified arrow to respect pi.
**)
instance interm_arrow fl pi #t1 (d1:interm t1 fl pi) #t2 (d2:interm t2 fl pi) : interm (interm_arrow_typ fl pi t1 t2) fl pi =
  { mldummy = () }

instance interm_arrow3 fl pi
  t1 {| d1:interm t1 fl pi |}
  t2 {| d2:interm t2 fl pi |}
  t3 {| d3:interm t3 fl pi |}
  t4 {| d4:interm t4 fl pi |}
  : interm (t1 -> t2 -> t3 -> MIOpi t4 fl pi) fl pi =
  { mldummy = () }

instance interm_bool fl pi : interm bool fl pi = { mldummy = () }
instance interm_int fl pi : interm int fl pi = { mldummy = () }
instance interm_option fl pi t1 {| d1:interm t1 fl pi |} : interm (option t1) fl pi =
  { mldummy = () }
instance interm_bytes fl pi : interm Bytes.bytes fl pi = { mldummy = () }

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
