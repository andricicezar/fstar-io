module Compiler.Languages

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Ghost

open CommonUtils

(** ** Source Language **)
include MIO

(** policy_spec is the type of the runtime check that is enforced when instrumenting.
    A policy_spec checks if the next operation with its arguments satisfy the property
    over the history. **)
type policy_spec = (history:trace) -> (isTrusted:bool) -> (cmd:io_cmds) -> (io_sig.args cmd) -> Type0

unfold
let has_event_respected_pi (e:event) (pi:policy_spec) (h:trace) : Type0 =
  match e with
  | EOpenfile isTrusted arg _ -> pi h isTrusted Openfile arg
  | ERead isTrusted arg _ -> pi h isTrusted Read arg
  | EWrite isTrusted arg _ -> pi h isTrusted Write arg
  | EClose isTrusted arg _ -> pi h isTrusted Close arg

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

effect MIOpi (a:Type) (mst:mst) (fl:FStar.Ghost.erased tflag) (pi : policy_spec) = 
  MIOwp a mst fl (pi_as_hist #a pi)

// TODO: do we really need mst?
class weak (t:Type u#a) (mst:mst) (fl:erased tflag) (pi:policy_spec) = { [@@@no_method] mldummy : unit }

instance weak_unit mst fl pi : weak unit mst fl pi = { mldummy = () }
instance weak_file_descr mst fl pi : weak file_descr mst fl pi = { mldummy = () }

instance weak_pair mst fl pi t1 {| d1:weak t1 mst fl pi |} t2 {| d2:weak t2 mst fl pi |} : weak (t1 * t2) mst fl pi = 
  { mldummy = () }
instance weak_either mst fl pi t1 {| d1:weak t1 mst fl pi |} t2 {| d2:weak t2 mst fl pi |} : weak (either t1 t2) mst fl pi =
  { mldummy = () }
instance weak_resexn mst fl pi t1 {| d1:weak t1 mst fl pi |} : weak (resexn t1) mst fl pi =
  { mldummy = () }

type weak_arrow_typ mst fl pi (t1 t2:Type) = t1 -> MIOpi t2 mst fl pi

(** An weak arrow is a statically/dynamically verified arrow to respect pi.
**)
instance weak_arrow mst fl pi #t1 (d1:weak t1 mst fl pi) #t2 (d2:weak t2 mst fl pi) : weak (weak_arrow_typ mst fl pi t1 t2) mst fl pi =
  { mldummy = () }

instance weak_arrow3 mst fl pi
  t1 {| d1:weak t1 mst fl pi |}
  t2 {| d2:weak t2 mst fl pi |}
  t3 {| d3:weak t3 mst fl pi |}
  t4 {| d4:weak t4 mst fl pi |}
  : weak (t1 -> t2 -> t3 -> MIOpi t4 mst fl pi) mst fl pi =
  { mldummy = () }

instance weak_bool mst fl pi : weak bool mst fl pi = { mldummy = () }
instance weak_int mst fl pi : weak int mst fl pi = { mldummy = () }
instance weak_option mst fl pi t1 {| d1:weak t1 mst fl pi |} : weak (option t1) mst fl pi =
  { mldummy = () }
instance weak_bytes mst fl pi : weak Bytes.bytes mst fl pi = { mldummy = () }

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
