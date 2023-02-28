module Compiler.Languages

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Ghost

open CommonUtils

(** ** Source Language **)
include IIO

(** access_policy is the type of the runtime check that is enforced when instrumenting.
    A access_policy checks if the next operation with its arguments satisfy the property
    over the history. **)
type access_policy = (history:trace) -> (isTrusted:bool) -> (cmd:io_cmds) -> (io_sig.args cmd) -> Type0

unfold
let has_event_respected_pi (e:event) (ap:access_policy) (h:trace) : Type0 =
  match e with
  | EOpenfile isTrusted arg _ -> ap h isTrusted Openfile arg
  | ERead isTrusted arg _ -> ap h isTrusted Read arg
  | EWrite isTrusted arg _ -> ap h isTrusted Write arg
  | EClose isTrusted arg _ -> ap h isTrusted Close arg

(** `enforced_locally pi` is a prefix-closed safety trace property. **)
let rec enforced_locally
  (ap : access_policy)
  (h l: trace) :
  Tot Type0 (decreases l) =
  match l with
  | [] -> True
  | e  ::  t ->
    has_event_respected_pi e ap h /\ enforced_locally (ap) (e::h) t

unfold
let pi_as_hist (#a:Type) (pi:access_policy) : hist a =
  (fun p h -> forall r lt. enforced_locally pi h lt ==> p lt r)

effect IIOpi (a:Type) (fl:FStar.Ghost.erased tflag) (pi : access_policy) = 
  IIOwp a fl (pi_as_hist #a pi)

class weak (t:Type u#a) = { [@@@no_method] mldummy : unit }

instance weak_unit : weak unit = { mldummy = () }
instance weak_file_descr : weak file_descr = { mldummy = () }

instance weak_pair t1 {| d1:weak t1 |} t2 {| d2:weak t2 |} : weak (t1 * t2) = 
  { mldummy = () }
instance weak_either t1 {| d1:weak t1 |} t2 {| d2:weak t2 |} : weak (either t1 t2) =
  { mldummy = () }
instance weak_resexn t1 {| d1:weak t1 |} : weak (resexn t1) =
  { mldummy = () }

type weak_arrow_typ fl pi (t1 t2:Type) = t1 -> IIOpi t2 fl pi

(** An weak arrow is a statically/dynamically verified arrow to respect pi.
**)
instance weak_arrow fl pi #t1 (d1:weak t1) #t2 (d2:weak t2) : weak (weak_arrow_typ fl pi t1 t2) =
  { mldummy = () }

instance weak_arrow3 fl pi
  t1 {| d1:weak t1 |}
  t2 {| d2:weak t2 |}
  t3 {| d3:weak t3 |}
  t4 {| d4:weak t4 |}
  : weak (t1 -> t2 -> t3 -> IIOpi t4 fl pi) =
  { mldummy = () }

instance weak_bool : weak bool = { mldummy = () }
instance weak_int : weak int = { mldummy = () }
instance weak_option t1 {| d1:weak t1 |} : weak (option t1) =
  { mldummy = () }
instance weak_bytes : weak Bytes.bytes = { mldummy = () }

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
