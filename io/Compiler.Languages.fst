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

(* Interesting regression, this is now not obvious. Is it due to the new
shape of enforced_locally? *)
//let enforced_locally_nil
//  (ap : access_policy)
//  (h : trace)
//  : Lemma (enforced_locally ap h [])
//    [SMTPat (enforced_locally ap h [])]
//  = assert_norm (enforced_locally ap h [])

let pi_as_hist (#a:Type) (pi:access_policy) : hist a =
  (fun p h -> forall r lt. enforced_locally pi h lt ==> p lt r)

effect IIOpi (a:Type) (fl:FStar.Ghost.erased tflag) (pi : access_policy) = 
  IIOwp a fl (pi_as_hist #a pi)

class weak (t:Type u#a) (fl:erased tflag) (pi:access_policy) = { [@@@no_method] mldummy : unit }

instance weak_unit fl pi : weak unit fl pi = { mldummy = () }
instance weak_file_descr fl pi : weak file_descr fl pi = { mldummy = () }

instance weak_pair fl pi t1 {| d1:weak t1 fl pi |} t2 {| d2:weak t2 fl pi |} : weak (t1 * t2) fl pi = 
  { mldummy = () }
instance weak_either fl pi t1 {| d1:weak t1 fl pi |} t2 {| d2:weak t2 fl pi |} : weak (either t1 t2) fl pi =
  { mldummy = () }
instance weak_resexn fl pi t1 {| d1:weak t1 fl pi |} : weak (resexn t1) fl pi =
  { mldummy = () }

type weak_arrow_typ fl pi (t1 t2:Type) = t1 -> IIOpi t2 fl pi

(** An weak arrow is a statically/dynamically verified arrow to respect pi.
**)
instance weak_arrow fl pi #t1 (d1:weak t1 fl pi) #t2 (d2:weak t2 fl pi) : weak (weak_arrow_typ fl pi t1 t2) fl pi =
  { mldummy = () }

instance weak_bool fl pi : weak bool fl pi = { mldummy = () }
instance weak_int fl pi : weak int fl pi = { mldummy = () }
instance weak_option fl pi t1 {| d1:weak t1 fl pi |} : weak (option t1) fl pi =
  { mldummy = () }

(**instance weak_fo_uint8 : weak_fo UInt8.t = { fo_pred = () }
instance weak_fo_string : weak_fo string = { fo_pred = () }
instance weak_fo_bytes : weak_fo Bytes.bytes = { fo_pred = () }
instance weak_fo_open_flag : weak_fo open_flag = { fo_pred = () } 
instance weak_fo_socket_bool_option : weak_fo socket_bool_option = { fo_pred = () }
instance weak_fo_file_descr : weak_fo file_descr = { fo_pred = () }
instance weak_fo_zfile_perm : weak_fo zfile_perm = { fo_pred = () }
instance weak_fo_pair_2 t1 t2 t3 {| weak_fo t1 |} {| weak_fo t2 |} {| weak_fo t3 |} : weak_fo (t1 * t2 * t3) = { fo_pred = () }
instance weak_fo_pair_3 t1 t2 t3 t4 {| weak_fo t1 |} {| weak_fo t2 |} {| weak_fo t3 |} {| weak_fo t4 |} : weak_fo (t1 * t2 * t3 * t4) = { fo_pred = () }
instance weak_fo_option t1 {| weak_fo t1 |} : weak_fo (option t1) = { fo_pred = () }
instance weak_fo_list t1 {| weak_fo t1 |} : weak_fo (list t1) = { fo_pred = () } **)
