module Compiler.Languages

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Ghost

open CommonUtils

(** ** Source Language **)
include IIO

(** ** Target Language **)
(** Tlang is a language that acts as an intermediate language between the rich IIO effect that has
    rich types and pre- and post-conditions and an ML language as OCaml.

    The task of compiling an IIO computation is big and it implies converting rich types and pre- and
    post-conditions to runtime checks. Therefore, this intermediate language simplifies our work.
    By compiling to this intermediate language, we convert all of this static requirments to dynamic checks
    but we keep the post-conditions around enough to show that the computation preserves its trace
    properties.

    So, Tlang is weakly typed and its computation can have only as post-condition that it respects a 
    trace property. The pre-condition must be trivial.
**)

type monitorable_prop = (cmd:io_cmds) -> (io_sig.args cmd) -> (history:trace) -> Tot bool

unfold
let has_event_respected_pi (e:event) (check:monitorable_prop) (h:trace) : bool =
  match e with
  | EOpenfile arg _ -> check Openfile arg h
  | ERead arg _ -> check Read arg h
  | EClose arg _ -> check Close arg h

let rec enforced_locally
  (check : monitorable_prop)
  (h l: trace) :
  Tot bool (decreases l) =
  match l with
  | [] -> true
  | e  ::  t ->
    if has_event_respected_pi e check h then enforced_locally (check) (e::h) t
    else false  
  
let pi_as_hist (#a:Type) (pi:monitorable_prop) : hist a =
  (fun p h -> forall r lt. enforced_locally pi h lt ==> p lt r)

effect IIOpi (a:Type) (fl:FStar.Ghost.erased tflag) (pi : monitorable_prop) = 
  IIOwp a fl (pi_as_hist #a pi)

class tlang (t:Type u#a) (pi:monitorable_prop) = { [@@@no_method] mldummy : unit }

instance tlang_unit (pi:monitorable_prop) : tlang unit pi = { mldummy = () }
instance tlang_file_descr (pi:monitorable_prop) : tlang file_descr pi = { mldummy = () }

instance tlang_bool (pi:monitorable_prop) : tlang bool pi = { mldummy = () }
instance tlang_int (pi:monitorable_prop) : tlang int pi = { mldummy = () }
instance tlang_option (pi:monitorable_prop) t1 {| d1:tlang t1 pi |} : tlang (option t1) pi =
  { mldummy = () }
instance tlang_pair (pi:monitorable_prop) t1 {| d1:tlang t1 pi |} t2 {| d2:tlang t2 pi |} : tlang (t1 * t2) pi = 
  { mldummy = () }
instance tlang_either (pi:monitorable_prop) t1 {| d1:tlang t1 pi |} t2 {| d2:tlang t2 pi |} : tlang (either t1 t2) pi =
  { mldummy = () }
instance tlang_resexn (pi:monitorable_prop) t1 {| d1:tlang t1 pi |} : tlang (resexn t1) pi =
  { mldummy = () }

type tlang_arrow_typ (fl:erased tflag) (t1 t2:Type) pi = t1 -> IIOpi t2 fl pi

(** An tlang arrow is a statically/dynamically verified arrow to respect pi.
**)
instance tlang_arrow (#fl:erased tflag) (pi:monitorable_prop) #t1 (d1:tlang t1 pi) #t2 (d2:tlang t2 pi) : tlang (tlang_arrow_typ fl t1 t2 pi) pi =
  { mldummy = () }

(**instance tlang_fo_uint8 : tlang_fo UInt8.t = { fo_pred = () }
instance tlang_fo_string : tlang_fo string = { fo_pred = () }
instance tlang_fo_bytes : tlang_fo Bytes.bytes = { fo_pred = () }
instance tlang_fo_open_flag : tlang_fo open_flag = { fo_pred = () } 
instance tlang_fo_socket_bool_option : tlang_fo socket_bool_option = { fo_pred = () }
instance tlang_fo_file_descr : tlang_fo file_descr = { fo_pred = () }
instance tlang_fo_zfile_perm : tlang_fo zfile_perm = { fo_pred = () }
instance tlang_fo_pair_2 t1 t2 t3 {| tlang_fo t1 |} {| tlang_fo t2 |} {| tlang_fo t3 |} : tlang_fo (t1 * t2 * t3) = { fo_pred = () }
instance tlang_fo_pair_3 t1 t2 t3 t4 {| tlang_fo t1 |} {| tlang_fo t2 |} {| tlang_fo t3 |} {| tlang_fo t4 |} : tlang_fo (t1 * t2 * t3 * t4) = { fo_pred = () }
instance tlang_fo_option t1 {| tlang_fo t1 |} : tlang_fo (option t1) = { fo_pred = () }
instance tlang_fo_list t1 {| tlang_fo t1 |} : tlang_fo (list t1) = { fo_pred = () } **)
