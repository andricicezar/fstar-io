module Compiler.Languages

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Ghost

open CommonUtils

(** ** Source Language **)
include IIO

(** ** Target Language **)
(** ILang is a language that acts as an intermediate language between the rich IIO effect that has
    rich types and pre- and post-conditions and an ML language as OCaml.

    The task of compiling an IIO computation is big and it implies converting rich types and pre- and
    post-conditions to runtime checks. Therefore, this intermediate language simplifies our work.
    By compiling to this intermediate language, we convert all of this static requirments to dynamic checks
    but we keep the post-conditions around enough to show that the computation preserves its trace
    properties.

    So, ILang is weakly typed and its computation can have only as post-condition that it respects a 
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

class ilang (t:Type u#a) (pi:monitorable_prop) = { [@@@no_method] mldummy : unit }

instance ilang_unit (pi:monitorable_prop) : ilang unit pi = { mldummy = () }
instance ilang_file_descr (pi:monitorable_prop) : ilang file_descr pi = { mldummy = () }

instance ilang_bool (pi:monitorable_prop) : ilang bool pi = { mldummy = () }
instance ilang_int (pi:monitorable_prop) : ilang int pi = { mldummy = () }
instance ilang_option (pi:monitorable_prop) t1 {| d1:ilang t1 pi |} : ilang (option t1) pi =
  { mldummy = () }
instance ilang_pair (pi:monitorable_prop) t1 {| d1:ilang t1 pi |} t2 {| d2:ilang t2 pi |} : ilang (t1 * t2) pi = 
  { mldummy = () }
instance ilang_either (pi:monitorable_prop) t1 {| d1:ilang t1 pi |} t2 {| d2:ilang t2 pi |} : ilang (either t1 t2) pi =
  { mldummy = () }
instance ilang_resexn (pi:monitorable_prop) t1 {| d1:ilang t1 pi |} : ilang (resexn t1) pi =
  { mldummy = () }

type ilang_arrow_typ (fl:erased tflag) (t1 t2:Type) pi = t1 -> IIOpi t2 fl pi

(** An ilang arrow is a statically verified arrow to respect pi.
    It can expect an argument that respects a different pi1, or it
    can return a function that respects pi2. 
**)
instance ilang_arrow (#fl:erased tflag) (#pi1 #pi2 pi:monitorable_prop) #t1 (d1:ilang t1 pi1) #t2 (d2:ilang t2 pi2) : ilang (ilang_arrow_typ fl t1 t2 pi) pi =
  { mldummy = () }

(**instance ilang_fo_uint8 : ilang_fo UInt8.t = { fo_pred = () }
instance ilang_fo_string : ilang_fo string = { fo_pred = () }
instance ilang_fo_bytes : ilang_fo Bytes.bytes = { fo_pred = () }
instance ilang_fo_open_flag : ilang_fo open_flag = { fo_pred = () } 
instance ilang_fo_socket_bool_option : ilang_fo socket_bool_option = { fo_pred = () }
instance ilang_fo_file_descr : ilang_fo file_descr = { fo_pred = () }
instance ilang_fo_zfile_perm : ilang_fo zfile_perm = { fo_pred = () }
instance ilang_fo_pair_2 t1 t2 t3 {| ilang_fo t1 |} {| ilang_fo t2 |} {| ilang_fo t3 |} : ilang_fo (t1 * t2 * t3) = { fo_pred = () }
instance ilang_fo_pair_3 t1 t2 t3 t4 {| ilang_fo t1 |} {| ilang_fo t2 |} {| ilang_fo t3 |} {| ilang_fo t4 |} : ilang_fo (t1 * t2 * t3 * t4) = { fo_pred = () }
instance ilang_fo_option t1 {| ilang_fo t1 |} : ilang_fo (option t1) = { fo_pred = () }
instance ilang_fo_list t1 {| ilang_fo t1 |} : ilang_fo (list t1) = { fo_pred = () } **)
