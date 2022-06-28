module ILang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common

open TC.Monitorable.Hist

(** ** ILang **)
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


  
unfold let pi_hist (a:Type) (pi:monitorable_prop) : Hist.hist a =
  (fun p h -> forall r lt. enforced_locally pi h lt ==> p lt r)

effect IIOpi (a:Type) (pi : monitorable_prop) = 
  IIO.IIOwp a (pi_hist a pi)

class ilang (t:Type u#a) (pi:monitorable_prop) = { mldummy : unit }

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

type verified_arrow (t1 t2:Type) pi = t1 -> IIOpi (resexn t2) pi

instance ilang_arrow (pi:monitorable_prop) t1 {| d1:ilang t1 pi |} t2 {| d2:ilang t2 pi |} : ilang (verified_arrow t1 t2 pi) pi =
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
