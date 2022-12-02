module Compiler.Languages

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Ghost

open CommonUtils
open TC.Monitorable.Hist

(** ** IIO **)
include IIO2

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



(** ** RILang **)

class rilang (t:Type u#a) (pi:monitorable_prop) = { 
  [@@@no_method]
  mldummy : unit }

instance rilang_unit (pi:monitorable_prop) : rilang unit pi = { mldummy = () }
instance rilang_file_descr (pi:monitorable_prop) : rilang file_descr pi = { mldummy = () }

instance rilang_bool (pi:monitorable_prop) : rilang bool pi = { mldummy = () }
instance rilang_int (pi:monitorable_prop) : rilang int pi = { mldummy = () }
instance rilang_option (pi:monitorable_prop) t1 {| d1:rilang t1 pi |} : rilang (option t1) pi =
  { mldummy = () }
instance rilang_pair (pi:monitorable_prop) t1 {| d1:rilang t1 pi |} t2 {| d2:rilang t2 pi |} : rilang (t1 * t2) pi = 
  { mldummy = () }
instance rilang_either (pi:monitorable_prop) t1 {| d1:rilang t1 pi |} t2 {| d2:rilang t2 pi |} : rilang (either t1 t2) pi =
  { mldummy = () }
instance rilang_resexn (pi:monitorable_prop) t1 {| d1:rilang t1 pi |} : rilang (resexn t1) pi =
  { mldummy = () }

type rilang_dm (pi:monitorable_prop) (a:Type) = c:(IO.Sig.iio a){pi_as_hist pi `Hist.hist_ord` IIO.dm_iio_theta c} 

let as_rilang_dm (w:IIO.dm_iio 'a (pi_as_hist 'p)) : rilang_dm 'p 'a = w

let as_iio_dm (w:rilang_dm 'p 'a) : IIO.dm_iio 'a (pi_as_hist 'p) = 
  let tree : IO.Sig.iio 'a = w in
  assert (pi_as_hist 'p `Hist.hist_ord` IIO.dm_iio_theta tree);
  tree

type rilang_arrow_typ (t1 t2:Type) pi = t1 -> rilang_dm pi t2

instance rilang_arrow (#pi1 #pi2 pi:monitorable_prop) #t1 (d1:rilang t1 pi1) #t2 (d2:rilang t2 pi2) : rilang (rilang_arrow_typ t1 t2 pi) pi =
  { mldummy = () }


(** ** MLang **)
noeq type monad = {
  m    : Type u#a -> Type u#(max 1 a);
  ret  : #a:Type -> a -> m a;
  (* TODO: bind should be polymorphic in two universes *)
  bind : #a:Type u#a -> #b:Type u#a -> m a -> (a -> m b) -> m b;
  (* We don't want acts to be part of this monad because we want to provide different versions *)
}

val free : monad
let free = { 
  m = IO.Sig.iio; 
  ret = IO.Sig.iio_return; 
  bind = IO.Sig.iio_bind; 
}

type acts (mon:monad) = op:(Universe.raise_t IO.Sig.io_cmds) -> arg:IO.Sig.io_sig.args (Universe.downgrade_val op) -> mon.m (IO.Sig.io_sig.res (Universe.downgrade_val op) arg)

(** **** Free Actions **)
val free_acts : acts free
let free_acts cmd arg = IO.Sig.Call.iio_call (Universe.downgrade_val cmd) arg

let spec_free_acts (ca:acts free) =
  (forall (cmd:IO.Sig.io_cmds) (arg:IO.Sig.io_sig.args cmd). IO.Sig.iio_wps cmd arg `Hist.hist_ord` IIO.dm_iio_theta (ca (Universe.raise_val cmd) arg))

let lemma_free_acts () : Lemma (spec_free_acts free_acts) = 
  assert (forall (cmd:IO.Sig.io_cmds) (arg:IO.Sig.io_sig.args cmd). IO.Sig.iio_wps cmd arg `Hist.hist_ord` IIO.dm_iio_theta (free_acts (Universe.raise_val cmd) arg));
  assert (spec_free_acts free_acts) by (assumption ())

(** ** MLang **)
class mlang (t:Type u#a) = { [@@@no_method] mldummy : unit }

(** *** FO instances **)
instance mlang_unit : mlang unit = { mldummy = () }

instance mlang_bool : mlang bool = { mldummy = () }
instance mlang_int : mlang int = { mldummy = () }

instance mlang_pair t1 t2 {| d1:mlang t1 |} {| d2:mlang t2 |} : mlang (t1 * t2) = 
  { mldummy = () }
instance mlang_either t1 t2 {| d1:mlang t1 |} {| d2:mlang t2 |} : mlang (either t1 t2) =
  { mldummy = () }

instance mlang_free_arrow #t1 #t2 (d1:mlang t1) (d2:mlang t2) : mlang (t1 -> free.m t2) =
  { mldummy = () }

instance mlang_effectpoly 
  (#ct:(Type->Type)->Type)
  (d1:mlang (ct free.m)) : 
  mlang (mon:monad -> acts mon -> ct mon.m) =
  { mldummy = () }

let dm_mon (pi:monitorable_prop) : monad = {
  m = rilang_dm pi;
  ret = (fun (x:'a) -> IIO.dm_iio_return 'a x);
  bind = (fun (m:rilang_dm pi 'a) (k:'a -> rilang_dm pi 'b) -> 
    let wp : Hist.hist 'b = Hist.hist_bind (pi_as_hist #'a pi) (fun _ -> pi_as_hist pi) in 
    let tr : IIO.dm_iio 'b wp = IIO.dm_iio_bind _ _ _ _ (as_iio_dm m) (fun x -> as_iio_dm (k x)) in
    lemma_bind_pi_implies_pi #'a #'b pi;
    let w = IIO.dm_iio_subcomp 'b wp (pi_as_hist pi) tr in
    as_rilang_dm w)
}

assume val dm_acts (pi:monitorable_prop) : acts (dm_mon pi)


(** *** Manual tests *)
(** Manual tests of MLang. 
    Types of programs that should be part of MLang:
   - [v] int -> free.m int
   - [ ] int -> free.m (int -> free.m int)
   - [v] (int -> free.m int) -> free.m int (?)
   - [v] mon:monad -> acts mon -> int -> mon.m int 
   - [v] mon:monad -> acts mon -> (int -> mon.m int) -> mon.m int 
   - [ ] mon:monad -> acts mon -> int -> mon.m (int -> mon.m int)
   - [v] (mon:monad -> acts mon -> int -> mon.m int) -> free.m int
   - [v] (mon:monad -> acts mon -> (int -> mon.m int) -> mon.m int) -> free.m int 

   Types of programs that should not be part of MLang:
   - [ ] how can I identify such cases?
**)

let test_mlang_free_arrow : mlang (int -> free.m int) =
  mlang_free_arrow mlang_int mlang_int

(** Cannot be typed because universe problems
let test_mlang_free_arrow_rhs_ho : mlang (int (int -> free.m int) -> free.m int) =
  mlang_free_arrow free.m mlang_int (mlang_free_arrow free.m mlang_int mlang_int)
 **)

let test_mlang_free_arrow_lhs_ho : mlang ((int -> free.m int) -> free.m int) =
  mlang_free_arrow (mlang_free_arrow mlang_int mlang_int) mlang_int

let test_mlang_fo_effectpoly : mlang (mon:monad -> acts mon -> int -> mon.m int) =
  mlang_effectpoly #(fun m -> int -> m int) (mlang_free_arrow mlang_int mlang_int)

let test_mlang_lhs_ho_effectpoly : mlang (mon:monad -> acts mon -> (int -> mon.m int) -> mon.m int) =
  mlang_effectpoly #(fun m -> (int -> m int) -> m int) (mlang_free_arrow (mlang_free_arrow mlang_int mlang_int) mlang_int)

(** This can not be typed because universe problems: 
let test_mlang_rhs_ho_effectpoly : mlang (mon:monad -> acts mon -> int -> mon.m (int -> mon.m int)) = **)

let test_mlang_prog1 : mlang ((mon:monad -> acts mon -> int -> mon.m int) -> free.m int) =
  mlang_free_arrow
    (mlang_effectpoly #(fun m -> int -> m int) (mlang_free_arrow mlang_int mlang_int))
    mlang_int

let test_mlang_prog2 : mlang ((mon:monad -> acts mon -> (int -> mon.m int) -> mon.m int) -> free.m int) =
  mlang_free_arrow
    (mlang_effectpoly 
      #(fun m -> (int -> m int) -> m int)
      (mlang_free_arrow (mlang_free_arrow mlang_int mlang_int) mlang_int))
    mlang_int
