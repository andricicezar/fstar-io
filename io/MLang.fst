module MLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common

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
class mlang (t:Type u#a) = { mldummy : unit }

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
