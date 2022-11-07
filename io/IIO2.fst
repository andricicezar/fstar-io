module IIO2

open FStar.Tactics
open ExtraTactics
open FStar.Calc

open Common
open DMFree
open IO.Sig
open IO.Sig.Call
open IO
open IIO

let rec contains (m:iio 'a) =
match m with
| Return x -> False
| Call GetTrace _ _ -> True 
| Call cmd arg k -> forall r. contains (k r)
| PartialCall pre k -> forall r. contains (k r)

type gio (flag:bool) (a:Type) = t:(dm_iio a trivial_hist){contains t ==> flag} 
  // if the tree contains GetTrace, then the flag must be true

type gio_arr (a:Type) (flag1:bool) (b:Type) (flag2:bool{flag1 ==> flag2}) = 
  #flag3:bool{flag1 ==> flag3} -> gio flag3 a -> gio (flag2 || flag3) b

(** *** Proof of Concept **)
(** we only need prog_s to use the special arrow **)
type prog_s = gio_arr unit false unit false
type ctx_t = m:(Type -> Type) -> m unit

(** ctx gets from the start instantiated with gio true **)
let instrument (c:ctx_t) : gio true unit = c (gio true)

let compile_prog (p:prog_s) : (gio_arr unit true unit true) =
  fun cs -> p cs

let link (p:prog_s) (c:ctx_t) = 
  (compile_prog p) (c (gio true))

let test_type : prog_s = fun c -> 
  io_call Openfile "../asdf"


(** *** Lift from IO to GIO *)
let dm_io' = dm_io unit trivial_hist

type prog_s = gio false -> gio false
type prog_i = gio_arr false false

val comp0 : prog_s -> prog_i
let comp0 p #flag c = p c

type prog_t = gio_arr true true 

val comp1 : prog_i -> prog_t
let comp1 p (c:gio true) =
  gio_arr_apply p c

(** TESTS **)
let gio_arr_apply (#flag1:bool) (#flag2:bool{flag1 ==> flag2}) (f:gio_arr 'a flag1 'b flag2) (x:gio 'flag3 'a) : Pure (gio (flag2 || 'flag3) 'b)
  (requires (flag1 ==> 'flag3)) 
  (ensures (fun _ -> True)) =
  f x 

assume val t1 : Type
assume val t2 : Type

assume val f1 : gio_arr t1 false t2 false
assume val f2 : gio_arr t1 false t2 true
[@@expect_failure]
assume val f2' : gio_arr t1 true t2 false
assume val f3 : gio_arr t1 true t2 true
assume val c1 : gio true t1
assume val c2 : gio false t1

[@@expect_failure]
let test1' : gio false t2 = gio_arr_apply f1 c1
let test1 : gio true t2 = gio_arr_apply f1 c1
[@@expect_failure]
let test2' : gio false t2 = gio_arr_apply f2 c1
let test2 : gio true t2 = gio_arr_apply f2 c1
[@@expect_failure]
let test3' : gio false t2 = gio_arr_apply f3 c1
let test3 : gio true t2 = gio_arr_apply f3 c1
let test4' : gio true t2 = gio_arr_apply f1 c2
let test4 : gio false t2 = gio_arr_apply f1 c2
[@@expect_failure]
let test5' : gio false t2 = gio_arr_apply f2 c2
let test5 : gio true t2 = gio_arr_apply f2 c2
[@@expect_failure]
let test6 : gio true t2 = gio_arr_apply f3 c2
