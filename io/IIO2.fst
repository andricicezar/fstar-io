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

let dm_iio' = dm_iio unit trivial_hist

type gio (flag:bool) = t:dm_iio'{contains t ==> flag} // if the tree contains GetTrace, then the flag must be true
type gio_arr (flag1:bool) (flag2:bool{flag1 ==> flag2}) = 
  cin:dm_iio' -> 
    cout:dm_iio'{(contains cin ==> contains cout) /\ ((contains cin ==> flag1) ==> (contains cout ==> flag2))}

let gio_arr_apply (#flag1:bool) (#flag2:bool{flag1 ==> flag2}) (f:gio_arr flag1 flag2) (x:gio 'flag3) : Pure (gio (flag2 || 'flag3))
  (requires (flag1 ==> 'flag3)) 
  (ensures (fun _ -> True)) =
  f x
  (**
  if flag1 = false && flag2 = false && 'flag3 = false then begin let r = f x in r end
  else if flag1 = false && flag2 = false && 'flag3 = true then begin let r = f x in r end
  else if flag1 = false && flag2 = true && 'flag3 = false then begin let r = f x in r end
  else if flag1 = false && flag2 = true && 'flag3 = true then begin let r = f x in r end
  else if flag1 = true && flag2 = true && 'flag3 = true then begin let r = f x in r end
  else f x **)

assume val f1 : gio_arr false false
assume val f2 : gio_arr false true
[@@expect_failure]
assume val f2' : gio_arr true false
assume val f3 : gio_arr true true
assume val c1 : gio true
assume val c2 : gio false

let test1 : gio true = gio_arr_apply f1 c1
let test2 : gio true = gio_arr_apply f2 c1
let test3 : gio true = gio_arr_apply f3 c1
let test4 : gio true = gio_arr_apply f1 c2
let test5 : gio true = gio_arr_apply f2 c2
[@@expect_failure]
let test6 : gio true = gio_arr_apply f3 c2
