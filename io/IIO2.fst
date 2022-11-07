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

(** fstar does not like type bool as an index for an effect --- not sure why **)
noeq
type tflag = | Contains | NotContain
let (!) (flag:tflag) = Contains? flag
let (+) (flag1:tflag) (flag2:tflag) = 
  match flag1, flag2 with
  | NotContain, NotContain -> NotContain
  | _ -> Contains

let (<=) (flag1:tflag) (flag2:tflag) =
  match flag1, flag2 with
  | Contains, NotContain -> False
  | _ -> True

type dm_gio (a:Type) (flag:tflag) (wp:hist a) = t:(dm_iio a wp){contains t ==> !flag} 
  // if the tree contains GetTrace, then the flag must be true

(** ** Model compilation **)
assume type ct (m:Type->Type)
assume type pt (m:Type->Type)

let gio flag (a:Type) = dm_gio a flag trivial_hist

// This way prog_s can not use the GetTrace
type prog_s = #fl1:tflag -> #fl2:tflag{fl1 <= fl2} -> ct (gio fl1) -> pt (gio fl2)
type ctx_s = ct (gio NotContain)

let link_s (p:prog_s) (c:ct (gio NotContain)) = p #NotContain #NotContain c

type prog_i = (#flag:tflag) -> ct (gio flag) -> pt (gio Contains)

let compile_s (p:prog_s) : prog_i = fun #fl (c:ct (gio fl)) -> p #fl #Contains c

type prog_t = ct (gio Contains) -> pt (gio Contains)
type ctx_t  = m:(Type->Type) -> ct m 
let link_t (p:prog_t) (c:ctx_t) = p (c (gio Contains))

let compile_i (p:prog_i) : prog_t = fun (c:ct (gio Contains)) -> p #Contains c

(** ** Defining F* Effect **)

let dm_gio_theta #a = theta #a #iio_cmds #iio_sig #event iio_wps

let dm_gio_return (a:Type) (x:a) : dm_gio a NotContain (hist_return x) by (compute ()) =
  dm_iio_return a x

val dm_gio_bind  : 
  a: Type ->
  b: Type ->
  flag_v : tflag ->
  flag_f : tflag ->
  wp_v: Hist.hist a ->
  wp_f: (_: a -> Hist.hist b) ->
  v: dm_gio a flag_v wp_v ->
  f: (x: a -> dm_gio b flag_f (wp_f x)) ->
  Tot (dm_gio b (flag_v + flag_f) (hist_bind wp_v wp_f))
let dm_gio_bind a b flag_v flag_f wp_v wp_f v f : (dm_gio b (flag_v + flag_f) (hist_bind wp_v wp_f)) = 
  let r = dm_iio_bind a b wp_v wp_f v f in
  assert (Contains? flag_v \/ Contains? flag_f ==> Contains? (flag_v + flag_f));
  assert (NotContain? flag_v /\ NotContain? flag_f ==> 
        (~(contains v) /\ (forall x. ~(contains (f x))))); // ==> ~(contains r));
  assume (~(contains v) /\ (forall x. ~(contains (f x))) ==> ~(contains r));
  r

val dm_gio_subcomp : 
  a: Type ->
  flag1 : tflag ->
  flag2 : tflag ->
  wp1: hist a ->
  wp2: hist a ->
  f: dm_gio a flag1 wp1 ->
  Pure (dm_gio a flag2 wp2) ((flag1 <= flag2) /\ hist_ord wp2 wp1) (fun _ -> True)
let dm_gio_subcomp a flag1 flag2 wp1 wp2 f = 
  dm_iio_subcomp a wp1 wp2 f

let dm_gio_if_then_else a _ _ wp1 wp2 f g b = dm_if_then_else iio_cmds iio_sig event iio_wps a wp1 wp2 f g b

total
reflectable
effect {
  GIOwp (a:Type) (flag:tflag) (wp : hist a) 
  with {
       repr       = dm_gio
     ; return     = dm_gio_return
     ; bind       = dm_gio_bind 
     ; subcomp    = dm_gio_subcomp
 //    ; if_then_else = dm_gio_if_then_else
     }
}

let lift_io_gio (a:Type) (wp:hist a) (f:dm_io a wp) :
  Tot (dm_gio a NotContain wp) =
  admit ();
  lift_io_iio a wp f
  
sub_effect IOwp ~> GIOwp = lift_io_gio

let get_trace () : GIOwp trace Contains
  (fun p h -> forall lt. lt == [] ==> p lt h) =
  GIOwp?.reflect (iio_call GetTrace ())

let prog (#fl1:tflag) (#fl2:tflag{fl1 <= fl2}) (c:unit -> GIOwp unit fl1 trivial_hist) : GIOwp unit fl2 trivial_hist =
  //let h = get_trace () in // not possible because it does not know if fl2 is true or not
  c ()

let ctx (_:unit) : GIOwp unit NotContain trivial_hist = ()

let test2 () : GIOwp unit Contains trivial_hist = prog #NotContain ctx
  
(** TODO:
1) is there a way to lift an HO type in IO to a GIO that has a parametric flag?
2) GIO is a horrible name.
3) is this good enough for a source language?
4) it should be easy to lift from IO to GIO false
5) it should be easy to lift from GIO false to GIO true
6) it should be easy to lift from GIO true to IIO
**)


(** ** Old experiments **)


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
