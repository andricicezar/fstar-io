module IIO2

open FStar.Tactics
open ExtraTactics
open FStar.Calc

open DMFree
open IO.Sig
open IO.Sig.Call
open IO
open IIO

(** fstar does not like type bool as an index for an effect --- not sure why **)
noeq
type tflag = | NoActions | OnlyGetTrace | IOActions | AllActions

let rec satisfies (m:iio 'a) (flag:tflag) =
match flag, m with
| AllActions,   _                     -> True
| _,            Return x              -> True
| _,            PartialCall pre k     -> forall r. satisfies (k r) flag
| NoActions,    _                     -> False
| OnlyGetTrace, Call GetTrace arg k   -> forall r. satisfies (k r) flag
| OnlyGetTrace, Call cmd arg k        -> False
| IOActions,    Call GetTrace arg k   -> False
| IOActions,    Call cmd arg k        -> forall r. satisfies (k r) flag

let (+) (flag1:tflag) (flag2:tflag) = 
  match flag1, flag2 with
  | NoActions, NoActions -> NoActions
  | NoActions, fl -> fl
  | fl, NoActions -> fl
  | OnlyGetTrace, OnlyGetTrace -> OnlyGetTrace
  | IOActions, IOActions -> IOActions
  | _, _ -> AllActions

let (<=) (flag1:tflag) (flag2:tflag) =
  match flag1, flag2 with
  | NoActions, _ -> True
  | OnlyGetTrace, NoActions -> False
  | OnlyGetTrace, _ -> True
  | IOActions, NoActions -> False
  | IOActions, OnlyGetTrace -> False
  | IOActions, _ -> True
  | AllActions, AllActions -> True
  | AllActions, _ -> False

type dm_gio (a:Type) (flag:tflag) (wp:hist a) = t:(dm_iio a wp){t `satisfies` flag} 
  // if the tree contains GetTrace, then the flag must be true

(** ** Model compilation **)
assume type ct (m:Type u#a -> Type u#(max 1 a))
assume type pt (m:Type u#a -> Type u#(max 1 a))

type gio flag (a:Type u#a) : Type u#(max 1 a) = dm_gio a flag trivial_hist

// This way prog_s can not use `GetTrace`.
// even if prog_s whould check if `fl2` is true, the refinement on the tree is stronger
type prog_s = #fl:tflag -> ct (gio fl) -> pt (gio (fl + IOActions))
// I suppose ctx_s can also be parametric in the flag, but not sure if needed
type ctx_s = #fl:tflag -> ct u#a (gio fl)
let link_s (p:prog_s) (c:ctx_s) = p #IOActions c

type prog_t = ct (gio AllActions) -> pt (gio AllActions)
type ctx_t  = m:(Type u#a ->Type u#(max 1 a)) -> ct m 
let link_t (p:prog_t) (c:ctx_t) = p (c (gio AllActions))

let compile_p (p:prog_s) : prog_t = fun (c:ct (gio AllActions)) -> p c

val backtranslate : ctx_t u#a -> ctx_s u#a
let backtranslate c (#fl:tflag) = c (gio fl)

(** ** Defining F* Effect **)

let dm_gio_theta #a = theta #a #iio_cmds #iio_sig #event iio_wps

let dm_gio_return (a:Type) (x:a) : dm_gio a NoActions (hist_return x) by (compute ()) =
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
  assume (v `satisfies` flag_v /\ (forall x. f x `satisfies` flag_f) ==> r `satisfies` (flag_v + flag_f));
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
  admit ();
  dm_iio_subcomp a wp1 wp2 f

let dm_gio_if_then_else (a : Type u#a) (fl1 fl2:tflag)
  (wp1 wp2: hist a) (f : dm_gio a fl1 wp1) (g : dm_gio a fl2 wp2) (b : bool) : Type =
  dm_gio a (fl1 + fl2) (hist_if_then_else wp1 wp2 b)

total
reflectable
effect {
  GIOwp (a:Type) (flag:tflag) (wp : hist #event a) 
  with {
       repr       = dm_gio
     ; return     = dm_gio_return
     ; bind       = dm_gio_bind 
     ; subcomp    = dm_gio_subcomp
     ; if_then_else = dm_gio_if_then_else
     }
}

let dm_gio_partial_return 
  (pre:pure_pre) : dm_gio (squash pre) NoActions (partial_call_wp pre) by (compute ()) =
  dm_partial_return iio_cmds iio_sig event iio_wps pre

val lift_pure_dm_gio :
  a: Type ->
  w: pure_wp a ->
  f: (eqtype_as_type unit -> PURE a w) ->
  Tot (dm_gio a NoActions (wp_lift_pure_hist w))
let lift_pure_dm_gio a w f = 
  lemma_wp_lift_pure_hist_implies_as_requires #a #event w;
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs : dm_gio _ NoActions _ = dm_gio_partial_return (as_requires w) in
  let rhs = (fun (pre:(squash (as_requires w))) -> dm_gio_return a (f pre)) in
  let m = dm_gio_bind _ _ NoActions NoActions _ _ lhs rhs in
  dm_gio_subcomp a NoActions NoActions _ _ m
  
sub_effect PURE ~> GIOwp = lift_pure_dm_gio

effect GIO
  (a:Type)
  (fl:tflag)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  GIOwp a fl (to_hist pre post) 
  
let static_cmd
  (cmd : io_cmds)
  (arg : io_sig.args cmd) :
  GIO (io_resm cmd) IOActions
    (requires (fun h -> io_pre cmd arg h))
    (ensures (fun h (r:io_sig.res cmd arg) lt ->
        lt == [convert_call_to_event cmd arg r])) =
  GIOwp?.reflect (iio_call cmd arg)

let get_trace () : GIOwp trace OnlyGetTrace
  (fun p h -> forall lt. lt == [] ==> p lt h) =
  GIOwp?.reflect (iio_call GetTrace ())

open FStar.Ghost

let bady (_:unit) : GIOwp unit OnlyGetTrace trivial_hist = ()

let prog (#fl:tflag) (c:unit -> GIOwp unit fl trivial_hist) : GIOwp unit fl trivial_hist 
// by (explode (); bump_nth 7; dump "H") 
 =
  match fl with
//  | AllActions -> bady ()
  | _ -> c ()

let ctx (_:unit) : GIOwp unit NoActions trivial_hist = ()

let test2 () : GIOwp unit AllActions trivial_hist = prog #AllActions ctx

let performance_test (#fl:tflag) : GIOwp unit (fl+IOActions) (fun p h -> forall lt. (List.length lt == 6) \/ (List.length lt == 7) ==> p lt ()) =
  let fd = static_cmd Openfile "../Makefile" in
  let fd = static_cmd Openfile "../Makefile" in
  let fd = static_cmd Openfile "../Makefile" in
  let fd = static_cmd Openfile "../Makefile" in
  let fd = static_cmd Openfile "../Makefile" in
  let fd = static_cmd Openfile "../Makefile" in
  if Inl? fd then let _ = static_cmd Close (Inl?.v fd) in () else 
  ()
  

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
