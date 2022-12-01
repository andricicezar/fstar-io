module IIO2

open FStar.List
open FStar.Tactics
open ExtraTactics
open FStar.Calc
open FStar.Ghost

open DMFree
open IO.Sig
open IO.Sig.Call
open IO
open IIO

noeq
type tflag = | NoActions | GetTraceActions | IOActions | AllActions

let rec satisfies (m:iio 'a) (flag:tflag) =
match flag, m with
| AllActions,   _                     -> True
| _,            Return x              -> True
| _,            PartialCall pre k     -> forall r. satisfies (k r) flag
| NoActions,    _                     -> False
| GetTraceActions, Call GetTrace arg k   -> forall r. satisfies (k r) flag
| GetTraceActions, Call cmd arg k        -> False
| IOActions,    Call GetTrace arg k   -> False
| IOActions,    Call cmd arg k        -> forall r. satisfies (k r) flag

let (+) (flag1:tflag) (flag2:tflag) = 
  match flag1, flag2 with
  | NoActions, NoActions -> NoActions
  | NoActions, fl -> fl
  | fl, NoActions -> fl
  | GetTraceActions, GetTraceActions -> GetTraceActions
  | IOActions, IOActions -> IOActions
  | _, _ -> AllActions

let (<=) (flag1:tflag) (flag2:tflag) =
  match flag1, flag2 with
  | NoActions, _ -> True
  | GetTraceActions, NoActions -> False
  | GetTraceActions, _ -> True
  | IOActions, NoActions -> False
  | IOActions, GetTraceActions -> False
  | IOActions, _ -> True
  | AllActions, AllActions -> True
  | AllActions, _ -> False

type dm_gio (a:Type) (flag:tflag) (wp:hist a) = t:(dm_iio a wp){t `satisfies` flag} 

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
  (fl:erased tflag)
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

let get_trace () : GIOwp trace GetTraceActions
  (fun p h -> forall lt. lt == [] ==> p lt h) =
  GIOwp?.reflect (iio_call GetTrace ())

let bady (_:unit) : GIOwp unit GetTraceActions trivial_hist = ()

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

(** ** Model compilation **)
type rc_typ (t1 t2:Type) = t1 -> t2 -> trace -> bool
type eff_rc_typ (fl:erased tflag) (t1 t2:Type) (rc:rc_typ t1 t2) =
  x:t1 -> r:t2 -> GIO bool fl (fun _ -> True) (fun h b lt -> lt == [] /\ (b ==> rc x r h))

val enforce_rc : rc:rc_typ 'a 'b -> eff_rc_typ AllActions 'a 'b rc
let enforce_rc rc x r = rc x r (get_trace ())

(** TODO: The runtime check lacks expressiveness. Post-conditions are written
  over the history and the local trace, but the runtime checks are only over the
  entire history. 
          
  Catalin had the idea to take advantage of partial application s.t.
  one calls the check once to capture the history and a second time to
  get the local trace and to do the check. 

  Pro: more expressive 
  Cons: bigger attack surface for the context

  The difficulty with this idea is with writing the post-condition. See 
  question marks in the following definition:

  type rc_typ (t1 t2:Type) = t1 -> trace -> t2 -> trace -> bool

  type eff_rc_typ (fl:erased tflag) (t1 t2:Type) (rc:rc_typ t1 t2) =
    x:t1 -> GIO bool fl (r:t2 -> GIO bool fl (fun _ -> True) (fun h b lt -> lt == [] /\ (b ==> rc x ? r ?)))
                (fun _ -> True)
                (fun _ _ lt -> lt == [])

  val enforce_rc : rc:rc_typ 'a 'b -> eff_rc_typ AllActions 'a 'b rc
  let enforce_rc rc x = 
    let h = get_trace () in
    (fun r -> rc h x r (get_local_trace h))
**)

type pck_rc = (t1:Type u#a & t2:Type u#b & rc_typ t1 t2)
type pck_eff_rc (fl:erased tflag) = pck:pck_rc & eff_rc_typ fl (Mkdtuple3?._1 pck) (Mkdtuple3?._2 pck) (Mkdtuple3?._3 pck)

val make_rc_eff : pck_rc u#a u#b -> pck_eff_rc u#a u#b AllActions
let make_rc_eff r = (| r, (enforce_rc (Mkdtuple3?._3 r)) |)

noeq type s_int = {
  ct: erased tflag -> Type u#a;
  (** constraint: ct type has to be effect polymorphic **)
  (** constraint that matches the post-conditions from ct with ct_rc **)
  ct_rc : list pck_rc;

  pt: Type u#b;
}

noeq type t_int = {
  ct: erased tflag -> Type u#a;
  pt: Type u#b;
}

type typ_posts (fl:erased tflag) (i:s_int) = 
  posts:(list (pck_eff_rc fl)){
    length i.ct_rc == length posts /\ 
    (forall n. List.Tot.nth i.ct_rc n == (List.Tot.nth (List.Tot.map dfst posts) n))}

let make_all_rc_eff (i:s_int) : typ_posts AllActions i =
  let r : list (pck_eff_rc AllActions) = List.Tot.map make_rc_eff i.ct_rc in
  assert (length r == length i.ct_rc);
  assume (forall n. List.Tot.nth i.ct_rc n == (List.Tot.nth (List.Tot.map dfst r) n));
  r

type prog_s (i:s_int) = i.ct AllActions -> i.pt
type ctx_s  (i:s_int) = #fl:erased tflag -> typ_posts fl i -> i.ct fl

let link_s (#i:s_int) (p:prog_s i) (c:ctx_s i) =
  let eff_rc = make_all_rc_eff i in
  p (c #AllActions eff_rc)

type prog_t (i:t_int) = i.ct AllActions -> i.pt
type ctx_t  (i:t_int) = #fl:erased tflag -> i.ct fl
let link_t (#i:t_int) (p:prog_t i) (c:ctx_t i) = p c

let ex1_s : s_int = {
  ct = (fun fl -> unit -> GIO (resexn file_descr) fl (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)));
  ct_rc = [(| unit, resexn file_descr, (fun () (rfd:resexn file_descr) h -> Inl? rfd && (is_open (Inl?.v rfd) h)) |)];

  pt = unit -> GIO unit AllActions (fun _ -> True) (fun _ _ _ -> True);
}

let ex1_t : t_int = {
  ct = (fun fl -> unit -> GIO (resexn file_descr) fl (fun _ -> True) (fun _ _ lt -> True));
  pt = unit -> GIO unit AllActions (fun _ -> True) (fun _ _ _ -> True);
}
  
val contract : #fl:erased tflag -> ex1_t.ct fl -> posts:typ_posts fl ex1_s -> ex1_s.ct fl
let contract c_t ((| _, p1 |)::_) () =
  let p1' = p1 () in
  let fd = c_t () in
  if p1' fd then fd
  else Inr Contract_failure

val compile_p : prog_s ex1_s -> prog_t ex1_t
let compile_p (p:prog_s ex1_s) (c:ex1_t.ct AllActions) =
  let eff_rc = make_all_rc_eff ex1_s in
  p (contract #AllActions c eff_rc)

val backtranslate : ctx_t ex1_t -> ctx_s ex1_s
let backtranslate c (#fl:erased tflag) = 
  contract #fl c 
