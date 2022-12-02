module IIO2

open FStar.Tactics
open FStar.Tactics.Typeclasses
open ExtraTactics
open FStar.Calc
open FStar.Ghost

open DMFree
open IO.Sig
open IO.Sig.Call
open IIO

open FStar.List.Tot

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

(** ** Defining F* Effect **)

type dm_giio (a:Type) (flag:tflag) (wp:hist a) = t:(dm_iio a wp){t `satisfies` flag} 

let dm_giio_theta #a = theta #a #iio_cmds #iio_sig #event iio_wps

let dm_giio_return (a:Type) (x:a) : dm_giio a NoActions (hist_return x) by (compute ()) =
  dm_iio_return a x

val dm_giio_bind  : 
  a: Type ->
  b: Type ->
  flag_v : tflag ->
  flag_f : tflag ->
  wp_v: Hist.hist a ->
  wp_f: (_: a -> Hist.hist b) ->
  v: dm_giio a flag_v wp_v ->
  f: (x: a -> dm_giio b flag_f (wp_f x)) ->
  Tot (dm_giio b (flag_v + flag_f) (hist_bind wp_v wp_f))
let dm_giio_bind a b flag_v flag_f wp_v wp_f v f : (dm_giio b (flag_v + flag_f) (hist_bind wp_v wp_f)) = 
  let r = dm_iio_bind a b wp_v wp_f v f in
  assume (v `satisfies` flag_v /\ (forall x. f x `satisfies` flag_f) ==> r `satisfies` (flag_v + flag_f));
  r

val dm_giio_subcomp : 
  a: Type ->
  flag1 : tflag ->
  flag2 : tflag ->
  wp1: hist a ->
  wp2: hist a ->
  f: dm_giio a flag1 wp1 ->
  Pure (dm_giio a flag2 wp2) ((flag1 <= flag2) /\ hist_ord wp2 wp1) (fun _ -> True)
let dm_giio_subcomp a flag1 flag2 wp1 wp2 f = 
  admit ();
  dm_iio_subcomp a wp1 wp2 f

let dm_giio_if_then_else (a : Type u#a) (fl1 fl2:tflag)
  (wp1 wp2: hist a) (f : dm_giio a fl1 wp1) (g : dm_giio a fl2 wp2) (b : bool) : Type =
  dm_giio a (fl1 + fl2) (hist_if_then_else wp1 wp2 b)

total
reflectable
effect {
  IIOwp (a:Type) (flag:tflag) (wp : hist #event a) 
  with {
       repr       = dm_giio
     ; return     = dm_giio_return
     ; bind       = dm_giio_bind 
     ; subcomp    = dm_giio_subcomp
     ; if_then_else = dm_giio_if_then_else
     }
}

let dm_giio_partial_return 
  (pre:pure_pre) : dm_giio (squash pre) NoActions (partial_call_wp pre) by (compute ()) =
  dm_partial_return iio_cmds iio_sig event iio_wps pre

val lift_pure_dm_giio :
  a: Type ->
  w: pure_wp a ->
  f: (eqtype_as_type unit -> PURE a w) ->
  Tot (dm_giio a NoActions (wp_lift_pure_hist w))
let lift_pure_dm_giio a w f = 
  lemma_wp_lift_pure_hist_implies_as_requires #a #event w;
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs : dm_giio _ NoActions _ = dm_giio_partial_return (as_requires w) in
  let rhs = (fun (pre:(squash (as_requires w))) -> dm_giio_return a (f pre)) in
  let m = dm_giio_bind _ _ NoActions NoActions _ _ lhs rhs in
  dm_giio_subcomp a NoActions NoActions _ _ m
  
sub_effect PURE ~> IIOwp = lift_pure_dm_giio

effect IIO
  (a:Type)
  (fl:tflag)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  IIOwp a fl (to_hist pre post) 
  
let static_cmd
  (cmd : io_cmds)
  (arg : io_sig.args cmd) :
  IIO (io_resm cmd) IOActions
    (requires (fun h -> io_pre cmd arg h))
    (ensures (fun h (r:io_sig.res cmd arg) lt ->
        lt == [convert_call_to_event cmd arg r])) =
  IIOwp?.reflect (iio_call cmd arg)

let get_trace () : IIOwp trace GetTraceActions
  (fun p h -> forall lt. lt == [] ==> p lt h) =
  IIOwp?.reflect (iio_call GetTrace ())

let performance_test (#fl:tflag) : IIOwp unit (fl+IOActions) (fun p h -> forall lt. (List.length lt == 6) \/ (List.length lt == 7) ==> p lt ()) =
  let fd = static_cmd Openfile "../Makefile" in
  let fd = static_cmd Openfile "../Makefile" in
  let fd = static_cmd Openfile "../Makefile" in
  let fd = static_cmd Openfile "../Makefile" in
  let fd = static_cmd Openfile "../Makefile" in
  let fd = static_cmd Openfile "../Makefile" in
  if Inl? fd then let _ = static_cmd Close (Inl?.v fd) in () else 
  ()

(** ** Model compilation **)
type rc_typ (t1 t2:Type) = t1 -> trace -> t2 -> trace -> bool

type eff_rc_typ_cont (fl:erased tflag) (t1:Type u#a) (t2:Type u#b) (rc:rc_typ t1 t2) (x:t1) (initial_h:erased trace) =
  y:t2 -> IIO ((erased trace) * bool) fl (fun h -> (initial_h `suffix_of` h)) (fun h (the_lt, b) lt -> apply_changes initial_h the_lt == h /\ lt == [] /\ (b ==> rc x initial_h y the_lt))
  
type eff_rc_typ (fl:erased tflag) (t1 t2:Type) (rc:rc_typ t1 t2) =
  x:t1 -> IIO (initial_h:(erased trace) & eff_rc_typ_cont fl t1 t2 rc x initial_h) fl (fun _ -> True) (fun h (| initial_h, _ |) lt -> h == reveal initial_h /\ lt == [])

let get_local_trace (h':trace) :
  IIO trace GetTraceActions
    (requires (fun h -> h' `suffix_of` h))
    (ensures (fun h lt' lt ->
      lt == [] /\
      h == (apply_changes h' lt'))) =
  let h = get_trace () in
  suffix_of_length h' h;
  let n : nat = (List.length h) - (List.length h') in
  let (lt', ht) = List.Tot.Base.splitAt n h in
  lemma_splitAt_equal n h;
  lemma_splitAt_suffix h h';
  List.Tot.Properties.rev_involutive lt';
  assert (h == apply_changes h' (List.rev lt'));
  List.rev lt'

val enforce_rc : (#a:Type u#a) -> (#b:Type u#b) -> rc:rc_typ a b -> eff_rc_typ AllActions a b rc
let enforce_rc #a #b rc x =
  let initial_h = get_trace () in
  let cont : eff_rc_typ_cont AllActions a b rc x (hide initial_h) = 
    (fun y -> ( 
      let lt = get_local_trace initial_h in 
      (hide lt, rc x initial_h y lt))) in
  (| hide initial_h, cont |)

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

type typ_posts (fl:erased tflag) (rcs:list pck_rc) = 
  posts:(list (pck_eff_rc fl)){
    length rcs == length posts /\ 
    (forall n. List.Tot.nth rcs n == (List.Tot.nth (List.Tot.map dfst posts) n))}

let make_all_rc_eff (i:s_int) : typ_posts AllActions i.ct_rc =
  let r : list (pck_eff_rc AllActions) = List.Tot.map make_rc_eff i.ct_rc in
  assert (length r == length i.ct_rc);
  assume (forall n. List.Tot.nth i.ct_rc n == (List.Tot.nth (List.Tot.map dfst r) n));
  r

type prog_s (i:s_int) = i.ct AllActions -> i.pt
type ctx_s  (i:s_int) = #fl:erased tflag -> typ_posts fl i.ct_rc -> i.ct fl

let link_s (#i:s_int) (p:prog_s i) (c:ctx_s i) =
  let eff_rc = make_all_rc_eff i in
  p (c #AllActions eff_rc)

type prog_t (i:t_int) = i.ct AllActions -> i.pt
type ctx_t  (i:t_int) = #fl:erased tflag -> i.ct fl
let link_t (#i:t_int) (p:prog_t i) (c:ctx_t i) = p c

let ex1_s : s_int = {
  ct = (fun fl -> unit -> IIO (resexn file_descr) fl (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)));
  ct_rc = [(| unit, resexn file_descr, (fun () h (rfd:resexn file_descr) lt -> Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h))) |)];

  pt = unit -> IIO unit AllActions (fun _ -> True) (fun _ _ _ -> True);
}

let ex1_t : t_int = {
  ct = (fun fl -> unit -> IIO (resexn file_descr) fl (fun _ -> True) (fun _ _ lt -> True));
  pt = unit -> IIO unit AllActions (fun _ -> True) (fun _ _ _ -> True);
}

#push-options "--split_queries"
val contract : #fl:erased tflag -> ex1_t.ct fl -> posts:typ_posts fl ex1_s.ct_rc -> ex1_s.ct fl
let contract c_t ((| _, p1 |)::_) x =
  let (| h, p1' |) = (p1 x) in
  let fd = c_t () in
  Classical.forall_intro (lemma_suffixOf_append h);
  if snd (p1' fd) then fd
  else Inr Contract_failure
#reset-options

val compile_p : prog_s ex1_s -> prog_t ex1_t
let compile_p (p:prog_s ex1_s) (c:ex1_t.ct AllActions) =
  let eff_rc = make_all_rc_eff ex1_s in
  p (contract #AllActions c eff_rc)

val backtranslate : ctx_t ex1_t -> ctx_s ex1_s
let backtranslate c (#fl:erased tflag) = 
  contract #fl c 


class exportable (t : Type u#a) (rcs:list pck_rc) (fl:erased tflag) = {
  etype : Type u#a;
  export : typ_posts fl rcs -> t -> etype;
}

class importable (t : Type u#a) (rcs:list pck_rc) (fl:erased tflag) = {
  itype : Type u#a; 
  import : itype -> (typ_posts fl rcs -> t);
}

let fast_convert (rcs:(list pck_rc){length rcs > 0}) (eff_rcs:typ_posts 'fl rcs) : typ_posts 'fl (tail rcs) =
  admit ();
  tail eff_rcs

#push-options "--split_queries"
let safe_importable_arrow_pre_post
  (fl:erased tflag)
  (t1:Type) (t2:Type)
  (rcs:(list pck_rc){List.length rcs > 0 /\ (Mkdtuple3?._1 (hd rcs) == t1 /\ (Mkdtuple3?._2 (hd rcs) == (resexn t2))) })
  {| d1:exportable t1 (tail rcs) fl |}
  {| d2:importable (resexn t2) (tail rcs) fl |}
  (pre : t1 -> trace -> Type0)
  (post : t1 -> trace -> (r:resexn t2) -> trace -> (b:Type0{r == Inr Contract_failure ==> b})) 
  (c2post: squash (forall x h r lt. pre x h /\ ((Mkdtuple3?._3 (hd rcs)) x h r lt) ==> post x h r lt))
  (f:d1.etype -> IIO (resexn d2.itype) fl (fun _ -> True) (fun _ _ _ -> True))
  (eff_rcs:typ_posts fl rcs)
  (x:t1) :
  IIO (resexn t2) fl (pre x) (post x) =
  assert ((forall n. List.Tot.nth rcs n == (List.Tot.nth (List.Tot.map dfst eff_rcs) n)));
  assert ((List.Tot.nth rcs 0 == (List.Tot.nth (List.Tot.map dfst eff_rcs) 0)));
  assert (hd rcs == hd (List.Tot.map dfst eff_rcs));
  let rc = dfst (hd eff_rcs) in
  let eff_rc = dsnd (hd eff_rcs) in
  assert (rc == (hd rcs));
  let (| _, eff_rc' |) = (eff_rc x) in
  let lss = fast_convert rcs eff_rcs in
  let res : resexn d2.itype = f (d1.export lss x) in
  match res with
  | Inr err -> (admit (); Inr err)
  | Inl res -> begin
    let res' : resexn t2 = d2.import res lss in
    if snd (eff_rc' res') then res'
    else Inr Contract_failure
  end
#reset-options
