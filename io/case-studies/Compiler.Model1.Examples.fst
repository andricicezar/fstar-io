module Compiler.Model1.Examples

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality
open FStar.List

open Compiler.Model1

(** Utils **)
type source_arrow (mst:mstate) (arg:Type u#a) (res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (fl:erased tflag) =
  x:arg -> MIO (resexn res) fl mst (pre x) (post x)

type c1typ (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (sgm:policy_spec) =
  squash (forall x h lt. pre x h /\ enforced_locally sgm h lt ==> post x h (Inr Contract_failure) lt)
  
type c2typ (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (sgm:policy_spec) (#mst:mstate) (dc:dc_typ mst #arg #(resexn res)) =
  squash (forall s0 s1 x h r lt . s0 `mst.abstracts` h /\ s1 `mst.abstracts` (apply_changes h lt) /\ pre x h /\ enforced_locally sgm h lt /\ dc x s0 r s1 ==> post x h r lt)

type stronger_sgms (sgm1:policy_spec) (sgm2:policy_spec) =
  squash (forall h lt. enforced_locally sgm1 h lt ==> enforced_locally sgm2 h lt)
  
#push-options "--compat_pre_core 1"


(** ** Testing **)
(** *** Test 1 - FO **)
let test1_pre = (fun () h -> True)
let test1_post = (fun () h (rfd:resexn file_descr) lt -> 
  (forall fd'. ~((EOpenfile Ctx "/etc/passwd" fd') `List.memP` lt)) /\ (Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)))

let mst1 : mstate = {
  typ = list file_descr;
  abstracts = (fun s h -> forall fd. memP fd s <==> is_open fd h);
}

let rec remove (#a:eqtype) (x:a) (l : list a) : list a =
  match l with
  | [] -> []
  | y::yy ->
    if x = y
    then remove x yy
    else y :: remove x yy

let rec lemma_remove_mem (#a:eqtype) (x:a) (y : a) (l:list a)
  : Lemma (ensures memP x (remove y l) <==> x <> y /\ memP x l)
          (decreases l)
          [SMTPat (memP x (remove y l))]
  = match l with
    | [] -> ()
    | _::tl -> lemma_remove_mem x y tl

let mst1_impl : mst_impl mst1 = {
  init = [];
  update = (fun s0 e h ->
    let s1 : list file_descr =
      match e with
      | EOpenfile _ f (Inl fd) -> fd :: s0
      | EClose _ fd' _ -> remove fd' s0
      | _ -> s0
    in s1
  );
}

type test1_ct = source_arrow mst1 unit file_descr test1_pre test1_post

let test1_sgm : policy_spec = 
  fun h c cmd arg -> 
    Ctx? c /\
    (match cmd with 
    | Openfile -> (arg <> "/etc/passwd")
    | _ -> True)

let test1_pi : policy test1_sgm mst1 =
  fun h cmd arg -> 
    match cmd, arg with 
    | Openfile, s ->
      if s = "/etc/passwd" then false 
      else true 
    | _ -> true

let test1_ct_rc : dc_typ mst1 =
  fun () s0 rfd s1 ->
    match rfd with
    | Inl fd -> List.mem fd s1
    | Inr _ -> false

let test1_ct_rcs : tree (pck_dc mst1) = 
  Node (| unit, resexn file_descr, test1_ct_rc |) 
    Leaf 
    Leaf

val test1_c1post : c1typ test1_pre test1_post test1_sgm 
let test1_c1post = 
  let rec aux (h:trace) (lt:trace) : Lemma
    (requires (enforced_locally test1_sgm h lt))
    (ensures (test1_post () h (Inr Contract_failure) lt))
    (decreases lt) = (
    match lt with
    | [] -> ()
    | e :: tail -> aux (e::h) tail) in
  Classical.forall_intro_2 (Classical.move_requires_2 aux)

let rec enforced_locally_test1_sgm_nopass h lt fd :
  Lemma
    (requires enforced_locally test1_sgm h lt)
    (ensures ~((EOpenfile Ctx "/etc/passwd" fd) `memP` lt))
    (decreases lt)
= match lt with
  | EOpenfile Ctx "/etc/passwd" fd' :: tl ->
    if fd = fd'
    then ()
    else enforced_locally_test1_sgm_nopass (EOpenfile Ctx "/etc/passwd" fd' :: h) tl fd
  | e :: tl ->
    enforced_locally_test1_sgm_nopass (e :: h) tl fd
  | [] -> ()

val test1_c2post : c2typ test1_pre test1_post test1_sgm test1_ct_rc
let test1_c2post =
  introduce forall s0 s1 x h r lt . s0 `mst1.abstracts` h /\ s1 `mst1.abstracts` (apply_changes h lt) /\ test1_pre x h /\ enforced_locally test1_sgm h lt /\ test1_ct_rc x s0 r s1 ==> test1_post x h r lt
  with begin
    introduce s0 `mst1.abstracts` h /\ s1 `mst1.abstracts` (apply_changes h lt) /\ test1_pre x h /\ enforced_locally test1_sgm h lt /\ test1_ct_rc x s0 r s1 ==> test1_post x h r lt
    with _. begin
      introduce forall fd'. ~((EOpenfile Ctx "/etc/passwd" fd') `memP` lt)
      with enforced_locally_test1_sgm_nopass h lt fd'
    end
  end

#set-options "--print_implicits"

let test1_ct_importable (fl:erased tflag) : safe_importable (test1_ct fl) fl test1_sgm mst1 test1_ct_rcs =
  safe_importable_arrow_pre_post_args_res _ _ test1_c1post test1_c2post #exportable_unit #importable_file_descr

val test1_stronger_sgms : stronger_sgms test1_sgm test1_sgm
let test1_stronger_sgms = 
  let rec aux (h:trace) (lt:trace) : Lemma
    (requires (enforced_locally test1_sgm h lt))
    (ensures (enforced_locally test1_sgm h lt))
    (decreases lt) = (match lt with
    | [] -> ()
    | e :: tail -> aux (e::h) tail) in 
  Classical.forall_intro_2 (Classical.move_requires_2 aux)

[@@ (postprocess_with (fun () -> norm [delta_only [`%test1_ct; `%source_arrow; `%test1_ct_importable]]; trefl ()))]
let test1 : src_interface = {
  mst = mst1;
  sgm = test1_sgm; pi = test1_pi;

  ct = test1_ct;
  ct_dcs = test1_ct_rcs;

  ct_importable = test1_ct_importable;
  psi = (fun _ _ lt -> (forall fd'. ~((EOpenfile Ctx "/etc/passwd" fd') `List.memP` lt)));
}

val test1_prog : prog_src test1
let test1_prog #fl ctx () : MIO int (fl + IOOps) mst1 (fun _ -> True) test1.psi =
  //let test = static_cmd Openfile "/etc/passwd" in
  let _ = ctx () in
  0 

val test1_ctx : ctx_src test1
let test1_ctx #fl sec_io eff_rcs () : MIO (resexn file_descr) fl mst1 (fun _ -> True) (test1_post ()) = 
  sec_io Openfile "/etc/passwd"

val test1_ctx_t : ctx_tgt (comp_int_src_tgt test1)
let test1_ctx_t #fl sec_io () : MIOpi (resexn file_descr) fl test1_sgm mst1 =
  sec_io Openfile "/etc/passwd"


(** ** Test 2 - HO left 1 **)
let mst2 : mstate = {
  typ = list file_descr;
  abstracts = (fun s h -> forall fd. memP fd s <==> is_open fd h);
}

let test2_sgm : policy_spec = (fun _ _ _ _ -> true)
let test2_pi : policy test2_sgm mst2 = (fun _ _ _ -> true)

let test2_cb (fl:erased tflag) = (fd:file_descr -> MIO (resexn unit) fl mst2 (fun h -> is_open fd h) (fun _ _ lt -> lt == []))
let test2_post = (fun _ h (rfd:resexn file_descr) lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h))
let test2_ct (fl:erased tflag) = (cb:test2_cb fl) -> MIO (resexn file_descr) fl mst2 (fun _ -> True) (test2_post cb)

let test2_rc  : dc_typ mst2 = 
  (fun () _ (rfd:resexn file_descr) s1 -> Inl? rfd && (Inl?.v rfd) `List.mem` s1)

let test2_rcs : tree (pck_dc mst2) =  
  Node 
     (| unit, resexn file_descr, test2_rc |) 
     (Node (| file_descr, unit, (fun fd s0 _ _ -> fd `List.mem` s0) |) Leaf Leaf)
     Leaf
  
val test2_c1post (a:Type) : c1typ #a #file_descr (fun _ _ -> True) test2_post test2_sgm
let test2_c1post a = ()


val test2_c2post (a:Type) : squash (forall s0 s1 (x:a) h r lt . s0 `mst2.abstracts` h /\ s1 `mst2.abstracts` (apply_changes h lt) /\ enforced_locally test2_sgm h lt /\ test2_rc () s0 r s1 ==> test2_post x h r lt)
let test2_c2post a = ()

let test2_ct_importable (fl:erased tflag) : safe_importable (test2_ct fl) fl test2_sgm mst2 test2_rcs = 
  let exportable_cb = exportable_arrow_pre_post_args file_descr unit #fl #test2_sgm #mst2 #(left test2_rcs) (fun fd h -> is_open fd h) (fun fd _ _ lt -> lt == []) in
  safe_importable_arrow_pre_post_res
    (fun _ _ -> True)  (** pre **)
    test2_post       (** post **)
    (test2_c1post (test2_cb fl))
    (test2_c2post (test2_cb fl))
    #exportable_cb
    #importable_file_descr

[@@ (postprocess_with (fun () -> norm [delta_only [`%test2_ct; `%test2_cb;`%test2_ct_importable]]; trefl ()))]
let test2 : src_interface = {
  mst = mst2;
  sgm = test2_sgm; pi = test2_pi; 
  ct = test2_ct; ct_dcs = test2_rcs; ct_importable = test2_ct_importable; 
  psi = (fun _ _ _ -> True);
}

val test2_prog : prog_src test2
let test2_prog #fl ctx () =
  let _ = ctx (fun fd -> Inl ()) in
  (** return exit code **) 0

val test2_ctx : ctx_src test2 
let test2_ctx #fl sec_io eff_rcs cb : MIO (resexn file_descr) fl mst2 (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)) = 
  let post1 = root eff_rcs in
  let (| _, pre1 |) = root (left eff_rcs) in 
  let rfd = sec_io Openfile "/etc/passwd" in
  match rfd with
  | Inl fd -> let _ = pre1 fd in rfd
  | _ -> rfd

val test2_ctx_t : ctx_tgt (comp_int_src_tgt test2)
let test2_ctx_t #fl sec_io cb : MIOpi (resexn file_descr) fl (comp_int_src_tgt test2).sgm mst2 = 
  let rfd = sec_io Openfile "/etc/passwd" in
  match rfd with
  | Inl fd -> begin
    //let _ = sec_io Close fd in 
    let _ = cb fd in 
    rfd
  end
  | _ -> rfd

(** ** Test 3 - HO right 1 **)
let mst3 : mstate = {
  typ = list file_descr;
  abstracts = (fun s h -> forall fd. memP fd s <==> is_open fd h);
}

let test3_sgm : policy_spec = (fun _ _ _ _ -> true)
let test3_pi : policy test3_sgm mst3 = (fun _ _ _ -> true)

let test3_cb (fl:erased tflag) = (fd:file_descr -> MIO (resexn unit) fl mst3 (fun h -> True) (fun _ _ lt -> True))
let test3_post #a = (fun (x:file_descr) h (r:a) lt -> True)
let test3_ct (fl:erased tflag) = x:file_descr -> MIO (resexn (test3_cb fl)) fl mst2 (fun _ -> True) (test3_post x)

let test3_rcs : tree (pck_dc mst3) =  
  Node (| file_descr, unit, (fun _ _ _ _ -> true) |) 
     Leaf
     (Node (| file_descr, resexn unit, (fun _ _ _ _ -> true) |) Leaf Leaf)

let test3_cb_importable (fl:erased tflag) : safe_importable (test3_cb fl) fl test3_sgm mst3 (right test3_rcs) = 
  safe_importable_arrow_pre_post_args_res
    #file_descr #unit
    #fl
    #test3_sgm
    #mst3
    #(right test3_rcs)
    (fun fd h -> True)
    (fun fd _ _ lt -> True)
    ()
    ()
    #exportable_file_descr
    #importable_unit
  
val test3_c1post (a:Type) : c1typ #file_descr #a (fun _ _ -> True) test3_post test3_sgm 
let test3_c1post a = ()
  
val test3_c2post (a:Type) : 
  squash (forall s0 s1 x h r lt . s0 `mst3.abstracts` h /\ s1 `mst3.abstracts` (apply_changes h lt) /\ enforced_locally test3_sgm h lt /\ (root test3_rcs)._3 x s0 r s1 ==> test3_post x h r lt)
let test3_c2post a = ()

let test3_ct_importable (fl:erased tflag) : safe_importable (test3_ct fl) fl test3_sgm mst3 test3_rcs = 
  safe_importable_arrow_pre_post_args
    #file_descr #(test3_cb fl) #fl #test3_sgm #mst3 #test3_rcs
    (fun _ _ -> True)  (** pre **)
    test3_post       (** post **)
    (test3_c1post (test3_cb fl))
    (test3_c2post (test3_cb fl))
    #exportable_file_descr
    #(safe_importable_is_importable (test3_cb_importable fl))

[@@ (postprocess_with (fun () -> norm [delta_only [`%test3_ct; `%test3_cb;`%test3_ct_importable]]; trefl ()))]
let test3 : src_interface = {
  mst = mst3;
  sgm = test3_sgm; pi = test3_pi;
  ct = test3_ct; ct_dcs = test3_rcs; ct_importable = test3_ct_importable; 
  psi = (fun _ _ _ -> True);
}

val test3_prog : prog_src test3
let test3_prog #fl ctx () : MIO int (IOOps + fl) mst3 (fun _ -> True) (fun _ _ _ -> True) =
  match static_op Prog Openfile "test.txt" with
  | Inl fd -> begin
    match ctx fd with
    | Inl cb -> let _ : resexn unit = cb fd in 0
    | Inr err -> -1
    end
  | Inr err -> -1

val test3_ctx : ctx_src test3 
let test3_ctx #fl sec_io eff_rcs fd = 
  Inl (fun (fd:file_descr) -> Inl () <: (MIOwp (resexn unit) mst3 fl trivial_hist))

val test3_ctx_t : ctx_tgt (comp_int_src_tgt test3)
let test3_ctx_t #fl sec_io fd : MIOpi (resexn (file_descr -> MIOpi (resexn unit) fl test3_sgm mst3)) fl test3_sgm mst3 = 
  Inl (fun (fd:file_descr) -> Inl () <: (MIOpi (resexn unit) fl test3_sgm mst3))
