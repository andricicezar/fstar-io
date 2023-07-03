module Compiler.Model1.Examples

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality
open FStar.List

open Compiler.Model1

(** Utils **)
type source_arrow (mst:mst) (arg:Type u#a) (res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (fl:erased tflag) =
  x:arg -> MIO (resexn res) mst fl (pre x) (post x)

type c1typ (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (pi:policy_spec) =
  squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> post x h (Inr Contract_failure) lt)
  
type c2typ (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (pi:policy_spec) (idc:idc_typ arg (resexn res)) =
  squash (forall x h lt r. pre x h /\ enforced_locally pi h lt /\ idc x h r lt ==> post x h r lt)

type stronger_pis (pi1:policy_spec) (pi2:policy_spec) =
  squash (forall h lt. enforced_locally pi1 h lt ==> enforced_locally pi2 h lt)
  
#push-options "--compat_pre_core 1"


(** ** Testing **)
(** *** Test 1 - FO **)
let test1_pre = (fun () h -> True)
let test1_post = (fun () h (rfd:resexn file_descr) lt -> 
  (forall fd'. ~((EOpenfile Ctx "/etc/passwd" fd') `List.memP` lt)) /\ (Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)))

let mst1 : mst = {
  cst = list file_descr;
  models = (fun s h -> forall fd. memP fd s <==> is_open fd h);
}

type test1_ct = source_arrow mst1 unit file_descr test1_pre test1_post

let test1_pi : policy_spec = 
  fun h c cmd arg -> 
    Ctx? c /\
    (match cmd with 
    | Openfile -> (arg <> "/etc/passwd")
    | _ -> True)

let test1_phi : policy mst1 test1_pi =
  fun h cmd arg -> 
    match cmd, arg with 
    | Openfile, s ->
      if s = "/etc/passwd" then false 
      else true 
    | _ -> true

let test1_ct_irc : idc_typ unit (resexn file_descr) =
  fun () h (rfd:resexn file_descr) lt -> Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h))

let test1_ct_rc : dc_typ mst1 test1_ct_irc =
  fun () s0 rfd s1 ->
    match rfd with
    | Inl fd -> List.mem fd s1
    | Inr _ -> false

let test1_ct_rcs : tree (pck_dc mst1) = 
  Node (| unit, resexn file_descr, test1_ct_irc, test1_ct_rc |) 
    Leaf 
    Leaf

val test1_c1post : c1typ test1_pre test1_post test1_pi 
let test1_c1post = 
  let rec aux (h:trace) (lt:trace) : Lemma
    (requires (enforced_locally test1_pi h lt))
    (ensures (test1_post () h (Inr Contract_failure) lt))
    (decreases lt) = (
    match lt with
    | [] -> ()
    | e :: tail -> aux (e::h) tail) in
  Classical.forall_intro_2 (Classical.move_requires_2 aux)

assume val test1_c2post : c2typ test1_pre test1_post test1_pi test1_ct_irc
//let test1_c2post = ()

#set-options "--print_implicits"

let test1_ct_importable (fl:erased tflag) : safe_importable (test1_ct fl) fl test1_pi mst1 test1_ct_rcs =
  safe_importable_arrow_pre_post_args_res _ _ test1_c1post test1_c2post #exportable_unit #importable_file_descr

val test1_stronger_pis : stronger_pis test1_pi test1_pi
let test1_stronger_pis = 
  let rec aux (h:trace) (lt:trace) : Lemma
    (requires (enforced_locally test1_pi h lt))
    (ensures (enforced_locally test1_pi h lt))
    (decreases lt) = (match lt with
    | [] -> ()
    | e :: tail -> aux (e::h) tail) in 
  Classical.forall_intro_2 (Classical.move_requires_2 aux)

[@@ (postprocess_with (fun () -> norm [delta_only [`%test1_ct; `%source_arrow; `%test1_ct_importable]]; trefl ()))]
let test1 : src_interface = {
  mst = mst1;
  pi = test1_pi; phi = test1_phi;

  ct = test1_ct;
  ct_dcs = test1_ct_rcs;

  ct_importable = test1_ct_importable;
  psi = (fun _ _ lt -> (forall fd'. ~((EOpenfile Ctx "/etc/passwd" fd') `List.memP` lt)));
}

val test1_prog : prog_src test1
let test1_prog #fl ctx () : MIO int mst1 (fl + IOActions) (fun _ -> True) test1.psi =
  //let test = static_cmd Openfile "/etc/passwd" in
  let _ = ctx () in
  0 

val test1_ctx : ctx_src test1
let test1_ctx #fl sec_io eff_rcs () : MIO (resexn file_descr) mst1 fl (fun _ -> True) (test1_post ()) = 
  sec_io Openfile "/etc/passwd"

val test1_ctx_t : ctx_tgt (comp_int_src_tgt test1)
let test1_ctx_t #fl sec_io () : MIOpi (resexn file_descr) fl test1_pi mst1 =
  sec_io Openfile "/etc/passwd"


(** ** Test 2 - HO left 1 **)
let mst2 : mst = {
  cst = list file_descr;
  models = (fun s h -> forall fd. memP fd s <==> is_open fd h);
}

let test2_pi : policy_spec = (fun _ _ _ _ -> true)
let test2_phi : policy mst2 test2_pi = (fun _ _ _ -> true)

let test2_cb (fl:erased tflag) = (fd:file_descr -> MIO (resexn unit) mst2 fl (fun h -> is_open fd h) (fun _ _ lt -> lt == []))
let test2_post = (fun _ h (rfd:resexn file_descr) lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h))
let test2_ct (fl:erased tflag) = (cb:test2_cb fl) -> MIO (resexn file_descr) mst2 fl (fun _ -> True) (test2_post cb)

let test2_rcs : tree (pck_dc mst2) =  
  Node 
     (| unit, resexn file_descr, (fun () h (rfd:resexn file_descr) lt -> Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h))),
              (fun () _ (rfd:resexn file_descr) s1 -> Inl? rfd && (Inl?.v rfd) `List.mem` s1) |) 
     (Node (| file_descr, unit, (fun fd h _ _ -> is_open fd h), (fun fd s0 _ _ -> fd `List.mem` s0) |) Leaf Leaf)
     Leaf
  
assume val test2_c1post : #a:Type -> squash (forall (x:a) h lt. enforced_locally test2_pi h lt ==> (exists r. test2_post x h r lt))

val test2_c2post : #a:Type -> squash (forall (x:a) h r lt. enforced_locally test2_pi h lt /\ (((root test2_rcs)._3) () h r lt) ==> test2_post x h r lt)
let test2_c2post #a = ()

let test2_ct_importable (fl:erased tflag) : safe_importable (test2_ct fl) fl test2_pi mst2 test2_rcs = 
  let exportable_cb = exportable_arrow_pre_post_args file_descr unit #fl #test2_pi #mst2 #(left test2_rcs) (fun fd h -> is_open fd h) (fun fd _ _ lt -> lt == []) in
  safe_importable_arrow_pre_post_res
    (fun _ _ -> True)  (** pre **)
    test2_post       (** post **)
    (test2_c1post #(test2_cb fl))
    (test2_c2post #(test2_cb fl))
    #exportable_cb
    #importable_file_descr

[@@ (postprocess_with (fun () -> norm [delta_only [`%test2_ct; `%test2_cb;`%test2_ct_importable]]; trefl ()))]
let test2 : src_interface = {
  mst = mst2;
  pi = test2_pi; phi = test2_phi; 
  ct = test2_ct; ct_dcs = test2_rcs; ct_importable = test2_ct_importable; 
  psi = (fun _ _ _ -> True);
}

val test2_prog : prog_src test2
let test2_prog #fl ctx () =
  let _ = ctx (fun fd -> Inl ()) in
  (** return exit code **) 0

val test2_ctx : ctx_src test2 
let test2_ctx #fl sec_io eff_rcs cb : MIO (resexn file_descr) mst2 fl (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)) = 
  let post1 = root eff_rcs in
  let (| _, pre1 |) = root (left eff_rcs) in 
  let rfd = sec_io Openfile "/etc/passwd" in
  match rfd with
  | Inl fd -> let _ = pre1 fd in rfd
  | _ -> rfd

val test2_ctx_t : ctx_tgt (comp_int_src_tgt test2)
let test2_ctx_t #fl sec_io cb : MIOpi (resexn file_descr) fl (comp_int_src_tgt test2).pi mst2 = 
  let rfd = sec_io Openfile "/etc/passwd" in
  match rfd with
  | Inl fd -> begin
    //let _ = sec_io Close fd in 
    let _ = cb fd in 
    rfd
  end
  | _ -> rfd

(** ** Test 3 - HO right 1 **)
let mst3 : mst = {
  cst = list file_descr;
  models = (fun s h -> forall fd. memP fd s <==> is_open fd h);
}

let test3_pi : policy_spec = (fun _ _ _ _ -> true)
let test3_phi : policy mst3 test3_pi = (fun _ _ _ -> true)

let test3_cb (fl:erased tflag) = (fd:file_descr -> MIO (resexn unit) mst3 fl (fun h -> True) (fun _ _ lt -> True))
let test3_post #a = (fun (x:file_descr) h (r:a) lt -> True)
let test3_ct (fl:erased tflag) = x:file_descr -> MIO (resexn (test3_cb fl)) mst2 fl (fun _ -> True) (test3_post x)

let test3_rcs : tree (pck_dc mst3) =  
  Node (| file_descr, unit, (fun _ _ _ _ -> true), (fun _ _ _ _ -> true) |) 
     Leaf
     (Node (| file_descr, resexn unit, (fun _ _ _ _ -> true), (fun _ _ _ _ -> true) |) Leaf Leaf)

let test3_cb_importable (fl:erased tflag) : safe_importable (test3_cb fl) fl test3_pi mst3 (right test3_rcs) = 
  safe_importable_arrow_pre_post_args_res
    #file_descr #unit
    #fl
    #test3_pi
    #mst3
    #(right test3_rcs)
    (fun fd h -> True)
    (fun fd _ _ lt -> True)
    ()
    ()
    #exportable_file_descr
    #importable_unit
  
assume val test3_c1post : #a:Type -> squash (forall x h lt. enforced_locally test3_pi h lt ==> (exists (r:a). test3_post x h r lt))
//let test3_c1post #a = () 
val test3_c2post : #a:Type -> squash (forall x h (r:a) lt. enforced_locally test3_pi h lt /\ ((root test3_rcs)._3 x h () lt) ==> test3_post x h r lt)
let test3_c2post #a = ()

let test3_ct_importable (fl:erased tflag) : safe_importable (test3_ct fl) fl test3_pi mst3 test3_rcs = 
  safe_importable_arrow_pre_post_args
    #file_descr #(test3_cb fl) #fl #test3_pi #mst3 #test3_rcs
    (fun _ _ -> True)  (** pre **)
    test3_post       (** post **)
    (test3_c1post #(test3_cb fl))
    (test3_c2post #(test3_cb fl))
    #exportable_file_descr
    #(safe_importable_is_importable (test3_cb_importable fl))

[@@ (postprocess_with (fun () -> norm [delta_only [`%test3_ct; `%test3_cb;`%test3_ct_importable]]; trefl ()))]
let test3 : src_interface = {
  mst = mst3;
  pi = test3_pi; phi = test3_phi;
  ct = test3_ct; ct_dcs = test3_rcs; ct_importable = test3_ct_importable; 
  psi = (fun _ _ _ -> True);
}

val test3_prog : prog_src test3
let test3_prog #fl ctx () : MIO int mst3 (IOActions + fl) (fun _ -> True) (fun _ _ _ -> True) =
  match static_cmd Prog Openfile "test.txt" with
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
let test3_ctx_t #fl sec_io fd : MIOpi (resexn (file_descr -> MIOpi (resexn unit) fl test3_pi mst3)) fl test3_pi mst3 = 
  Inl (fun (fd:file_descr) -> Inl () <: (MIOpi (resexn unit) fl test3_pi mst3))
