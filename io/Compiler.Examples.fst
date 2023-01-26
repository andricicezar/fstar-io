module Compiler.Examples

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality
open FStar.List

open BeyondCriteria

open Compiler.Languages
open Compiler.IIO.To.TLang
open Compiler.Model

(** Examples objectives:
1. motivating examples
  1a. containing refinement types
  1b. higher-order contracts are not enough
    1b.i. one example comparing with Computational contracts
          and Temporal Higher-order contracts papers
  1c. Properties
    1c.i. Trace Properties
    1c.ii. Hyperproperties
    1c.iii. Relational Hyperproperties
2. testing
  2a. FO
  2b. HO
**)

(** Utils **)
type source_arrow (arg:Type u#a) (res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (fl:erased tflag) =
  x:arg -> IIO (resexn res) fl (pre x) (post x)

type c1typ (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (pi:monitorable_prop) =
  squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> post x h (Inr Contract_failure) lt)
  
type c2typ (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (pi:monitorable_prop) (rc:rc_typ arg (resexn res)) =
  squash (forall x h lt r. pre x h /\ enforced_locally pi h lt /\ rc x h r lt ==> post x h r lt)

type stronger_pis (pi1:monitorable_prop) (pi2:monitorable_prop) =
  squash (forall h lt. enforced_locally pi1 h lt ==> enforced_locally pi2 h lt)


(** ** Testing **)
(** *** Test 1 - FO **)
let test1_pre = (fun () h -> True)
let test1_post = (fun () h (rfd:resexn file_descr) lt -> 
  (forall fd'. ~((EOpenfile "/etc/passwd" fd') `List.memP` lt)) /\ (Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)))

type test1_ct = source_arrow unit file_descr test1_pre test1_post

let test1_pi : monitorable_prop = 
  fun cmd arg h -> 
    match cmd, arg with 
    | Openfile, s -> 
      if s = "/etc/passwd" then false 
      else true 
    | _ -> true
    
let test1_ct_rc = (fun () h (rfd:resexn file_descr) lt -> Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h)))
let test1_ct_rcs : tree pck_rc = 
  Node (| unit, resexn file_descr, test1_ct_rc |) 
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

assume val test1_c2post : c2typ test1_pre test1_post test1_pi test1_ct_rc
//let test1_c2post = ()

let test1_ct_importable (fl:erased tflag) : safe_importable (test1_ct fl) test1_pi test1_ct_rcs fl =
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
  spec_pi = test1_pi; inst_pi = test1_pi;
  inst_pi_stronger_spec_pi = test1_stronger_pis;

  ct = test1_ct;
  ct_rcs = test1_ct_rcs;

  ct_importable = test1_ct_importable;
  p_post = (fun _ _ lt -> (forall fd'. ~((EOpenfile "/etc/passwd" fd') `List.memP` lt)));
}

val test1_prog : prog_src test1
let test1_prog #fl ctx () : IIO int (fl + IOActions) (fun _ -> True) test1.p_post =
  //let test = static_cmd Openfile "/etc/passwd" in
  let _ = ctx () in
  0 

val test1_ctx : ctx_src test1
let test1_ctx #fl io_acts eff_rcs () : IIO (resexn file_descr) fl (fun _ -> True) (test1_post ()) = 
  io_acts Openfile "/etc/passwd"

val test1_ctx_t : ctx_tgt (comp_int_src_tgt test1)
let test1_ctx_t #fl #pi io_acts () : IIOpi (resexn file_descr) fl pi = 
  io_acts Openfile "/etc/passwd"

(** ** Test 2 - HO left 1 **)
let test2_pi : monitorable_prop = (fun _ _ _ -> true)
val test2_stronger_pis : squash (forall h lt. enforced_locally test2_pi h lt ==> enforced_locally test2_pi h lt)
let test2_stronger_pis = ()

let test2_cb (fl:erased tflag) = (fd:file_descr -> IIO (resexn unit) fl (fun h -> is_open fd h) (fun _ _ lt -> lt == []))
let test2_post = (fun _ h (rfd:resexn file_descr) lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h))
let test2_ct (fl:erased tflag) = (cb:test2_cb fl) -> IIO (resexn file_descr) fl (fun _ -> True) (test2_post cb)

let test2_rcs : tree pck_rc =  
  Node (| unit, resexn file_descr, (fun () h (rfd:resexn file_descr) lt -> Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h))) |) 
     (Node (| file_descr, unit, (fun fd h _ _ -> is_open fd h) |) Leaf Leaf)
     Leaf
  
assume val test2_c1post : #a:Type -> squash (forall (x:a) h lt. enforced_locally test2_pi h lt ==> (exists r. test2_post x h r lt))

val test2_c2post : #a:Type -> squash (forall (x:a) h r lt. enforced_locally test2_pi h lt /\ ((Mkdtuple3?._3 (root test2_rcs)) () h r lt) ==> test2_post x h r lt)
let test2_c2post #a = ()

let test2_ct_importable (fl:erased tflag) : safe_importable (test2_ct fl) test2_pi test2_rcs fl = 
  let exportable_cb = exportable_arrow_pre_post_args file_descr unit #test2_pi #(left test2_rcs) #fl (fun fd h -> is_open fd h) (fun fd _ _ lt -> lt == []) in
  safe_importable_arrow_pre_post_res
    (fun _ _ -> True)  (** pre **)
    test2_post       (** post **)
    (test2_c1post #(test2_cb fl))
    (test2_c2post #(test2_cb fl))
    #exportable_cb
    #importable_file_descr

[@@ (postprocess_with (fun () -> norm [delta_only [`%test2_ct; `%test2_cb;`%test2_ct_importable]]; trefl ()))]
let test2 : src_interface = {
  spec_pi = test2_pi; inst_pi = test2_pi; inst_pi_stronger_spec_pi = test2_stronger_pis;
  ct = test2_ct; ct_rcs = test2_rcs; ct_importable = test2_ct_importable; 
  p_post = (fun _ _ _ -> True);
}

val test2_prog : prog_src test2
let test2_prog #fl ctx () =
  let _ = ctx (fun fd -> Inl ()) in
  (** return exit code **) 0

val test2_ctx : ctx_src test2 
let test2_ctx #fl io_acts eff_rcs cb : IIO (resexn file_descr) fl (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)) = 
  let post1 = root eff_rcs in
  let (| _, pre1 |) = root (left eff_rcs) in 
  let rfd = io_acts Openfile "/etc/passwd" in
  match rfd with
  | Inl fd -> let _ = pre1 fd in rfd
  | _ -> rfd

val test2_ctx_t : ctx_tgt (comp_int_src_tgt test2)
let test2_ctx_t #fl io_acts cb : IIOpi (resexn file_descr) fl (comp_int_src_tgt test2).spec_pi = 
  let rfd = io_acts Openfile "/etc/passwd" in
  match rfd with
  | Inl fd -> begin
    //let _ = io_acts Close fd in 
    let _ = cb fd in 
    rfd
  end
  | _ -> rfd

(** ** Test 3 - HO right 1 **)
let test3_pi : monitorable_prop = (fun _ _ _ -> true)
val test3_stronger_pis : squash (forall h lt. enforced_locally test3_pi h lt ==> enforced_locally test3_pi h lt)
let test3_stronger_pis = ()

let test3_cb (fl:erased tflag) = (fd:file_descr -> IIO (resexn unit) fl (fun h -> True) (fun _ _ lt -> True))
let test3_post #a = (fun (x:file_descr) h (r:a) lt -> True)
let test3_ct (fl:erased tflag) = x:file_descr -> IIO (resexn (test3_cb fl)) fl (fun _ -> True) (test3_post x)

let test3_rcs : tree pck_rc =  
  Node (| file_descr, unit, (fun x h r lt -> true) |) 
     Leaf
     (Node (| file_descr, resexn unit, (fun fd h _ _ -> true) |) Leaf Leaf)

let test3_cb_importable (fl:erased tflag) : safe_importable (test3_cb fl) test3_pi (right test3_rcs) fl = 
  safe_importable_arrow_pre_post_args_res
    #file_descr #unit
    #test3_pi
    #(right test3_rcs)
    #fl
    (fun fd h -> True)
    (fun fd _ _ lt -> True)
    ()
    ()
    #exportable_file_descr
    #importable_unit
  
assume val test3_c1post : #a:Type -> squash (forall x h lt. enforced_locally test3_pi h lt ==> (exists (r:a). test3_post x h r lt))
//let test3_c1post #a = () 
val test3_c2post : #a:Type -> squash (forall x h (r:a) lt. enforced_locally test3_pi h lt /\ ((Mkdtuple3?._3 (root test3_rcs)) x h () lt) ==> test3_post x h r lt)
let test3_c2post #a = ()

let test3_ct_importable (fl:erased tflag) : safe_importable (test3_ct fl) test3_pi test3_rcs fl = 
  safe_importable_arrow_pre_post_args
    #file_descr #(test3_cb fl) #test3_pi #test3_rcs #fl
    (fun _ _ -> True)  (** pre **)
    test3_post       (** post **)
    (test3_c1post #(test3_cb fl))
    (test3_c2post #(test3_cb fl))
    #exportable_file_descr
    #(safe_importable_is_importable (test3_cb_importable fl))

[@@ (postprocess_with (fun () -> norm [delta_only [`%test3_ct; `%test3_cb;`%test3_ct_importable]]; trefl ()))]
let test3 : src_interface = {
  spec_pi = test3_pi; inst_pi = test3_pi; inst_pi_stronger_spec_pi = test3_stronger_pis;
  ct = test3_ct; ct_rcs = test3_rcs; ct_importable = test3_ct_importable; 
  p_post = (fun _ _ _ -> True);
}

val test3_prog : prog_src test3
let test3_prog #fl ctx () : IIO int (IOActions + fl) (fun _ -> True) (fun _ _ _ -> True) =
  match static_cmd Openfile "test.txt" with
  | Inl fd -> begin
    match ctx fd with
    | Inl cb -> let _ : resexn unit = cb fd in 0
    | Inr err -> -1
    end
  | Inr err -> -1

val test3_ctx : ctx_src test3 
let test3_ctx #fl io_acts eff_rcs fd = 
  Inl (fun (fd:file_descr) -> Inl ())

val test3_ctx_t : ctx_tgt (comp_int_src_tgt test3)
let test3_ctx_t #fl io_acts fd : IIOpi (resexn (file_descr -> IIOpi (resexn unit) fl test3_pi)) fl test3_pi = 
  Inl (fun (fd:file_descr) -> Inl ())
