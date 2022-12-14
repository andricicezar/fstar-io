module Compiler.Examples

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality
open FStar.List

open BeyondCriteria

open Compiler.Languages
open Compile.IIO.To.ILang
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


(** ** Testing **)
(** *** Example 1 - FO **)
let ex1_ct_pre = (fun () h -> True)
let ex1_ct_post = (fun () h (rfd:resexn file_descr) lt -> (forall fd'. ~((EOpenfile "/etc/passwd" fd') `List.memP` lt)) /\ (Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)))
let ex1_spec_pi : monitorable_prop = (fun cmd arg h -> match cmd, arg with | Openfile, s -> if s = "/etc/passwd" then false else true | _ -> true)
let ex1_inst_pi : monitorable_prop = ex1_spec_pi
let ex1_ct_rc = (fun () h (rfd:resexn file_descr) lt -> Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h)))

val ex1_c1post : squash (forall h lt. ex1_ct_pre () h /\ enforced_locally ex1_spec_pi h lt ==> (ex1_ct_post () h (Inr Contract_failure) lt))
let ex1_c1post = 
  let rec aux (h:trace) (lt:trace) : Lemma
    (requires (enforced_locally ex1_spec_pi h lt))
    (ensures (ex1_ct_post () h (Inr Contract_failure) lt))
    (decreases lt) = (
    match lt with
    | [] -> ()
    | e :: tail -> aux (e::h) tail) in
  Classical.forall_intro_2 (Classical.move_requires_2 aux)

val ex1_c2post : squash (forall x h r lt. ex1_ct_pre () h /\ enforced_locally ex1_spec_pi h lt /\ (ex1_ct_rc x h r lt) ==> ex1_ct_post x h r lt)
let ex1_c2post = ()
                                                  
val ex1_stronger_pis : squash (forall h lt. enforced_locally ex1_inst_pi h lt ==> enforced_locally ex1_spec_pi h lt)
let ex1_stronger_pis = 
  let rec aux (h:trace) (lt:trace) : Lemma
    (requires (enforced_locally ex1_inst_pi h lt))
    (ensures (enforced_locally ex1_spec_pi h lt))
    (decreases lt) = (match lt with
    | [] -> ()
    | e :: tail -> aux (e::h) tail) in 
  Classical.forall_intro_2 (Classical.move_requires_2 aux)

let ex1 : src_interface = {
  spec_pi = ex1_spec_pi; inst_pi = ex1_inst_pi;
  inst_pi_stronger_spec_pi = ex1_stronger_pis;

  ct = (fun fl -> unit -> IIO (resexn file_descr) fl (ex1_ct_pre ()) (ex1_ct_post ()));
  ct_rcs = Node (| unit, resexn file_descr, ex1_ct_rc |) Leaf Leaf;

  ct_importable = (fun fl -> 
    safe_importable_arrow_pre_post_args_res _ _ ex1_c1post ex1_c2post #exportable_unit #importable_file_descr);
  p_post = (fun _ _ _ lt -> (forall fd'. ~((EOpenfile "/etc/passwd" fd') `List.memP` lt)));
}

val ex1_prog : prog_src ex1
let ex1_prog #fl ctx args : IIO int (fl + IOActions) (fun _ -> True) (ex1.p_post args) =
  //let test = static_cmd Openfile "/etc/passwd" in
  let _ = ctx () in
  0 

val ex1_ctx : ctx_src ex1
let ex1_ctx #fl io_acts eff_rcs () : IIO (resexn file_descr) fl (fun _ -> True) (ex1_ct_post ()) = 
  io_acts Openfile "/etc/passwd"

val ex1_ctx_t : ctx_tgt (comp_int_src_tgt ex1)
let ex1_ctx_t #fl io_acts () : IIOpi (resexn file_descr) fl (comp_int_src_tgt ex1).spec_pi = 
  io_acts Openfile "/etc/passwd"

(** ** Example 2 - HO left 1 **)
let ex2_pi : monitorable_prop = (fun _ _ _ -> true)
val ex2_stronger_pis : squash (forall h lt. enforced_locally ex2_pi h lt ==> enforced_locally ex2_pi h lt)
let ex2_stronger_pis = ()

let ex2_cb (fl:erased tflag) = (fd:file_descr -> IIO (resexn unit) fl (fun h -> is_open fd h) (fun _ _ lt -> lt == []))
let ex2_post = (fun _ h (rfd:resexn file_descr) lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h))
let ex2_ct (fl:erased tflag) = (cb:ex2_cb fl) -> IIO (resexn file_descr) fl (fun _ -> True) (ex2_post cb)

let ex2_rcs : tree pck_rc =  
  Node (| unit, resexn file_descr, (fun () h (rfd:resexn file_descr) lt -> Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h))) |) 
     (Node (| file_descr, unit, (fun fd h _ _ -> is_open fd h) |) Leaf Leaf)
     Leaf
  
assume val ex2_c1post : #a:Type -> squash (forall (x:a) h lt. enforced_locally ex2_pi h lt ==> (exists r. ex2_post x h r lt))

val ex2_c2post : #a:Type -> squash (forall (x:a) h r lt. enforced_locally ex2_pi h lt /\ ((Mkdtuple3?._3 (root ex2_rcs)) () h r lt) ==> ex2_post x h r lt)
let ex2_c2post #a = ()

let ex2_ct_importable (fl:erased tflag) : safe_importable (ex2_ct fl) ex2_pi ex2_rcs fl = 
  let exportable_cb = exportable_arrow_pre_post_args file_descr unit #ex2_pi #(left ex2_rcs) #fl (fun fd h -> is_open fd h) (fun fd _ _ lt -> lt == []) in
  safe_importable_arrow_pre_post_res
    (fun _ _ -> True)  (** pre **)
    ex2_post       (** post **)
    (ex2_c1post #(ex2_cb fl))
    (ex2_c2post #(ex2_cb fl))
    #exportable_cb
    #importable_file_descr

[@@ (postprocess_with (fun () -> norm [delta_only [`%ex2_ct; `%ex2_cb;`%ex2_ct_importable]]; trefl ()))]
let ex2 : src_interface = {
  spec_pi = ex2_pi; inst_pi = ex2_pi; inst_pi_stronger_spec_pi = ex2_stronger_pis;
  ct = ex2_ct; ct_rcs = ex2_rcs; ct_importable = ex2_ct_importable; 
  p_post = (fun _ _ _ _ -> True);
}

val ex2_prog : prog_src ex2
let ex2_prog #fl ctx args =
  let _ = ctx (fun fd -> Inl ()) in
  (** return exit code **) 0

val ex2_ctx : ctx_src ex2 
let ex2_ctx #fl io_acts eff_rcs cb : IIO (resexn file_descr) fl (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)) = 
  let post1 = root eff_rcs in
  let (| _, pre1 |) = root (left eff_rcs) in 
  let rfd = io_acts Openfile "/etc/passwd" in
  match rfd with
  | Inl fd -> let _ = pre1 fd in rfd
  | _ -> rfd

val ex2_ctx_t : ctx_tgt (comp_int_src_tgt ex2)
let ex2_ctx_t #fl io_acts cb : IIOpi (resexn file_descr) fl (comp_int_src_tgt ex2).spec_pi = 
  let rfd = io_acts Openfile "/etc/passwd" in
  match rfd with
  | Inl fd -> begin
    //let _ = io_acts Close fd in 
    let _ = cb fd in 
    rfd
  end
  | _ -> rfd

(** ** Example 3 - HO right 1 **)
let ex3_pi : monitorable_prop = (fun _ _ _ -> true)
val ex3_stronger_pis : squash (forall h lt. enforced_locally ex3_pi h lt ==> enforced_locally ex3_pi h lt)
let ex3_stronger_pis = ()

let ex3_cb (fl:erased tflag) = (fd:file_descr -> IIO (resexn unit) fl (fun h -> True) (fun _ _ lt -> True))
let ex3_post #a = (fun (x:file_descr) h (r:a) lt -> True)
let ex3_ct (fl:erased tflag) = x:file_descr -> IIO (resexn (ex3_cb fl)) fl (fun _ -> True) (ex3_post x)

let ex3_rcs : tree pck_rc =  
  Node (| file_descr, unit, (fun x h r lt -> true) |) 
     Leaf
     (Node (| file_descr, resexn unit, (fun fd h _ _ -> true) |) Leaf Leaf)

let ex3_cb_importable (fl:erased tflag) : safe_importable (ex3_cb fl) ex3_pi (right ex3_rcs) fl = 
  safe_importable_arrow_pre_post_args_res
    #file_descr #unit
    #ex3_pi
    #(right ex3_rcs)
    #fl
    (fun fd h -> True)
    (fun fd _ _ lt -> True)
    ()
    ()
    #exportable_file_descr
    #importable_unit
  
assume val ex3_c1post : #a:Type -> squash (forall x h lt. enforced_locally ex3_pi h lt ==> (exists (r:a). ex3_post x h r lt))
//let ex3_c1post #a = () 
val ex3_c2post : #a:Type -> squash (forall x h (r:a) lt. enforced_locally ex3_pi h lt /\ ((Mkdtuple3?._3 (root ex3_rcs)) x h () lt) ==> ex3_post x h r lt)
let ex3_c2post #a = ()

let ex3_ct_importable (fl:erased tflag) : safe_importable (ex3_ct fl) ex3_pi ex3_rcs fl = 
  safe_importable_arrow_pre_post_args
    #file_descr #(ex3_cb fl) #ex3_pi #ex3_rcs #fl
    (fun _ _ -> True)  (** pre **)
    ex3_post       (** post **)
    (ex3_c1post #(ex3_cb fl))
    (ex3_c2post #(ex3_cb fl))
    #exportable_file_descr
    #(safe_importable_is_importable (ex3_cb_importable fl))

[@@ (postprocess_with (fun () -> norm [delta_only [`%ex3_ct; `%ex3_cb;`%ex3_ct_importable;`%ex3_cb_importable;`%safe_importable_is_importable]]; trefl ()))]
let ex3 : src_interface = {
  spec_pi = ex3_pi; inst_pi = ex3_pi; inst_pi_stronger_spec_pi = ex3_stronger_pis;
  ct = ex3_ct; ct_rcs = ex3_rcs; ct_importable = ex3_ct_importable; 
  p_post = (fun _ _ _ _ -> True);
}

val ex3_prog : prog_src ex3
let ex3_prog #fl ctx args : IIO int (IOActions + fl) (fun _ -> True) (fun _ _ _ -> True) =
  match static_cmd Openfile "test.txt" with
  | Inl fd -> begin
    match ctx fd with
    | Inl cb -> let _ : resexn unit = cb fd in 0
    | Inr err -> -1
    end
  | Inr err -> -1

val ex3_ctx : ctx_src ex3 
let ex3_ctx #fl io_acts eff_rcs fd = 
  Inl (fun (fd:file_descr) -> Inl ())

val ex3_ctx_t : ctx_tgt (comp_int_src_tgt ex3)
let ex3_ctx_t #fl io_acts fd : IIOpi (resexn (file_descr -> IIOpi (resexn unit) fl ex3_pi)) fl ex3_pi = 
  Inl (fun (fd:file_descr) -> Inl ())
