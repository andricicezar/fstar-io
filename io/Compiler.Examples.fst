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
    safe_importable_arrow_pre_post_args unit _ _ _ ex1_c1post ex1_c2post);
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

let ex3_pi : monitorable_prop = (fun _ _ _ -> true)
let ex3_post = (fun h (rfd:resexn file_descr) lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h))

assume val ex3_stronger_pis : squash (forall h lt. enforced_locally ex3_pi h lt ==> enforced_locally ex3_pi h lt)

let ex3_rcs : tree pck_rc =  
  Node (| unit, resexn file_descr, (fun () h (rfd:resexn file_descr) lt -> Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h))) |) 
     (Node (| file_descr, unit, (fun fd h _ _ -> is_open fd h) |) Leaf Leaf)
     Leaf
  
assume val ex3_c1post : squash (forall h lt. enforced_locally ex3_pi h lt ==> (exists (rfd:resexn file_descr). Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)))
val ex3_c2post : squash (forall h (rfd:resexn file_descr) lt. Inl? rfd && (is_open (Inl?.v rfd) (rev lt @ h)) ==> (Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)))
let ex3_c2post = ()

let ex3 : src_interface = {
  spec_pi = ex3_pi;
  inst_pi = ex3_pi;
  inst_pi_stronger_spec_pi = ex3_stronger_pis;

  ct = (fun fl -> (fd:file_descr -> IIO (resexn unit) fl (fun h -> is_open fd h) (fun _ _ lt -> lt == [])) -> IIO (resexn file_descr) fl (fun _ -> True) ex3_post);
  ct_rcs = ex3_rcs;

  ct_importable = (fun fl -> 
    let exportable_cb = exportable_arrow_pre_post_args file_descr unit #ex3_pi #(left ex3_rcs) #fl (fun fd h -> is_open fd h) (fun fd _ _ lt -> lt == []) in
    safe_importable_arrow_pre_post exportable_cb importable_file_descr (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)) ex3_c1post ex3_c2post);

  p_post = (fun _ _ _ _ -> True);
}

val ex3_prog : prog_src ex3
let ex3_prog #fl ctx args =
  let _ = ctx (fun fd -> Inl ()) in
  0

val ex3_ctx : ctx_src ex3 
let ex3_ctx #fl io_acts eff_rcs cb : IIO (resexn file_descr) fl (fun _ -> True) (fun h rfd lt -> Inl? rfd ==> is_open (Inl?.v rfd) (rev lt @ h)) = 
  let post1 = root eff_rcs in
  let (| _, pre1 |) = root (left eff_rcs) in 
  let rfd = io_acts Openfile "/etc/passwd" in
  match rfd with
  | Inl fd -> let _ = pre1 fd in rfd
  | _ -> rfd

val ex3_ctx_t : ctx_tgt (comp_int_src_tgt ex3)
let ex3_ctx_t #fl io_acts cb : IIOpi (resexn file_descr) fl (comp_int_src_tgt ex3).spec_pi = 
  let rfd = io_acts Openfile "/etc/passwd" in
  match rfd with
  | Inl fd -> begin
    //let _ = io_acts Close fd in 
    let _ = cb fd in 
    rfd
  end
  | _ -> rfd
