module Compiler.Model2.Examples

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality
open FStar.List

open Compiler.Model2

(** Utils **)
type source_arrow (arg:Type u#a) (res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (fl:erased tflag) =
  x:arg -> MIO (resexn res) fl (pre x) (post x)

type c1_post (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (pi:policy_spec) =
  squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> post x h (Inr Contract_failure) lt)
  
type c2_post (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (pi:policy_spec) (dc:dc_typ arg (resexn res)) =
  squash (forall x h lt r. pre x h /\ enforced_locally pi h lt /\ dc x h r lt ==> post x h r lt)

type c1_pre (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (pi:policy_spec) (dc:dc_typ arg unit) =
  squash (forall h x. dc x h () [] ==> pre x h)

type c2_pre (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (pi:policy_spec) =
  squash (forall x h lt r. pre x h /\ post x h r lt ==> enforced_locally pi h lt)

type stronger_pis (pi1:policy_spec) (pi2:policy_spec) =
  squash (forall h lt. enforced_locally pi1 h lt ==> enforced_locally pi2 h lt)


(** ** Testing **)
(** *** Test 1 - FO **)
let test1_pi : policy_spec = 
  fun h c cmd arg -> 
    Ctx? c /\
    (match cmd with 
    | Openfile -> (arg <> "/etc/passwd")
    | _ -> True)

let test1_phi : policy test1_pi =
  fun h cmd arg -> 
    match cmd, arg with 
    | Openfile, s -> 
      if s = "/etc/passwd" then false 
      else true 
    | _ -> true

let test1_pre = (fun (fd:file_descr) h -> b2t(is_open fd h))
let test1_post = (fun (fd:file_descr) h (r:resexn unit) lt -> enforced_locally test1_pi h lt)

type test1_pt = source_arrow file_descr unit test1_pre test1_post
    
let test1_pt_rc = (fun (fd:file_descr) h _ lt -> is_open fd h)
let test1_pt_rcs : tree pck_dc = 
  Node (| file_descr, unit, test1_pt_rc |) 
    Leaf 
    Leaf

val test1_c1_pre : c1_pre test1_pre test1_post test1_pi test1_pt_rc
let test1_c1_pre = ()

val test1_c2_pre : c2_pre test1_pre test1_post test1_pi
let test1_c2_pre = ()

let test1_pt_exportable (fl:erased tflag) : exportable (test1_pt fl) fl test1_pi test1_pt_rcs =
  exportable_arrow_pre_post_args
    _ _
    test1_pre
    test1_post
    #test1_c1_pre
    #test1_c2_pre
                                                  
val test1_stronger_pis : stronger_pis test1_pi test1_pi
let test1_stronger_pis = 
  let rec aux (h:trace) (lt:trace) : Lemma
    (requires (enforced_locally test1_pi h lt))
    (ensures (enforced_locally test1_pi h lt))
    (decreases lt) = (match lt with
    | [] -> ()
    | e :: tail -> aux (e::h) tail) in 
  Classical.forall_intro_2 (Classical.move_requires_2 aux)

[@@ (postprocess_with (fun () -> norm [delta_only [`%test1_pt; `%source_arrow; `%test1_pt_exportable]]; trefl ()))]
let test1 : src_interface = {
  pi = test1_pi; phi = test1_phi;

  pt = test1_pt;
  pt_dcs = test1_pt_rcs;
  
  pt_exportable = test1_pt_exportable;
}

val test1_prog : prog_src test1
let test1_prog #fl fd : MIO (resexn unit) (fl+IOActions) (test1_pre fd) (test1_post fd) =
  // weird behavior of F*
  let r : mio_sig.res Close fd = static_cmd Ctx Close fd in
  r <: resexn unit

val test1_ctx : ctx_src test1
let test1_ctx #fl io_acts eff_rcs prog () : MIOpi int fl test1.pi = 
  let fd = io_acts Openfile "/etc/passwd" in
  (match fd with
  | Inl fd -> let _ = prog fd in ()
  | Inr err -> ());
  0

val test1_ctx_t : ctx_tgt (comp_int_src_tgt test1)
let test1_ctx_t #fl io_acts prog () : MIOpi int fl test1.pi =
  let fd = io_acts Openfile "/etc/passwd" in
  (match fd with
  | Inl fd -> let _ = prog fd in ()
  | Inr err -> ());
  0
