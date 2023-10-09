module NoState 

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality
open FStar.List

open Compiler.Model1

(** Utils **)
type c1typ (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (sgm:policy_spec) =
  squash (forall x h lt. pre x h /\ enforced_locally sgm h lt ==> post x h (Inr Contract_failure) lt)

(** ** Testing **)
(** *** Test 1 - FO **)
let post = (fun () h (rfd:resexn file_descr) lt -> 
  (forall fd'. ~((EOpenfile Ctx "/etc/passwd" fd') `List.memP` lt)))

let mst1 : mstate = {
  typ = empty;
  abstracts = (fun s h -> True);
}

type ct (fl:erased tflag) = x:unit -> MIO (resexn file_descr) fl mst1 (fun _ -> True) (post x)

let sgm : policy_spec = 
  fun h c cmd arg -> 
    Ctx? c /\
    (match cmd with 
    | Openfile -> (arg <> "/etc/passwd")
    | _ -> True)

let pi : policy sgm mst1 =
  fun h cmd arg -> 
    match cmd, arg with 
    | Openfile, s ->
      if s = "/etc/passwd" then false 
      else true 
    | _ -> true

let ct_dcs : tree (pck_dc mst1) = 
  Node (| unit, resexn file_descr, (fun _ _ _ _ -> true) |) 
    Leaf 
    Leaf

val c1post : c1typ (fun _ _ -> True) post sgm 
let c1post = 
  let rec aux (h:trace) (lt:trace) : Lemma
    (requires (enforced_locally sgm h lt))
    (ensures (post () h (Inr Contract_failure) lt))
    (decreases lt) = (
    match lt with
    | [] -> ()
    | e :: tail -> aux (e::h) tail) in
  Classical.forall_intro_2 (Classical.move_requires_2 aux)

let rec enforced_locally__sgm_nopass h lt fd :
  Lemma
    (requires enforced_locally sgm h lt)
    (ensures ~((EOpenfile Ctx "/etc/passwd" fd) `memP` lt))
    (decreases lt)
= match lt with
  | EOpenfile Ctx "/etc/passwd" fd' :: tl ->
    if fd = fd'
    then ()
    else enforced_locally__sgm_nopass (EOpenfile Ctx "/etc/passwd" fd' :: h) tl fd
  | e :: tl ->
    enforced_locally__sgm_nopass (e :: h) tl fd
  | [] -> ()

#set-options "--print_implicits"

let ct_importable (fl:erased tflag) : safe_importable (ct fl) fl sgm mst1 ct_dcs =
  safe_importable_arrow_pre_post_args_res _ _ c1post () #solve #solve

[@@ (postprocess_with (fun () -> norm [delta_only [`%ct; `%ct_importable]]; trefl ()))]
let nostate : src_interface = {
  mst = mst1;
  sgm = sgm; pi = pi;

  ct = ct;
  ct_dcs = ct_dcs;

  ct_importable = ct_importable;
  psi = (fun _ _ lt -> (forall fd'. ~((EOpenfile Ctx "/etc/passwd" fd') `List.memP` lt)));
}
  
#push-options "--compat_pre_core 1"

val prog : prog_src nostate
let prog #fl ctx () : MIO int (fl ⊕ IOOps) mst1 (fun _ -> True) nostate.psi =
  let _ = ctx () in
  0 

val ctx : ctx_src nostate
let ctx #fl sec_io eff_rcs () : MIO (resexn file_descr) fl mst1 (fun _ -> True) (post ()) = 
  sec_io Openfile "/etc/passwd"

val ctx_t : ctx_tgt (comp_int_src_tgt nostate)
let ctx_t #fl sec_io () : MIOpi (resexn file_descr) fl sgm mst1 =
  sec_io Openfile "/etc/passwd"


