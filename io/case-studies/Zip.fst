module Zip 

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality
open FStar.List

open Compiler.Model1

let mymst : mstate = { typ = trace; abstracts = (fun s h -> s == h); }

let rec is_opened_by_prog (h:trace) (fd:file_descr) : bool =
  match h with
  | [] -> false
  | EOpenfile Prog _ res :: tl ->
    if Inl? res && fd = Inl?.v res then true
    else is_opened_by_prog tl fd
  | EClose _ fd' res :: tl ->
    if Inl? res && fd = fd' then false
    else is_opened_by_prog tl fd
  | e :: tl -> is_opened_by_prog tl fd

val sgm : policy_spec
let sgm h c cmd arg =
  match c, cmd with
  | Ctx, Read ->
    let fd : file_descr = arg in
    is_opened_by_prog h fd
  | Ctx, Write ->
    let (fd, _) : file_descr * string = arg in
    is_opened_by_prog h fd
  | Ctx, _ -> false
  | Prog, _ -> true

val pi : policy sgm mymst
let pi h cmd arg =
  match cmd with
  | Read ->
    let fd : file_descr = arg in
    is_opened_by_prog h fd
  | Write ->
    let (fd, _) : file_descr * string = arg in
    is_opened_by_prog h fd
  | _ -> false

type zip_cb (fl:erased tflag) = 
  fd:file_descr -> MIO (resexn unit) fl mymst (fun h -> is_open fd h) (fun h _ lt -> enforced_locally sgm h lt)

type zip (fl:erased tflag) =
  afd:file_descr -> MIO (resexn (zip_cb fl)) fl mymst (fun h -> is_open afd h) (fun h _ lt -> enforced_locally sgm h lt)

let zip_dcs : tree (pck_dc mymst) =  
  Node (| file_descr, unit, (fun _ _ _ _ -> true) |) 
     Leaf
     (Node (| file_descr, resexn unit, (fun _ _ _ _ -> true) |) Leaf Leaf)

let zip_cb_importable (fl:erased tflag) : safe_importable (zip_cb fl) fl sgm mymst (right zip_dcs) = 
  safe_importable_arrow_pre_post_args_res _ _ () () #exportable_file_descr #solve

let zip_importable (fl:erased tflag) : safe_importable (zip fl) fl sgm mymst zip_dcs = 
  safe_importable_arrow_pre_post_args _ _ () () #solve #(safe_importable_is_importable (zip_cb_importable fl))

[@@ (postprocess_with (fun () -> norm [delta_only [`%zip; `%zip_cb;`%zip_importable]]; trefl ()))]
let zip_int : src_interface = {
  mst = mymst;
  sgm = sgm; pi = pi;
  ct = zip; ct_dcs = zip_dcs; ct_importable = zip_importable; 
  psi = (fun h _ lt -> enforced_locally sgm h lt);
}

#push-options "--compat_pre_core 1"

val prog : prog_src zip_int
let prog #fl ctx () : MIO int (IOOps ⊕ fl) mymst (fun _ -> True) (fun h _ lt -> enforced_locally sgm h lt) =
  lemma_append_enforced_locally sgm;
  match static_op Prog Openfile "archive.zipfst" with
  | Inl afd -> begin
    match ctx afd with
    | Inl cb -> begin
      match static_op Prog Openfile "somefile.txt" with
      | Inl fd -> let _ = cb fd in 0
      | _ -> -1
    end
    | _ -> -2
    end
  | _ -> -3

val ctx_t : ctx_tgt (comp_int_src_tgt zip_int)
let ctx_t #fl sec_io afd : MIOpi (resexn (file_descr -> MIOpi (resexn unit) fl sgm mymst)) fl sgm mymst = 
  let _ = sec_io Write (afd, "Archive Header") in
  let cb : (file_descr -> MIOpi (resexn unit) fl sgm mymst) = (fun fd -> 
    match sec_io Read fd with
    | Inr err -> Inr err
    | Inl msg -> begin
        let _ = sec_io Write (afd, "File Header") in
        let _ = sec_io Write (afd, msg) in
        Inl ()
    end) in
  Inl cb 


val ctx : ctx_src zip_int 
let ctx #fl sec_io _ afd = 
  let _ = sec_io Write (afd, "Archive Header") in
  let cb : (file_descr -> MIOpi (resexn unit) fl sgm mymst) = (fun fd -> 
    match sec_io Read fd with
    | Inr err -> Inr err
    | Inl msg -> begin
        let _ = sec_io Write (afd, "File Header") in
        let _ = sec_io Write (afd, msg) in
        Inl ()
    end) in
  Inl cb 
