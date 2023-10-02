module IOLogging

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality
open FStar.List

open Compiler.Model2

(** Utils **)
type source_arrow (mst:mstate) (arg:Type u#a) (res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (fl:erased tflag) =
  x:arg -> MIO (resexn res) fl mst (pre x) (post x)

type c1_post (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (sgm:policy_spec) =
  squash (forall x h lt. pre x h /\ enforced_locally sgm h lt ==> post x h (Inr Contract_failure) lt)

type c2_post (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (sgm:policy_spec) (#mst:mstate) (dc:dc_typ mst #arg #(resexn res)) =
  squash (forall x h r lt s0 s1. s0 `mst.abstracts` h /\ s1 `mst.abstracts` (apply_changes h lt) /\ pre x h /\ enforced_locally sgm h lt /\ dc x s0 r s1 ==> post x h r lt)

type c1_pre (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (sgm:policy_spec) (#mst:mstate) (dc:dc_typ mst #arg #unit) =
  squash (forall x s0 s1 h. s0 `mst.abstracts` h /\ s1 `mst.abstracts` h /\ dc x s0 () s1 ==> pre x h)

type c2_pre (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (sgm:policy_spec) =
  squash (forall x h lt r. pre x h /\ post x h r lt ==> enforced_locally sgm h lt)

type stronger_sgms (sgm1:policy_spec) (sgm2:policy_spec) =
  squash (forall h lt. enforced_locally sgm1 h lt ==> enforced_locally sgm2 h lt)



let mymst : mstate = {
  typ = option event;
  abstracts = (fun s h ->
    (h == [] /\ s == None)
    \/ (exists e es. h == e::es /\ s == Some e));
}

val get_caller : event -> caller
let get_caller = function
  | EOpenfile c _ _
  | ERead     c _ _
  | EWrite    c _ _
  | EClose    c _ _
  -> c

assume val stdout : file_descr

val to_string : op:io_ops -> string
let to_string o =
  match o with
  | Openfile -> "Openfile ..."
  | Read -> "Read ..."
  | Write -> "Write ..."
  | Close -> "Close ..."

val sgm : policy_spec
let sgm h c op arg =
  match c, op with
  | Ctx, _ ->
    h =!= []
    /\ List.Tot.hd h == EWrite Prog (stdout, to_string op) (Inl ())
  | Prog, Write ->
    (* The verified program can write when: 1) nothing was written
    or 2) the last write was by the context. *)
    Nil? h \/ (get_caller (List.Tot.hd h) == Ctx)
  | _ -> False

val pi0 : s:mymst.typ -> op:io_ops -> arg:io_sig.args op -> r:bool
let pi0 (s0:option event) op arg =
  match s0 with
  | Some (EWrite Prog (fd, inp) (Inl ())) ->
    fd = stdout && inp = to_string op
  | _ -> false

val pi : policy sgm mymst
let pi s0 op arg = 
  pi0 s0 op arg

let log_pre = (fun (op:io_ops) (h:trace) -> h == [] \/ get_caller (List.Tot.hd h) == Ctx)
let log_post = (fun (op:io_ops) h (r:resexn unit) lt -> r =!= Inr Contract_failure /\ lt == [EWrite Prog (stdout, to_string op) r])

type log_pt = source_arrow mymst io_ops unit log_pre log_post

let log_pt_rc : dc_typ mymst = (fun op s0 _ _ -> None? s0 || (get_caller (Some?.v s0) = Ctx))
let log_pt_dcs : tree (pck_dc mymst) =
   Node (| io_ops, unit, log_pt_rc |)
     Leaf
     Leaf

val log_c1_pre : c1_pre log_pre log_post sgm log_pt_rc
let log_c1_pre = ()

val log_c2_pre : c2_pre log_pre log_post sgm
let log_c2_pre = ()

instance interm_io_ops fl sgm mst : interm io_ops fl sgm mst = { mldummy = () }
instance importable_io_ops (#fl:erased tflag) (#sgm:policy_spec) #mst : importable io_ops fl sgm mst Leaf = {
  ityp = io_ops;
  c_ityp = solve;
  import = (fun x Leaf -> Inl x)
}

let log_pt_exportable (fl:erased tflag) : exportable (log_pt fl) fl sgm mymst log_pt_dcs =
   exportable_arrow_pre_post_args
     _ _
     log_pre
     log_post
     #log_c1_pre
     #log_c2_pre

val log_stronger_sgms : stronger_sgms sgm sgm
let log_stronger_sgms =
   let rec aux (h:trace) (lt:trace) : Lemma
     (requires (enforced_locally sgm h lt))
     (ensures (enforced_locally sgm h lt))
     (decreases lt) = (match lt with
     | [] -> ()
     | e :: tail -> aux (e::h) tail) in
   Classical.forall_intro_2 (Classical.move_requires_2 aux)

[@@ (postprocess_with (fun () -> norm [delta_only [`%log_pt; `%source_arrow; `%log_pt_exportable]]; trefl ()))]
 let test1 : src_interface = {
   mst = mymst;
   sgm = sgm; pi = pi;

   pt = log_pt;
   pt_dcs = log_pt_dcs;

   pt_exportable = log_pt_exportable;
}

#push-options "--compat_pre_core 1"
val test1_prog : prog_src test1
let test1_prog #fl op : MIO (resexn unit) (fl+IOOps) mymst (log_pre op) (log_post op) =
  // weird behavior of F*
  let r : (mio_sig mymst).res Write (stdout, to_string op) = static_op Prog Write (stdout, to_string op) in
  r <: resexn unit
  
val test1_ctx_t : ctx_tgt (comp_int_src_tgt test1)
let test1_ctx_t #fl io_acts prog () : MIOpi int fl test1.sgm mymst =
  lemma_append_enforced_locally test1.sgm;
  let _ = prog Openfile in
  let fd = io_acts Openfile "/etc/passwd" in
  0

val test1_ctx : ctx_src test1
let test1_ctx #fl io_acts eff_dcs log () = 
  let (| _, eff_ck |) : eff_pck_dc fl mymst = root eff_dcs in
  let (| _, pre |) = eff_ck Openfile in
  if snd (pre ()) then
    let _ = log Openfile in
    let fd = io_acts Openfile "/etc/passwd" in
    0
  else -1
