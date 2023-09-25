module IOLogging

open FStar.Ghost
open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality
open FStar.List

open Compiler.Model2

(** Utils **)
type source_arrow (mst:mst) (arg:Type u#a) (res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (fl:erased tflag) =
  x:arg -> MIO (resexn res) mst fl (pre x) (post x)

type c1_post (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (pi:policy_spec) =
  squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> post x h (Inr Contract_failure) lt)

type c2_post (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (pi:policy_spec) (#mst:mst) (dc:dc_typ mst #arg #(resexn res)) =
  squash (forall x h r lt s0 s1. s0 `mst.models` h /\ s1 `mst.models` (apply_changes h lt) /\ pre x h /\ enforced_locally pi h lt /\ dc x s0 r s1 ==> post x h r lt)

type c1_pre (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (pi:policy_spec) (#mst:mst) (dc:dc_typ mst #arg #unit) =
  squash (forall x s0 s1 h. s0 `mst.models` h /\ s1 `mst.models` h /\ dc x s0 () s1 ==> pre x h)

type c2_pre (#arg:Type u#a) (#res:Type u#b) (pre:arg -> trace -> Type0) (post:arg -> trace -> resexn res -> trace -> Type0) (pi:policy_spec) =
  squash (forall x h lt r. pre x h /\ post x h r lt ==> enforced_locally pi h lt)

type stronger_pis (pi1:policy_spec) (pi2:policy_spec) =
  squash (forall h lt. enforced_locally pi1 h lt ==> enforced_locally pi2 h lt)



let mymst : mst = {
  cst = option event;
  models = (fun s h ->
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

val to_string : cmd:io_cmds -> string
let to_string o =
  match o with
  | Openfile -> "Openfile ..."
  | Read -> "Read ..."
  | Write -> "Write ..."
  | Close -> "Close ..."

val pi : policy_spec
let pi h c cmd arg =
  match c, cmd with
  | Ctx, _ ->
    h =!= []
    /\ List.Tot.hd h == EWrite Prog (stdout, to_string cmd) (Inl ())
  | Prog , Write -> True
    (* The verified program can write when: 1) nothing was written
    or 2) the last write was by the context. *)
//    Nil? h \/ (get_caller (List.Tot.hd h) == Ctx)
  | _ -> False

val phi0 : s:mymst.cst -> cmd:io_cmds -> arg:io_sig.args cmd -> r:bool
let phi0 (s0:option event) cmd arg =
  match s0 with
  | Some (EWrite Prog (fd, inp) (Inl ())) ->
    fd = stdout && inp = to_string cmd
  | _ -> false

val phi : policy mymst pi
let phi s0 cmd arg = 
  phi0 s0 cmd arg

let log_pre = (fun (op:io_cmds) (h:trace) -> True)
let log_post = (fun (op:io_cmds) h (r:resexn unit) lt -> r =!= Inr Contract_failure /\ lt == [EWrite Prog (stdout, to_string op) r])

type log_pt = source_arrow mymst io_cmds unit log_pre log_post

let log_pt_rc : dc_typ mymst = (fun op s0 _ _ -> None? s0 || (get_caller (Some?.v s0) = Ctx))
let log_pt_rcs : tree (pck_dc mymst) =
   Node (| io_cmds, unit, log_pt_rc |)
     Leaf
     Leaf

val log_c1_pre : c1_pre log_pre log_post pi log_pt_rc
let log_c1_pre = ()

val log_c2_pre : c2_pre log_pre log_post pi
let log_c2_pre = 
  assert (forall op h lt r. r =!= Inr Contract_failure /\ lt == [EWrite Prog (stdout, to_string op) r] ==> enforced_locally pi h lt);
  assert (forall x h lt r. log_post x h r lt ==> enforced_locally pi h lt);
  assert (forall x h lt r. log_pre x h /\ log_post x h r lt ==> enforced_locally pi h lt)

instance interm_io_cmds fl pi mst : interm io_cmds fl pi mst = { mldummy = () }
instance importable_io_cmds (#fl:erased tflag) (#pi:policy_spec) #mst : importable io_cmds fl pi mst Leaf = {
  ityp = io_cmds;
  c_ityp = solve;
  import = (fun x Leaf -> Inl x)
}

let log_pt_exportable (fl:erased tflag) : exportable (log_pt fl) fl pi mymst log_pt_rcs =
   exportable_arrow_pre_post_args
     _ _
     log_pre
     log_post
     #log_c1_pre
     #log_c2_pre

val log_stronger_pis : stronger_pis pi pi
let log_stronger_pis =
   let rec aux (h:trace) (lt:trace) : Lemma
     (requires (enforced_locally pi h lt))
     (ensures (enforced_locally pi h lt))
     (decreases lt) = (match lt with
     | [] -> ()
     | e :: tail -> aux (e::h) tail) in
   Classical.forall_intro_2 (Classical.move_requires_2 aux)

[@@ (postprocess_with (fun () -> norm [delta_only [`%log_pt; `%source_arrow; `%log_pt_exportable]]; trefl ()))]
 let test1 : src_interface = {
   mst = mymst;
   pi = pi; phi = phi;

   pt = log_pt;
   pt_dcs = log_pt_rcs;

   pt_exportable = log_pt_exportable;
}

val prog : op:io_cmds -> arg:io_sig.args op ->
  MIO (resexn unit) mymst AllActions
   (fun h -> h == [] \/ get_caller (List.Tot.hd h) == Ctx)
   (fun _ res lt -> res =!= Inr Contract_failure /\ lt == [EWrite Prog (stdout, to_string op) res])

#push-options "--compat_pre_core 2"

let prog op arg =
  let r : (mio_sig mymst).res Write (stdout, to_string op) = static_cmd Prog Write (stdout, to_string op) in
  r <: resexn unit

#push-options "--compat_pre_core 1"
val test1_prog : prog_src test1
let test1_prog #fl op : MIO (resexn unit) mymst (fl+IOActions) (log_pre op) (log_post op) =
  // weird behavior of F*
  let r : (mio_sig mymst).res Write (stdout, to_string op) = static_cmd Prog Write (stdout, to_string op) in
  r <: resexn unit

val test1_ctx : ctx_src test1
let test1_ctx #fl io_acts eff_rcs prog () : MIOpi int fl test1.pi mymst = 
  let _ = prog Openfile in
  let fd = io_acts Openfile "/etc/passwd" in
  0

assume val lemma_append_enforced_locally : pi:_ ->
  Lemma (forall h lt1 lt2.
      enforced_locally pi h lt1 /\
      enforced_locally pi (apply_changes h lt1) lt2 ==>
      enforced_locally pi h (lt1 @ lt2))
  
val test1_ctx_t : ctx_tgt (comp_int_src_tgt test1)
let test1_ctx_t #fl io_acts prog () : MIOpi int fl test1.pi mymst =
  lemma_append_enforced_locally test1.pi;
  let _ = prog Openfile in
  let fd = io_acts Openfile "/etc/passwd" in
  0
