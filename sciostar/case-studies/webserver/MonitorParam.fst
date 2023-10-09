module MonitorParam

open FStar.Tactics
open FStar.List.Tot
open MIO.Sig

let rec is_opened_by_untrusted (h:trace) (fd:file_descr) : bool =
  match h with
  | [] -> false
  | EOpenfile Ctx _ res :: tl ->
    if Inl? res && fd = Inl?.v res then true
    else is_opened_by_untrusted tl fd
  | EClose _ fd' res :: tl ->
    if Inl? res && fd = fd' then false
    else is_opened_by_untrusted tl fd
  | e :: tl -> is_opened_by_untrusted tl fd

val wrote_to : file_descr -> trace -> bool
let rec wrote_to client h =
  match h with
  | [] -> false
  | EAccept _ arg res :: tl -> begin
    match res with
    | Inl fd -> if fd = client then false else wrote_to client tl
    | _ -> wrote_to client tl
  end
  | EWrite Prog arg _ :: tl ->
    let (fd, _) = arg in
    if fd = client then true
    else wrote_to client tl
  | _ :: tl -> wrote_to client tl

let rec did_not_respond (h:trace) : bool =
  match h with
  | [] -> false
  | ERead Prog _ _ :: tl -> true
  | EWrite Prog _ _ :: tl -> false
  | e :: tl -> did_not_respond tl

type status =
| DidNotRespond
| Responded

let models_status (c:status) (h:trace) : bool =
  match c with
  | DidNotRespond -> did_not_respond h
  | Responded -> not (did_not_respond h)

noeq type cst = {
  opened : list file_descr ;
  st : status ;
  written : list file_descr
}


let models (c : cst) (h : trace) : Type0 =
  c.st `models_status` h /\
  (forall fd. fd `mem` c.opened <==> is_opened_by_untrusted h fd) /\
  (forall fd. fd `mem` c.written <==> wrote_to fd h)

let mymst : mstate = {
  typ = cst;
  abstracts = models;
}

let mkcst x y z = {
  opened = x ;
  st = y ;
  written = z
}

let my_init_cst : mymst.typ =
  mkcst [] Responded []

let updst (c : cst) s : cst = {
  opened = c.opened ;
  st = s ;
  written = c.written
}

let open_cst (fd : file_descr) (c : cst) : cst = {
  opened = fd :: c.opened ;
  st = c.st ;
  written = c.written
}

let write_cst (fd : file_descr) (c : cst) : cst = {
  opened = c.opened ;
  st = Responded ;
  written = fd :: c.written
}

let is_neq (#a:eqtype) (x y : a) : bool = x <> y

let close_cst (fd : file_descr) (c : cst) : cst = {
  opened = filter (is_neq fd) c.opened ;
  st = c.st ;
  written = c.written
}

let accept_cst (fd : file_descr) (c : cst) : cst = {
  opened = c.opened ;
  st = c.st ;
  written = filter (is_neq fd) c.written
}


let my_update_cst (s0:cst) (e:event) : (s1:cst{forall h. s0 `models` h ==> s1 `models` (e::h)}) =
  let (| caller, cmd, arg, res |) = destruct_event e in
  match cmd, res with
  | Accept, Inl fd ->
    mem_filter_equiv (is_neq fd) s0.written ;
    accept_cst fd s0
  | Read, _ ->
    let (fd, _) : file_descr * UInt8.t = arg in
    if caller = Prog then updst s0 DidNotRespond else s0
  | Openfile, Inl fd -> if caller = Ctx then open_cst fd s0 else s0
  | Close, Inl rr ->
    mem_filter_equiv (is_neq arg) s0.opened ;
    close_cst arg s0
  | Write, _ ->
    let arg : file_descr * Bytes.bytes = arg in
    let (fd, bb) = arg in
    if caller = Prog then write_cst fd s0 else s0
  | _ -> s0

let mymst_impl : mst_impl mymst = {
  init = my_init_cst;
  update = (fun s e h -> my_update_cst s e);
}
