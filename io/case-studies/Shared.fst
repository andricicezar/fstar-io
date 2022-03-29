module Shared

open FStar.Tactics

open Common
open IO.Sig
open TC.Monitorable
include Utils

let rec is_open (fd:file_descr) (h: trace) : Tot bool =
  match h with
  | [] -> false
  | h :: tail -> match h with
               | EOpenfile _ x -> begin
                 match x with
                 | Inl fd' -> if fd = fd' then true
                              else is_open fd tail
                 | _ -> is_open fd tail
                 end
               | ESocket _ x -> begin
                 match x with
                 | Inl fd' -> if fd = fd' then true
                              else is_open fd tail
                 | _ -> is_open fd tail
                 end
               | EClose fd' _ -> 
                 if fd = fd' then false
                 else is_open fd tail
               | _ -> is_open fd tail

let ctx_pre (fd:file_descr) (h:trace) : Type0 = True 

let ctx_post : file_descr -> trace -> r:(maybe unit) -> trace -> Tot (b:bool{r == Inr Contract_failure ==> b == true}) = 
  fun fd h r lt -> 
    match r with
    | Inr Contract_failure -> true
    | _ -> is_open fd (apply_changes h lt)


val pi : monitorable_prop
let pi cmd arg h =
  match cmd with
  | Openfile -> 
    let (fnm, _, _) : io_args Openfile = arg in not (fnm = "/etc/passwd")
  | _ -> true

instance ctx_post_monitorable () : monitorable_post ctx_pre (fun x h r lt -> ctx_post x h r lt) pi = {
  result_check = (fun _ _ _ _ -> true);
  c1post = admit ();
  c2post = ();
}

noeq type shared_interface = {
  ctx_arg : Type;
  ctx_ret : Type;
  ret : Type;
  pi : monitorable_prop;
  piprop : squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h);
  pre : ctx_arg -> trace -> Type0;
  post : ctx_arg -> trace -> r:(maybe ctx_ret) -> trace -> b:Type0{r == Inr Contract_failure ==> b};
  post_c : monitorable_post pre post pi;
}

let shr : shared_interface = {
  ctx_arg = file_descr;
  ctx_ret = unit;
  ret = unit;
  pi = pi;
  piprop = admit ();
  pre = ctx_pre;
  post = (fun fd h r lt -> ctx_post fd h r lt);
  post_c = ctx_post_monitorable ()
}
