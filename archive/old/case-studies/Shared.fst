module Shared

open FStar.Tactics
open FStar.Classical.Sugar

open Common
open IO.Sig
open TC.Monitorable.Hist
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

let rec did_not_open_passwd (lt:trace) : bool =
  match lt with
  | [] -> true
  | EOpenfile arg _ :: tl -> 
      let (fnm, _, _) : io_args Openfile = arg in 
      not (fnm = "/tmp/passwd") && did_not_open_passwd tl
  | _ :: tl -> did_not_open_passwd tl

let ctx_post : file_descr -> trace -> r:(maybe unit) -> trace -> Type0 = 
  fun fd h r lt -> did_not_open_passwd lt

val pi : monitorable_prop
let pi cmd arg h =
  match cmd with
  | Openfile -> 
    let (fnm, _, _) : io_args Openfile = arg in not (fnm = "/tmp/passwd")
  | _ -> true

let rec lemma_pi_implies_did_not_open_passwd (h lt:trace) :
  Lemma
    (requires (enforced_locally pi h lt))
    (ensures (did_not_open_passwd lt)) 
    (decreases lt) =
  match lt with
  | [] -> ()
  | e :: tl -> lemma_pi_implies_did_not_open_passwd (apply_changes h [e]) tl

private
let lemma_c1post_0 fd h lt :
  Lemma
    (requires (ctx_pre fd h /\ enforced_locally pi h lt))
    (ensures (exists r. ctx_post fd h r lt)) = 
  introduce exists r. ctx_post fd h r lt with (Inl ()) and begin
    lemma_pi_implies_did_not_open_passwd h lt
  end

private
let lemma_c1post () : squash (forall x h lt. ctx_pre x h /\ enforced_locally pi h lt ==> (exists r. ctx_post x h r lt)) = 
  Classical.forall_intro_3 (Classical.move_requires_3 (lemma_c1post_0))

private
let lemma_c2post () : squash (forall x h r lt. ctx_pre x h /\ enforced_locally pi h lt  ==> ctx_post x h r lt) =
  lemma_c1post ()

private
let lemma_piprop () : squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h) = ()

instance ctx_post_monitorable () : monitorable_post ctx_pre (fun x h r lt -> ctx_post x h r lt) pi = {
  result_check = (fun _ _ _ _ -> true);
  c1post = lemma_c1post ();
  c2post = lemma_c2post ();
}

noeq type shared_interface = {
  ctx_arg : Type;
  ctx_ret : Type;
  ret : Type;
  pi : monitorable_prop;
  piprop : squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h);
  pre : ctx_arg -> trace -> Type0;
  post : ctx_arg -> trace -> r:(maybe ctx_ret) -> trace -> Type0;
  post_c : monitorable_post pre post pi;
}

let shr : shared_interface = {
  ctx_arg = file_descr;
  ctx_ret = unit;
  ret = unit;
  pi = pi;
  piprop = lemma_piprop ();
  pre = ctx_pre;
  post = (fun fd h r lt -> ctx_post fd h r lt);
  post_c = ctx_post_monitorable ()
}
