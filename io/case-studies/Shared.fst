module Shared

open FStar.Tactics

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


(** The post-condition is too storng to be able to write a monitorable prop (pi).
   The problem is that we can not prevent with the pi the closing of a file_descr by the 
   plugin **)
let ctx_post : file_descr -> trace -> r:(maybe unit) -> trace -> Tot (b:bool{r == Inr Contract_failure ==> b == true}) = 
  fun fd h r lt -> 
    match r with
    | Inr Contract_failure -> true
    | _ -> not (is_open fd h) || is_open fd (apply_changes h lt)


val pi : monitorable_prop
let pi cmd arg h =
  match cmd with
  | Openfile -> 
    let (fnm, _, _) : io_args Openfile = arg in not (fnm = "/etc/passwd")
  | _ -> true

private
let lemma_c1post_0 fd h lt :
  Lemma
    (requires (ctx_pre fd h /\ enforced_locally pi h lt))
    (ensures (exists r. ctx_post fd h r lt)) = admit ()

private
let lemma_c1post () : squash (forall x h lt. ctx_pre x h /\ enforced_locally pi h lt ==> (exists r. ctx_post x h r lt)) = 
  Classical.forall_intro_3 (Classical.move_requires_3 (lemma_c1post_0))

private
let lemma_c2post () : squash (forall x h r lt. ctx_pre x h /\ enforced_locally pi h lt  ==> ctx_post x h r lt) = admit ()

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
