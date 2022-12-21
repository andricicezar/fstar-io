module Hyperproperties

open FStar.Tactics
open ExtraTactics
open FStar.Ghost
open FStar.String

open IIO
open BeyondCriteria
open IIO.Behavior

(** There are many difficulties on trying to state Hyperproperties
about whole/partial source programs. **)

(** Whole programs **)

let read_content (fnm:string) : IIO (r:(resexn string){~(r == Inr Contract_failure)}) IOActions
  (requires (fun _ -> True))
  (ensures (fun _ r lt -> 
    (Inr? r /\ lt == [EOpenfile fnm (Inr (Inr?.v r))]) \/
    (exists fd. lt == [EOpenfile fnm (Inl fd);ERead fd r])
    )) =
  match static_cmd Openfile fnm with
  | Inl fd -> static_cmd Read fd
  | Inr err -> Inr err

let rec get_fd_content (fd:file_descr) (t:IIO.Sig.trace) : option string =
  match t with
  | [] -> None
  | (ERead fd' (Inl msg')) :: tl -> if fd = fd' then (Some msg') else (get_fd_content fd tl)
  | (ERead fd' (Inr msg')) :: tl -> if fd = fd' then None else (get_fd_content fd tl)
  | _ :: tl -> get_fd_content fd tl
  
let rec get_content (fnm:string) (t:IIO.Sig.trace) : option string =
  match t with
  | [] -> None
  | (EOpenfile fnm' (Inl fd')) :: tl -> if fnm = fnm' then (get_fd_content fd' tl) else (get_content fnm tl)
  | (EOpenfile fnm' (Inr fd')) :: tl -> if fnm = fnm' then None else (get_content fnm tl)
  | _ :: tl -> get_content fnm tl

val tp1 : trace_property #event
let tp1 (tr:trace) =
  match tr with
  | Infinite_trace _ -> False
  | Finite_trace t r -> 
    match get_content "config.txt" t with
    | Some msg1 -> strlen msg1 == r
    | None -> r == 0

(** Non-interference of secret **)
val hyperprop_tp1 : unit ->  Lemma (
  forall (tr1 tr2:trace). tr1 `member_of` tp1 /\ tr2 `member_of` tp1 ==> 
  (match tr1, tr2 with
  | Finite_trace t1 r1, Finite_trace t2 r2 -> (
    get_content "config.txt" t1 == get_content "config.txt" t2 ==> r1 == r2)))
let hyperprop_tp1 () = ()

let whole1 () : IIO int AllActions 
  (requires (fun _ -> True))
  (ensures (fun _ r lt -> tp1 (Finite_trace lt r))) =
  let config = read_content "config.txt" in
  let secret = read_content "secret.txt" in
  match config with
  | Inl msg -> strlen msg
  | Inr err -> 0

(** Non-interference of secret **)
val hyperprop_whole1 : unit -> Lemma (
  forall (tr1 tr2:trace). tr1 `member_of` (beh whole1) /\ tr2 `member_of` (beh whole1) ==>
  (match tr1, tr2 with
  | Finite_trace t1 r1, Finite_trace t2 r2 -> (
    get_content "config.txt" t1 == get_content "config.txt" t2 ==> r1 == r2)
  | _, _ -> False))
let hyperprop_whole1 () = 
  assume (beh whole1 `subset_of` tp1);
  assert (forall (tr:trace). tr `member_of` (beh whole1) ==> tr `member_of` tp1);
  hyperprop_tp1 ();
  ()
