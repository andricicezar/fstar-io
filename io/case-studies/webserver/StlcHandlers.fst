module StlcHandlers

open FStar.Tactics
open FStar.Constructive
open FStar.Classical
open FStar.FunctionalExtensionality
open FStar.StrongExcludedMiddle
open FStar.Ghost
open FStar.Bytes
open FStar.UInt32
open FStar.List.Tot

open Compiler.StlcToFStar
open Compiler.Languages
open Compiler.Model1
open Utils
open WebServer

#push-options "--compat_pre_core 1"

let tgt_cs_int = comp.comp_int cs_int
type tgt_handler = ctx_tgt tgt_cs_int

let ctx_env =
  extend (TArr TString (TSum TFDesc TExn)) (* openfile *)
  (extend (TArr TUnit (TSum TFDesc TExn)) (* socket *)
  (extend (TArr (TPair TFDesc TBytes) (TSum TUnit TExn)) (* write *)
          empty)) 

let handler_env =
  extend (TArr TString (TSum TFDesc TExn)) (* openfile *)
  (extend (TArr TUnit (TSum TFDesc TExn)) (* socket *)
  (extend (TArr (TPair TFDesc TBytes) (TSum TUnit TExn)) (* write *)
  (extend TFDesc (* client *)
  (extend (TArr TBytes (TSum TUnit TExn)) (*send *) 
  (extend TBytes empty))))) (* req *)

let bt_ctx (e:exp{ELam? e}) (t:typ) (h:typing ctx_env e t) (#fl:erased tflag) (#pi:policy_spec) (#mst:mst) (sec_io:io_lib fl pi mst Ctx) : (typ_to_fstar t fl pi mst) =
   let write : FStar.Universe.raise_t file_descr * FStar.Universe.raise_t bytes -> MIOpi (either (FStar.Universe.raise_t unit) (FStar.Universe.raise_t exn)) fl pi _ = fun fdb ->
     let fd = FStar.Universe.downgrade_val (fst fdb) in
     let b = FStar.Universe.downgrade_val (snd fdb) in
     match sec_io Write (fd, b) with
     | Inl unit -> Inl (FStar.Universe.raise_val unit)
     | Inr ex -> Inr (FStar.Universe.raise_val ex) in
   let socket : FStar.Universe.raise_t unit -> MIOpi (either (FStar.Universe.raise_t file_descr) (FStar.Universe.raise_t exn)) fl pi _ = fun _u ->
     match sec_io Socket () with
     | Inl fd -> Inl (FStar.Universe.raise_val fd)
     | Inr ex -> Inr (FStar.Universe.raise_val ex) in
   let openfile : FStar.Universe.raise_t string -> MIOpi (either (FStar.Universe.raise_t file_descr) (FStar.Universe.raise_t exn)) fl pi _ = fun s ->
     let s = FStar.Universe.downgrade_val s in
     match sec_io Openfile (s, [O_RDWR], 0x650) with
     | Inl fd -> Inl (FStar.Universe.raise_val fd)
     | Inr ex -> Inr (FStar.Universe.raise_val ex) in
   let ctx_venv = 
     vextend #fl #mst #pi #(TArr TString (TSum TFDesc TExn)) openfile (
     vextend #fl #mst #pi #(TArr TUnit (TSum TFDesc TExn)) socket (
     vextend #fl #mst #pi #(TArr (TPair TFDesc TBytes) (TSum TUnit TExn)) write (
     vempty #fl #pi #mst))) in
   exp_to_fstar' ctx_env e t h ctx_venv

let bt_handler (e:exp) (h:typing handler_env e (TSum TUnit TExn)) : tgt_handler =
 fun #fl sec_io (client : int) (req : Bytes.bytes) (send : Bytes.bytes -> MIOpi (either unit exn) fl pi _) ->
   let client : FStar.Universe.raise_t file_descr = FStar.Universe.raise_val client in
   let write : FStar.Universe.raise_t file_descr * FStar.Universe.raise_t bytes -> MIOpi (either (FStar.Universe.raise_t unit) (FStar.Universe.raise_t exn)) fl pi _ = fun fdb ->
     let fd = FStar.Universe.downgrade_val (fst fdb) in
     let b = FStar.Universe.downgrade_val (snd fdb) in
     match sec_io Write (fd, b) with
     | Inl unit -> Inl (FStar.Universe.raise_val unit)
     | Inr ex -> Inr (FStar.Universe.raise_val ex) in
   let socket : FStar.Universe.raise_t unit -> MIOpi (either (FStar.Universe.raise_t file_descr) (FStar.Universe.raise_t exn)) fl pi _ = fun _u ->
     match sec_io Socket () with
     | Inl fd -> Inl (FStar.Universe.raise_val fd)
     | Inr ex -> Inr (FStar.Universe.raise_val ex) in
   let openfile : FStar.Universe.raise_t string -> MIOpi (either (FStar.Universe.raise_t file_descr) (FStar.Universe.raise_t exn)) fl pi _ = fun s ->
     let s = FStar.Universe.downgrade_val s in
     match sec_io Openfile (s, [O_RDWR], 0x650) with
     | Inl fd -> Inl (FStar.Universe.raise_val fd)
     | Inr ex -> Inr (FStar.Universe.raise_val ex) in
   let send : FStar.Universe.raise_t bytes -> MIOpi (either (FStar.Universe.raise_t unit) (FStar.Universe.raise_t exn)) fl pi _ = fun b -> match send (FStar.Universe.downgrade_val b) with
     | Inl unit -> Inl (FStar.Universe.raise_val unit)
     | Inr ex -> Inr (FStar.Universe.raise_val ex) in
   let req : FStar.Universe.raise_t bytes = FStar.Universe.raise_val req in
   let handler_venv = 
     vextend #fl #mymst #pi #_ openfile (
     vextend #fl #mymst #pi #_ socket (
     vextend #fl #mymst #pi #(TArr (TPair TFDesc TBytes) (TSum TUnit TExn)) write (
     vextend #fl #mymst #pi #TFDesc client (
     vextend #fl #mymst #pi #(TArr TBytes (TSum TUnit TExn)) send (
     vextend #fl #mymst #pi #TBytes req (
     vempty #fl #pi #mymst)))))) in
   let v = exp_to_fstar handler_env e (TSum TUnit TExn) h handler_venv in
   match v with
   | Inl v -> Inl (FStar.Universe.downgrade_val v)
   | Inr w -> Inr (FStar.Universe.downgrade_val w)

let rec e_nat (n : nat) =
  if n = 0 then EZero else ESucc (e_nat (n - 1))
let rec ty_nat #env (n : nat) : typing env (e_nat n) TNat =
  if n = 0 then TyZero else TySucc (ty_nat #env (n - 1))


let e_let_in (t : typ) (rhs : exp) (result : exp) =
  EApp (ELam t result) rhs
let ty_let_in #env (t : typ) (u : typ) (#rhs : exp) (#result : exp) (ty_rhs : typing env rhs t) (ty_result : typing (extend t env) result u) : typing env (e_let_in t rhs result) u =
  TyApp (TyLam t ty_result) ty_rhs

let v_openfile = 0
let v_socket = 1
let v_write = 2
let v_client = 3
let v_send = 4
let v_req = 5

let e_openfile = EVar v_openfile
let e_socket = EVar v_socket
let e_client = EVar v_client
let e_write = EVar v_write
let e_send = EVar v_send
let e_req = EVar v_req

let ty_openfile = TyVar #handler_env v_openfile
let ty_socket = TyVar #handler_env v_socket
let ty_client = TyVar #handler_env v_client
let ty_write = TyVar #handler_env v_write
let ty_send = TyVar #handler_env v_send
let ty_req = TyVar #handler_env v_req

(* Some handlers from Adversarialhandlers.fst *)

let handler1 : tgt_handler =
  let e : exp = EInl EUnit in
  let h : typing handler_env e (TSum TUnit TExn) = TyInl TyUnit in
  bt_handler e h

let handler2 : tgt_handler =
  let e : exp = EApp e_send (EBytesCreate (e_nat 501) (EByteLit 10uy)) in
  let h : typing handler_env e (TSum TUnit TExn) = TyApp ty_send (TyBytesCreate (ty_nat 501) (TyByteLit #_ #10uy)) in
  bt_handler e h

let handler3 : tgt_handler =
  let e : exp = e_let_in (TSum TFDesc TExn) (EApp e_openfile (EStringLit "/etc/passwd")) (EInl EUnit) in
  let h : typing handler_env e (TSum TUnit TExn) = ty_let_in (TSum TFDesc TExn) (TSum TUnit TExn) (TyApp ty_openfile (TyStringLit #_ #"/etc/passwd")) (TyInl TyUnit) in
  bt_handler e h

let handler4 : tgt_handler =
  let e : exp = EApp e_write (EPair e_client (EBytesCreate (e_nat 501) (EByteLit 10uy))) in
  let h : typing handler_env e (TSum TUnit TExn) = TyApp ty_write (TyPair ty_client (TyBytesCreate (ty_nat 501) (TyByteLit #_ #10uy))) in
  bt_handler e h

let handler5 : tgt_handler =
  let e : exp = e_let_in (TSum TFDesc TExn) (EApp e_socket EUnit) (EInl EUnit) in
  let h : typing handler_env e (TSum TUnit TExn) = ty_let_in (TSum TFDesc TExn) (TSum TUnit TExn) (TyApp ty_socket TyUnit) (TyInl TyUnit) in
  bt_handler e h
