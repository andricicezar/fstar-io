module Itree

open FStar.List.Tot

(* Enconding of interaction trees, specialised to a free monad

   For now, they are unconstrained, which means that wrong data
   can be represented.

*)

noeq
type op_sig (op : Type) = {
  args : op -> eqtype ;
  res : op -> eqtype
}

type ichoice (op : Type) (s : op_sig op) =
| Tau_choice : ichoice op s
| Call_choice : o:op -> s.args o -> s.res o -> ichoice op s

type ipos op s = list (ichoice op s)

type inode op (s : op_sig op) (a:Type) =
| Ret : a -> ipos op s -> inode op s a
| Call : o:op -> s.args o -> inode op s a
| Tau : inode op s a

type raw_itree op s a =
  ipos op s -> option (inode op s a)

let isRet #op #s #a (n : option (inode op s a)) =
  match n with
  | Some (Ret x p) -> true
  | _ -> false

let ret_pos #op #s #a (n : option (inode op s a) { isRet n }) =
  match n with
  | Some (Ret x p) -> p

let valid_itree (#op:eqtype) #s #a (t : raw_itree op s a) =
  Some? (t []) /\
  // (forall p. None? (t p) ==> (forall q. None? (t (p @ q)))) /\ // Fails for bind
  // (forall p. Some? (t p) ==> (forall pi pe. p = pi @ pe ==> Some? (t pi))) /\ // Fails for bind
  // (forall p. isRet (t p) ==> (forall q. isRet (t (p @ q)) /\ ret_pos (t (p @ q)) = ret_pos (t p) @ q)) /\ // Fails at bind
  (forall p. isRet (t p) ==> (exists q. p = q @ (ret_pos (t p)))) /\
  isRet (t []) ==> ret_pos (t []) = [] // weaker than the above but helps with the root condition

let itree (op:eqtype) s a =
  t:(raw_itree op s a) { valid_itree t }

let ret #op #s #a (x:a) : itree op s a =
  fun p -> Some (Ret x p)

let call (#op:eqtype) #s #a (o : op) (x : s.args o) (k : s.res o -> itree op s a) : itree op s a =
  fun p ->
    match p with
    | [] -> Some (Call o x)
    | Tau_choice :: p -> None
    | Call_choice o' x' y :: p ->
      if o = o' && x = x'
      then k y p
      else None

let tau #op #s #a (k : itree op s a) : itree op s a =
  fun p ->
    match p with
    | [] -> Some Tau
    | Tau_choice :: p -> k p
    | _ -> None

let bind #op #s #a #b (x : itree op s a) (f : a -> itree op s b) : itree op s b =
  fun p ->
    match x p with
    | None -> None
    | Some (Ret u q) -> f u q
    | Some (Call o arg) -> Some (Call o arg)
    | Some Tau -> Some Tau

(* A loop with no events/effects except non-termination *)
let loop #op #s a : itree op s a =
  fun p -> Some Tau

(* Monad instance

   Without GetTrace for now

*)

open Common

type cmds = | Openfile | Read | Close

unfold let io_args cmd : eqtype =
  match cmd with
  | Openfile -> string
  | Read -> file_descr
  | Close -> file_descr

unfold let io_res cmd : eqtype =
  match cmd with
  | Openfile -> file_descr
  | Read -> string
  | Close -> unit

let io_op_sig : op_sig cmds = {
  args = io_args ;
  res = io_res
}

let io a = itree cmds io_op_sig a
