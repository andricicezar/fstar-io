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

(* If we specialised itrees to our needs, we might not need noeq, branching would be known. *)
// noeq
// type itree_choice =
// | Tau_pos : itree_choice
// | Event_pos : #x : Type -> x -> itree_choice

// type itree_pos = list itree_choice

(* It will be a pain to define a notion of prefix given the noeq *)
(* let prefix p1 p2 =
  exists l. p2 = p1 @ l
*)

// noeq
// type itree_node (e : Type -> Type) 'r =
// | Ret : 'r -> itree_node e 'r
// | Tau : itree_node e 'r
// | Event : #x : Type -> e x -> itree_node e 'r

(* First approach, unguarded. Would need an interface to operate safely. *)
// type itree1 (e : Type -> Type) (r : Type) =
//   itree_pos -> option (itree_node e r)

(* Second approach, constraint the tree so that it is consistent. *)
(*
type itree2 (e : Type -> Type) (r : Type) =
  t:(itree_pos -> option (itree_node e r)) {
    (* Once we reach a terminal node, we can't go futher *)
    (forall p q. t p = None -> t (p @ q) = None) /\
    (* Conistency: if a node is Ret, one cannot take the next position *)
    (forall p q. t p = Some (Ret x) -> t (p @ q) = None) /\
    (* Conistency for Tau, the only valid position afterward is using Tau_pos *)
    (forall p. t p = Some Tau -> t (p @ [Tau_pos]) <> None) /\
    (forall p c. t p = Some Tau -> c <> Tau_pos -> t (p @ [c]) = None) /\
    (* Conistency for Event, the only valid positions afterward are Event_pos *)
    (forall p e x. t p = Some (Event e) -> t (p @ [Event_pos x]) <> None) /\
    (forall p e. t p = Some (Event e) -> t (p @ [Tau_pos]) = None)
  }
*)

(* Third approach, first take a subset of positions and then a map from it to nodes. *)
(*
type itree3 (e : Type -> Type) (r : Type) = {
  pos_sub : itree_pos -> bool { TODO closed by prefix does not contain both p @ Tau_pos and p @ Event_pos, and if p @ Even_pos for one x, then for all x } ;
  tree : p: itree_pos { pos_sub p } -> itree_node e r
}
*)
