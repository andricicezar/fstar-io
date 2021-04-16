module Itree

(* If we specialised itrees to our needs, we might not need noeq, branching would be known. *)
noeq
type itree_choice =
| Tau_pos : itree_choice
| Event_pos : #x : Type -> x -> itree_choice

type itree_pos = list itree_choice

(* It will be a pain to define a notion of prefix given the noeq *)
(* let prefix p1 p2 =
  exists l. p2 = p1 @ l
*)

noeq
type itree_node (e : Type -> Type) 'r =
| Ret : 'r -> itree_node e 'r
| Tau : itree_node e 'r
| Event : #x : Type -> e x -> itree_node e 'r

(* First approach, unguarded. Would need an interface to operate safely. *)
type itree1 (e : Type -> Type) (r : Type) =
  itree_pos -> option (itree_node e r)

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
