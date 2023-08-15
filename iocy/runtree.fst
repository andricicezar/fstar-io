module Runtree

open FStar.Tactics
open FStar.List.Tot.Base

(** Open challenges with the runtree data structure

  1) how does one define `await id`?
  
  2) can one define a membership function (⋳) that checks that a trace is possible in the runtree
     ∀ rt t. t ⋳ rt <==> t ∈ as_traces rt

  3) otherwise, is there another representation that has a membership function and for which a monad morphism exists (here repr_as_traces)?
     
     ∀ rt rt'. repr_as_traces (to_repr rt) `bind_st` repr_as_traces (to_repr rt') == repr_as_traces (to_repr (rt `bind_rt` rt'))

     3.1) what is bind of set of traces (bind_st)?

     that property can also be written without the equality: 
     
     ∀ rt rt' t. t ∈ (repr_as_traces (to_repr rt) `bind_st` repr_as_traces (to_repr rt')) <==> t ∈ repr_as_traces (to_repr (rt `bind_rt` rt'))

     A solution would be to convert the tree into a directed graph by converting the `EAwait id` events into direct edges
     from the awaited node to the current node.

     3.2) directed graphs are not monads, so at a first glance it sounds like there is no monad morphism.
          However, it is a subclass of graphs produced from runtrees, so maybe there is hope?

  4) how can one define non-termination?
**)


type runtree 'e : Type =
| Leaf : runtree 'e
| Node : list 'e -> k1:runtree 'e -> k2:runtree 'e -> runtree 'e

let empty_runtree #e : runtree e = Leaf

let return_runtree (lt:list 'e) : runtree 'e = Node lt Leaf Leaf

let async_runtree (l:runtree 'e) : runtree 'e = Node [] l Leaf

let rec append_runtree (x:runtree 'e) (y:runtree 'e) : Tot (runtree 'e) (decreases x) =
  match x, y with
  | _, Leaf -> x
  | Leaf, _ -> y
  | Node ltx Leaf Leaf, Node lty k1y k2y -> Node (ltx @ lty) k1y k2y
  | Node ltx k1x k2x, _ ->
      Node ltx k1x (append_runtree k2x y)

let rec lemma_append_runtree_assoc l1 l2 l3 : Lemma (l1 `append_runtree` (l2 `append_runtree` l3) == (l1 `append_runtree` l2) `append_runtree` l3) =
  match l1, l2, l3 with
  | Leaf, _, _ -> ()
  | Node ltx Leaf Leaf, Leaf, _ -> ()
  | Node ltx Leaf Leaf, Node lty k1y k2y, Leaf -> ()
  | Node ltx Leaf Leaf, Node lty k1y k2y, Node ltz k1z k2z ->
      List.Tot.Properties.append_assoc ltx lty ltz
  | Node _ _ k2x, _, _ -> lemma_append_runtree_assoc k2x l2 l3
  
  begin
    match l2 with
    | Leaf -> ()
    | Node lty Leaf Leaf -> begin
      match l3 with
      | Leaf -> ()
      | Node ltz k1z k2z ->
        List.Tot.Properties.append_assoc ltx lty ltz
    end
    | Node lty k1y k2y -> begin
      match l3 with
      | Leaf -> ()
      | Node ltz k1z k2z -> () 
    end
  end
  | Node _ _ k2x -> lemma_append_runtree_assoc k2x l2 l3

let f = Node [1;2;3] Leaf Leaf
let async1 = Node [] (Node [4;5] Leaf Leaf) Leaf
let k1 = Node [6;7] Leaf Leaf
let prog1 = Node [1;2;3] (Node [4;5] Leaf Leaf) (Node [6;7] Leaf Leaf)

let _ = assert (append_runtree (append_runtree f async1) k1 == prog1)

let rec interleave (t1:list 'e) (t2:list 'e) : list (list 'e) =
  match t1, t2 with
  | [], [] -> []
  | _, [] -> [t1]
  | [], _ -> [t2]
  | _, _ -> 
      (map (append [hd t1]) (interleave (tail t1) t2)) @
      (map (append [hd t2]) (interleave t1 (tail t2)))

let _ =
  assert (interleave #int [0] [] == [ [0] ]);
  assert (interleave #int [] [0] == [ [0] ]);
  assert (interleave #int [0] [1;2] == [ [0;1;2]; [1;0;2]; [1;2;0] ]);
  assert (interleave #int [1;2] [0] == [ [1;2;0]; [1;0;2]; [0;1;2] ]);
  assert (flatten (map (interleave [0]) [[]]) == [ [0] ])

let product (xs:list 'a) (ys:list 'b) : list ('a * 'b) =
  concatMap (fun x -> map (fun y -> (x, y)) ys) xs

let uncurry2 (f:'a -> 'b -> 'c) ((a,b):('a * 'b)) : 'c = f a b

let product_map (f:'a -> 'a -> list 'a) (l1:list 'a) (l2:list 'a) : list 'a =
  match l1, l2 with
  | [], [] -> []
  | [], l2 -> l2
  | l1, [] -> l1
  | _, _ -> concatMap (uncurry2 f) (product l1 l2)

val (===) : list 'a -> list 'a -> Type0
let (===) l1 l2 = forall e. e `memP` l1 <==> e `memP` l2

let _ =
  assert (product_map interleave [[]; [1;2]] [[]] === [ [1;2] ]);
  assert (product_map interleave [[1;2];[]] [[]] === [ [1;2] ]);
  assert (product_map interleave [[1;2]] [[0]] === [ [1;2;0]; [0;1;2]; [1;0;2] ])

let _ =
  assert (product_map interleave [[0;1;2];[0;2;1]] [[5;6]] === [
      [0; 1; 2; 5; 6]; [0; 1; 5; 2; 6]; [0; 1; 5; 6; 2]; [0; 5; 1; 2; 6]; [0; 5; 1; 6; 2];
      [0; 5; 6; 1; 2]; [5; 0; 1; 2; 6]; [5; 0; 1; 6; 2]; [5; 0; 6; 1; 2]; [5; 6; 0; 1; 2];
      [0; 2; 1; 5; 6]; [0; 2; 5; 1; 6]; [0; 2; 5; 6; 1]; [0; 5; 2; 1; 6]; [0; 5; 2; 6; 1];
      [0; 5; 6; 2; 1]; [5; 0; 2; 1; 6]; [5; 0; 2; 6; 1]; [5; 0; 6; 2; 1]; [5; 6; 0; 2; 1]
    ]) by (compute ())

type event (e:Type0) =
| Ev : e -> event e
| EJoin : event e

type trace 'e = list (event 'e)

let filter_out_join (t:trace 'e) : trace 'e =
  filter (fun ev -> not (EJoin? ev)) t
  
let rec split_trace_join (t:trace 'e) acc : Tot ((trace 'e) * (trace 'e)) (decreases t) =
  match t with
  | [] -> (acc, [])
  | EJoin :: tl -> (acc, t)
  | ev :: tl -> split_trace_join tl (acc@[ev])

let interleave_traces (t1:trace 'e) (t2:trace 'e) : list (trace 'e) =
  let t1 = filter_out_join t1 in
  match t1, t2 with
  | [], [] -> []
  | _, [] -> [t1]
  | [], _ -> [t2]
  | _, _ -> 
      let (t2', t2'') = split_trace_join t2 [] in
      map (fun t -> t@t2'') (interleave t1 t2')

let _ =
  assert (interleave_traces [Ev 1;Ev 2] [Ev 3;EJoin;Ev 4] == [ [Ev 1;Ev 2;Ev 3;EJoin;Ev 4]; [Ev 1;Ev 3;Ev 2;EJoin; Ev 4]; [Ev 3;Ev 1;Ev 2;EJoin;Ev 4] ]);
  assert (interleave_traces [EJoin;Ev 1;Ev 2] [Ev 3] == [ [Ev 1;Ev 2;Ev 3]; [Ev 1;Ev 3;Ev 2;]; [Ev 3;Ev 1;Ev 2] ]);
  assert (interleave_traces [Ev 0] [Ev 1;Ev 2] == [ [Ev 0;Ev 1;Ev 2]; [Ev 1;Ev 0;Ev 2]; [Ev 1;Ev 2;Ev 0] ])

let reduce_interleave (l:list (list (trace 'e))) : list (trace 'e) = fold_left (product_map interleave_traces) [] l

let _ =
  assert (reduce_interleave ([[[Ev 2]]]) == [ [Ev 2] ]);
  assert (reduce_interleave ([[[]];[[Ev 2]]]) == [ [Ev 2] ])

(** The tree is traversed Deep First and post-order **)
let rec as_traces (t:runtree (event 'e)) : list (trace 'e) =
  match t with
  | Leaf -> []
  | Node lt k1 k2 -> 
    let trs = reduce_interleave [as_traces k1; as_traces k2] in
    if List.length trs > 0 then map (append lt) trs
    else [lt]

// let _ = assert (as_traces #int (Node [] Leaf Leaf) == as_traces Leaf) by (compute (); dump "H")

let as_simpl_traces (t:runtree (event 'e)) : list (list 'e) =
  map (map (fun (x:event 'e) -> match x with | Ev ev -> ev | EJoin -> admit ()))
    (map (fun (t1:trace 'e) -> filter_out_join t1) (as_traces t))

let _ = 
  assert (map (as_traces) [
             Node [ ] Leaf Leaf;
             Node [Ev 2] Leaf Leaf] === [[[]];[[Ev 2]]])
let _ = 
  assert (map (as_traces) [
             Leaf; 
             Node [Ev 2] Leaf Leaf] == [[]; [[Ev 2]]]) 

let _ =
  assert (
         as_traces (
           Node [Ev 1] (Node [ ] Leaf Leaf) (Node [Ev 2] Leaf Leaf))
          === [ [Ev 1;Ev 2] ])

let _ =
  assert (
         as_traces (
           Node [Ev 1] Leaf (Node [Ev 2] Leaf Leaf))
          === [ [Ev 1;Ev 2] ])

let _ = 
  assert (
         as_traces (Node [Ev 1]
            (Node [Ev 0] Leaf Leaf)
            (Node [Ev 2] Leaf Leaf))
          === [ [Ev 1;Ev 0;Ev 2]; [Ev 1;Ev 2;Ev 0] ]) by (compute ())

let _ = 
  assert (
         as_traces (Node [Ev 1]
            (Node [Ev 2;Ev 3] Leaf Leaf)
            (Node [Ev 4;EJoin;Ev 5] Leaf Leaf))
          == [
      [Ev 1; Ev 2; Ev 3; Ev 4; EJoin; Ev 5];
      [Ev 1; Ev 2; Ev 4; Ev 3; EJoin; Ev 5];
      [Ev 1; Ev 4; Ev 2; Ev 3; EJoin; Ev 5]
    ]) by (compute ())

let _ =
  assert (
         as_traces (Node []
            (Node [Ev 0] Leaf Leaf)
            (Node [Ev 1] 
               Leaf
               (Node [Ev 2] Leaf Leaf)))
          === [ [Ev 1;Ev 0;Ev 2]; [Ev 1;Ev 2;Ev 0]; [Ev 0;Ev 1;Ev 2] ]) by (compute ())

let _ = 
  assert (
      as_simpl_traces (
        Node []
          (Node [Ev 0] (Node [Ev 1] Leaf Leaf) (Node [Ev 2] Leaf Leaf))
          (Node [Ev 5; Ev 6] Leaf Leaf)) === [
      [5; 6; 0; 2; 1]; [5; 0; 6; 2; 1]; [5; 0; 2; 6; 1]; [5; 0; 2; 1; 6]; [0; 5; 6; 2; 1];
      [0; 5; 2; 6; 1]; [0; 5; 2; 1; 6]; [0; 2; 5; 6; 1]; [0; 2; 5; 1; 6]; [0; 2; 1; 5; 6];
      [5; 6; 0; 1; 2]; [5; 0; 6; 1; 2]; [5; 0; 1; 6; 2]; [5; 0; 1; 2; 6]; [0; 5; 6; 1; 2];
      [0; 5; 1; 6; 2]; [0; 5; 1; 2; 6]; [0; 1; 5; 6; 2]; [0; 1; 5; 2; 6]; [0; 1; 2; 5; 6]]) by (compute ())

