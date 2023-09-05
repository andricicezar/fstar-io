module Event_Structure

open FStar.Tactics
open FStar.List.Tot.Base

(**
[@"opaque_to_smt"]
type element a = nat * a

[@"opaque_to_smt"]
type set a = list a

[@"opaque_to_smt"]
let set_mem (#a: Type) (x: (element a)) (s: set a) : Type0 =
  reveal_opaque (`%element) element;
  reveal_opaque (`%set) set;
  let (pos, x) = x in
  match nth s pos with
  | Some x' -> x == x'
  | None -> False
let (∈) = set_mem
let (∉) x s = ~(x ∈ s)

let set_subset (#a:Type) (s0:set a) (s1:set a) : Type0 =
  forall x. x ∈ s0 ==> x ∈ s1 
let (⊆) = set_subset

[@"opaque_to_smt"]
let set_add_fresh_element (#a:Type) (x:a) (s0:set a) : Pure (set a * element a)
  (requires True)
  (ensures (fun (s1, x) -> s0 ⊆ s1 /\ x ∈ s1)) =
  reveal_opaque (`%set) set;
  reveal_opaque (`%set_mem) (set_mem #a);
  let x' : element a = (length s0, x) in
  let s1 = s0@[x] in
  assume (forall x. x ∈ s0 ==> x ∈ s1);
  assume (nth s1 (length s0) == Some x);
  (s1, x')
let (⊕) = set_add_fresh_element

[@"opaque_to_smt"]
let empty_set (#a:Type) : (s0:(set a){forall x. x ∉ s0}) = 
  reveal_opaque (`%set) set;
  reveal_opaque (`%set_mem) (set_mem #a);
  let s0 = [] in
  assert (forall x. x ∉ s0) by (compute ());
  s0

let rec add_list_to_set (s0:set 'a) (xs:list 'a) : Tot (set 'a) (decreases xs) =
  match xs with
  | [] -> s0
  | x :: tl -> let (s1, _) = (x ⊕ s0) in
              add_list_to_set s1 tl
**)

type id_typ = nat // this should be > 0


type elem (a:Type) =
| El : id:id_typ -> v:a -> elem a

let id = El?.id 
let v = El?.v


(** We need a set that allows the same value to appear more than once and that allows
    us to distingusih between the appearances.
    
    To do that, we box the values into a constructor that associates to each value
    an id.

    The ids given to the elements are internal to the state, however to be able to do
    unions and avoid quantifiers, I made the sets parametric. 
**)

type base_set a = elem a -> Type0
let (∈) (#a:Type) (el:elem a) (s:base_set a) = s el
let (∉) (#a:Type) (el:elem a) (s:base_set a) = ~(el ∈ s)

type set0 a (n:nat) = st0:nat{st0 >= n} -> base_set a
type set a (n:nat) = s:(set0 a n){
  (forall st0 x. x ∈ s st0 ==> (st0-n) < id x /\ id x <= st0) /\
  // (forall st0 i. (st0-n) < i /\ i <= st0 ==> (exists x. id x == i /\ x ∈ s st0)) /\
  (forall st0 x y. x ∈ s st0 /\ y ∈ s st0 /\ x =!= y ==> id x =!= id y)
//  (forall st0 x y. x ∈ s st0 /\ y ∈ s st0 /\ id x == id y ==> x == y)
}

let empty_set_lemma (s:set 'a 0) : Lemma (forall st0 x. x ∉ s st0) = ()

let empty_set (#a:Type) : set a 0 = fun _ _ -> False

let eq_set (s1:set 'a 'n) (s2:set 'a 'm) : Type0 =
  'n == 'm /\ (forall st0 x. s1 st0 x <==> s2 st0 x)

let return_set (#a:Type) (x:a) : set a 1 = fun st0 y -> El st0 x == y

let add_set (#a:Type) (#n:nat) (s0:set a n) (x:a) : set a (n+1) =
  fun (st0:nat{st0 >= n+1}) y -> El st0 x == y \/ y ∈ s0 (st0-1)
let (⊕) #a #n = add_set #a #n




let __test_set1 : set int 4 = (((return_set 1) ⊕ 2) ⊕ 2) ⊕ 4
let _ = assert (El 2 2 ∈ __test_set1 4 /\ El 3 2 ∈ __test_set1 4)

[@expect_failure]
let _ = assert (El 4 2 ∈ __test_set1 4)
[@expect_failure]
let _ = assert (El 1 2 ∈ __test_set1 4)
let _ = assert (El 1 2 ∉ __test_set1 4)

let __test_mem (s0:nat{s0 >= 4}) =
  assert (exists (id1 id2:id_typ). El id1 2 ∈ __test_set1 s0 /\ id1 <= id2 /\  El id2 2 ∈ __test_set1 s0)

let _ = assert (exists (id1 id2:id_typ). id1 <= id2 /\ 
                      El id1 1 ∈ __test_set1 4 /\
                      El (id1+1) 2 ∈ __test_set1 4 /\
                      El id2 2 ∈ __test_set1 4 /\
                      El (id2+1) 4 ∈ __test_set1 4)

let union_set (#a:Type) (#n #m:nat) (s0:set a n) (s1:set a m) : set a (n+m) =
  fun (st0:nat{st0 >= n+m}) x -> x ∈ s0 (st0-m) \/ x ∈ s1 st0

let subset_set (#a:Type) (#n #m:nat) (s0:set a n) (s1:set a m) : Type0 =
  n <= m ==> (forall x (st0:nat{st0 >= m}). x ∈ s0 st0 ==> x ∈ s1 st0)
let (⊆) #a #n #m = subset_set #a #n #m

let _ = assert (__test_set1 `subset_set` __test_set1)
let __test_set2 = __test_set1 `union_set` __test_set1
let _ = assert (__test_set1 `subset_set` __test_set2)
let _ = assert (forall id v. El id v ∈ __test_set1 4 <==>
                      El id v ∈ __test_set2 8 /\ El (id+4) v ∈ __test_set2 8)

type relation a = elem a -> elem a -> Type0

(** non-strict partial order **)
type partial_order (#a:Type) (#n:nat) (s:set a n) = st0:nat{st0 >= n} -> rel:(relation a){
  (forall x. x ∈ s st0 ==> x `rel` x) /\
  (forall x y z. x ∈ s st0 /\ y ∈ s st0 /\ z ∈ s st0 ==> (x `rel` y /\ y `rel` z ==> x `rel` z)) /\
  (forall x y. x ∈ s st0 /\ y ∈ s st0 ==> (x `rel` y /\ y `rel` x ==> x == y))
}

let empty_partial_order (#a:Type) (#n:nat) (s:set a n) : partial_order s =
  fun st0 x y -> x ∈ s st0 /\ x == y

let extend_partial_order
  (#a:Type)
  (#n:nat)
  (#s:set a n)
  (po:partial_order s)
  (ev1:(st0:nat{st0 >= n} -> elem a){forall st0. ev1 st0 ∈ s st0})
  (ev2:(st0:nat{st0 >= n} -> elem a){forall st0. ev2 st0 ∈ s st0})
  : partial_order s =
  fun st0 ev1' ev2' -> ev1' ∈ s st0 /\ ev2' ∈ s st0 /\ 
    (((ev2 st0 `po st0` ev1 st0 ==> ev1 st0 == ev2 st0) /\ (ev1' `po st0` ev1 st0 /\ ev2 st0 `po st0` ev2')) \/ (ev1' `po st0` ev2'))

(**
type partial_order (e:Type) = rel:(relation e) {
  (forall x. x `rel` x) /\
  (forall x y z. (x `rel` y /\ y `rel` z ==> x `rel` z)) /\
  (forall x y. (x `rel` y /\ y `rel` x ==> x == y))

let empty_partial_order (#a:Type) : partial_order a =
  fun x y -> x == y

let extend_partial_order ((<=):partial_order 'e) (ev1:(elem 'e)) (ev2:(elem 'e)) : partial_order 'e =
  fun ev1' ev2' -> ((ev2 <= ev1 ==> ev1 == ev2) /\ (ev1' <= ev1 /\ ev2 <= ev2')) \/ (ev1' <= ev2')
}**)

  (**
let bottom (po:partial_order 'e) : Type0 =
  exists bot. forall ev. bot `po` ev 

let union_partial_order (po1:partial_order 'e) (po2:partial_order 'e) : partial_order 'e =
  fun ev1 ev2 -> ev1 `po1` ev2 \/ ev1 `po2` ev2 \/ ((e1 `po1` e1) /\ (exists bot. (forall ev. bot `po2` ev) ==> bot `po2` e2))
**)

type poset (a:Type) (n:nat) =
  s:set a n
  & po:partial_order s
  & bot:option (st0:nat{st0 >= n} -> elem a){(None? bot <==> n == 0)
    /\ (Some? bot ==> (forall st0. Some?.v bot st0 ∈ s st0 /\ (forall x. x ∈ s st0 ==> Some?.v bot st0 `po st0` x)))}
  & top_r:option (st0:nat{st0 >= n} -> elem a){(None? top_r <==> n == 0) /\
    (Some? top_r ==> (forall st0. Some?.v top_r st0 ∈ s st0 /\ (forall x. x ∈ s st0 /\ x =!= Some?.v top_r st0 ==> ~(Some?.v top_r st0 `po st0` x))))}

let empty_poset (#a:Type) : poset a 0 = (| empty_set, empty_partial_order empty_set, None, None |)

let return_poset (el:'e) : poset 'e 1 =
  let s = return_set el in
  (| s, empty_partial_order s, Some (fun st0 -> El st0 el), Some (fun st0 -> El st0 el) |)


let new_po0
  (#n #m:nat)
  (#s1:set 'e n)
  (po1:partial_order s1)
  (#s2:set 'e m)
  (po2:partial_order s2)
  (top_r1 : (st0:nat{st0 >= n}) -> elem 'e)
  (st0:nat{st0 >= n + m})
  : relation 'e = (fun x y ->
  (x ∈ s1 (st0-m) /\ y ∈ s1 (st0-m) /\ x `po1 (st0-m)` y) \/
  (x ∈ s2 st0 /\ y ∈ s2 st0 /\ x `po2 st0` y) \/
  (x ∈ s1 (st0-m) /\ y ∈ s2 st0 /\ x `po1 (st0-m)` (top_r1 (st0-m))))

let new_po
  (#n #m:nat)
  (#s1:set 'e n)
  (po1:partial_order s1)
  (#s2:set 'e m)
  (po2:partial_order s2)
  (top_r1 : (st0:nat{st0 >= n}) -> elem 'e) :
  partial_order (s1 `union_set` s2) =
  fun st0 -> 
    let rel = new_po0 po1 po2 top_r1 st0 in
    let s = s1 `union_set` s2 in
    assert (forall x. x ∈ s st0 ==> x `rel` x);
    assume (forall x y z. x ∈ s st0 /\ y ∈ s st0 /\ z ∈ s st0 ==> (x `rel` y /\ y `rel` z ==> x `rel` z));
    assert (forall x y. x ∈ s st0 /\ y ∈ s st0 ==> (x `rel` y /\ y `rel` x ==> x == y));
    rel


let append_poset (#n #m:nat) (pos1:poset 'e n) (pos2:poset 'e m) : poset 'e (n+m) =
  let (| s1, po1, bot1, top_r1 |) = pos1 in
  let (| s2, po2, bot2, top_r2 |) = pos2 in
  match bot1, bot2 with
  | None, None
  | None, _ -> pos2
  | _, None -> pos1
  | _, _ -> begin
    let s = s1 `union_set` s2 in
    let po : partial_order s = new_po po1 po2 (Some?.v top_r1) in
    let bot = Some (fun (st0:nat{st0 >= n+m}) -> Some?.v bot1 (st0-m)) in
    let top = Some (fun (st0:nat{st0 >= n+m}) -> Some?.v top_r2 st0) in
    (| s1 `union_set` s2, po, bot , top |)
  end

let subset_poset (#n #m:nat) (pos1:poset 'e n) (pos2:poset 'e m) : Type0 =
  let (| s1, po1, bot1, top_r1 |) = pos1 in
  let (| s2, po2, bot2, top_r2 |) = pos2 in
  s1 `subset_set` s2 /\
  (forall st0 x y. x ∈ s1 st0 /\ y ∈ s1 st0 /\ x `po1 st0` y ==> x `po2 st0` y)
  
type trace 'e = list 'e
  
type marked = id_typ -> Type0

let empty_marked : marked = fun _ -> False

let mark (m:marked) (v:id_typ) : marked = fun v' -> v == v' \/ m v'

let rec test_membership0 (t:trace int) (#n:nat) (p:poset int n) (el_prev:elem int) (marked_ids:marked) : Type0 =
  let (| s, po, bot, top |) = p in
  match t with
  | [] -> True
  | h :: tl -> exists id_h. ~(marked_ids id_h) /\ 
                      (El id_h h ∈ s n) /\
                      ((el_prev `po n` El id_h h) \/ ~(El id_h h `po n` el_prev)) /\
                      test_membership0 tl p (El id_h h) (mark marked_ids id_h)

let test_membership (t:trace int) (#n:nat) (p:poset int n) : Type0 =
  let (| s, po, bot, top |) = p in
  match t with
  | [] -> n == 0
  | h :: tl -> Some? bot /\ (let b = Some?.v bot n in
               h == v b /\ test_membership0 tl p b (mark empty_marked (id b)))

(**  1
    | \
    2  3 **)
let __test_set : set int 3 = ((empty_set ⊕ 1) ⊕ 2) ⊕ 3
let __test_po : partial_order __test_set =
  extend_partial_order
    (extend_partial_order (empty_partial_order __test_set) (fun id -> El (id-2) 1) (fun id -> El (id-1) 2))
    (fun id -> El (id-2) 1) (fun id -> El id 3)

let __test_poset : poset int 3 =
  (| __test_set, __test_po, Some (fun (st0:nat{st0 >= 3}) -> El (st0-2) 1), Some (fun id -> El id 3) |)

let _ =
  assert ([1;2] `test_membership` __test_poset);
  assert ([1;3] `test_membership` __test_poset)

let _ =
  assert (~([2;1] `test_membership` __test_poset));
  assert (~([3;1] `test_membership` __test_poset))

let _ = assert ([1;2;3] `test_membership` __test_poset)

let _ = assert ([1;3;2] `test_membership` __test_poset)

let _ = assert (~([3;1;2] `test_membership` __test_poset))

(**  1
    | \
    2  3
     \ |
       4 **)
       
let __test_set3 : set int 4 = (((return_set 1) ⊕ 2) ⊕ 3) ⊕ 4
let __test_po3 : partial_order __test_set3 =
  extend_partial_order 
    (extend_partial_order
        (extend_partial_order
        (extend_partial_order (empty_partial_order __test_set3) (fun id -> El (id-3) 1) (fun id -> El (id-2) 2))
        (fun id -> El (id-3) 1) (fun id -> El (id-1) 3))
      (fun id -> El (id-1) 3) (fun id -> El id 4))
    (fun id -> El (id-2) 2) (fun id -> El id 4)

#set-options "--z3rlimit 12"
let __test_poset3 : poset int 4 =
  (| __test_set3, __test_po3, Some (fun (st0:nat{st0 >= 4}) -> El (st0-3) 1), Some (fun id -> El id 4) |)

let _ =
  assert ([1;2;3;4] `test_membership` __test_poset3)

let _ =
  assert ([1;3;2;4] `test_membership` __test_poset3)

let _ =
  assert ([1] `test_membership` __test_poset3);
  assert (~([5] `test_membership` __test_poset3));
  assert (~([1;5] `test_membership` __test_poset3))

let _ =
  assert (~([1;1] `test_membership` __test_poset3))

let _ =
  assert (~([1;4;3;2] `test_membership` __test_poset3))

type event_typ 'e = option (nat * 'e)

let op (e:'e) (th_id:nat) : poset (event_typ 'e) 1 =
  let s = return_set (Some (th_id, e)) in
  (| s, empty_partial_order s, Some (fun st0 -> El st0 (Some (th_id, e))), Some (fun st0 -> El st0 (Some (th_id, e))) |)


(**
     bot st0                               El (st0-1) None        (new bot) 
      |             async                   /        \
      |          ---------->               /          \
      |                                   v           v
      v                              bot (st0-2)   El st0 None    (new top)
     top_r st0                            |
                                          |
                                          v
                                    top_r (st0-2)
**)

let async (#n:nat) (p:poset (event_typ 'e) n) : poset (event_typ 'e) (n+2) = 
  let (| s, po, bot, top_r |) = p in
  let s' = (s ⊕ None) ⊕ None in
  assert (forall st0. El st0 None ∈ s' st0 /\ El (st0-1) None ∈ s' st0);
  let po : partial_order s' = (fun st0 x y -> (x == El (st0-1) None /\ y ∈ s' st0) \/
                                            (x == El st0 None /\ y == El st0 None) \/
                                            (x ∈ s (st0-2) /\ y ∈ s (st0-2) /\ x `po (st0-2)` y)) in
  (| s', po, Some (fun (st0:nat{st0 >= n+2}) -> El (st0-1) None), Some (fun st0 -> El st0 None) |)

(** CA: Not very principled since the po is defined over x and y which are not part of S **)
let await (#e:Type) (th_id:nat) : poset (event_typ e) 1 =
  let s : set (event_typ e) 1 = return_set None in
  let po : partial_order s = (fun st0 x y -> (x ∈ s st0 /\ y ∈ s st0) \/ (y == El st0 None /\ Some? (v x) /\ fst (Some?.v (v x)) == th_id)) in
  (| s, po, Some (fun st0 -> El st0 None), Some (fun st0 -> El st0 None) |)

let rec membership0 (t:trace 'e) (#n:nat) (p:poset (event_typ 'e) n) (el_prev:elem (event_typ 'e)) (marked_ids:marked) : Type0 =
  let (| s, po, bot, top |) = p in
  match t with
  | [] -> True
  | ev :: tl -> exists id_ev id_th. 
                      ~(marked_ids id_ev) /\ 
                      (let el = El id_ev (Some (id_th, ev)) in
                        (el ∈ s n) /\
                        ((el_prev `po n` el) \/ ~(el `po n` el_prev)) /\
                        membership0 tl p el (mark marked_ids id_ev))

let membership (t:trace 'e) (#n:nat) (p:poset (event_typ 'e) n) : Type0 =
  let (| s, po, bot, top |) = p in
  match t with
  | [] -> n == 0
  | h :: tl -> Some? bot /\ (let bot_el = Some?.v bot n in
              match v bot_el with
              | None -> membership0 t p bot_el (mark empty_marked (id bot_el))
              | Some b' -> h == snd b' /\ membership0 tl p bot_el (mark empty_marked (id bot_el)))

#reset-options

let prog0 () : poset (event_typ int) 3 = async (op 2 2)
let __test_prog0 () = 
  let (| s, po, bot, top_r |) = prog0 () in
  assert (Some? bot /\ Some?.v bot 3 == El 2 None);
  assert (Some? top_r /\ Some?.v top_r 3 == El 3 None);
  assert (El 1 (Some (2,2)) ∈ s 3);
  assert (El 2 None ∈ s 3);
  assert (El 3 None ∈ s 3)

let prog01 () : poset (event_typ int) 4 = op 1 1 `append_poset` async (op 2 2)

let __test_prog01 () = 
  let (| s, po, bot, top_r |) = prog01 () in
  assert (Some? bot /\ Some?.v bot 4 == El 1 (Some (1,1)));
  assert (Some? top_r /\ Some?.v top_r 4 == El 4 None);
  assert (El 1 (Some (1,1)) ∈ s 4);
  assert (El 2 (Some (2,2)) ∈ s 4);
  assert (El 3 None ∈ s 4);
  assert (El 4 None ∈ s 4)

let prog02 () : poset (event_typ int) 4 = async (op 2 2) `append_poset` op 1 1

let __test_prog02 () = 
  let (| s, po, bot, top_r |) = prog02 () in
  assert (Some? bot /\ Some?.v bot 4 == El 2 None);
  assert (Some? top_r /\ Some?.v top_r 4 == El 4 (Some (1,1)));
  assert (El 1 (Some (2,2)) ∈ s 4);
  assert (El 2 None ∈ s 4);
  assert (El 3 None ∈ s 4);
  assert (El 4 (Some (1,1)) ∈ s 4)

let prog03 () : poset (event_typ int) 5 = (async (op 2 2) `append_poset` op 1 1) `append_poset` op 3 1

let __test_prog03 () = 
  let (| s, po, bot, top_r |) = prog03 () in
  assert (Some? bot /\ Some?.v bot 5 == El 2 None);
  assert (Some? top_r /\ Some?.v top_r 5 == El 5 (Some (1,3)));
  assert (El 1 (Some (2,2)) ∈ s 5);
  assert (El 2 None ∈ s 5);
  assert (El 3 None ∈ s 5);
  assert (El 4 (Some (1,1)) ∈ s 5);
  assert (El 5 (Some (1,3)) ∈ s 5)

let prog04 () : poset (event_typ int) 5 = (op 1 1 `append_poset` async (op 2 2)) `append_poset` op 3 1

let __test_prog04 () = 
  let (| s, po, bot, top_r |) = prog04 () in
  assert (Some? bot /\ Some?.v bot 5 == El 1 (Some (1,1)));
  assert (Some? top_r /\ Some?.v top_r 5 == El 5 (Some (1,3)));
  assert (El 1 (Some (1,1)) ∈ s 5);
  assert (El 2 (Some (2,2)) ∈ s 5);
  assert (El 3 None ∈ s 5);
  assert (El 4 None ∈ s 5);
  assert (El 5 (Some (1,3)) ∈ s 5)
  
let prog05 () : poset (event_typ int) 4 = async (op 2 2) `append_poset` await 2

let __test_prog05 () = 
  let (| s, po, bot, top_r |) = prog05 () in
  assert (Some? bot /\ Some?.v bot 4 == El 2 None);
  assert (Some? top_r /\ Some?.v top_r 4 == El 4 None);
  assert (El 1 (Some (2,2)) ∈ s 4);
  assert (El 2 None ∈ s 4);
  assert (El 3 None ∈ s 4);
  assert (El 4 None ∈ s 4)

(** Test:
          (1,1)
            |
            *
           /  \
       (2,2)   *
         |     |
         |   (1,3)
           \   |
               *
               |
             (1,4)
**)

let prog1 () : poset (event_typ int) 7 = (((op 1 1 `append_poset` async (op 2 2)) `append_poset` (op 3 1)) `append_poset` await 2) `append_poset` op 4 1

let __test_prog1 () = 
  let (| s, po, bot, top_r |) = prog1 () in
  assert (Some? bot /\ Some?.v bot 7 == El 1 (Some (1,1)));
  assert (Some? top_r /\ Some?.v top_r 7 == El 7 (Some (1,4)));
  assert (El 1 (Some (1,1)) ∈ s 7);
  assert (El 5 (Some (1,3)) ∈ s 7);
  assert (El 6 None ∈ s 7);
  assert (El 7 (Some (1,4)) ∈ s 7)

#set-options "--z3rlimit 64"
let __test_prog1'' () = 
  let (| s, po, bot, top_r |) = (((op 1 1 `append_poset` async (op 2 2)) `append_poset` (op 3 1)) `append_poset` await 2) `append_poset` op 4 1 in
  assert (Some? bot /\ Some?.v bot 7 == El 1 (Some (1,1)));
  assert (Some? top_r /\ Some?.v top_r 7 == El 7 (Some (1,4)));
  assert (El 2 (Some (2,2)) ∈ s 7);
  assert (El 3 None ∈ s 7);
  assert (El 4 None ∈ s 7)

let _ = assert ([1;4] `membership` prog1 ()) 
  
let _ = assert (~([4;1] `membership` prog1 ()))

#set-options "--z3rlimit 64"
let _ = assert ([1;2;3;4] `membership` prog1 ())

let _ = assert ([1;3;2;4] `membership` prog1 ())

let _ = assert ([1;3;4;2] `membership` prog1 ()) 
