module Event_Structure

open FStar.Tactics
open FStar.List.Tot.Base

type id_typ = nat

type elem (a:Type) =
| El : id:id_typ -> v:a -> elem a

let id = El?.id 
let v = El?.v

let make_el (id:id_typ) (v:'a) = El id v

(** We need a set that allows the same value to appear multiple times and that allows
    us to distingusih between the appearances.
    
    To do that, we box the values into a constructor that associates to each value
    an id.

    The ids given to the elements are internal to the state, however to be able to do
    unions and avoid quantifiers, I made the sets parametric. 
**)

type base_set a = elem a -> Type0
let (∈) (#a:Type) (el:elem a) (s:base_set a) = s el
let (∉) (#a:Type) (el:elem a) (s:base_set a) = ~(el ∈ s)

type set0 a (n:nat) = ofst:nat{ofst >= n} -> base_set a
type set a (n:nat) = s:(set0 a n){
  (forall ofst x. x ∈ s ofst ==> (ofst-n) < id x /\ id x <= ofst) /\
  // (forall ofst i. (ofst-n) < i /\ i <= ofst ==> (exists x. id x == i /\ x ∈ s ofst)) /\
  (forall ofst x y. x ∈ s ofst /\ y ∈ s ofst /\ x =!= y ==> id x =!= id y)
//  (forall ofst x y. x ∈ s ofst /\ y ∈ s ofst /\ id x == id y ==> x == y)
}

let empty_set_lemma (s:set 'a 0) : Lemma (forall ofst x. x ∉ s ofst) = ()

let empty_set (#a:Type) : set a 0 = fun _ _ -> False

let eq_set (s1:set 'a 'n) (s2:set 'a 'm) : Type0 =
  'n == 'm /\ (forall ofst x. s1 ofst x <==> s2 ofst x)

let return_set (#a:Type) (x:a) : set a 1 = fun ofst y -> make_el ofst x == y

let add_set (#a:Type) (#n:nat) (s0:set a n) (x:a) : set a (n+1) =
  fun (ofst:nat{ofst >= n+1}) y -> make_el ofst x == y \/ y ∈ s0 (ofst-1)
let (⊕) #a #n = add_set #a #n




let __test_set1 : set int 4 = (((return_set 1) ⊕ 2) ⊕ 2) ⊕ 4
let _ = assert (make_el 2 2 ∈ __test_set1 4 /\ make_el 3 2 ∈ __test_set1 4)

[@expect_failure]
let _ = assert (make_el 4 2 ∈ __test_set1 4)
[@expect_failure]
let _ = assert (make_el 1 2 ∈ __test_set1 4)
let _ = assert (make_el 1 2 ∉ __test_set1 4)

let __test_mem (s0:nat{s0 >= 4}) =
  assert (exists (id1 id2:id_typ). make_el id1 2 ∈ __test_set1 s0 /\ id1 <= id2 /\  El id2 2 ∈ __test_set1 s0)

let _ = assert (exists (id1 id2:id_typ). id1 <= id2 /\ 
                      make_el id1 1 ∈ __test_set1 4 /\
                      make_el (id1+1) 2 ∈ __test_set1 4 /\
                      make_el id2 2 ∈ __test_set1 4 /\
                      make_el (id2+1) 4 ∈ __test_set1 4)

let union_set (#a:Type) (#n #m:nat) (s0:set a n) (s1:set a m) : set a (n+m) =
  fun (ofst:nat{ofst >= n+m}) x -> x ∈ s0 (ofst-m) \/ x ∈ s1 ofst

let subset_set (#a:Type) (#n #m:nat) (s0:set a n) (s1:set a m) : Type0 =
  n <= m ==> (forall x (ofst:nat{ofst >= m}). x ∈ s0 ofst ==> x ∈ s1 ofst)
let (⊆) #a #n #m = subset_set #a #n #m

let _ = assert (__test_set1 `subset_set` __test_set1)
let __test_set2 = __test_set1 `union_set` __test_set1
let _ = assert (__test_set1 `subset_set` __test_set2)
let _ = assert (forall id v. make_el id v ∈ __test_set1 4 <==>
                      make_el id v ∈ __test_set2 8 /\ El (id+4) v ∈ __test_set2 8)

type relation a = elem a -> elem a -> Type0

(** non-strict partial order **)
type partial_order (#a:Type) (#n:nat) (s:set a n) = ofst:nat{ofst >= n} -> rel:(relation a){
  (forall x. x ∈ s ofst ==> x `rel` x) /\
  (forall x y z. x ∈ s ofst /\ y ∈ s ofst /\ z ∈ s ofst ==> (x `rel` y /\ y `rel` z ==> x `rel` z)) /\
  (forall x y. x ∈ s ofst /\ y ∈ s ofst ==> (x `rel` y /\ y `rel` x ==> x == y))
}

let empty_partial_order (#a:Type) (#n:nat) (s:set a n) : partial_order s =
  fun ofst x y -> x ∈ s ofst /\ x == y

let extend_partial_order
  (#a:Type)
  (#n:nat)
  (#s:set a n)
  (po:partial_order s)
  (ev1:(ofst:nat{ofst >= n} -> elem a){forall ofst. ev1 ofst ∈ s ofst})
  (ev2:(ofst:nat{ofst >= n} -> elem a){forall ofst. ev2 ofst ∈ s ofst})
  : partial_order s =
  fun ofst ev1' ev2' -> ev1' ∈ s ofst /\ ev2' ∈ s ofst /\ 
    (((ev2 ofst `po ofst` ev1 ofst ==> ev1 ofst == ev2 ofst) /\ (ev1' `po ofst` ev1 ofst /\ ev2 ofst `po ofst` ev2')) \/ (ev1' `po ofst` ev2'))

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
  & bot:option (ofst:nat{ofst >= n} -> elem a){(None? bot <==> n == 0)
    /\ (Some? bot ==> (forall ofst. Some?.v bot ofst ∈ s ofst /\ (forall x. x ∈ s ofst ==> Some?.v bot ofst `po ofst` x)))}
  & top_r:option (ofst:nat{ofst >= n} -> elem a){(None? top_r <==> n == 0) /\
    (Some? top_r ==> (forall ofst. Some?.v top_r ofst ∈ s ofst /\ (forall x. x ∈ s ofst /\ x =!= Some?.v top_r ofst ==> ~(Some?.v top_r ofst `po ofst` x))))}

let empty_poset (#a:Type) : poset a 0 = (| empty_set, empty_partial_order empty_set, None, None |)

let return_poset (el:'e) : poset 'e 1 =
  let s = return_set el in
  (| s, empty_partial_order s, Some (fun ofst -> make_el ofst el), Some (fun ofst -> El ofst el) |)


let new_po0
  (#n #m:nat)
  (#s1:set 'e n)
  (po1:partial_order s1)
  (#s2:set 'e m)
  (po2:partial_order s2)
  (top_r1 : (ofst:nat{ofst >= n}) -> elem 'e)
  (ofst:nat{ofst >= n + m})
  : relation 'e = (fun x y ->
  (x ∈ s1 (ofst-m) /\ y ∈ s1 (ofst-m) /\ x `po1 (ofst-m)` y) \/
  (x ∈ s2 ofst /\ y ∈ s2 ofst /\ x `po2 ofst` y) \/
  (x ∈ s1 (ofst-m) /\ y ∈ s2 ofst /\ x `po1 (ofst-m)` (top_r1 (ofst-m))))

let new_po
  (#n #m:nat)
  (#s1:set 'e n)
  (po1:partial_order s1)
  (#s2:set 'e m)
  (po2:partial_order s2)
  (top_r1 : (ofst:nat{ofst >= n}) -> elem 'e) :
  partial_order (s1 `union_set` s2) =
  fun ofst -> 
    let rel = new_po0 po1 po2 top_r1 ofst in
    let s = s1 `union_set` s2 in
    assert (forall x. x ∈ s ofst ==> x `rel` x);
    assume (forall x y z. x ∈ s ofst /\ y ∈ s ofst /\ z ∈ s ofst ==> (x `rel` y /\ y `rel` z ==> x `rel` z));
    assert (forall x y. x ∈ s ofst /\ y ∈ s ofst ==> (x `rel` y /\ y `rel` x ==> x == y));
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
    let bot = Some (fun (ofst:nat{ofst >= n+m}) -> Some?.v bot1 (ofst-m)) in
    let top = Some (fun (ofst:nat{ofst >= n+m}) -> Some?.v top_r2 ofst) in
    (| s1 `union_set` s2, po, bot , top |)
  end

let subset_poset (#n #m:nat) (pos1:poset 'e n) (pos2:poset 'e m) : Type0 =
  let (| s1, po1, bot1, top_r1 |) = pos1 in
  let (| s2, po2, bot2, top_r2 |) = pos2 in
  s1 `subset_set` s2 /\
  (forall ofst x y. x ∈ s1 ofst /\ y ∈ s1 ofst /\ x `po1 ofst` y ==> x `po2 ofst` y)
  
type trace 'e = list 'e
  
type marked = id_typ -> Type0

let empty_marked : marked = fun _ -> False

let mark (m:marked) (v:id_typ) : marked = fun v' -> v == v' \/ m v'

let rec test_membership0 (t:trace int) (#n:nat) (p:poset int n) (el_prev:elem int) (marked_ids:marked) : Type0 =
  let (| s, po, bot, top |) = p in
  match t with
  | [] -> True
  | h :: tl -> exists id_h. ~(marked_ids id_h) /\ 
                      (make_el id_h h ∈ s n) /\
                      ((el_prev `po n` make_el id_h h) \/ ~(El id_h h `po n` el_prev)) /\
                      test_membership0 tl p (make_el id_h h) (mark marked_ids id_h)

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
    (extend_partial_order (empty_partial_order __test_set) (fun id -> make_el (id-2) 1) (fun id -> El (id-1) 2))
    (fun id -> make_el (id-2) 1) (fun id -> El id 3)

let __test_poset : poset int 3 =
  (| __test_set, __test_po, Some (fun (ofst:nat{ofst >= 3}) -> make_el (ofst-2) 1), Some (fun id -> El id 3) |)

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
        (extend_partial_order (empty_partial_order __test_set3) (fun id -> make_el (id-3) 1) (fun id -> El (id-2) 2))
        (fun id -> make_el (id-3) 1) (fun id -> El (id-1) 3))
      (fun id -> make_el (id-1) 3) (fun id -> El id 4))
    (fun id -> make_el (id-2) 2) (fun id -> El id 4)

#set-options "--z3rlimit 12"
let __test_poset3 : poset int 4 =
  (| __test_set3, __test_po3, Some (fun (ofst:nat{ofst >= 4}) -> make_el (ofst-3) 1), Some (fun id -> El id 4) |)

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
  (| s, empty_partial_order s, Some (fun ofst -> make_el ofst (Some (th_id, e))), Some (fun ofst -> El ofst (Some (th_id, e))) |)


(**
     bot ofst                               make_el (ofst-1) None        (new bot) 
      |             async                   /        \
      |          ---------->               /          \
      |                                   v           v
      v                              bot (ofst-2)   make_el ofst None    (new top)
     top_r ofst                            |
                                          |
                                          v
                                    top_r (ofst-2)
**)

let async (#n:nat) (p:poset (event_typ 'e) n) : poset (event_typ 'e) (n+2) = 
  let (| s, po, bot, top_r |) = p in
  let s' = (s ⊕ None) ⊕ None in
  assert (forall ofst. make_el ofst None ∈ s' ofst /\ El (ofst-1) None ∈ s' ofst);
  let po : partial_order s' = (fun ofst x y -> (x == make_el (ofst-1) None /\ y ∈ s' ofst) \/
                                            (x == make_el ofst None /\ y == El ofst None) \/
                                            (x ∈ s (ofst-2) /\ y ∈ s (ofst-2) /\ x `po (ofst-2)` y)) in
  (| s', po, Some (fun (ofst:nat{ofst >= n+2}) -> make_el (ofst-1) None), Some (fun ofst -> El ofst None) |)

(** CA: Not very principled since the po is defined over xs and ys which are not part of S **)
let await (#e:Type) (th_id:nat) : poset (event_typ e) 1 =
  let s : set (event_typ e) 1 = return_set None in
  let po : partial_order s = (fun ofst x y -> (x ∈ s ofst /\ y ∈ s ofst) \/ (y == make_el ofst None /\ Some? (v x) /\ fst (Some?.v (v x)) == th_id)) in
  (| s, po, Some (fun ofst -> make_el ofst None), Some (fun ofst -> El ofst None) |)

let rec membership0 (t:trace 'e) (#n:nat) (p:poset (event_typ 'e) n) (el_prev:elem (event_typ 'e)) (marked_ids:marked) : Type0 =
  let (| s, po, bot, top |) = p in
  match t with
  | [] -> True
  | ev :: tl -> exists id_ev id_th. 
                      ~(marked_ids id_ev) /\ 
                      (let el = make_el id_ev (Some (id_th, ev)) in
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
  assert (Some? bot /\ Some?.v bot 3 == make_el 2 None);
  assert (Some? top_r /\ Some?.v top_r 3 == make_el 3 None);
  assert (make_el 1 (Some (2,2)) ∈ s 3);
  assert (make_el 2 None ∈ s 3);
  assert (make_el 3 None ∈ s 3)

let prog01 () : poset (event_typ int) 4 = op 1 1 `append_poset` async (op 2 2)

let __test_prog01 () = 
  let (| s, po, bot, top_r |) = prog01 () in
  assert (Some? bot /\ Some?.v bot 4 == make_el 1 (Some (1,1)));
  assert (Some? top_r /\ Some?.v top_r 4 == make_el 4 None);
  assert (make_el 1 (Some (1,1)) ∈ s 4);
  assert (make_el 2 (Some (2,2)) ∈ s 4);
  assert (make_el 3 None ∈ s 4);
  assert (make_el 4 None ∈ s 4)

let prog02 () : poset (event_typ int) 4 = async (op 2 2) `append_poset` op 1 1

let __test_prog02 () = 
  let (| s, po, bot, top_r |) = prog02 () in
  assert (Some? bot /\ Some?.v bot 4 == make_el 2 None);
  assert (Some? top_r /\ Some?.v top_r 4 == make_el 4 (Some (1,1)));
  assert (make_el 1 (Some (2,2)) ∈ s 4);
  assert (make_el 2 None ∈ s 4);
  assert (make_el 3 None ∈ s 4);
  assert (make_el 4 (Some (1,1)) ∈ s 4)

let prog03 () : poset (event_typ int) 5 = (async (op 2 2) `append_poset` op 1 1) `append_poset` op 3 1

let __test_prog03 () = 
  let (| s, po, bot, top_r |) = prog03 () in
  assert (Some? bot /\ Some?.v bot 5 == make_el 2 None);
  assert (Some? top_r /\ Some?.v top_r 5 == make_el 5 (Some (1,3)));
  assert (make_el 1 (Some (2,2)) ∈ s 5);
  assert (make_el 2 None ∈ s 5);
  assert (make_el 3 None ∈ s 5);
  assert (make_el 4 (Some (1,1)) ∈ s 5);
  assert (make_el 5 (Some (1,3)) ∈ s 5)

let prog04 () : poset (event_typ int) 5 = (op 1 1 `append_poset` async (op 2 2)) `append_poset` op 3 1

let __test_prog04 () = 
  let (| s, po, bot, top_r |) = prog04 () in
  assert (Some? bot /\ Some?.v bot 5 == make_el 1 (Some (1,1)));
  assert (Some? top_r /\ Some?.v top_r 5 == make_el 5 (Some (1,3)));
  assert (make_el 1 (Some (1,1)) ∈ s 5);
  assert (make_el 2 (Some (2,2)) ∈ s 5);
  assert (make_el 3 None ∈ s 5);
  assert (make_el 4 None ∈ s 5);
  assert (make_el 5 (Some (1,3)) ∈ s 5)
  
let prog05 () : poset (event_typ int) 4 = async (op 2 2) `append_poset` await 2

let __test_prog05 () = 
  let (| s, po, bot, top_r |) = prog05 () in
  assert (Some? bot /\ Some?.v bot 4 == make_el 2 None);
  assert (Some? top_r /\ Some?.v top_r 4 == make_el 4 None);
  assert (make_el 1 (Some (2,2)) ∈ s 4);
  assert (make_el 2 None ∈ s 4);
  assert (make_el 3 None ∈ s 4);
  assert (make_el 4 None ∈ s 4)

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
  assert (Some? bot /\ Some?.v bot 7 == make_el 1 (Some (1,1)));
  assert (Some? top_r /\ Some?.v top_r 7 == make_el 7 (Some (1,4)));
  assert (make_el 1 (Some (1,1)) ∈ s 7);
  assert (make_el 5 (Some (1,3)) ∈ s 7);
  assert (make_el 6 None ∈ s 7);
  assert (make_el 7 (Some (1,4)) ∈ s 7)

#set-options "--z3rlimit 64"
let __test_prog1'' () = 
  let (| s, po, bot, top_r |) = (((op 1 1 `append_poset` async (op 2 2)) `append_poset` (op 3 1)) `append_poset` await 2) `append_poset` op 4 1 in
  assert (Some? bot /\ Some?.v bot 7 == make_el 1 (Some (1,1)));
  assert (Some? top_r /\ Some?.v top_r 7 == make_el 7 (Some (1,4)));
  assert (make_el 2 (Some (2,2)) ∈ s 7);
  assert (make_el 3 None ∈ s 7);
  assert (make_el 4 None ∈ s 7)

let _ = assert ([1;4] `membership` prog1 ()) 
  
let _ = assert (~([4;1] `membership` prog1 ()))

#set-options "--z3rlimit 64"
let _ = assert ([1;2;3;4] `membership` prog1 ())

let _ = assert ([1;3;2;4] `membership` prog1 ())

let _ = assert ([1;3;4;2] `membership` prog1 ()) 
