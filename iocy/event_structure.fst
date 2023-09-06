module Event_Structure

open FStar.Tactics
open FStar.List.Tot.Base

type id_typ = nat

type elem (a:Type) = id_typ * a
//| El : id:id_typ -> v:a -> elem a

let el_id (x:elem 'a) : id_typ = fst x
let el_v (x:elem 'a) : 'a = snd x

let make_el (id:id_typ) (v:'a) : elem 'a = (id, v)

(** We need a set that allows the same value to appear multiple times and that allows
    us to distingusih between the appearances.
    
    To do that, we box the values into a constructor that associates to each value
    an id.

    The ids given to the elements are internal to the state, however to be able to do
    unions and avoid quantifiers, I made the sets parametric into an offset (ofst) that
    is offseting the ids. So when setting the id of an element, the offset is used.

    However, the offset is "reversed".
**)

type base_set a = elem a -> Type0
let (∈) (#a:Type) (el:elem a) (s:base_set a) = s el
let (∉) (#a:Type) (el:elem a) (s:base_set a) = ~(el ∈ s)

type set0 a (n:nat) = ofst:nat{ofst >= n} -> base_set a
type set a (n:nat) = s:(set0 a n){
  (forall ofst x. x ∈ s ofst ==> (ofst-n) < el_id x /\ el_id x <= ofst) /\
  // (forall ofst i. (ofst-n) < i /\ i <= ofst ==> (exists x. id x == i /\ x ∈ s ofst)) /\
  (forall ofst x y. x ∈ s ofst /\ y ∈ s ofst /\ x =!= y ==> el_id x =!= el_id y)
//  (forall ofst x y. x ∈ s ofst /\ y ∈ s ofst /\ id x == id y ==> x == y)
}

let empty_set_lemma (s:set 'a 0) : Lemma (forall ofst x. x ∉ s ofst) = ()

let empty_set (#a:Type) : set a 0 = fun _ _ -> False

let eq_set (s1:set 'a 'n) (s2:set 'a 'm) : Type0 =
  'n == 'm /\ (forall ofst x. s1 ofst x <==> s2 ofst x)

let return_set (#a:Type) (x:a) : set a 1 = fun ofst y -> make_el ofst x == y

let add_set (#a:Type) (#n:nat) (s:set a n) (x:a) : set a (n+1) =
  fun (ofst:nat{ofst >= n+1}) y -> make_el ofst x == y \/ y ∈ s (ofst-1)
let (⊕) #a #n = add_set #a #n

(**
let lemma_mem_add (#a:Type) (x:a) (#n:nat) (s:set a n) (ofst:nat{ofst >= n+1}) :
  Lemma (make_el ofst x ∈ (s ⊕ x) ofst) [SMTPat (make_el ofst x ∈ (s ⊕ x) ofst)] = ()

let lemma_mem_add2 (#a:Type) (x:a) (#n:nat) (s:set a n) (ofst:nat{ofst >= n+2}) (y:a) :
  Lemma (make_el (ofst-1) x ∈ ((s ⊕ x) ⊕ y) ofst) [SMTPat (make_el (ofst-1) x ∈ ((s ⊕ x) ⊕ y) ofst)] = ()
**)

let __test_set1 : set int 4 = (((return_set 1) ⊕ 2) ⊕ 2) ⊕ 4
let _ = assert (make_el 2 2 ∈ __test_set1 4 /\ make_el 3 2 ∈ __test_set1 4)

[@expect_failure]
let _ = assert (make_el 4 2 ∈ __test_set1 4)
[@expect_failure]
let _ = assert (make_el 1 2 ∈ __test_set1 4)
let _ = assert (make_el 1 2 ∉ __test_set1 4)

let __test_mem (s0:nat{s0 >= 4}) =
  assert (exists (id1 id2:id_typ). make_el id1 2 ∈ __test_set1 s0 /\ id1 <= id2 /\ make_el id2 2 ∈ __test_set1 s0)

let _ = assert (exists (id1 id2:id_typ). id1 <= id2 /\ 
                      make_el id1 1 ∈ __test_set1 4 /\
                      make_el (id1+1) 2 ∈ __test_set1 4 /\
                      make_el id2 2 ∈ __test_set1 4 /\
                      make_el (id2+1) 4 ∈ __test_set1 4)

let union_set (#a:Type) (#n #m:nat) (s0:set a n) (s1:set a m) : set a (n+m) =
  fun (ofst:nat{ofst >= n+m}) x -> x ∈ s0 (ofst-m) \/ x ∈ s1 ofst

let lemma_mem_union_set_rhs (#a:Type) (x:a) (#n:nat) (s1:set a n) (#m:nat) (s2:set a m) (id:id_typ) (ofst:nat{ofst >= n+m}) :
  Lemma (requires (ofst-m < id))
        (ensures (make_el id x ∈ (s1 `union_set` s2) ofst) <==>
                 (make_el id x ∈ s2 ofst))
  [SMTPat (make_el id x ∈ (s1 `union_set` s2) ofst)] = ()
  
let lemma_mem_union_set_lhs (#a:Type) (x:a) (#n:nat) (s1:set a n) (#m:nat) (s2:set a m) (id:id_typ) (ofst:nat{ofst >= n+m}) :
  Lemma (requires (id <= ofst-m))
        (ensures (make_el id x ∈ (s1 `union_set` s2) ofst) <==> 
                (make_el id x ∈ s1 (ofst-m)))
  [SMTPat (make_el id x ∈ (s1 `union_set` s2) ofst)] = ()

let subset_set (#a:Type) (#n #m:nat) (s0:set a n) (s1:set a m) : Type0 =
  n <= m ==> (forall x (ofst:nat{ofst >= m}). x ∈ s0 ofst ==> x ∈ s1 ofst)
let (⊆) #a #n #m = subset_set #a #n #m

let _ = assert (__test_set1 `subset_set` __test_set1)
let __test_set2 = __test_set1 `union_set` __test_set1
let _ = assert (__test_set1 `subset_set` __test_set2)
let _ = assert (forall id v. make_el id v ∈ __test_set1 4 <==>
                      make_el id v ∈ __test_set2 8 /\ make_el (id+4) v ∈ __test_set2 8)

type relation a (n:nat) = ofst:nat{ofst >= n} -> elem a -> elem a -> Type0

let empty_rel (#a:Type) (#n:nat) (s:set a n) : relation a n =
  fun ofst x y -> x ∈ s ofst /\ x == y
  
let extend_rel
  (#a:Type)
  (#n:nat)
  (s:set a n)
  (po:relation a n)
  (ev1:(ofst:nat{ofst >= n} -> elem a){forall ofst. ev1 ofst ∈ s ofst})
  (ev2:(ofst:nat{ofst >= n} -> elem a){forall ofst. ev2 ofst ∈ s ofst})
  : relation a n =
  fun ofst ev1' ev2' -> ev1' ∈ s ofst /\ ev2' ∈ s ofst /\ 
    (((ev2 ofst `po ofst` ev1 ofst ==> ev1 ofst == ev2 ofst) /\ (ev1' `po ofst` ev1 ofst /\ ev2 ofst `po ofst` ev2')) \/ (ev1' `po ofst` ev2'))

type poset0 (a:Type) (n:nat) =
  set a n
  *
  relation a n
  *
  option (ofst:nat{ofst >= n} -> elem a)
  *
  option (ofst:nat{ofst >= n} -> elem a)

type poset (a:Type) (n:nat) =
  p:(poset0 a n){
    let (s, rel, bot, top_r) = p in
    (forall ofst x. x ∈ s ofst ==> x `rel ofst` x) /\
    (forall ofst x y z. x ∈ s ofst /\ y ∈ s ofst /\ z ∈ s ofst ==> (x `rel ofst` y /\ y `rel ofst` z ==> x `rel ofst` z)) /\
    (forall ofst x y. x ∈ s ofst /\ y ∈ s ofst ==> (x `rel ofst` y /\ y `rel ofst` x ==> x == y)) /\
    (None? bot <==> n == 0) /\
    (Some? bot ==> (forall ofst. Some?.v bot ofst ∈ s ofst /\ (forall x. x ∈ s ofst ==> Some?.v bot ofst `rel ofst` x))) /\
    (None? top_r <==> n == 0) /\
    (Some? top_r ==> (forall ofst. Some?.v top_r ofst ∈ s ofst /\ (forall x. x ∈ s ofst /\ x =!= Some?.v top_r ofst ==> ~(Some?.v top_r ofst `rel ofst` x))))
  }

let empty_poset (#a:Type) : poset a 0 = (empty_set, empty_rel empty_set, None, None)

let return_poset (el:'e) : poset 'e 1 =
  let s = return_set el in
  (s, empty_rel s, Some (fun ofst -> make_el ofst el), Some (fun ofst -> make_el ofst el))

let new_po
  (#n #m:nat)
  (s1:set 'e n)
  (rel1:relation 'e n)
  (s2:set 'e m)
  (rel2:relation 'e m)
  (top_r1 : (ofst:nat{ofst >= n}) -> elem 'e)
  : relation 'e (n+m) = (fun (ofst:nat{ofst >= n + m}) x y ->
  (x ∈ s1 (ofst-m) /\ y ∈ s1 (ofst-m) /\ x `rel1 (ofst-m)` y) \/
  (x ∈ s2 ofst /\ y ∈ s2 ofst /\ x `rel2 ofst` y) \/
  (x ∈ s1 (ofst-m) /\ y ∈ s2 ofst /\ x `rel1 (ofst-m)` (top_r1 (ofst-m))))

let append_poset (#n #m:nat) (pos1:poset 'e n) (pos2:poset 'e m) : poset 'e (n+m) =
  let (s1, rel1, bot1, top_r1)  = pos1 in
  let (s2, rel2, bot2, top_r2) = pos2 in
  match bot1, bot2 with
  | None, None
  | None, _ -> pos2
  | _, None -> pos1
  | _, _ -> begin
    let s = s1 `union_set` s2 in
    let rel : relation 'e (n+m) = new_po s1 rel1 s2 rel2 (Some?.v top_r1) in
    let bot = Some (fun (ofst:nat{ofst >= n+m}) -> Some?.v bot1 (ofst-m)) in
    let top = Some (fun (ofst:nat{ofst >= n+m}) -> Some?.v top_r2 ofst) in
    (s1 `union_set` s2, rel, bot , top)
  end

let mem_poset (#a:Type) (#n:nat) (ofst:nat{ofst >= n}) (el:elem a) (p:poset a n)  : Type0 =
  let (s, _, _, _) = p in el ∈ s ofst


let lemma_mem_poset_set_rhs (#a:Type) (x:a) (#n:nat) (p1:poset a n) (#m:nat) (p2:poset a m) (id:id_typ) (ofst:nat{ofst >= n+m}) :
  Lemma (requires (ofst-m < id))
        (ensures (make_el id x `mem_poset ofst` (p1 `append_poset` p2)) <==>
                 (make_el id x `mem_poset ofst` p2))
  [SMTPat (make_el id x `mem_poset ofst` (p1 `append_poset` p2))] = ()
  
let lemma_mem_poset_set_lhs (#a:Type) (x:a) (#n:nat) (p1:poset a n) (#m:nat) (p2:poset a m) (id:id_typ) (ofst:nat{ofst >= n+m}) :
  Lemma (requires (id <= ofst-m))
        (ensures (make_el id x `mem_poset ofst` (p1 `append_poset` p2)) <==> 
                 (make_el id x `mem_poset (ofst-m)` p1))
  [SMTPat (make_el id x `mem_poset ofst` (p1 `append_poset` p2))] = ()


let subset_poset (#n #m:nat) (pos1:poset 'e n) (pos2:poset 'e m) : Type0 =
  let (s1, rel1, bot1, top_r1) = pos1 in
  let (s2, rel2, bot2, top_r2) = pos2 in
  s1 `subset_set` s2 /\
  (forall ofst x y. x ∈ s1 ofst /\ y ∈ s1 ofst /\ x `rel1 ofst` y ==> x `rel2 ofst` y)

type event_typ 'e = option (nat * 'e)

let op (e:'e) (th_id:nat) : poset (event_typ 'e) 1 =
  let s = return_set (Some (th_id, e)) in
  (s, empty_rel s, Some (fun ofst -> make_el ofst (Some (th_id, e))), Some (fun ofst -> make_el ofst (Some (th_id, e))))


(**
     bot ofst                               make_el (ofst-1) None        (new bot) 
      |             async                   /        \
      |          ---------->               /          \
      |                                   v           v
      v                              bot (ofst-2)   make_el ofst None    (new top_r)
     top_r ofst                            |
                                          |
                                          v
                                    top_r (ofst-2)
**)

let async (#n:nat) (p:poset (event_typ 'e) n) : poset (event_typ 'e) (n+2) = 
  let (s, rel, bot, top_r) = p in
  let s' = s `union_set` (return_set None `union_set` return_set None) in
  assert (forall ofst. make_el ofst None ∈ s' ofst /\ make_el (ofst-1) None ∈ s' ofst);
  let rel' : relation (event_typ 'e) (n+2) = (fun ofst x y -> (x == make_el (ofst-1) None /\ y ∈ s' ofst) \/
                                            (x == make_el ofst None /\ y == make_el ofst None) \/
                                            (x ∈ s (ofst-2) /\ y ∈ s (ofst-2) /\ x `rel (ofst-2)` y)) in
  (s', rel', Some (fun (ofst:nat{ofst >= n+2}) -> make_el (ofst-1) None), Some (fun ofst -> make_el ofst None))

(** CA: Not very principled since the po is defined over xs and ys which are not part of S **)
let await (#e:Type) (th_id:nat) : poset (event_typ e) 1 =
  let s : set (event_typ e) 1 = return_set None in
  let rel = (fun ofst x y -> (x ∈ s ofst /\ y ∈ s ofst) \/ (y == make_el ofst None /\ Some? (el_v x) /\ fst (Some?.v (el_v x)) == th_id)) in
  (s, rel, Some (fun ofst -> make_el ofst None), Some (fun ofst -> make_el ofst None))

let prog04 () : poset (event_typ int) 5 = (op 1 1 `append_poset` async (op 2 2)) `append_poset` op 3 1

#set-options "--timing"
let __test_prog04 () = 
  let (s, _, bot, top_r) = prog04 () in
  assert (Some? bot /\ Some?.v bot 5 == make_el 1 (Some (1,1)));
  assert (Some? top_r /\ Some?.v top_r 5 == make_el 5 (Some (1,3)));
  assert (make_el 1 (Some (1,1)) ∈ s 5);
  assert (make_el 2 (Some (2,2)) ∈ s 5);
  assert (make_el 3 None ∈ s 5);
  assert (make_el 4 None ∈ s 5);
  assert (make_el 5 (Some (1,3)) ∈ s 5)
#reset-options
  
#set-options "--timing"
let __test_prog04' () = 
  let (s, _, bot, top_r) = prog04 () in
  assert (Some? bot /\ Some?.v bot 5 == make_el 1 (Some (1,1)));
  assert (Some? top_r /\ Some?.v top_r 5 == make_el 5 (Some (1,3)));
  assert (make_el 1 (Some (1,1)) `mem_poset 5` prog04 ());
  assert (make_el 2 (Some (2,2)) `mem_poset 5` prog04 ());
  assert (make_el 3 None `mem_poset 5` prog04 ());
  assert (make_el 4 None `mem_poset 5` prog04 ());
  assert (make_el 5 (Some (1,3)) `mem_poset 5` prog04 ())
#reset-options
  
let prog05 () : poset (event_typ int) 4 = async (op 2 2) `append_poset` await 2

#set-options "--timing"
let __test_prog05 () = 
  let (s, _, bot, top_r) = prog05 () in
  assert (Some? bot /\ Some?.v bot 4 == make_el 2 None);
  assert (Some? top_r /\ Some?.v top_r 4 == make_el 4 None);
  assert (make_el 1 (Some (2,2)) ∈ s 4);
  assert (make_el 2 None ∈ s 4);
  assert (make_el 3 None ∈ s 4);
  assert (make_el 4 None ∈ s 4)
#reset-options

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

let prog1 : poset (event_typ int) 7 =
  (((op 1 1 `append_poset` async (op 2 2)) `append_poset` (op 3 1)) `append_poset` await 2) `append_poset` op 4 1

// TODO: why do I have performance problems here?
// TODO: test on a smaller case if await works:
//        (async (op 2 2)) `append_poset` await 2) `append_poset` op 4 1
//           assert ([2;4] `membership` _)
//           assert (~([4;2] `membership` _)


let __test_prog1' () = 
  let (s, po, bot, top_r) = prog1 in
  assert (make_el 1 (Some (1,1)) ∈ s 7)
 
let lemma_mem_union_set_lhs' (#a:Type) (x:a) (id:id_typ) (#n:nat) (s1:set a n) (#m:nat) (s2:set a m) (#r:nat) (s3:set a r) (ofst:nat{ofst >= n+m+r}) :
  Lemma (requires (ofst-r-m < id /\ id <= ofst-r))
        (ensures (make_el id x ∈ (s1 `union_set` (s2 `union_set` s3)) ofst) <==> 
                 (make_el id x ∈ s2 (ofst-r)))
  [SMTPat (make_el id x ∈ (s1 `union_set` (s2 `union_set` s3)) ofst)] = ()
 
let lemma_mem_union_set_lhs'''' (#a:Type) (x:a) (id:id_typ) (#n:nat) (s1:set a n) (#m:nat) (s2:set a m) (#r:nat) (s3:set a r) (ofst:nat{ofst >= n+m+r}) :
  Lemma (requires (ofst-r < id))
        (ensures (make_el id x ∈ (s1 `union_set` (s2 `union_set` s3)) ofst) <==> 
                 (make_el id x ∈ s3 ofst))
  [SMTPat (make_el id x ∈ (s1 `union_set` (s2 `union_set` s3)) ofst)] = ()
 
let lemma_mem_union_set_lhs'' (#a:Type) (x:a) (id:id_typ) (#n:nat) (s1:set a n) (#m:nat) (s2:set a m) (#r:nat) (s3:set a r) (ofst:nat{ofst >= n+m+r}) :
  Lemma (requires (ofst-r-m < id /\ id <= ofst-r))
        (ensures (make_el id x ∈ ((s1 `union_set` s2) `union_set` s3) ofst) <==> 
                 (make_el id x ∈ s2 (ofst-r)))
  [SMTPat (make_el id x ∈ ((s1 `union_set` s2) `union_set` s3) ofst)] = ()
 
let lemma_mem_union_set_lhs''' (#a:Type) (x:a) (id:id_typ) (#n:nat) (s1:set a n) (#m:nat) (s2:set a m) (#r:nat) (s3:set a r) (ofst:nat{ofst >= n+m+r}) :
  Lemma (requires (id <= ofst-r-m))
        (ensures (make_el id x ∈ ((s1 `union_set` s2) `union_set` s3) ofst) <==> 
                 (make_el id x ∈ s1 (ofst-r-m)))
  [SMTPat (make_el id x ∈ ((s1 `union_set` s2) `union_set` s3) ofst)] = ()

#set-options "--timing --z3rlimit 24"

let _ = 
  let (s, po, bot, top_r) = prog1 in
  assert (make_el 1 (Some (1,1)) ∈ s 7)

let _ = 
  let (s, po, bot, top_r) = prog1 in
  assert (make_el 2 (Some (2,2)) ∈ s 7)

let _ = 
  let (s, po, bot, top_r) = prog1 in
  assert (make_el 3 None ∈ s 7)

let _ = 
  let (s, po, bot, top_r) = prog1 in
  assert (make_el 4 None ∈ s 7)

let _ = 
  let (s, po, bot, top_r) = prog1 in
  assert (make_el 5 (Some (1,3)) ∈ s 7)

let _ = 
  let (s, po, bot, top_r) = prog1 in
  assert (make_el 6 None ∈ s 7)

let _ = 
  let (s, po, bot, top_r) = prog1 in
  assert (make_el 7 (Some (1,4)) ∈ s 7)
  
let __test_prog1 () = 
  // let (s, po, bot, top_r) = prog1 in
  //assert (Some? bot /\ Some?.v bot 7 == make_el 1 (Some (1,1)));
  //assert (Some? top_r /\ Some?.v top_r 7 == make_el 7 (Some (1,4)));
  assert (make_el 1 (Some (1,1)) `mem_poset 7` prog1);
  assert (make_el 2 (Some (2,2)) `mem_poset 7` prog1);
 //  assert (make_el 3 None `mem_poset 7` prog1)
//  assert (make_el 4 None `mem_poset 7` prog1)
  assert (make_el 5 (Some (1,3)) `mem_poset 7` prog1);
  assert (make_el 6 None `mem_poset 7` prog1);
  assert (make_el 7 (Some (1,4)) `mem_poset 7` prog1)

(** mem_poset is 10x faster than ∈ **)
  
type trace 'e = list 'e
  
type marked (a:Type) = a -> Type0

let empty_marked (#a:Type) : marked a = fun _ -> False

let mark (m:marked 'a) (v:'a) : marked 'a = fun v' -> v == v' \/ m v'

let rec sat0 (t:trace 'e) (#n:nat) (s:set (event_typ 'e) n) (rel:relation (event_typ 'e) n) (el_prev:elem (event_typ 'e)) (marked_ids:marked (elem (event_typ 'e))) : Type0 =
  match t with
  | [] -> True
  | ev :: tl -> exists el. (el ∈ s n) /\
                      ~(marked_ids el) /\ 
                      (Some? (el_v el) /\ snd (Some?.v (el_v el)) == ev) /\
                      ((el_prev `rel n` el) \/ ~(el `rel n` el_prev)) /\
                      sat0 tl s rel el (mark marked_ids el)

let sat (t:trace 'e) (#n:nat) (p:poset (event_typ 'e) n) : Type0 =
  let (s, rel, bot, _) = p in
  match t with
  | [] -> n == 0
  | h :: tl -> Some? bot /\ (let bot_el = Some?.v bot n in
              match el_v bot_el with
              | None -> sat0 t s rel bot_el (mark empty_marked bot_el)
              | Some b' -> h == snd b' /\ sat0 tl s rel bot_el (mark empty_marked bot_el))

let rec sat0' (t:trace 'e) (#n:nat) (p:poset (event_typ 'e) n) (el_prev:elem (event_typ 'e)) (marked_ids:marked id_typ) : Type0 =
  let (_, rel, _, _) = p in
  match t with
  | [] -> True
  | ev :: tl -> exists id_ev id_th. 
                      ~(marked_ids id_ev) /\ 
                      (let el = make_el id_ev (Some (id_th, ev)) in
                        (el `mem_poset n` p) /\
                        ((el_prev `rel n` el) \/ ~(el `rel n` el_prev)) /\
                        sat0' tl p el (mark marked_ids id_ev))

let sat' (t:trace 'e) (#n:nat) (p:poset (event_typ 'e) n) : Type0 =
  let (_, _, bot, _) = p in
  match t with
  | [] -> n == 0
  | h :: tl -> Some? bot /\ (let bot_el = Some?.v bot n in
              match el_v bot_el with
              | None -> sat0' t p bot_el (mark empty_marked (el_id bot_el))
              | Some b' -> h == snd b' /\ sat0' tl p bot_el (mark empty_marked (el_id bot_el)))

#set-options "--z3rlimit 64"
let _ = assert ([1;4] `sat` prog1) 
// 12305ms when sat0 uses ∈

let _ = assert ([1;4] `sat'` prog1) 
// 22118ms when sat0 uses mem_poset

let _ = assert (~([4;1] `sat` prog1))

let _ = assert (([1;2;3] `sat` ((((op 1 1 `append_poset` async (op 2 2)) `append_poset` (op 3 1)) `append_poset` await 2) `append_poset` op 4 1))) 

let _ = assert (([1;2;4] `sat` prog1))

#set-options "--z3rlimit 512 --fuel 200 --ifuel 200"

let _ = assert (([1;2;3;4] `sat` prog1))

let _ = assert ([1;3;2;4] `sat` prog1)

let _ = assert (~([1;3;4;2] `sat` prog1))

  
let rec test_membership0 (t:trace int) (#n:nat) (p:poset int n) (el_prev:elem int) (marked_ids:marked) : Type0 =
  let (s, rel, _, _) = p in
  match t with
  | [] -> True
  | h :: tl -> exists id_h. ~(marked_ids id_h) /\ 
                      (make_el id_h h ∈ s n) /\
                      ((el_prev `rel n` make_el id_h h) \/ ~(make_el id_h h `rel n` el_prev)) /\
                      test_membership0 tl p (make_el id_h h) (mark marked_ids id_h)

let test_membership (t:trace int) (#n:nat) (p:poset int n) : Type0 =
  let (_, _, bot, _) = p in
  match t with
  | [] -> n == 0
  | h :: tl -> Some? bot /\ (let b = Some?.v bot n in
               h == el_v b /\ test_membership0 tl p b (mark empty_marked (el_id b)))

(**  1
    | \
    2  3 **)
let __test_set : set int 3 = ((empty_set ⊕ 1) ⊕ 2) ⊕ 3
let __test_po : relation int 3 =
  extend_rel __test_set
    (extend_rel __test_set (empty_rel __test_set) (fun id -> make_el (id-2) 1) (fun id -> make_el (id-1) 2))
    (fun id -> make_el (id-2) 1) (fun id -> make_el id 3)

let __test_poset : poset int 3 =
  (__test_set, __test_po, Some (fun (ofst:nat{ofst >= 3}) -> make_el (ofst-2) 1), Some (fun id -> make_el id 3))

let __test_123 () =
  assert ([1;2] `test_membership` __test_poset);
  assert ([1;3] `test_membership` __test_poset)

let __test_124 () =
  assert (~([2;1] `test_membership` __test_poset));
  assert (~([3;1] `test_membership` __test_poset))

let __test_125 () = assert ([1;2;3] `test_membership` __test_poset)

let __test_126 () = assert ([1;3;2] `test_membership` __test_poset)

let __test_128 () = assert (~([3;1;2] `test_membership` __test_poset))

(**  1
    | \
    2  3
     \ |
       4 **)
       
let __test_set3 : set int 4 = (((return_set 1) ⊕ 2) ⊕ 3) ⊕ 4
let __test_po3 : relation int 4 =
  extend_rel __test_set3
    (extend_rel __test_set3
        (extend_rel __test_set3
        (extend_rel __test_set3 (empty_rel __test_set3) (fun id -> make_el (id-3) 1) (fun id -> make_el (id-2) 2))
        (fun id -> make_el (id-3) 1) (fun id -> make_el (id-1) 3))
      (fun id -> make_el (id-1) 3) (fun id -> make_el id 4))
    (fun id -> make_el (id-2) 2) (fun id -> make_el id 4)
   
let __test_poset3 : poset int 4 =
  (__test_set3, __test_po3, Some (fun (ofst:nat{ofst >= 4}) -> make_el (ofst-3) 1), Some (fun id -> make_el id 4)) 

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
