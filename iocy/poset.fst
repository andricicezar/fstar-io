module Poset

open FStar.Tactics
open FStar.List.Tot.Base

(** *** Definition of a special type of set **)

(** We need a set that allows the same value to appear multiple times and that allows
    us to distingusih between the appearances.
    
    To do that, we box the values into a constructor that associates to each value
    an id.

    The ids given to the elements are internal to the state, however to be able to do
    unions and avoid quantifiers, I made the sets parametric into an offset (ofst) that
    is offseting the ids. So when setting the id of an element, the offset is used.

    However, the offset is "reversed".
**)
type prop_set a = a -> Type0

type uniq_val_id = nat
type uniq_val (a:Type) = uniq_val_id * a
let uid (x:uniq_val 'a) : uniq_val_id = fst x
let uv  (x:uniq_val 'a) : 'a = snd x
let make_uniq_val (id:uniq_val_id) (v:'a) : uniq_val 'a = (id, v)

type _set a = prop_set (uniq_val a)
let (∈) (#a:Type) (x:uniq_val a) (s:_set a) = s x
let (∉) (#a:Type) (x:uniq_val a) (s:_set a) = ~(x ∈ s)

type set0 a (n:nat) = ofst:nat{ofst >= n} -> _set a
type set a (n:nat) = s:(set0 a n){
  (forall ofst x. x ∈ s ofst ==> (ofst-n) < uid x /\ uid x <= ofst) /\
  // (forall ofst i. (ofst-n) < i /\ i <= ofst ==> (exists x. id x == i /\ x ∈ s ofst)) /\
  (forall ofst x y. x ∈ s ofst /\ y ∈ s ofst /\ x =!= y ==> uid x =!= uid y)
//  (forall ofst x y. x ∈ s ofst /\ y ∈ s ofst /\ id x == id y ==> x == y)
}

type set_elem (a:Type) (n:nat) =
  ofst:nat{ofst >= n} -> uniq_val a
  
let empty_set_lemma (s:set 'a 0) : Lemma (forall ofst x. x ∉ s ofst) = ()

let empty_set (#a:Type) : set a 0 = fun _ _ -> False

let eq_set (s1:set 'a 'n) (s2:set 'a 'm) : Type0 =
  'n == 'm /\ (forall ofst x. s1 ofst x <==> s2 ofst x)

let return_set (#a:Type) (x:a) : set a 1 = fun ofst y -> make_uniq_val ofst x == y

let add_set (#a:Type) (#n:nat) (s:set a n) (x:a) : set a (n+1) =
  fun (ofst:nat{ofst >= n+1}) y -> make_uniq_val ofst x == y \/ y ∈ s (ofst-1)
let (⊕) #a #n = add_set #a #n

let subset_set (#a:Type) (#n #m:nat) (s0:set a n) (s1:set a m) : Type0 =
  n <= m ==> (forall x (ofst:nat{ofst >= m}). x ∈ s0 ofst ==> x ∈ s1 ofst)
let (⊆) #a #n #m = subset_set #a #n #m

let union_set (#a:Type) (#n #m:nat) (s0:set a n) (s1:set a m) : set a (n+m) =
  fun (ofst:nat{ofst >= n+m}) x -> x ∈ s0 (ofst-m) \/ x ∈ s1 ofst

(**
let lemma_mem_add (#a:Type) (x:a) (#n:nat) (s:set a n) (ofst:nat{ofst >= n+1}) :
  Lemma (make_uniq_val ofst x ∈ (s ⊕ x) ofst) [SMTPat (make_uniq_val ofst x ∈ (s ⊕ x) ofst)] = ()

let lemma_mem_add2 (#a:Type) (x:a) (#n:nat) (s:set a n) (ofst:nat{ofst >= n+2}) (y:a) :
  Lemma (make_uniq_val (ofst-1) x ∈ ((s ⊕ x) ⊕ y) ofst) [SMTPat (make_uniq_val (ofst-1) x ∈ ((s ⊕ x) ⊕ y) ofst)] = ()
**)

let lemma_mem_union_set_rhs (#a:Type) (x:a) (#n:nat) (s1:set a n) (#m:nat) (s2:set a m) (id:uniq_val_id) (ofst:nat{ofst >= n+m}) :
  Lemma (requires (ofst-m < id))
        (ensures (make_uniq_val id x ∈ (s1 `union_set` s2) ofst) <==>
                 (make_uniq_val id x ∈ s2 ofst))
  [SMTPat (make_uniq_val id x ∈ (s1 `union_set` s2) ofst)] = ()
  
let lemma_mem_union_set_lhs (#a:Type) (x:a) (#n:nat) (s1:set a n) (#m:nat) (s2:set a m) (id:uniq_val_id) (ofst:nat{ofst >= n+m}) :
  Lemma (requires (id <= ofst-m))
        (ensures (make_uniq_val id x ∈ (s1 `union_set` s2) ofst) <==> 
                (make_uniq_val id x ∈ s1 (ofst-m)))
  [SMTPat (make_uniq_val id x ∈ (s1 `union_set` s2) ofst)] = ()

let __test_set1 : set int 4 = (((return_set 1) ⊕ 2) ⊕ 2) ⊕ 4
let _ = assert (make_uniq_val 2 2 ∈ __test_set1 4 /\ make_uniq_val 3 2 ∈ __test_set1 4)

[@expect_failure]
let _ = assert (make_uniq_val 4 2 ∈ __test_set1 4)
[@expect_failure]
let _ = assert (make_uniq_val 1 2 ∈ __test_set1 4)
let _ = assert (make_uniq_val 1 2 ∉ __test_set1 4)

let __test_mem (s0:nat{s0 >= 4}) =
  assert (exists (id1 id2:uniq_val_id). make_uniq_val id1 2 ∈ __test_set1 s0 /\ id1 <= id2 /\ make_uniq_val id2 2 ∈ __test_set1 s0)

let _ = assert (exists (id1 id2:uniq_val_id). id1 <= id2 /\ 
                      make_uniq_val id1 1 ∈ __test_set1 4 /\
                      make_uniq_val (id1+1) 2 ∈ __test_set1 4 /\
                      make_uniq_val id2 2 ∈ __test_set1 4 /\
                      make_uniq_val (id2+1) 4 ∈ __test_set1 4)

let _ = assert (__test_set1 `subset_set` __test_set1)
let __test_set2 = __test_set1 `union_set` __test_set1
let _ = assert (__test_set1 `subset_set` __test_set2)
let _ = assert (forall id v. make_uniq_val id v ∈ __test_set1 4 <==>
                      make_uniq_val id v ∈ __test_set2 8 /\ make_uniq_val (id+4) v ∈ __test_set2 8)

(** *** Relation **)

type relation a (n:nat) = ofst:nat{ofst >= n} -> uniq_val a -> uniq_val a -> Type0

let empty_rel (#a:Type) (#n:nat) (s:set a n) : relation a n =
  fun ofst x y -> x ∈ s ofst /\ x == y

let extend_rel
  (#a:Type)
  (#n:nat)
  (s:set a n)
  (po:relation a n)
  (ev1:(set_elem a n){forall ofst. ev1 ofst ∈ s ofst})
  (ev2:(set_elem a n){forall ofst. ev2 ofst ∈ s ofst})
  : relation a n =
  fun ofst ev1' ev2' -> ev1' ∈ s ofst /\ ev2' ∈ s ofst /\ 
    (((ev2 ofst `po ofst` ev1 ofst ==> ev1 ofst == ev2 ofst) /\ (ev1' `po ofst` ev1 ofst /\ ev2 ofst `po ofst` ev2')) \/ (ev1' `po ofst` ev2'))

(** *** Data structure **)
type th_id : eqtype = int
type event a = option a
type elem0 (a:Type) = th_id * event a
type elem (a:Type) (n:nat) = set_elem (elem0 a) n

unfold let lshift_elem (#n:nat) (#m:nat) (x:elem 'a n) : elem 'a (n+m) =
  fun (ofst:nat{ofst >= n+m}) -> x (ofst-m)

unfold let rshift_elem (#n:nat) (#m:nat) (x:elem 'a m) : elem 'a (n+m) =
  fun (ofst:nat{ofst >= n+m}) -> x ofst

let get_id (x:elem 'a 'n) (ofst:nat{ofst >= 'n}) : th_id = fst (snd (x ofst))

let make_elem (#a:Type) (v:elem0 a) (n:nat) : elem a n = fun ofst -> make_uniq_val ofst v

type poset0 (a:Type) (n:nat) =
  set (elem0 a) n        (** set **)
  *
  relation (elem0 a) n   (** partial order between elements **) 
  *
  option (elem a n)  (** the least element **)
  *
  (th_id -> option (elem a n)) (** the maximal elements, one for each thread not awaited **)
  *
  list (th_id * (elem a n))

type poset (a:Type) (n:nat) =
  p:(poset0 a n){
    let (s, rel, least, maxs, urel) = p in

    (** poset properties **)
    (forall ofst x. x ∈ s ofst ==> x `rel ofst` x) /\
    (forall ofst x y z. x ∈ s ofst /\ y ∈ s ofst /\ z ∈ s ofst ==> (x `rel ofst` y /\ y `rel ofst` z ==> x `rel ofst` z)) /\
    (forall ofst x y. x ∈ s ofst /\ y ∈ s ofst ==> (x `rel ofst` y /\ y `rel ofst` x ==> x == y)) /\

    (** property of the least element **)
    (None? least <==> n == 0) /\
    (n <> 0 ==> Some? least /\ (forall ofst. Some?.v least ofst ∈ s ofst /\ (forall x. x ∈ s ofst ==> Some?.v least ofst `rel ofst` x))) /\

    (** each element of the maxs function is a maximal element **)
    (forall (tid:th_id). match maxs tid with
      | Some max -> (forall ofst. tid == get_id max ofst /\ max ofst ∈ s ofst)
      | _ -> True) /\

    (** the maxs function captures all maximal elements **)
    (forall (x:elem a n) ofst. (x ofst ∈ s ofst /\ (forall (y:elem a n). y ofst ∈ s ofst /\ get_id x ofst == get_id y ofst ==> ~(x ofst `rel ofst` y ofst))) ==>
      (maxs (get_id x ofst) == Some x)) /\

    (n <> 0 ==> (forall ofst. Some? (maxs (get_id (Some?.v least) ofst)))) /\

    (** urel properties **)
    (forall tid x. (tid, x) `memP` urel ==> (None? (maxs tid)) /\ (forall ofst. x ofst ∈ s ofst))
}

let empty_poset (#a:Type) : poset a 0 = (empty_set, empty_rel empty_set, None, (fun _ -> None), [])

let return_poset (el0:elem0 'a) : poset 'a 1 =
  let s = return_set el0 in
  let el = make_elem el0 1 in
  let maxs = (fun tid -> if tid = (fst el0) then Some el else None) in
  (s, empty_rel s, Some el, maxs, [])

let new_po
  (#n #m:nat)
  (s1:set (elem0 'e) n)
  (rel1:relation (elem0 'e) n)
  (s2:set (elem0 'e) m)
  (rel2:relation (elem0 'e) m)
  (least1 : option (elem 'e n))
  (maxs1 : th_id -> option (elem 'e n))
  (urel2 : list (th_id * elem 'e m))
  (_:squash (n <> 0 ==> (forall (ofst:nat{ofst >= n+m}). Some? least1 /\ Some? (maxs1 (get_id (Some?.v least1) (ofst-m))))))
  : relation (elem0 'e) (n+m) = (
  fun (ofst:nat{ofst >= n + m}) x y ->
    (x ∈ s1 (ofst-m) /\ y ∈ s1 (ofst-m) /\ x `rel1 (ofst-m)` y) \/
    (x ∈ s2 ofst /\ y ∈ s2 ofst /\ x `rel2 ofst` y) \/
    (x ∈ s1 (ofst-m) /\ y ∈ s2 ofst /\ x `rel1 (ofst-m)` (Some?.v (maxs1 (get_id (Some?.v least1) (ofst-m)))) (ofst-m)) \/
    (x ∈ s1 (ofst-m) /\ y ∈ s2 ofst /\ (exists (u:th_id * elem 'e m). u `memP` urel2 /\ Some? (maxs1 (fst u)) /\
                                             x `rel1 (ofst-m)` (Some?.v (maxs1 (fst u)) (ofst-m)) /\ snd u ofst `rel2 ofst` y))
  )

unfold let (let?) (x: option 'a) (f: 'a -> option 'b): option 'b
  = match x with
  | Some x -> f x
  | None   -> None

let new_maxs 
  (#n #m:nat)
  (maxs1 : th_id -> option (elem 'e n))
  (maxs2 : th_id -> option (elem 'e m))
  : th_id -> option (elem 'e (n+m)) = 
  (fun tid -> 
    let x = (
      let? x = maxs2 tid in Some (rshift_elem x)) in

let new_urel
  (#n #m:nat)
  (maxs1 : th_id -> option (elem 'e n))
  (urel1 : list (th_id * elem 'e n))
  (urel2 : list (th_id * elem 'e m))
  : list (th_id * elem 'e (n+m)) =
  filter (fun (tid,_) -> not (Some? (maxs1 tid))) (
    (map (fun (tid, el) -> (tid, lshift_elem el)) urel1) @
    (map (fun (tid, el) -> (tid, rshift_elem el)) urel2))

let lemma_new_urel
  (#n #m:nat)
  (maxs1 : th_id -> option (elem 'e n))
  (urel1 : list (th_id * elem 'e n))
  (urel2 : list (th_id * elem 'e m))
  (maxs : th_id -> option (elem 'e (n+m)))
  (s : set (elem0 'e) (n+m)) :
  Lemma (
    let urel = new_urel maxs1 urel1 urel2 in
    (forall tid x. (tid, x) `memP` urel ==> (None? (maxs tid)) /\ (forall ofst. x ofst ∈ s ofst))) = admit ()

let concat_poset (#n #m:nat) (pos1:poset 'e n) (pos2:poset 'e m) : poset 'e (n+m) =
  let (s1, rel1, least1, maxs1, urel1)  = pos1 in
  let (s2, rel2, least2, maxs2, urel2) = pos2 in
  match least1, least2 with
  | None, None
  | None, _ -> assert (n+m == m); pos2
  | _, None -> assert (n+m == n); pos1
  | _, _ -> begin
    let s = s1 `union_set` s2 in
    let rel : relation (elem0 'e) (n+m) = new_po s1 rel1 s2 rel2 least1 maxs1 urel2 () in
    let least : option (elem 'e (n+m)) = Some (lshift_elem (Some?.v least1)) in
    let maxs = new_maxs maxs1 maxs2 in
    let urel = new_urel maxs1 urel1 urel2 in
    let p : poset0 'e (n+m) = (s, rel, least, maxs, urel) in

    assert (forall ofst x. x ∈ s ofst ==> x `rel ofst` x);
    assert (forall ofst x y z. x ∈ s ofst /\ y ∈ s ofst /\ z ∈ s ofst ==> (x `rel ofst` y /\ y `rel ofst` z ==> x `rel ofst` z));
    assert (forall ofst x y. x ∈ s ofst /\ y ∈ s ofst ==> (x `rel ofst` y /\ y `rel ofst` x ==> x == y));

    (** property of the least element **)
    assert (None? least <==> n == 0);
    assert (n <> 0 ==> Some? least /\ (forall ofst. Some?.v least ofst ∈ s ofst /\ (forall x. x ∈ s ofst ==> Some?.v least ofst `rel ofst` x)));

    (** the maxs function captures all maximal elements **)
    assert (forall (x:elem 'e n) ofst. (x ofst ∈ s ofst /\ (forall (y:elem 'e n). y ofst ∈ s ofst /\ get_id x ofst == get_id y ofst ==> ~(x ofst `rel ofst` y ofst))) ==>
      (maxs (get_id x ofst) == Some x));

    assert (n <> 0 ==> (forall ofst. Some? (maxs (get_id (Some?.v least) ofst))));

    (** the maxs function returns the last event produced by the thread `tid` **)
    assert (forall (tid:th_id). match maxs tid with
      | Some max -> (forall ofst. tid == get_id max ofst /\ max ofst ∈ s ofst)
      | _ -> True);

    lemma_new_urel maxs1 urel1 urel2 maxs s;
    (** urel properties **)
    assert (forall tid x. (tid, x) `memP` urel ==> (None? (maxs tid)) /\ (forall ofst. x ofst ∈ s ofst));
    p
  end

let subset_poset (#n #m:nat) (pos1:poset 'e n) (pos2:poset 'e m) : Type0 =
  let (s1, rel1, least1, _, _) = pos1 in
  let (s2, rel2, least2, _, _) = pos2 in
  s1 `subset_set` s2 /\
  (forall ofst x y. x ∈ s1 ofst /\ y ∈ s1 ofst /\ x `rel1 ofst` y ==> x `rel2 ofst` y)

let op (tid:th_id) (e:'e) : poset 'e 1 =
  return_poset (tid, Some e)

(**
     least                                   make_uniq_val (tid, None)        (new least) 
      |             async                   /        
      |          ---------->               /          
      |                                   v           
      v                                 least
     max_r                                |
                                          |
                                          v
                                        max_r
**)

(** here tid is the id of the current thread, 
    and p has a different id (aka get_id least <> tid) **)
let async (#n:nat) (tid:th_id) (p:poset 'e n) :
  Pure (poset 'e (n+1)) 
    (requires (let (_, _, _, maxs, _) = p in None? (maxs tid)))
    (ensures (fun _ -> True)) = 
  let cp = return_poset (tid, None) in 
  let (s, rel, least, maxs, urel) = p in
  let urel' = if Some? least then (tid, Some?.v least)::urel else urel in
  let p' : poset 'e n = (s, rel, least, maxs, urel') in
  cp `concat_poset` p'


let await (#e:Type) (tid:th_id) (wid:th_id{wid <> tid}) : poset e 1 =
  let (s, rel, least, maxs, urel) = return_poset (tid, None) in
  (s, rel, least, maxs, [(wid, Some?.v least)])

(** *** Tests **)
let prog01 () : poset int 3 = op 1 1 `concat_poset` (op 1 2 `concat_poset` op 1 3)

#set-options "--timing"
let __test_prog01 () = 
  let (s, rel, least, maxs, urel) = prog01 () in
  assert (Some? least /\ Some?.v least 3 == make_uniq_val 1 (1, Some 1));
  assert (urel == []);
  assert (forall tid. tid <> 1 ==> None? (maxs tid));
  assert (Some? (maxs 1) /\ Some?.v (maxs 1) 3 == make_uniq_val 3 (1, Some 3));
  assert (make_uniq_val 1 (1, Some 1) ∈ s 3);
  assert (make_uniq_val 2 (1, Some 2) ∈ s 3);
  assert (make_uniq_val 3 (1, Some 3) ∈ s 3);
  assert (make_uniq_val 1 (1, Some 1) `rel 3` make_uniq_val 2 (1, Some 2));
  assert (make_uniq_val 1 (1, Some 1) `rel 3` make_uniq_val 3 (1, Some 3));
  assert (~(make_uniq_val 2 (1, Some 2) `rel 3` make_uniq_val 1 (1, Some 1)));
  ()
#reset-options

let prog04 () : poset int 4 = (op 1 1 `concat_poset` async 1 (op 2 2)) `concat_poset` op 1 3

#set-options "--timing --z3rlimit 64 --fuel 32 --ifuel 32"
let __test_prog04 () = 
  let (s, rel, least, maxs, urel) = prog04 () in
  assert (Some? least /\ Some?.v least 4 == make_uniq_val 1 (1, Some 1));
 // assert (Some? max_r /\ Some?.v maxs 4 == make_uniq_val 4 (Some (1,3)));
  assert (make_uniq_val 1 (1, Some 1) ∈ s 4);
  assert (make_uniq_val 2 (1, None) ∈ s 4);
  assert (make_uniq_val 3 (2, Some 2) ∈ s 4);
  assert (make_uniq_val 4 (1, Some 3) ∈ s 4);
  assert (make_uniq_val 1 (1, Some 1) `rel 4` make_uniq_val 3 (2, Some 2));
  assert (make_uniq_val 1 (1, Some 1) `rel 4` make_uniq_val 4 (1, Some 3));
  assert (~(make_uniq_val 4 (1, Some 3) `rel 4` make_uniq_val 3 (2, (Some 2))));
  assert (~(make_uniq_val 3 (2, Some 2) `rel 4` make_uniq_val 4 (1, (Some 3))));
  ()
#reset-options
  
let prog05 () : poset int 3 = async 1 (op 2 2) `concat_poset` await 1 2

#set-options "--timing --z3rlimit 64 --fuel 32 --ifuel 32"
let __test_prog05 () : Tot unit by (
  norm [delta_only [`%async;`%await;`%op;`%concat_poset;`%return_poset;`%new_po];zeta;iota]) = 
  let (s, rel, least, maxs, urel) = async 1 (op 2 2) `concat_poset` await 1 2 in //prog05 () in
  assert (Some? least /\ Some?.v least 3 == make_uniq_val 1 (1, None));
  // assert (Some? max_r /\ Some?.v max_r 4 == make_uniq_val 4 None);
  assert (make_uniq_val 1 (1, None) ∈ s 3);
  assert (make_uniq_val 2 (2, Some 2) ∈ s 3);
  assert (make_uniq_val 3 (1, None) ∈ s 3);
  assert (make_uniq_val 1 (1, None) `rel 3` make_uniq_val 3 (1, None));
  assert (make_uniq_val 1 (1, None) `rel 3` make_uniq_val 2 (2, Some 2));
  assert (make_uniq_val 2 (2, Some 2) `rel 3` make_uniq_val 3 (1, None));
  assert (~(make_uniq_val 3 (1, None) `rel 3` make_uniq_val 2 (2, Some 2)));
  assert (~(make_uniq_val 2 (2, Some 2) `rel 3` make_uniq_val 1 (1, None)));
  assert (~(make_uniq_val 3 (1, None) `rel 3` make_uniq_val 1 (1, None)));
  ()
#reset-options
 
let lemma_mem_union_set_lhs' (#a:Type) (x:a) (id:uniq_val_id) (#n:nat) (s1:set a n) (#m:nat) (s2:set a m) (#r:nat) (s3:set a r) (ofst:nat{ofst >= n+m+r}) :
  Lemma (requires (ofst-r-m < id /\ id <= ofst-r))
        (ensures (make_uniq_val id x ∈ (s1 `union_set` (s2 `union_set` s3)) ofst) <==> 
                 (make_uniq_val id x ∈ s2 (ofst-r)))
  [SMTPat (make_uniq_val id x ∈ (s1 `union_set` (s2 `union_set` s3)) ofst)] = ()
 
let lemma_mem_union_set_lhs'''' (#a:Type) (x:a) (id:uniq_val_id) (#n:nat) (s1:set a n) (#m:nat) (s2:set a m) (#r:nat) (s3:set a r) (ofst:nat{ofst >= n+m+r}) :
  Lemma (requires (ofst-r < id))
        (ensures (make_uniq_val id x ∈ (s1 `union_set` (s2 `union_set` s3)) ofst) <==> 
                 (make_uniq_val id x ∈ s3 ofst))
  [SMTPat (make_uniq_val id x ∈ (s1 `union_set` (s2 `union_set` s3)) ofst)] = ()
 
let lemma_mem_union_set_lhs'' (#a:Type) (x:a) (id:uniq_val_id) (#n:nat) (s1:set a n) (#m:nat) (s2:set a m) (#r:nat) (s3:set a r) (ofst:nat{ofst >= n+m+r}) :
  Lemma (requires (ofst-r-m < id /\ id <= ofst-r))
        (ensures (make_uniq_val id x ∈ ((s1 `union_set` s2) `union_set` s3) ofst) <==> 
                 (make_uniq_val id x ∈ s2 (ofst-r)))
  [SMTPat (make_uniq_val id x ∈ ((s1 `union_set` s2) `union_set` s3) ofst)] = ()
 
let lemma_mem_union_set_lhs''' (#a:Type) (x:a) (id:uniq_val_id) (#n:nat) (s1:set a n) (#m:nat) (s2:set a m) (#r:nat) (s3:set a r) (ofst:nat{ofst >= n+m+r}) :
  Lemma (requires (id <= ofst-r-m))
        (ensures (make_uniq_val id x ∈ ((s1 `union_set` s2) `union_set` s3) ofst) <==> 
                 (make_uniq_val id x ∈ s1 (ofst-r-m)))
  [SMTPat (make_uniq_val id x ∈ ((s1 `union_set` s2) `union_set` s3) ofst)] = ()

#set-options "--timing --z3rlimit 24"

(** Test:
          (1,1)
            |
            *
           /  \
      (2,2)    (1,3)
            \  |
               *
               |
             (1,4)
**)

let prog1 : poset int 6 =
  (((op 1 1 `concat_poset` async 1 (op 2 2)) `concat_poset` (op 1 3)) `concat_poset` await 1 2) `concat_poset` op 1 4

// TODO: why do I have performance problems here?
// TODO: test on a smaller case if await works:
//        (async (op 2 2)) `append_poset` await 2) `append_poset` op 4 1
//           assert ([2;4] `membership` _)
//           assert (~([4;2] `membership` _)


let __test_prog1' () = 
  let (s, rel, least, maxs, urel) = prog1 in
  assert (make_uniq_val 1 (1, Some 1) ∈ s 6)

let _ = 
  let (s, rel, least, maxs, urel) = prog1 in
  assert (make_uniq_val 1 (1, Some 1) ∈ s 6)

let _ = 
  let (s, rel, least, maxs, urel) = prog1 in
  assert (make_uniq_val 2 (1, None) ∈ s 6)

let _ = 
  let (s, rel, least, maxs, urel) = prog1 in
  assert (make_uniq_val 3 (2, Some 2) ∈ s 6)

let _ = 
  let (s, rel, least, maxs, urel) = prog1 in
  assert (make_uniq_val 4 (1, Some 3) ∈ s 6)

let _ = 
  let (s, rel, least, maxs, urel) = prog1 in
  assert (make_uniq_val 5 (1, None) ∈ s 6)

let _ = 
  let (s, rel, least, maxs, urel) = prog1 in
  assert (make_uniq_val 6 (1, Some 4) ∈ s 6)
  
type trace 'e = list 'e
  
type marked (a:Type) = a -> Type0

let empty_marked (#a:Type) : marked a = fun _ -> False

let mark (m:marked 'a) (v:'a) : marked 'a = fun v' -> v == v' \/ m v'

let rec sat0 (t:trace 'e) (#n:nat) (s:set (elem0 'e) n) (rel:relation (elem0 'e) n)
  (el_prev:uniq_val (elem0 'e)) (used_els:marked (uniq_val (elem0 'e))) : Type0 =
  match t with
  | [] -> True
  | ev :: tl -> exists el. 
                      (~(used_els el) /\
                      (el ∈ s n /\
                      (((el_prev `rel n` el) \/ ~(el `rel n` el_prev)) /\
                      ((Some? (snd (uv el)) /\ (Some?.v (snd (uv el))) == ev) /\
                      sat0 tl s rel el (mark used_els el)))))

let sat (t:trace 'e) (#n:nat) (p:poset 'e n) : Type0 =
  let (s, rel, least, maxs, urel) = p in
  match t with
  | [] -> n == 0
  | h :: tl -> Some? least /\ (let least_el = Some?.v least n in
              match snd (uv least_el) with
              | None -> sat0 t s rel least_el (mark empty_marked least_el)
              | Some b' -> h == b' /\ sat0 tl s rel least_el (mark empty_marked least_el))

#set-options "--z3rlimit 64"
#set-options "--z3rlimit 512 --fuel 200 --ifuel 200"
#push-options "--timing"

let _ = assert ([1;4] `sat` prog1) 
// 3000-4000ms when sat0 uses ∈

let _ = assert (~([4;1] `sat` prog1))

(** ** From here it does not verify **)

//#set-options "--z3rlimit 128"
let _ = assert ([1;2;3] `sat` prog1) 

let _ = assert (([1;2;4] `sat` prog1))

#set-options "--z3rlimit 512 --fuel 200 --ifuel 200"

let _ = assert (([1;2;3;4] `sat` prog1))

let _ = assert ([1;3;2;4] `sat` prog1)

let _ = assert (~([1;3;4;2] `sat` prog1))











(*** Old tests **)

  
let rec test_membership0 (t:trace int) (#n:nat) (p:poset int n) (el_prev:elem int) (marked_ids:marked id_typ) : Type0 =
  let (s, rel, _, _) = p in
  match t with
  | [] -> True
  | h :: tl -> exists id_h. ~(marked_ids id_h) /\ 
                      id_h <= n /\
                      (make_uniq_val id_h h ∈ s n) /\
                      ((el_prev `rel n` make_uniq_val id_h h) \/ ~(make_uniq_val id_h h `rel n` el_prev)) /\
                      test_membership0 tl p (make_uniq_val id_h h) (mark marked_ids id_h)

let test_membership (t:trace int) (#n:nat) (p:poset int n) : Type0 =
  let (_, _, least, _) = p in
  match t with
  | [] -> n == 0
  | h :: tl -> Some? least /\ (let b = Some?.v least n in
               h == el_v b /\ test_membership0 tl p b (mark empty_marked (el_id b)))

(**  1
    | \
    2  3 **)
let __test_set : set int 3 = ((empty_set ⊕ 1) ⊕ 2) ⊕ 3
let __test_po : relation int 3 =
  extend_rel __test_set
    (extend_rel __test_set (empty_rel __test_set) (fun id -> make_uniq_val (id-2) 1) (fun id -> make_uniq_val (id-1) 2))
    (fun id -> make_uniq_val (id-2) 1) (fun id -> make_uniq_val id 3)

let __test_poset : poset int 3 =
  (__test_set, __test_po, Some (fun (ofst:nat{ofst >= 3}) -> make_uniq_val (ofst-2) 1), Some (fun id -> make_uniq_val id 3))

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
       
let __test_set3 : set int 4 = return_set 1 `union_set` return_set 2 `union_set` return_set 3 `union_set` return_set 4
let __test_po3 : relation int 4 =
  extend_rel __test_set3
    (extend_rel __test_set3
        (extend_rel __test_set3
        (extend_rel __test_set3 (empty_rel __test_set3) (fun id -> make_uniq_val (id-3) 1) (fun id -> make_uniq_val (id-2) 2))
        (fun id -> make_uniq_val (id-3) 1) (fun id -> make_uniq_val (id-1) 3))
      (fun id -> make_uniq_val (id-1) 3) (fun id -> make_uniq_val id 4))
    (fun id -> make_uniq_val (id-2) 2) (fun id -> make_uniq_val id 4)
   
let __test_poset3 : poset int 4 =
  (__test_set3, __test_po3, Some (fun (ofst:nat{ofst >= 4}) -> make_uniq_val (ofst-3) 1), Some (fun id -> make_uniq_val id 4)) 

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
