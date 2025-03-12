module Poset_Comp

open FStar.Tactics
open FStar.List.Tot.Base

#set-options "--print_universes"

type set (a:eqtype) = list a

type uniq_val_id = nat
type uniq_val (a:eqtype) = uniq_val_id * a
let make_uniq_val (#a:eqtype) id (x:a) : uniq_val a = (id, x)

let (∈) (#a:eqtype) ((id, x):uniq_val a) (s:list a) : bool = 
  if id < length s then index s id = x
  else false
  
let (∉) (#a:eqtype) (x:uniq_val a) (s:set a) = not (x ∈ s)

let empty_set #a : set a = []

let eq_set (s1:set 'a) (s2:set 'a) : bool = s1 = s2

let return_set (#a:eqtype) (x:a) : set a = [x]

let add_set (#a:eqtype) (s:set a) (x:a) : set a =
  s @ [x]
  
let (⊕) #a s x = add_set #a s x

let subset_set (#a:eqtype) (s0:set a) (s1:set a) : bool =
  s0 `subset` s1
let (⊆) #a = subset_set #a

let union_set (#a:eqtype) (s0:set a) (s1:set a) : set a =
  s0 @ s1

let __test_set1 : set int = (((return_set 1) ⊕ 2) ⊕ 2) ⊕ 4
let _ = assert (make_uniq_val 1 2 ∈ __test_set1 /\ make_uniq_val 2 2 ∈ __test_set1)

[@expect_failure]
let _ = assert (make_uniq_val 3 2 ∈ __test_set1)
[@expect_failure]
let _ = assert (make_uniq_val 0 2 ∈ __test_set1)
let _ = assert (make_uniq_val 0 2 ∉ __test_set1)

let __test_mem =
  assert (exists (id1 id2:uniq_val_id). make_uniq_val id1 2 ∈ __test_set1 /\ id1 <= id2 /\ make_uniq_val id2 2 ∈ __test_set1)

let _ = assert (exists (id1 id2:uniq_val_id). id1 <= id2 /\ 
                      make_uniq_val id1 1 ∈ __test_set1 /\
                      make_uniq_val (id1+1) 2 ∈ __test_set1 /\
                      make_uniq_val id2 2 ∈ __test_set1 /\
                      make_uniq_val (id2+1) 4 ∈ __test_set1)

let _ = assert (__test_set1 `subset_set` __test_set1)
let __test_set2 = __test_set1 `union_set` __test_set1
let _ = assert (__test_set1 `subset_set` __test_set2)

(** *** Relation **)

type relation = list (uniq_val_id * uniq_val_id)

let empty_rel (#a:eqtype) (s:set a) : relation = []

//  fold_left (fun (x:relation) _ -> let l = length x in x @ [(l,l)]) [] s

let extend_rel
  (#a:eqtype)
  (s:set a)
  (rel:relation)
  (ev1:uniq_val_id{ev1 < length s})
  (ev2:uniq_val_id{ev2 < length s})
  : relation = rel @ [(ev1, ev2)]

(** *** Data structure **)
type th_id : eqtype = int
type event a = option a
type elem0 (a:eqtype) = th_id * event a
type elem (a:eqtype) = uniq_val (elem0 a)

let get_id (x:elem 'a) : th_id = fst (snd x)

let make_elem (#a:eqtype) (v:elem0 a) (id:uniq_val_id) : elem a = make_uniq_val id v

type poset0 (a:eqtype) =
  set (elem0 a)       (** set **)
  *
  relation   (** partial order between elements **) 
  *
  option (elem a)  (** the least element **)
  *
  (th_id -> option uniq_val_id) (** the maximal elements, one for each thread not awaited **)
  *
  list (th_id * uniq_val_id)

type poset (a:eqtype) =
  p:(poset0 a){
    let (s, rel, least, maxs, urel) = p in
    let (≼) = fun x y -> fst x == fst y \/ (fst x, fst y) `memP` rel in

    (** poset properties **)
    (forall x. x ∈ s ==> x ≼ x) /\
    (forall x y z. x ∈ s /\ y ∈ s /\ z ∈ s ==> (x ≼ y /\ y ≼ z ==> x ≼ z)) /\
    (forall x y. x ∈ s /\ y ∈ s ==> (x ≼ y /\ y ≼ x ==> x == y)) /\

    (** property of the least element **)
    (None? least <==> s == []) /\
    (s <> [] ==> Some? least /\ (Some?.v least ∈ s /\ (forall x. x ∈ s ==> Some?.v least ≼ x))) /\

    (** each element of the maxs function is a maximal element **)
    (forall (tid:th_id). match maxs tid with
      | Some max -> (max < length s /\ tid == fst (index s max))
      | _ -> True) /\

    (** the maxs function captures all maximal elements **)
    (forall (x:elem a). (x ∈ s /\ (forall (y:elem a). y ∈ s /\ get_id x == get_id y ==> ~(x ≼ y ))) ==>
      (maxs (get_id x) == Some (fst x))) /\

    (s <> [] ==> (Some? (maxs (get_id (Some?.v least))))) /\

    (** urel properties **)
    (forall tid x. (tid, x) `memP` urel ==> (None? (maxs tid)) /\ x < length s)
}

let empty_poset (#a:eqtype) : poset a = (empty_set, empty_rel (empty_set #a), None, (fun _ -> None), [])

let return_poset (el0:elem0 'a) : poset 'a =
  let s = return_set el0 in
  let el = make_elem el0 0 in
  let maxs : th_id -> option uniq_val_id = (fun tid -> if tid = (fst el0) then Some 0 else None) in
  (s, empty_rel s, Some el, maxs, [])

let new_po
  (s1:set (elem0 'e))
  (rel1:relation)
  (s2:set (elem0 'e))
  (rel2:relation)
  (least1 : option (elem 'e))
  (least2 : option (elem 'e))
  (maxs1 : th_id -> option uniq_val_id)
  (urel2 : list (th_id * uniq_val_id))
  (_:squash (Some? least2 /\ Some? least1 /\ Some? (maxs1 (get_id (Some?.v least1)))))
  : relation = 
  let n = length s1 in
  rel1 @ 
  (map #_ #(uniq_val_id * uniq_val_id) (fun (x:(uniq_val_id*uniq_val_id)) -> (fst x+n, snd x+n)) rel2) @ 
  [((Some?.v (maxs1 (get_id (Some?.v least1)))), (n + fst (Some?.v least2)))] @
  (map (fun (x:th_id*uniq_val_id) -> let (tid, eid) = x in 
                                   assume (Some? (maxs1 tid)); 
                                   (Some?.v (maxs1 tid), (n+eid<:uniq_val_id)))
    (filter (fun (x:th_id*uniq_val_id) -> Some? (maxs1 (fst x))) urel2))

unfold let (let?) (x: option 'a) (f: 'a -> option 'b): option 'b
  = match x with
  | Some x -> f x
  | None   -> None

let new_maxs 
  (maxs1 : th_id -> option uniq_val_id)
  (n : nat)
  (maxs2 : th_id -> option uniq_val_id)
  : th_id -> option uniq_val_id = 
  (fun tid -> 
    let x = (
      let? x = maxs2 tid in Some ((x+n)<:uniq_val_id)) in
    if Some? x then x
    else (let? x = maxs1 tid in Some x))

let new_urel
  (maxs1 : th_id -> option uniq_val_id)
  (urel1 : list (th_id * uniq_val_id))
  (urel2 : list (th_id * uniq_val_id))
  : list (th_id * uniq_val_id) =
  filter (fun (tid,_) -> not (Some? (maxs1 tid))) (urel1@urel2)

let lemma_new_urel
  (maxs1 : th_id -> option uniq_val_id)
  (urel1 : list (th_id * uniq_val_id))
  (urel2 : list (th_id * uniq_val_id))
  (maxs : th_id -> option uniq_val_id)
  (s : set (elem0 'e)) :
  Lemma (
    let urel = new_urel maxs1 urel1 urel2 in
    (forall tid x. (tid, fst x) `memP` urel ==> (None? (maxs tid)) /\ x ∈ s )) = admit ()

let concat_poset (pos1:poset 'e) (pos2:poset 'e) : poset 'e =
  let (s1, rel1, least1, maxs1, urel1)  = pos1 in
  let (s2, rel2, least2, maxs2, urel2) = pos2 in
  match least1, least2 with
  | None, None
  | None, _ -> pos2
  | _, None -> pos1
  | _, _ -> begin
    let n = length s1 in
    let s = s1 `union_set` s2 in
    let rel : relation = new_po s1 rel1 s2 rel2 least1 least2 maxs1 urel2 () in
    let least : option (elem 'e) = least1 in
    let maxs = new_maxs maxs1 n maxs2 in
    let urel = new_urel maxs1 urel1 urel2 in
    let p : poset0 'e = (s, rel, least, maxs, urel) in

    let (≼) = fun x y -> fst x == fst y \/ (fst x, fst y) `memP` rel in

    (** poset properties **)
    assert (forall x. x ∈ s ==> x ≼ x);
    admit ();
    assert (forall x y z. x ∈ s /\ y ∈ s /\ z ∈ s ==> (x ≼ y /\ y ≼ z ==> x ≼ z));
    assert (forall x y. x ∈ s /\ y ∈ s ==> (x ≼ y /\ y ≼ x ==> x == y));


    (** property of the least element **)
    assert (None? least <==> s == []);
    assert (s <> [] ==> Some? least /\ (Some?.v least ∈ s /\ (forall x. x ∈ s ==> Some?.v least ≼ x)));

    (** each element of the maxs function is a maximal element **)
    assert (forall (tid:th_id). match maxs tid with
      | Some max -> (max < length s /\ tid == fst (index s max))
      | _ -> True);

    (** the maxs function captures all maximal elements **)
    assert (forall (x:elem 'e). (x ∈ s /\ (forall (y:elem 'e). y ∈ s /\ get_id x == get_id y ==> ~(x ≼ y ))) ==>
      (maxs (get_id x) == Some (fst x)));

    assert (s <> [] ==> (Some? (maxs (get_id (Some?.v least)))));

    (** urel properties **)
    lemma_new_urel maxs1 urel1 urel2 maxs s;
    assert (forall tid x. (tid, x) `memP` urel ==> (None? (maxs tid)) /\ x < length s);
  
    p
  end

(**
let subset_poset (#n #m:nat) (pos1:poset 'e) (pos2:poset 'e) : Type0 =
  let (s1, rel1, least1, _, _) = pos1 in
  let (s2, rel2, least2, _, _) = pos2 in
  s1 `subset_set` s2 /\
  (forall x y. x ∈ s1 /\ y ∈ s1 /\ x `rel1` y ==> x `rel2` y)
**)

let op (#a:eqtype) (tid:th_id) (e:a) : poset a =
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
let async (#a:eqtype) (tid:th_id) (p:poset a) :
  Pure (poset a) 
    (requires (let (_, _, _, maxs, _) = p in None? (maxs tid)))
    (ensures (fun _ -> True)) = 
  let cp = return_poset (tid, None) in 
  let (s, rel, least, maxs, urel) = p in
  let urel' = if Some? least then (tid, fst (Some?.v least))::urel else urel in
  let p' : poset a = (s, rel, least, maxs, urel') in
  cp `concat_poset` p'


let await (#e:eqtype) (tid:th_id) (wid:th_id{wid <> tid}) : poset e =
  let (s, rel, least, maxs, urel) = return_poset (tid, None) in
  (s, rel, least, maxs, [(wid, fst (Some?.v least))])

(** *** Tests **)
let prog01 () : poset int = op 1 1 `concat_poset` (op 1 2 `concat_poset` op 1 3)

#set-options "--timing"
let __test_prog01 () = 
  let (s, rel, least, maxs, urel) = prog01 () in
  assert (Some? least /\ Some?.v least == make_uniq_val 0 (1, Some 1));
  assert (urel == []);
  assert (forall tid. tid <> 1 ==> None? (maxs tid));
  assert (Some? (maxs 1) /\ Some?.v (maxs 1) == 2);
  assert (make_uniq_val 0 (1, Some 1) ∈ s);
  assert (make_uniq_val 1 (1, Some 2) ∈ s);
  assert (make_uniq_val 2 (1, Some 3) ∈ s);
  let (≼) = fun x y -> fst x == fst y \/ (fst x, fst y) `memP` rel in
  assert (make_uniq_val 0 (1, Some 1) ≼ make_uniq_val 1 (1, Some 2));
  assert (make_uniq_val 0 (1, Some 1) ≼ make_uniq_val 2 (1, Some 3));
  assert (~(make_uniq_val 1 (1, Some 2) ≼ make_uniq_val 0 (1, Some 1)));
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
