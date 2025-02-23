module CooperativeMultiThreadingWithIndexT

open FStar.List.Tot

let incr (#k:nat) (i:nat{i < k}) : i:nat{i < k} = (i + 1) % k

val update: #a:Type -> l:list a -> i:nat{i < length l} -> x:a -> Tot (list a)
let rec update #a (l: list a) (i:nat{i < length l}) (x : a): Tot (list a) =
  if i = 0 then
    x :: tl l
  else
    hd l :: update (tl l) (i - 1) x

let rec lemma_update_eq_length (#a:Type) (l:list a) (i:nat{i < length l}) (x:a)  : Lemma (length l == length (update l i x)) =
  if i = 0 then
    ()
  else
    lemma_update_eq_length (tl l) (i - 1) x


let rec strict_prefix_of #a (s l : list a) :
  Pure Type0 (requires True) (ensures fun _ -> True) (decreases l)
= match l with
  | [] -> False
  | x :: l ->
    match s with
    | [] -> True
    | y :: s -> x == y /\ s `strict_prefix_of` l

let prefix_of #a (s l : list a) =
  s == l \/ s `strict_prefix_of` l

let rec strict_prefix_of_trans #a (p q r : list a) :
  Lemma (ensures p `strict_prefix_of` q ==> q `strict_prefix_of` r ==> p `strict_prefix_of` r) (decreases p)
= begin match p with
  | [] -> ()
  | x :: p' ->
    begin match q with
    | [] -> ()
    | y :: q' ->
      begin match r with
      | [] -> ()
      | z :: r' -> strict_prefix_of_trans p' q' r'
      end
    end
  end

let rec strict_prefix_or_eq_append #a (s l : list a) :
  Lemma
    (ensures l == [] \/ s `strict_prefix_of` (s @ l))
    (decreases s)
= match s with
  | [] -> ()
  | y :: s -> strict_prefix_or_eq_append s l

let prefix_of_append #a (s l : list a) :
  Lemma (s `prefix_of` (s @ l))
= strict_prefix_or_eq_append s l

let prefix_of_trans #a :
  Lemma (ensures FStar.Preorder.transitive #(list a) prefix_of)
= introduce forall (x:list a) (y:list a) (z:list a). (prefix_of x y /\ prefix_of y z) ==> prefix_of x z with
    introduce (prefix_of x y /\ prefix_of y z) ==> prefix_of x z with pq.
      eliminate x == y \/ x `strict_prefix_of` y
      returns _
      with _ . ()
      and _ . eliminate y == z \/ y `strict_prefix_of` z
              returns _
              with _ . ()
              and _ . strict_prefix_of_trans x y z

let prefix_of_reflexive #a :
  Lemma (ensures FStar.Preorder.reflexive #(list a) prefix_of)
= ()

open SharedRefs

noeq
type atree (r : ref int) (a:Type0) =
  | Return : a -> atree r a
  | Yield : continuation r a -> atree r a
and continuation (r : ref int) a =
  unit -> SST (atree r a)
              (fun h0 -> h0 `contains` r /\ is_shared r h0)
              (fun h0 _ h1 -> modifies_only_shared_and_encapsulated h0 h1 /\ gets_shared Set.empty h0 h1)

let rec get_number_of_steps (tid : int) (hist : list int) =
  match hist with
  | [] -> 0
  | h :: t -> if (h = tid) then 1 + get_number_of_steps tid t else get_number_of_steps tid t

let rec lemma_get_number_of_steps_append_tid (tid : int) (hist : list int) :
  Lemma (ensures get_number_of_steps tid (hist @ [tid]) = get_number_of_steps tid hist + 1) =
  match hist with
  | [] -> ()
  | h :: t -> lemma_get_number_of_steps_append_tid tid t

let rec lemma_get_number_of_steps_append_tid_other (tid : int) (tid' : int) (hist : list int) :
  Lemma (requires ~ (tid == tid')) (ensures get_number_of_steps tid' (hist @ [tid]) == get_number_of_steps tid' hist) =
  match hist with
  | [] -> ()
  | h :: t -> lemma_get_number_of_steps_append_tid_other tid tid' t

let fairness_ticks (limit : int) (ticks : nat) (l : list int) (n : int) =
      (forall (j:int{0 <= j /\ j < n /\ j < limit}). get_number_of_steps j l = ticks + 1)
    /\ (forall (j:int{0 <= j /\ j >= n /\ j < limit}). get_number_of_steps j l = ticks)

let fairness (limit : int) (l : list int) (n : int) =
  exists (ticks : nat) . fairness_ticks limit ticks l n

let mm_fairness (k : int) (l : list int) (tid : int) :
  Lemma (requires (fairness k l tid /\ 0 <= tid /\ tid < k))
        (ensures (fairness k (l @ [tid]) (incr #k tid)))
=
  eliminate exists (ticks : nat) . fairness_ticks k ticks l tid
  returns fairness k (l @ [tid]) (incr #k tid)
  with _ .
    if (tid = k - 1)
    then
      introduce exists (ticks' : nat) . fairness_ticks k ticks' (l @ [tid]) (incr #k tid)
      with (ticks + 1)
      and begin
        introduce forall (j:int{0 <= j /\ j < (incr #k tid)}). get_number_of_steps j (l @ [tid]) = (ticks + 1) + 1 with
          ();
        assert (forall (j:int{0 <= j /\ j < tid}). get_number_of_steps j l = ticks + 1);
        assert (forall (j:int{0 <= j /\ j >= tid /\ j < k}). get_number_of_steps j l = ticks);
        introduce forall (j:int{0 <= j /\ j >= (incr #k tid) /\ j < k}). get_number_of_steps j (l @ [tid]) = ticks + 1 with begin
          eliminate (j = tid) \/ ~(j = tid)
          returns (get_number_of_steps j (l @ [tid]) = ticks + 1)
          with _ .
            lemma_get_number_of_steps_append_tid tid l
          and _.
            lemma_get_number_of_steps_append_tid_other tid j l
        end
      end
    else
      introduce exists (ticks' : nat) . fairness_ticks k ticks' (l @ [tid]) (incr #k tid)
      with ticks
      and begin
        admit ()
        // introduce forall (j:int{0 <= j /\ j < (incr #k tid)}). get_number_of_steps j (l @ [tid]) = ticks + 1 with
        //   assert (j <= tid);
        //   eliminate (j = tid) \/ (j < tid)
        //   returns get_number_of_steps j (l @ [tid]) = ticks + 1
        //   with _.
        //     lemma_get_number_of_steps_append tid l
        //   and _. admit ()
      end

type counter (k : int) = (hist:(list int) & next:int & inactive:int{fairness k hist next /\ 0 <= next /\ next < k /\ 0 <= inactive /\ inactive <= k})

let counter_preorder k : FStar.Preorder.preorder (counter k) =
  let order = fun (v : counter k) (v' : counter k) -> prefix_of v._1 v'._1 in
  prefix_of_trans #int;
  prefix_of_reflexive #int;
  order

#push-options "--split_queries always"
let rec scheduler
  (fuel:nat)
  (r : ref int)
  (tasks:list (continuation r unit))
  (counter_mref : mref (counter (length tasks)) (counter_preorder (length tasks)))
  : SST unit
    (requires (fun h0 -> h0 `contains` counter_mref /\ is_private counter_mref h0 /\ h0 `contains` r /\ is_shared r h0))
    (ensures (fun h0 _ h1 -> gets_shared Set.empty h0 h1)) =
  let counter_st = sst_read' counter_mref in
  let hist = counter_st._1 in
  let i = counter_st._2 in
  let inactive = counter_st._3 in
  if fuel = 0 || inactive >= length tasks then ()
  else begin
  let tmp = sst_alloc #int #(FStar.Heap.trivial_preorder _) inactive in
  let k = index tasks i () in
  let k' : unit -> SST (atree r unit) (fun h0 -> h0 `contains` r /\ is_shared r h0) (fun h0 _ h1 -> modifies_only_shared_and_encapsulated h0 h1 /\ gets_shared Set.empty h0 h1) =
    match k with
    | Return x ->
      let () = sst_write_ref tmp (inactive + 1) in
      fun () -> Return x
    | Yield k ->
      let () = sst_write_ref tmp 0 in
      k
  in
  let inactive' = sst_read tmp in
  let tasks' = update tasks i k' in
  lemma_update_eq_length tasks i k';
  mm_fairness (length tasks) hist i;
  let counter_st' : counter (length tasks) = (| hist @ [i], (incr #(length tasks') i), inactive' |) in
  prefix_of_append hist [i];
  assert (prefix_of hist (hist @ [i]));
  assert (counter_preorder _ counter_st counter_st');
  let () = sst_write counter_mref counter_st' in
  scheduler (fuel-1) r tasks' counter_mref
  end
#pop-options

let lemma_get_number_of_steps_empty (tid : int) : Lemma (ensures get_number_of_steps tid [] = 0) = ()

let fairness_init (k : int) : Lemma (ensures fairness k [] 0) =
  introduce forall (j:int{0 <= j /\ j < 0}). get_number_of_steps j [] = 0 + 1 with
  ();
  introduce forall (j:int{0 <= j /\ j >= 0}). get_number_of_steps j [] = 0 with
  ();
  introduce exists (ticks : nat) . (forall (j:int{0 <= j /\ j < 0}). get_number_of_steps j [] = ticks + 1) /\ (forall (j:int{0 <= j /\ j >= 0}). get_number_of_steps j [] = ticks)
  with 0
  and ();
  ()

let run (tasks: list (r:ref int -> continuation r unit){length tasks > 0}) :
  SST unit (requires (fun h0 -> True)) (ensures (fun _ _ _ -> True)) =
  fairness_init (length tasks);
  let counter_init : counter (length tasks) = (| [], 0, 0 |) in
  let counter_mref = sst_alloc #_ #(counter_preorder (length tasks)) counter_init in
  let s = sst_alloc_shared 42 in
  let tasks = map (fun (f : (r:ref int) -> continuation r unit) -> f s) tasks in
  scheduler 5000 s tasks counter_mref

let res_a (r : ref int) : continuation r unit = fun () ->
  let () = sst_write_ref r 42 in
  Return ()

let res_b (r : ref int) : continuation r unit = fun () ->
  let j = sst_read r in
  let m = sst_alloc #int #(FStar.Heap.trivial_preorder _) 42 in
  Yield (fun () -> let () = sst_write r j in Return ())

let mm () : SST unit (requires (fun _ -> True)) (ensures (fun _ _ _ -> True)) = run [res_a; res_b]
