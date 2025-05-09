module CooperativeMultiThreadingWithIndexTShareableTyp

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

let lemma_prefix_of_append #a (s l : list a) :
  Lemma (s `prefix_of` (s @ l))
= strict_prefix_or_eq_append s l

open LabeledRefs

noeq
type atree (#t:shareable_typ) (r : ref (to_Type t)) (a:Type0) =
  | Return : a -> atree r a
  | Yield : continuation r a -> atree r a
and continuation (#t:shareable_typ) (r : ref (to_Type t)) a =
  unit -> SST (atree r a)
              (requires (fun _ -> witnessed (contains_pred r) /\ witnessed (is_shared r)))
              (ensures (fun h0 _ h1 -> modifies_only_shared_and_encapsulated h0 h1 /\ gets_shared Set.empty h0 h1))

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

let lemma_fairness_step (k : int) (l : list int) (tid : int) :
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
        introduce forall (j:int{0 <= j /\ j < (incr #k tid)}). get_number_of_steps j (l @ [tid]) = ticks + 1 with begin
          assert (j <= tid);
          eliminate (j = tid) \/ (j < tid)
          returns get_number_of_steps j (l @ [tid]) = ticks + 1
          with _.
            lemma_get_number_of_steps_append_tid tid l
          and _.
            lemma_get_number_of_steps_append_tid_other tid j l
        end;
        introduce forall (j:int{0 <= j /\ j >= (incr #k tid) /\ j < k}). get_number_of_steps j (l @ [tid]) = ticks with begin
          assert (j > tid);
          lemma_get_number_of_steps_append_tid_other tid j l
        end
      end

type counter_state (k : int) = hist:(list int) & next:int & inactive:int{fairness k hist next /\ 0 <= next /\ next < k /\ 0 <= inactive /\ inactive <= k}

let counter_preorder k : FStar.Preorder.preorder (counter_state k) =
  let order = fun (v : counter_state k) (v' : counter_state k) -> prefix_of v._1 v'._1 in
  prefix_of_trans #int;
  prefix_of_reflexive #int;
  order

let counter_t k = mref (counter_state k) (counter_preorder k)

let fairness_init (k : int) : Lemma (ensures fairness k [] 0) =
  introduce forall (j:int{0 <= j /\ j < 0}). get_number_of_steps j [] = 0 + 1 with
  ();
  introduce forall (j:int{0 <= j /\ j >= 0}). get_number_of_steps j [] = 0 with
  ();
  introduce exists (ticks : nat) . (forall (j:int{0 <= j /\ j < 0}). get_number_of_steps j [] = ticks + 1) /\ (forall (j:int{0 <= j /\ j >= 0}). get_number_of_steps j [] = ticks)
  with 0
  and ();
  ()

#push-options "--split_queries always"
let rec scheduler (fuel:nat) (#t:shareable_typ) (r : ref (to_Type t)) (tasks:list (continuation r unit)) (counter:counter_t (length tasks))
  : SST unit
    (requires (fun h0 -> h0 `contains` counter /\ is_private counter h0 /\ h0 `contains` r /\ is_shared r h0))
    (ensures (fun h0 _ h1 -> modifies_shared_and_encapsulated_and h0 h1 (Set.singleton (addr_of counter)) /\ gets_shared Set.empty h0 h1)) 
=
  witness (contains_pred r);
  witness (is_shared r);
  let counter_st = sst_read counter in
  let hist = counter_st._1 in
  let i = counter_st._2 in
  let inactive = counter_st._3 in
  if fuel = 0 || inactive >= length tasks then ()
  else begin
  match index tasks i () with
  | Return x ->
    let inactive' = inactive + 1 in
    let k' : unit -> SST (atree r unit) (fun _ -> witnessed (contains_pred r) /\ witnessed (is_shared r)) (fun h0 _ h1 -> modifies_only_shared_and_encapsulated h0 h1 /\ gets_shared Set.empty h0 h1) =
      fun () -> Return x in
    let tasks' = update tasks i k' in
    lemma_update_eq_length tasks i k';
    lemma_fairness_step (length tasks) hist i;
    lemma_prefix_of_append hist [i];
    let counter_st' : counter_state (length tasks) = (| hist @ [i], (incr #(length tasks') i), inactive' |) in
    let () = sst_write counter counter_st' in
    scheduler (fuel-1) r tasks' counter
  | Yield k' ->
    let inactive' = 0 in
    let tasks' = update tasks i k' in
    lemma_update_eq_length tasks i k';
    lemma_fairness_step (length tasks) hist i;
    lemma_prefix_of_append hist [i];
    let counter_st' : counter_state (length tasks) = (| hist @ [i], (incr #(length tasks') i), inactive' |) in
    let () = sst_write counter counter_st' in
    scheduler (fuel-1) r tasks' counter
  end
#pop-options

let counter_init (k : nat{k > 0}) : counter_state k = fairness_init k; (| [], 0, 0 |)

let run (fuel : nat) (#t:shareable_typ) (init:to_Type t) (tasks:list (r:ref (to_Type t) -> continuation r unit){length tasks > 0}) :
  SST (to_Type t) 
    (requires (fun h0 -> 
      forall_refs_heap contains_pred h0 init /\ 
      forall_refs_heap is_shared h0 init)) 
    (ensures (fun h0 _ h1 -> True)) =
  let counter = sst_alloc #_ #(counter_preorder _) (counter_init (length tasks)) in
  let s : ref (to_Type t) = sst_alloc_shared init in
  let tasks = map (fun (f : (r:ref (to_Type t)) -> continuation r unit) -> f s) tasks in
  scheduler fuel s tasks counter;
  sst_read s
  
let res_a (r : ref int) : continuation r unit = fun () ->
  recall (contains_pred r);
  recall (is_shared r);
  let () = sst_write_ref r 42 in
  Return ()

let res_b (r : ref int) : continuation r unit = fun () ->
  recall (contains_pred r);
  recall (is_shared r);
  let j = sst_read r in
  let m = sst_alloc #int #(FStar.Heap.trivial_preorder _) 42 in
  Yield (fun () ->
    recall (contains_pred r);
    recall (is_shared r);
    let () = sst_write r j in
    Return ())

let nmm () : SST int (requires (fun _ -> True)) (ensures (fun _ _ _ -> True)) = run 5000 0 [res_a; res_b]
