module Pure_Free

open FStar.Tactics
open FStar.List.Tot.Base

type w_post (a:Type) = a -> Type0
type w_pre = Type0

type w0 (a:Type) = w_post a -> w_pre

unfold
let w_post_ord (#a:Type) (p1 p2:w_post a) = forall (r:a). p1 r ==> p2 r

let w_monotonic (#a:Type) (wp:w0 a) =
  forall (p1 p2:w_post a). (p1 `w_post_ord` p2) ==> (wp p1 ==> wp p2)

type w (a:Type) = wp:(w0 a){w_monotonic wp}

unfold
let w_ord0 (#a:Type) (wp1:w a) (wp2:w a) = forall (p:w_post a). wp1 p ==> wp2 p

let w_ord = w_ord0
unfold let (⊑) = w_ord

unfold
let w_return0 (#a:Type) (x:a) : w a = fun p -> p x
let w_return = w_return0

unfold
let w_bind0 (#a:Type u#a) (#b:Type u#b) (wp : w a) (kwp : a -> w b) : w b =
  fun (p:w_post b) -> wp (fun (x:a) -> kwp x p)
let w_bind = w_bind0
  
noeq
type free (a:Type u#a) : Type u#(max 1 a) =
| Require : (pre:pure_pre) -> k:((squash pre) -> free u#a a) -> free a
| Return : a -> free a

let free_return (#a:Type) (x:a) : free a =
  Return x

let rec free_bind
  (#a:Type u#a)
  (#b:Type u#b)
  (l : free a)
  (cont : a -> free b) :
  free b =
  match l with
  | Require pre k ->
      Require pre (fun _ -> free_bind (k ()) cont)
  | Return x -> cont x

let w_require (pre:pure_pre) : w (squash pre) = 
  let wp' : w0 (squash pre) = fun p -> pre /\ p () in
  assert (forall (post1 post2:w_post (squash pre)). (w_post_ord post1 post2 ==> (wp' post1 ==> wp' post2)));
  assert (w_monotonic wp');
  wp'

val theta : (#a:Type) -> free a -> w a
let rec theta m =
  match m with
  | Require pre k ->
      w_bind (w_require pre) (fun r -> theta (k r))
  | Return x -> w_return x

let theta_monad_morphism_ret (v:'a) :
  Lemma (theta (free_return v) == w_return v) = ()

let theta_lax_monad_morphism_bind (m:free 'a) (km:'a -> free 'b) :
  Lemma (w_bind (theta m) (fun x -> theta (km x)) ⊑ theta (free_bind m km)) = 
  match m with
  | Return x -> ()
  | Require pre k -> admit ()
      

let dm (a:Type u#a) (wp:w a) =
  m:(free a){wp ⊑ theta m}

let dm_return (a:Type u#a) (x:a) : dm a (w_return0 x) =
  Return x

let dm_bind
  (a:Type u#a)
  (b:Type u#b)
  (wp:w a)
  (kwp:a -> w b)
  (c:dm a wp)
  (kc:(x:a -> dm b (kwp x))) :
  dm b (w_bind0 wp kwp) =
  theta_lax_monad_morphism_bind c kc;
  free_bind c kc

let dm_subcomp
  (a:Type u#a)
  (wp1:w a)
  (wp2:w a)
  (c:dm a wp1) :
  Pure (dm a wp2)
    (requires (wp2 `w_ord0` wp1))
    (ensures (fun _ -> True)) =
    c 

let w_if_then_else (wp1 wp2:w 'a) (b:bool) : w 'a =
  fun p -> (b ==> wp1 p) /\ ((~b) ==> wp2 p)

let dm_if_then_else (a : Type u#a) 
  (wp1 wp2: w a) (f : dm a wp1) (g : dm a wp2) (b : bool) : Type =
  dm a (w_if_then_else wp1 wp2 b)

let dm_partial_return
  (pre:pure_pre) : dm (squash pre) (w_require pre) =
  let m = Require pre (Return) in
  assert (w_require pre ⊑ theta m);
  m

unfold
let lift_pure_w (#a:Type) (wp : pure_wp a) : w a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  wp
  //(fun (p:w_post a) -> wp (fun (r:a) -> p r))

let lift_pure_w_as_requires (#a:Type) (wp : pure_wp a) :
  Lemma (forall (p:w_post a) h. lift_pure_w wp p ==> as_requires wp) =
    assert (forall (p:w_post a) x. p x ==> True) ;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    assert (forall (p:w_post a). wp (fun x -> p x) ==> wp (fun _ -> True))

let lift_pure_dm 
  (a : Type u#a) 
  (wp : pure_wp a)
  (f:(eqtype_as_type unit -> PURE a wp)) : 
  dm a (lift_pure_w wp) =
  lift_pure_w_as_requires #a wp;
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs = dm_partial_return (as_requires wp) in
  let rhs = (fun (pre:(squash (as_requires wp))) -> dm_return a (f ())) in
  let m = dm_bind _ _ _ _ lhs rhs in
  dm_subcomp a _ (lift_pure_w wp) m
  
reflectable
reifiable
total
effect {
  FreeWP (a:Type) (wp : w a)
  with {
       repr       = dm
     ; return     = dm_return
     ; bind       = dm_bind
     ; subcomp    = dm_subcomp
     ; if_then_else = dm_if_then_else
     }
}

sub_effect PURE ~> FreeWP = lift_pure_dm

effect Free
  (a:Type u#a)
  (pre : Type0)
  (post : a -> Pure Type0 (requires pre) (ensures (fun _ -> True))) =
  FreeWP a (fun p -> pre /\ (forall (r:a). post r ==> p r))

(** *** Tests partiality of the effect **)
let test_using_assume (fd:int) : Free int (requires True) (ensures fun r -> fd % 2 == 0) =
  assume (fd % 2 == 0) ;
  fd

// A second test to make sure exfalso isn't used
let test_assume #a #pre (f : unit -> Free a (requires pre) (ensures fun r -> True)) : Free a True (fun r -> True) =
  assume pre ;
  f ()

let test_assert p : Free unit (requires p) (ensures fun r -> True) =
  assert p

let partial_match (l : list nat) : Free unit (requires l <> []) (ensures fun r -> True) =
  match l with
  | x :: r -> ()

let partial_match_io (l : list int) : Free int (requires l <> []) (ensures fun r -> True) =
  match l with
  | s :: _ -> s + 10 

let partial_match_pre (l : list nat) : Free nat (requires l <> []) (ensures fun r -> r == hd l) =
  match l with
  | x :: r -> x

assume val p : prop
assume val p' : prop
assume val pure_lemma (_ : unit) : Lemma p
assume val some_f (_ : squash p) : Free unit (requires True) (ensures fun _ -> True)
assume val some_f' : unit -> Free unit (requires p) (ensures fun _ -> p')

let pure_lemma_test () : Free unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;
  some_f ()

let pure_lemma_test2 () : Free unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;
  some_f () ;
  some_f' () ;
  assert p'


(**** Performance test - Quick Sort from Tutorial **)


//Some auxiliary definitions to make this a standalone example
let rec length #a (l:list a)
  : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl

let rec append #a (l1 l2:list a)
  : list a
  = match l1 with
    | [] -> l2
    | hd :: tl -> hd :: append tl l2

let total_order (#a:Type) (f: (a -> a -> bool)) =
    (forall a. f a a)                                         (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1=!=a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)
    /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                       (* totality *)
let total_order_t (a:Type) = f:(a -> a -> bool) { total_order f }

let rec sorted #a  (f:total_order_t a) (l:list a)
  : bool
  = match l with
    | [] -> true
    | [x] -> true
    | x :: y :: xs -> f x y && sorted f (y :: xs)

//SNIPPET_START: count permutation
let rec count (#a:eqtype) (x:a) (l:list a)
  : nat
  = match l with
    | hd::tl -> (if hd = x then 1 else 0) + count x tl
    | [] -> 0

let mem (#a:eqtype) (i:a) (l:list a)
  : bool
  = count i l > 0

let is_permutation (#a:eqtype) (l m:list a) =
  forall x. count x l = count x m

let rec append_count (#t:eqtype)
                     (l1 l2:list t)
  : Lemma (ensures (forall a. count a (append l1 l2) = (count a l1 + count a l2)))
  = match l1 with
    | [] -> ()
    | hd::tl -> append_count tl l2
//SNIPPET_END: count permutation

let rec partition (#a:Type) (f:a -> bool) (l:list a)
  : x:(list a & list a) { length (fst x) + length (snd x) = length l }
  = match l with
    | [] -> [], []
    | hd::tl ->
      let l1, l2 = partition f tl in
      if f hd
      then hd::l1, l2
      else l1, hd::l2

let rec sort #a (f:total_order_t a) (l:list a)
  : Tot (list a) (decreases (length l))
  = match l with
    | [] -> []
    | pivot :: tl ->
      let hi, lo  = partition (f pivot) tl in
      append (sort f lo) (pivot :: sort f hi)

let rec partition_mem_permutation (#a:eqtype)
                                  (f:(a -> bool))
                                  (l:list a)
  : Lemma (let l1, l2 = partition f l in
           (forall x. mem x l1 ==> f x) /\
           (forall x. mem x l2 ==> not (f x)) /\
           (is_permutation l (append l1 l2)))
  = match l with
    | [] -> ()
    | hd :: tl -> 
      partition_mem_permutation f tl;
      let hi, lo = partition f tl in
      append_count hi lo;
      append_count hi (hd::lo);
      append_count (hd :: hi) lo

let rec sorted_concat (#a:eqtype)
                      (f:total_order_t a)
                      (l1:list a{sorted f l1})
                      (l2:list a{sorted f l2})
                      (pivot:a)
  : Lemma (requires (forall y. mem y l1 ==> not (f pivot y)) /\
                    (forall y. mem y l2 ==> f pivot y))
          (ensures sorted f (append l1 (pivot :: l2)))
  = match l1 with
    | [] -> ()
    | hd :: tl -> sorted_concat f tl l2 pivot

let permutation_app_lemma (#a:eqtype) (hd:a) (tl:list a)
                          (l1:list a) (l2:list a)
   : Lemma (requires (is_permutation tl (append l1 l2)))
           (ensures (is_permutation (hd::tl) (append l1 (hd::l2))))
  = append_count l1 l2;
    append_count l1 (hd :: l2)
  
let rec sort_correct (#a:eqtype) (f:total_order_t a) (l:list a)
  : Lemma (ensures (
           sorted f (sort f l) /\
           is_permutation l (sort f l)))
          (decreases (length l))
  = match l with
    | [] -> ()
    | pivot :: tl ->
      let hi, lo  = partition (f pivot) tl in
      partition_mem_permutation (f pivot) tl;
      append_count lo hi;
      append_count hi lo;
      assert (is_permutation tl (append lo hi));
      sort_correct f hi;
      sort_correct f lo;
      sorted_concat f (sort f lo) (sort f hi) pivot;
      append_count (sort f lo) (sort f hi);
      assert (is_permutation tl (sort f lo `append` sort f hi));
      permutation_app_lemma pivot tl (sort f lo) (sort f hi)
      

#push-options "--fuel 1 --ifuel 1"
let rec pure_sort_intrinsic (#a:eqtype) (f:total_order_t a) (l:list a)
  : Pure (list a)
    (requires True) (ensures (fun m -> sorted f m /\ is_permutation l m))
   (decreases (length l))
  = match l with
    | [] -> []
    | pivot :: tl ->
      let hi, lo  = partition (f pivot) tl in
      partition_mem_permutation (f pivot) tl;
      append_count lo hi;  append_count hi lo;
      sorted_concat f (pure_sort_intrinsic f lo) (pure_sort_intrinsic f hi) pivot;
      append_count (pure_sort_intrinsic f lo) (pure_sort_intrinsic f hi);
      permutation_app_lemma pivot tl (pure_sort_intrinsic f lo) (pure_sort_intrinsic f hi);
      append (pure_sort_intrinsic f lo) (pivot :: pure_sort_intrinsic f hi)

#reset-options
#push-options "--log_queries"
let rec sort_intrinsic (#a:eqtype) (f:total_order_t a) (l:list a)
  : Free (list a)
    (requires True) (ensures (fun m -> sorted f m /\ is_permutation l m))
   (decreases (length l))
  = match l with
    | [] -> []
    | pivot :: tl ->
      let hi, lo  = partition (f pivot) tl in
      partition_mem_permutation (f pivot) tl;
      append_count lo hi;  append_count hi lo;
      sorted_concat f (sort_intrinsic f lo) (sort_intrinsic f hi) pivot;
      append_count (sort_intrinsic f lo) (sort_intrinsic f hi);
      permutation_app_lemma pivot tl (sort_intrinsic f lo) (sort_intrinsic f hi);
      append (sort_intrinsic f lo) (pivot :: sort_intrinsic f hi)
  
