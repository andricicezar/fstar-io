module Util

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc

(** Properties of prefix and suffix on lists *)

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

let suffix_of #a (p l : list a) =
  p == l \/ p `strict_suffix_of` l

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

let rec strict_prefix_length #a (s l : list a) :
  Lemma (ensures s `strict_prefix_of` l ==> length s < length l) (decreases l)
= match l with
  | [] -> ()
  | x :: l ->
    match s with
    | [] -> ()
    | y :: s -> strict_prefix_length s l

let prefix_length #a (s l : list a) :
  Lemma
    (requires s `prefix_of` l)
    (ensures length s <= length l)
= strict_prefix_length s l

let rec strict_prefix_append_one #a (p : list a) x :
  Lemma (ensures p `strict_prefix_of` (p @ [x])) (decreases p)
= match p with
  | [] -> ()
  | y :: q -> strict_prefix_append_one q x

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

let rec strict_prefix_of_append #a (p q r : list a) :
  Lemma (ensures p `strict_prefix_of` q ==> (r @ p) `strict_prefix_of` (r @ q)) (decreases r)
= match r with
  | [] -> ()
  | x :: r' -> strict_prefix_of_append p q r'

let prefix_of_append_left #a (p q r : list a) :
  Lemma
    (requires p `prefix_of` q)
    (ensures (r @ p) `prefix_of` (r @ q ))
= strict_prefix_of_append p q r

let rec prefix_of_append_one #a (s l : list a) x :
  Lemma (s `prefix_of` (l @ [ x ]) ==> s `prefix_of` l \/ s == l @ [ x ])
= assert (~ (l @ [x] == [])) ;
  assert (s `prefix_of` (l @ [ x ]) ==> s == l @ [x] \/ s `strict_prefix_of` (l @ [ x ])) ;
  match l with
  | [] -> ()
  | y :: l' ->
    begin match s with
    | z :: s' -> prefix_of_append_one s' l' x
    | [] -> ()
    end

(** [l `list_minus` l'] return [Some r] when [l == l' @ r] and [None]
    otherwise.
*)
let rec list_minus (#a : eqtype) (l l' : list a) : option (list a) =
  match l with
  | [] ->
    begin match l' with
    | [] -> Some []
    | y :: l' -> None
    end
  | x :: l ->
    begin match l' with
    | [] -> None
    | y :: l' ->
      if x = y
      then l `list_minus` l'
      else None
    end

let rec list_minus_smaller (#a : eqtype) (l l' : list a) :
  Lemma (forall r. l `list_minus` l' == Some r ==> (l == [] /\ l' == []) \/ r << l)
= match l with
  | [] -> ()
  | x :: l ->
    begin match l' with
    | [] -> ()
    | y :: l' ->
      if x = y
      then list_minus_smaller l l'
      else ()
    end

let rec list_minus_Some (#a : eqtype) (l l' : list a) :
  Lemma (forall r. l `list_minus` l' == Some r ==> l == l' @ r)
= match l with
  | [] -> ()
  | x :: l ->
    begin match l' with
    | [] -> ()
    | y :: l' ->
      if x = y
      then list_minus_Some l l'
      else ()
    end

(** flatten but with sep after each cons *)

let rec flatten_sep #a (sep : list a) (l : list (list a)) : list a =
  match l with
  | [] -> []
  | x :: r -> x @ sep @ flatten_sep sep r

let rec flatten_sep_append #a (sep : list a) (l r : list (list a)) :
  Lemma (flatten_sep sep (l @ r) == flatten_sep sep l @ flatten_sep sep r)
= match l with
  | [] -> ()
  | x :: l ->
    flatten_sep_append sep l r ;
    forall_intro_3 (append_assoc #a)

let flatten_sep_nil #a (sep : list a) :
  Lemma (flatten_sep sep [] == [])
= ()

(** mem property *)

let rec mem_append (#a : eqtype) l r (x : a) :
  Lemma (mem x (l @ r) == (mem x l || mem x r))
= match l with
  | [] -> ()
  | hd :: tl -> if hd = x then () else mem_append tl r x

(** Minimal version of indefinite description for natural numbers *)

let indefinite_description_ghost_nat_min (p : (nat -> prop) { exists n. p n }) :
  GTot (n : nat { p n /\ (forall m. m < n ==> ~ (p m)) })
= let bound = indefinite_description_ghost nat p in
  let rec aux (x : nat { x <= bound }) :
    Ghost nat (requires forall m. m < bound - x ==> ~ (p m)) (ensures fun n -> p n /\ (forall m. m < n ==> ~ (p m)))
  = if x = 0
    then bound
    else begin
      if strong_excluded_middle (p (bound - x))
      then bound - x
      else aux (x - 1)
    end
  in aux bound

(** Properties of index *)

let rec index_append_left #a (l1 l2 : list a) (n : nat) :
  Lemma
    (requires n < length l1 /\ n < length (l1 @ l2))
    (ensures index (l1 @ l2) n == index l1 n)
= if n = 0
  then ()
  else index_append_left (tl l1) l2 (n-1)

let rec index_append_right #a (l1 l2 : list a) (n : nat) :
  Lemma
    (requires n >= length l1 /\ n < length (l1 @ l2))
    (ensures index (l1 @ l2) n == index l2 (n - length l1))
= match l1 with
  | [] -> ()
  | x :: l1' ->
    begin if n = 0
      then ()
      else index_append_right l1' l2 (n-1)
    end

let index_append #a (l1 l2 : list a) (i : nat) :
  Lemma (i < length (l1 @ l2) ==> index (l1 @ l2) i == (if i < length l1 then index l1 i else index l2 (i - length l1)))
= if i < length l1
  then index_append_left l1 l2 i
  else if i < length (l1 @ l2)
  then index_append_right l1 l2 i
  else ()

(** Properties on splitAt *)

let firstn #a (n : nat) (l : list a) =
  fst (splitAt n l)

let skipn #a (n : nat) (l : list a) =
  snd (splitAt n l)

let rec splitAt_eq #a (n : nat) (l : list a) :
  Lemma (l == firstn n l @ skipn n l)
= match n, l with
  | 0, _ -> ()
  | _, [] -> ()
  | _, _ :: l' -> splitAt_eq (n - 1) l'

let rec lemma_firstn_length (#a:Type) (n : nat) (l : list a) :
  Lemma
    (requires n <= length l)
    (ensures length (firstn n l) = n)
= match n, l with
  | 0, _ -> ()
  | _, [] -> ()
  | _, _ :: l' -> lemma_firstn_length (n - 1) l'

let rec index_firstn #a (n : nat) (l : list a) :
  Lemma (forall i. n <= length l ==> i < n ==> i < length (firstn n l) ==> index (firstn n l) i == index l i)
= match n, l with
  | 0, _ -> ()
  | _, [] -> ()
  | _, _ :: l' -> index_firstn (n - 1) l'

let rec splitAt_append_left #a (n : nat) (l1 l2 : list a) :
  Lemma
    (requires n <= length l1)
    (ensures splitAt n (l1 @ l2) == (firstn n l1, skipn n l1 @ l2))
= match n, l1 with
  | 0, _ -> ()
  | _, [] -> ()
  | _, _ :: l' -> splitAt_append_left (n - 1) l' l2

let firstn_append_left #a (n : nat) (l1 l2 : list a) :
  Lemma
    (requires n <= length l1)
    (ensures firstn n (l1 @ l2) == firstn n l1)
= splitAt_append_left n l1 l2

let skipn_append_left #a (n : nat) (l1 l2 : list a) :
  Lemma
    (requires n <= length l1)
    (ensures skipn n (l1 @ l2) == skipn n l1 @ l2)
= splitAt_append_left n l1 l2

let rec splitAt_append_right #a (n : nat) (l1 l2 : list a) :
  Lemma
    (requires n >= length l1)
    (ensures splitAt n (l1 @ l2) == (l1 @ firstn (n - length l1) l2, skipn (n - length l1) l2))
= match n, l1 with
  | 0, _ -> ()
  | _, [] -> ()
  | _, _ :: l' -> splitAt_append_right (n - 1) l' l2

let firstn_append_right #a (n : nat) (l1 l2 : list a) :
  Lemma
    (requires n >= length l1)
    (ensures firstn n (l1 @ l2) == l1 @ firstn (n - length l1) l2)
= splitAt_append_right n l1 l2

let skipn_append_right #a (n : nat) (l1 l2 : list a) :
  Lemma
    (requires n >= length l1)
    (ensures skipn n (l1 @ l2) == skipn (n - length l1) l2)
= splitAt_append_right n l1 l2

let firstn_all #a (n : nat) (l : list a) :
  Lemma (requires n >= length l) (ensures firstn n l == l)
= calc (==) {
    firstn n l ;
    == {}
    firstn n (l @ []) ;
    == { firstn_append_right n l [] }
    l @ firstn (n - length l) [] ;
    == {}
    l ;
  }
