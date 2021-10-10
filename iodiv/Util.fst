module Util

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc

(** Similar to strict_prefix_of, but the opposite.

    I believe the names should be swapped but well...
*)
let rec strict_suffix_of #a (s l : list a) :
  Pure Type0 (requires True) (ensures fun _ -> True) (decreases l)
= match l with
  | [] -> False
  | x :: l ->
    match s with
    | [] -> True
    | y :: s -> x == y /\ s `strict_suffix_of` l

let rec strict_suffix_or_eq_append #a (s l : list a) :
  Lemma
    (ensures l == [] \/ s `strict_suffix_of` (s @ l))
    (decreases s)
= match s with
  | [] -> ()
  | y :: s -> strict_suffix_or_eq_append s l

let rec strict_suffix_length #a (s l : list a) :
  Lemma (ensures s `strict_suffix_of` l ==> length s < length l) (decreases l)
= match l with
  | [] -> ()
  | x :: l ->
    match s with
    | [] -> ()
    | y :: s -> strict_suffix_length s l

let rec strict_suffix_append_one #a (p : list a) x :
  Lemma (ensures p `strict_suffix_of` (p @ [x])) (decreases p)
= match p with
  | [] -> ()
  | y :: q -> strict_suffix_append_one q x

let rec strict_suffix_of_trans #a (p q r : list a) :
  Lemma (ensures p `strict_suffix_of` q ==> q `strict_suffix_of` r ==> p `strict_suffix_of` r) (decreases p)
= begin match p with
  | [] -> ()
  | x :: p' ->
    begin match q with
    | [] -> ()
    | y :: q' ->
      begin match r with
      | [] -> ()
      | z :: r' -> strict_suffix_of_trans p' q' r'
      end
    end
  end

let rec strict_suffix_of_append #a (p q r : list a) :
  Lemma (ensures p `strict_suffix_of` q ==> (r @ p) `strict_suffix_of` (r @ q)) (decreases r)
= match r with
  | [] -> ()
  | x :: r' -> strict_suffix_of_append p q r'

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
