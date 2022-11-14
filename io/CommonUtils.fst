module CommonUtils

open FStar.Monotonic.Pure
open FStar.Exn
open FStar.Tactics
open FStar.List.Tot

include UnixTypes

exception Contract_failure

type zfile_perm = int

type lfds = (list file_descr) //{List.no_repeats_p l})

let list_subset_of_list (l1:lfds) (l2:lfds) : Type0 =
  (forall x. (List.memP x l2) ==>  (List.memP x l1))

type resexn a = either a exn

let compose #a #b #c (g:b->c) (f:a->b) = fun x -> g (f x)

let id #a (x:a) = x

unfold let inl_app #a #b (f:a -> b) : resexn a -> resexn b =
  fun x ->
    match x with
    | Inl x -> Inl (f x)
    | Inr err -> Inr err

let cdr #a (_, (x:a)) : a = x

let elim_pure #a #wp ($f : unit -> PURE a wp) p
 : Pure a (requires (wp p)) (ensures (fun r -> p r))
  //: PURE a (fun p' -> wp p /\ (forall r. p r ==> p' r))
   // ^ basically this, requires monotonicity
 = FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
   f ()

let suffix_of (l1 l2: list 'a)
: Tot Type0 (decreases l2)
= l1 == l2 \/ l1 `strict_suffix_of` l2

let suffix_of_length (l1 l2: list 'a)
: Lemma
  (requires (suffix_of l1 l2))
  (ensures (List.length l1 <= List.length l2))
  (decreases l2) = admit ()


val rev_nil : (a:Type) -> Lemma (List.rev #a [] == [])
let rev_nil a = ()

val append_rev: l1:list 'a -> l2:list 'a ->
  Lemma (
    ((List.rev l1)@(List.rev l2)) == (List.rev (l2@l1)))
let append_rev l1 l2 = List.rev_append l2 l1

let rev_head_append
  (h:list 'a)
  (e:'a)
  (l:list 'a) :
  Lemma
    ((List.rev (e::l) @ h) == (List.rev l @ (e::h))) = admit ()
  

let rec lemma_splitAt_equal (n:nat) (l:list 'a) :
  Lemma
    (requires (n <= List.length l))
    (ensures (
      let b0, b1 = List.Tot.Base.splitAt n l in
      b0 @ b1 == l)) = 
  match n, l with
  | 0, _ -> ()
  | _, x::xs -> lemma_splitAt_equal (n-1) xs

let lemma_splitAt_equal_length (l l':list 'a) :
  Lemma
    (requires (l' `suffix_of` l /\ List.length l == List.length l'))
    (ensures (l == l')) =
  assume (~(l == l'));
  match l with
  | [] -> ()
  | _ :: xs -> 
    assert (l' `suffix_of` xs);
    suffix_of_length l' xs;
    assert (List.length xs < List.length l')

let rec lemma_splitAt_suffix (l l':list 'a) :
  Lemma
    (requires (l' `suffix_of` l))
    (ensures (
      suffix_of_length l' l;
      let _, b1 = List.Tot.Base.splitAt (List.length l - List.length l') l in
      b1 == l')) =
  suffix_of_length l' l;
  let n:nat = List.length l - List.length l' in
  match n, l with
  | 0, _ -> lemma_splitAt_equal_length l l'
  | _, x::xs -> lemma_splitAt_suffix xs l'

let rec lemma_suffixOf_append (l l':list 'a) :
  Lemma (l `suffix_of` (l' @ l)) =
  match l' with
  | [] -> ()
  | x::xs -> lemma_suffixOf_append l xs

let lemma_rev_rev_equal (l l':list 'a) :
  Lemma
    (requires (rev l == rev l'))
    (ensures (l == l')) 
    (decreases l, l') = admit () 

let lemma_append_rev_inv_tail (l l' l'':list 'a) :
  Lemma 
    (requires (rev l' @ l) == (rev l'' @ l))
    (ensures (l' == l'')) = 
  List.Tot.Properties.append_inv_tail l (rev l') (rev l'');
  lemma_rev_rev_equal l' l''
   

