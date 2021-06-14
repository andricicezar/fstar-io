module Itree

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Classical

(* General properties first. Like on lists. *)

let rec suffix_of (#a: Type) (l1 l2 : list a) :
  Pure Type0
    (requires True)
    (ensures (fun _ -> True))
    (decreases l2)
= match l2 with
  | [] -> l1 == []
  | x :: t -> l1 == x :: t \/ l1 `suffix_of` t

let rec suffix_le_length (#a : Type) (l1 l2 : list a) :
  Lemma
    (requires True)
    (ensures l1 `suffix_of` l2 ==> length l1 <= length l2)
= match l2 with
  | [] -> ()
  | x :: t -> suffix_le_length l1 t

let suffix_same_length (#a : Type) (l1 l2 : list a) :
  Lemma
    (requires length l1 == length l2 /\ l1 `suffix_of` l2)
    (ensures l1 == l2)
= match l2 with
  | [] -> ()
  | x :: t -> suffix_le_length l1 t

let rec minus_suffix (#a : Type) (l2 l1 : list a) :
  Pure (list a) (requires l1 `suffix_of` l2) (ensures (fun l -> l @ l1 == l2)) =
  match l2 with
  | [] -> []
  | x :: t ->
    if length l1 = length (x :: t)
    then begin suffix_same_length l1 (x :: t) ; [] end
    else x :: (t `minus_suffix` l1)

let rec suffix_of_trans #a (l1 l2 l3 : list a) :
  Lemma
    (requires True)
    (ensures l1 `suffix_of` l2 /\ l2 `suffix_of` l3 ==> l1 `suffix_of` l3)
    (decreases l3)
= match l3 with
  | [] -> ()
  | x :: t -> suffix_of_trans l1 l2 t

let suffix_of_trans_mid #a l2 :
  Lemma (requires True) (ensures forall l1 l3. l1 `suffix_of` l2 /\ l2 `suffix_of` l3 ==> l1 `suffix_of` l3)
=
  let lem (l1 l3 : list a) :
    Lemma
      (requires l1 `suffix_of` l2 /\ l2 `suffix_of` l3)
      (ensures l1 `suffix_of` l3)
      [SMTPat (l1 `suffix_of` l3)]
    = suffix_of_trans l1 l2 l3
  in
  ()

let suffix_of_trans_forall a :
  Lemma (requires True) (ensures forall l1 l2 (l3 : list a). l1 `suffix_of` l2 /\ l2 `suffix_of` l3 ==> l1 `suffix_of` l3)
= forall_intro_3 (suffix_of_trans #a)

// let minus_suffix_trans #a (p q r : list a) :
//   Lemma
//     (requires p `suffix_of` q /\ q `suffix_of` r)
//     (ensures r `minus_suffix` q == (r `minus_suffix` p) `minus_suffix` (q `minus_suffix` p))
// = admit ()

// let prefix_of (#a: Type) (p l : list a) : Type0 =
//   exists q. l == p @ q

let rec prefix_of #a (p l : list a) : Type0 =
  match p with
  | [] -> True
  | x :: p ->
    match l with
    | y :: l -> x == y /\ p `prefix_of` l
    | [] -> False

let rec minus_prefix #a (l p : list a) :
  Pure (list a) (requires p `prefix_of` l) (ensures (fun r -> p @ r == l)) =
  match p with
  | [] -> l
  | x :: p ->
    match l with
    | y :: l -> l `minus_prefix` p

(* Enconding of interaction trees, specialised to a free monad

   For now, they are unconstrained, which means that wrong data
   can be represented.

*)

noeq
type op_sig (op : Type) = {
  args : op -> eqtype ;
  res : op -> eqtype
}

type ichoice (op : Type) (s : op_sig op) =
| Tau_choice : ichoice op s
| Call_choice : o:op -> s.args o -> s.res o -> ichoice op s

type ipos op s = list (ichoice op s)

type inode op (s : op_sig op) (a:Type) =
| Ret : a -> inode op s a
| Call : o:op -> s.args o -> inode op s a
| Tau : inode op s a

type raw_itree op s a =
  ipos op s -> option (inode op s a)

let isRet #op #s #a (n : option (inode op s a)) =
  match n with
  | Some (Ret x) -> true
  | _ -> false

let ret_val #op #s #a (n : option (inode op s a) { isRet n }) =
  match n with
  | Some (Ret x) -> x

let valid_itree (#op:eqtype) #s #a (t : raw_itree op s a) =
  True
  // Some? (t []) // /\
  // (forall p. None? (t p) ==> (forall q. None? (t (p @ q)))) /\ // Fails for bind
  // (forall p. Some? (t p) ==> (forall pi pe. p = pi @ pe ==> Some? (t pi))) /\ // Fails for bind // Maybe specialise for each node case
  // (forall p.
  //   isRet (t p) ==>
  //   begin
  //     ret_pos (t p) `suffix_of` p /\
  //     // Going forward after a result has been reached
  //     // Same as below, but with prefix_of, for some reason it helps the proof for tau
  //     begin
  //       forall q.
  //         p `prefix_of` q ==>
  //         begin
  //           isRet (t q) /\
  //           ret_pos (t q) == ret_pos (t p) @ (q `minus_prefix` p) /\
  //           ret_val (t q) == ret_val (t p)
  //         end
  //     end
  //     // begin
  //     //   forall q.
  //     //     isRet (t (p @ q)) /\ // or with prefix + some minus_prefix? for minus_prefix we would need to def prefix recursively x :: p `prefix_of` y :: l = x == y /\ p prefix of l
  //     //     ret_pos (t (p @ q)) == ret_pos (t p) @ q // /\
  //     //     // ret_val (t (p @ q)) == ret_val (t p)
  //     // end // /\
  //     // Going back to when the result was found
  //     // begin
  //     //   let q = p `minus_suffix` ret_pos (t p) in
  //     //   isRet (t q) // /\
  //     //   // ret_val (t q) == ret_val (t p) // /\
  //     //   // ret_pos (t q) == [] // /\
  //     // end
  //   end
  // ) /\
  // (isRet (t []) ==> ret_pos (t []) == [])

let itree (op:eqtype) s a =
  t:(raw_itree op s a) { valid_itree t }

let ret #op #s #a (x:a) : itree op s a =
  fun p ->
    match p with
    | [] -> Some (Ret x)
    | _ -> None

let call (#op:eqtype) #s #a (o : op) (x : s.args o) (k : s.res o -> itree op s a) : itree op s a =
  fun p ->
    match p with
    | [] -> Some (Call o x)
    | Tau_choice :: p -> None
    | Call_choice o' x' y :: p ->
      if o = o' && x = x'
      then k y p
      else None

let tau #op #s #a (k : itree op s a) : itree op s a =
  fun p ->
    match p with
    | [] -> Some Tau
    | Tau_choice :: p -> k p
    | Call_choice _ _ _ :: _ -> None

// Before we can bind, we have to find a prefix of the position which returns and then forwards the suffix
// pp is an accumaltor prefix, not efficient
let rec find_ret #op #s #a (m : itree op s a) (pp p : ipos op s) : Pure (option (a * ipos op s)) (requires True) (ensures fun r -> True) (decreases p) =
  if isRet (m pp)
  then Some (ret_val (m pp), p)
  else begin
    match p with
    | [] -> None
    | c :: p -> find_ret m (pp @ [c]) p
  end

let rec find_ret_None_noRet #op #s #a (m : itree op s a) (pp p : ipos op s) :
  Lemma
    (requires find_ret m pp p == None)
    (ensures ~ (isRet (m (pp @ p))))
    (decreases p)
= if isRet (m pp)
  then ()
  else begin
    match p with
    | [] -> ()
    | c :: p -> append_assoc pp [c] p ; find_ret_None_noRet m (pp @ [c]) p
  end

let cast_node #op #s #a #b (n : (option (inode op s a)) { ~ (isRet n) }) : option (inode op s b) =
  match n with
  | Some Tau -> Some Tau
  | Some (Call o x) -> Some (Call o x)
  | None -> None

let bind #op #s #a #b (m : itree op s a) (f : a -> itree op s b) : itree op s b =
  // suffix_of_trans_forall (ichoice op s) ;
  fun p ->
    match find_ret m [] p with
    | Some (x, q) -> f x q
    | None -> find_ret_None_noRet m [] p ; cast_node (m p)

(* A loop with no events/effects except non-termination *)
let loop #op #s a : itree op s a =
  fun p -> Some Tau

(* Monad instance

   Without GetTrace for now

*)

open Common

type cmds = | Openfile | Read | Close

unfold let io_args cmd : eqtype =
  match cmd with
  | Openfile -> string
  | Read -> file_descr
  | Close -> file_descr

unfold let io_res cmd : eqtype =
  match cmd with
  | Openfile -> file_descr
  | Read -> string
  | Close -> unit

let io_op_sig : op_sig cmds = {
  args = io_args ;
  res = io_res
}

(*
  The trace can be read from the position + eventually the node it leads to.
  Care has to be taken to actually remove the postfix when it leads to return
  because the postfix is forwarded, thus essentially ignored, and could be
  garbage.
*)

let wp a = (a -> Type0) -> Type0

let wp_return #a (x : a) : wp a =
  fun post -> post x

let wp_bind #a #b (w : wp a) (f : a -> wp b) : wp b =
  fun post -> w (fun x -> f x post)

let stronger_wp #a (wp1 wp2 : wp a) : Type0 =
  forall post. wp1 post ==> wp2 post

let io_wp #a (t : itree cmds io_op_sig a) =
  fun post -> forall p. isRet (t p) ==> post (ret_val (t p))

let io a (w : wp a) =
  t:itree cmds io_op_sig a { io_wp t `stronger_wp` w }

let io_return a (x : a) : io a (wp_return x) =
  assert (isRet (ret #cmds #io_op_sig #a x [])) ;
  ret x

let io_bind a b w wf (m : io a w) (f : (x:a) -> io b (wf x)) : io b (wp_bind w wf) =
  assume (forall p q. isRet (m p) ==> find_ret m [] (p @ q) == Some (ret_val (m p), q)) ; // probably need to extend valid_itree to enforce this
  assert (forall p q. isRet (m p) ==> isRet (f (ret_val (m p)) q) ==> ret_val (bind m f (p @ q)) == ret_val (f (ret_val (m p)) q)) ;
  assert (forall p q post. (forall p. isRet (bind m f p) ==> post (ret_val (bind m f p))) ==> isRet (m p) ==> isRet (f (ret_val (m p)) q) ==> post (ret_val (f (ret_val (m p)) q))) ;
  bind m f

[@@allow_informative_binders]
reifiable total layered_effect {
  IO : a:Type -> wp a -> Effect
  with
    repr   = io ;
    return = io_return ;
    bind   = io_bind
}
