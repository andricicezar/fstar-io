module Itree

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Classical

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
| Ret : a -> ipos op s -> inode op s a
| Call : o:op -> s.args o -> inode op s a
| Tau : inode op s a

type raw_itree op s a =
  ipos op s -> option (inode op s a)

let isRet #op #s #a (n : option (inode op s a)) =
  match n with
  | Some (Ret x p) -> true
  | _ -> false

let ret_pos #op #s #a (n : option (inode op s a) { isRet n }) =
  match n with
  | Some (Ret x p) -> p

let ret_val #op #s #a (n : option (inode op s a) { isRet n }) =
  match n with
  | Some (Ret x p) -> x

let rec suffix_of (#a: Type) (l1 l2 : list a) :
  Pure Type0
    (requires True)
    (ensures (fun _ -> True))
    (decreases l2)
= match l2 with
  | [] -> l1 == []
  | x :: t -> l1 == x :: t \/ l1 `suffix_of` t

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

let valid_itree (#op:eqtype) #s #a (t : raw_itree op s a) =
  Some? (t []) /\
  // (forall p. None? (t p) ==> (forall q. None? (t (p @ q)))) /\ // Fails for bind
  // (forall p. Some? (t p) ==> (forall pi pe. p = pi @ pe ==> Some? (t pi))) /\ // Fails for bind
  (forall p.
    isRet (t p) ==>
    ret_pos (t p) `suffix_of` p // /\ // Is there an easy way to get the prefix now? probably l `minus_suffix` s defined as suffix_of
    // isRet (t q) /\
    // ret_val (t q) == ret_val (t p)
    // /\ ret_pos (t q) == [] // /\
    // (forall q.
    //   isRet (t (p @ q)) // /\
    //   // ret_pos (t (p @ q)) == ret_pos (t p) @ q /\
    //   // ret_val (t (p @ q)) == ret_val (t p)
    // )
  ) /\
  (isRet (t []) ==> ret_pos (t []) == [])

let itree (op:eqtype) s a =
  t:(raw_itree op s a) { valid_itree t }

let ret #op #s #a (x:a) : itree op s a =
  fun p -> Some (Ret x p)

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
    | _ -> None

let bind #op #s #a #b (x : itree op s a) (f : a -> itree op s b) : itree op s b =
  suffix_of_trans_forall (ichoice op s) ;
  fun p ->
    match x p with
    | None -> None
    | Some (Ret u q) -> f u q
    | Some (Call o arg) -> Some (Call o arg)
    | Some Tau -> Some Tau

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
  ret x

let bind_isRet_inv #op #s #a #b (m : itree op s a) (f : a -> itree op s b) :
  Lemma
    (requires True)
    (ensures (
      forall p.
        isRet (bind m f p) ==>
        isRet (m p) /\ isRet (f (ret_val (m p)) (ret_pos (m p)))
    ))
= ()

let bind_isRet #op #s #a #b (m : itree op s a) (f : a -> itree op s b) :
  Lemma
    (requires True)
    (ensures (
      forall p.
        isRet (m p) ==>
        isRet (f (ret_val (m p)) (ret_pos (m p))) ==>
        isRet (bind m f p)
    ))
= ()

let bind_ret_val #op #s #a #b (m : itree op s a) (f : a -> itree op s b) :
  Lemma
    (requires True)
    (ensures (
      forall p.
        isRet (m p) ==>
        isRet (f (ret_val (m p)) (ret_pos (m p))) ==>
        ret_val (bind m f p) == ret_val (f (ret_val (m p)) (ret_pos (m p)))
    ))
= ()

// Can we prove something like below?
// We actually want to relate
// f (ret_val (m p)) q
// and
// f (ret_val (m p)) (ret_pos (m p))
// which we know are both some Ret
// can we replace the suffix [ret_pos (m p)] with [q] in [p] and give that position to [bind m f]?
// We already know that there exists [pi] such that [p = pi @ (ret_pos (m p))]
// so we want to use that [pi] and then [pi @ q] basically
// but we probably need also that [m pi] is [Ret x []]
// and that the [x] is constant basically once you reach Ret

// let ret_prefix #op #s #a p (t : itree op s a { isRet (t p) }) : q: ipos op s { p = q @ ret_pos (t p) } =
//   firstn // maybe look into exists -> squash or something

// let bind_ret_val' #op #s #a #b (m : itree op s a) (f : a -> itree op s b) :
//   Lemma
//     (requires True)
//     (ensures (
//       forall p q.
//         isRet (m p) ==>
//         // isRet (f (ret_val (m p)) (ret_pos (m p))) ==> // We don't have this
//         isRet (f (ret_val (m p)) q) ==>
//         (forall post. post (ret_val (bind m f p)) ==> post (ret_val (f (ret_val (m p)) q))) // here we want to apply bind m f to pi @ q
//     ))
// = admit ()

let io_bind a b w wf (m : io a w) (f : (x:a) -> io b (wf x)) : io b (wp_bind w wf) =
  // assert (io_wp x `stronger_wp` w) ;
  assert (forall post. (forall p. isRet (m p) ==> post (ret_val (m p))) ==> w post) ;
  // assert (forall x. io_wp (f x) `stronger_wp` wf x) ;
  assert (forall x post. (forall p. isRet (f x p) ==> post (ret_val (f x p))) ==> wf x post) ;
  bind_isRet m f ;
  bind_ret_val m f ;
  // assume (io_wp (bind x f) `stronger_wp` wp_bind w wf) ;
  // assume (forall post. (forall p. isRet (bind m f p) ==> post (ret_val (bind m f p))) ==> w (fun x -> wf x post)) ;
  assume (forall p q post. isRet (m p) ==> isRet (f (ret_val (m p)) q) ==> post (ret_val (f (ret_val (m p)) q))) ;
  // bind_ret_val' m f ;
  bind m f

[@@allow_informative_binders]
reifiable total layered_effect {
  IO : a:Type -> wp a -> Effect
  with
    repr   = io ;
    return = io_return ;
    bind   = io_bind
}
