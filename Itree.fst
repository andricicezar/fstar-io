module Itree

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Classical
open FStar.IndefiniteDescription

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

(** Encoding of interaction trees, specialised to a free monad

   The idea is to bypass the absence of coinductive datatypes in F* by instead
   doing something similar to how one would encode the type [stream A] as
   functions [nat -> A].
   Here we define itrees as functions from positions (or paths in the tree) to
   nodes which contain a label corresponding to either [Ret] for return, [Tau]
   for delays, and [Call] for the monadic operations.

*)

noeq
type op_sig (op : Type) = {
  args : op -> eqtype ;
  res : op -> eqtype
}

type ichoice (op : Type) (s : op_sig op) =
| Tau_choice : ichoice op s
| Call_choice : o:op -> s.args o -> s.res o -> ichoice op s

(** Type of positions as sequences of choices in the tree *)
type ipos op s = list (ichoice op s)

(** Nodes of an itree *)
type inode op (s : op_sig op) (a:Type) =
| Ret : a -> inode op s a
| Call : o:op -> s.args o -> inode op s a
| Tau : inode op s a

(** A *raw* itree

    This type is unconstrained, and potentially nonsensical data could be
    represented.

*)
type raw_itree op s a =
  ipos op s -> option (inode op s a)

let isRet #op #s #a (n : option (inode op s a)) =
  match n with
  | Some (Ret x) -> true
  | _ -> false

let ret_val #op #s #a (n : option (inode op s a) { isRet n }) =
  match n with
  | Some (Ret x) -> x

let isEvent #op #s #a (n : option (inode op s a)) =
  match n with
  | Some (Call o x) -> true
  | Some Tau -> true
  | _ -> false

let valid_itree (#op:eqtype) #s #a (t : raw_itree op s a) =
  forall p. isRet (t p) ==> (forall q. p `strict_suffix_of` q ==> None? (t q)) // Ret is final
  // Should we instead use some [consistent t p] boolean predicate that would traverse the itree?
  // Maybe forall p. (p == [] /\ Some? (t [])) \/ (exists q c. p == q @ [c] /\ consistent_choice (t q) c)
  // where consistent_choice n c checks that both are call or both tau
  // Two other options:
  // - say that isCall (t p) ==> forall y. Some? (t (p @ [Call_choice o x y])) where o and x are extracted from isCall
  //   and that isCall (t p) ==> None?(p @ [Tau_choice])
  //   and that None is final probably
  // - define the itree at a given position (not just the node) and say that at every (Some) position, the resulting
  //   itree is either ret or call or tau. Probably not going to work for SMT.

(** Itrees are defined by refinement over [raw_itree].

    The choice of only specifying what happens when an itree returns and
    nothing more can seem arbitrary as it doesn't forbid all ill-formed
    itrees. The reason for this choice is that it seems to be the minimal
    requirement to obtain a Dijkstra monad in the end.

*)
let itree (op:eqtype) s a =
  t:(raw_itree op s a) { valid_itree t }

(** return of the monad *)
let ret #op #s #a (x:a) : itree op s a =
  fun p ->
    match p with
    | [] -> Some (Ret x)
    | _ -> None

(** monadic operations *)
let call (#op:eqtype) #s #a (o : op) (x : s.args o) (k : s.res o -> itree op s a) : itree op s a =
  fun p ->
    match p with
    | [] -> Some (Call o x)
    | Tau_choice :: p -> None
    | Call_choice o' x' y :: p ->
      if o = o' && x = x'
      then k y p
      else None

(** delay *)
let tau #op #s #a (k : itree op s a) : itree op s a =
  fun p ->
    match p with
    | [] -> Some Tau
    | Tau_choice :: p -> k p
    | Call_choice _ _ _ :: _ -> None

(** Before we can bind, we have to find a prefix of the position which returns
    and then forwards the suffix.
    Indeed, take for instance [ret x p] it will only return its contents it [p]
    is the empty list (or root position). [find_ret (ret x) [] p] will thus
    return [Some (x, p)] meaning that we can graft the other tree in place of
    the return leaf by forwarding the position [p] to it.

    [pp] is an accumaltor prefix, not efficient.
*)
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

let rec find_ret_append_aux #op #s #a (m : itree op s a) pp p q :
  Lemma
    (ensures isRet (m (pp @ p)) ==> find_ret m pp (p @ q) == Some (ret_val (m (pp @ p)), q))
    (decreases p)
= if isRet (m pp)
  then strict_suffix_or_eq_append pp p
  else begin
    match p with
    | [] -> ()
    | c :: p ->
      begin
        append_assoc pp [c] p ;
        find_ret_append_aux m (pp @ [c]) p q
      end
  end

let find_ret_append #op #s #a (m : itree op s a) :
  Lemma (ensures forall p q. isRet (m p) ==> find_ret m [] (p @ q) == Some (ret_val (m p), q))
= forall_intro_2 (find_ret_append_aux m [])

let rec find_ret_strict_suffix_aux #op #s #a (m : itree op s a) pp p q u p' :
  Lemma
    (ensures
      find_ret m pp p == Some (u, p') ==>
      p `strict_suffix_of` q ==>
      (exists q'. find_ret m pp q == Some (u, q') /\ p' `strict_suffix_of` q')
    )
    (decreases p)
= if isRet (m pp)
  then ()
  else begin
    match p with
    | [] -> ()
    | c :: p ->
      begin
        match q with
        | [] -> ()
        | c' :: q ->
          find_ret_strict_suffix_aux m (pp @ [c]) p q u p'
      end
  end

let find_ret_strict_suffix #op #s #a (m : itree op s a) :
  Lemma
    (ensures
      forall p q u p'.
        find_ret m [] p == Some (u, p') ==>
        p `strict_suffix_of` q ==>
        (exists q'. find_ret m [] q == Some (u, q') /\ p' `strict_suffix_of` q')
    )
= forall_intro_4 (find_ret_strict_suffix_aux m [])

let rec find_ret_Event_None #op #s #a (m : itree op s a) (pp p : ipos op s) :
  Lemma
    (requires isEvent (m (pp @ p)))
    (ensures find_ret m pp p == None)
    (decreases p)
= if isRet (m pp)
  then begin
    match p with
    | [] -> ()
    | c :: p -> strict_suffix_or_eq_append pp (c :: p)
  end
  else begin
    match p with
    | [] -> ()
    | c :: p -> append_assoc pp [c] p ; find_ret_Event_None m (pp @ [c]) p
  end

let rec find_ret_smaller #op #s #a (m : itree op s a) (pp p : ipos op s) :
  Lemma (ensures forall x q. find_ret m pp p == Some (x, q) ==> p == q \/ q << p) (decreases p)
= if isRet (m pp)
  then ()
  else begin
    match p with
    | [] -> ()
    | c :: p' -> find_ret_smaller m (pp @ [c]) p'
  end

let rec find_ret_length #op #s #a (m : itree op s a) (pp p : ipos op s) :
  Lemma (ensures forall x q. find_ret m pp p == Some (x, q) ==> length q <= length p) (decreases p)
= if isRet (m pp)
  then ()
  else begin
    match p with
    | [] -> ()
    | c :: p' -> find_ret_length m (pp @ [c]) p'
  end

let find_ret_val #op #s #a (m : itree op s a) (pp p : ipos op s) :
  Pure a (requires Some? (find_ret m pp p)) (ensures fun _ -> True)
= match find_ret m pp p with
  | Some (x, q) -> x

let find_ret_pos #op #s #a (m : itree op s a) (pp p : ipos op s) :
  Pure (ipos op s) (requires Some? (find_ret m pp p)) (ensures fun _ -> True)
= match find_ret m pp p with
  | Some (x, q) -> q

let rec find_ret_prefix #op #s #a (m : itree op s a) (pp p : ipos op s) :
  Pure (ipos op s) (requires Some? (find_ret m pp p)) (ensures fun q -> isRet (m q)) (decreases p)
= if isRet (m pp)
  then pp
  else begin
    match p with
    | c :: p -> find_ret_prefix m (pp @ [c]) p
  end

let rec find_ret_Some_pos #op #s #a (m : itree op s a) (pp p : ipos op s) :
  Lemma (ensures
    Some? (find_ret m pp p) ==>
    pp @ p == (find_ret_prefix m pp p) @ (find_ret_pos m pp p)
  ) (decreases p)
= if isRet (m pp)
  then ()
  else begin
    match p with
    | [] -> ()
    | c :: p -> append_assoc pp [c] p ; find_ret_Some_pos m (pp @ [c]) p
  end

let rec find_ret_prefix_val #op #s #a (m : itree op s a) (pp p : ipos op s) :
  Lemma (ensures
    Some? (find_ret m pp p) ==>
    ret_val (m (find_ret_prefix m pp p)) == find_ret_val m pp p
  ) (decreases p)
= if isRet (m pp)
  then ()
  else begin
    match p with
    | [] -> ()
    | c :: p -> find_ret_prefix_val m (pp @ [c]) p
  end

let cast_node #op #s #a #b (n : (option (inode op s a)) { ~ (isRet n) }) : option (inode op s b) =
  match n with
  | Some Tau -> Some Tau
  | Some (Call o x) -> Some (Call o x)
  | None -> None

(** bind function

    We use [find_ret] as described above.
    We also make use of [cast_node] to deal with the case where there is
    no return leaf in the considered branch and the return type can then
    be anything as we return [m p] which is of type [inode op s a]
    instead of [inode op s b].

*)
let bind #op #s #a #b (m : itree op s a) (f : a -> itree op s b) : itree op s b =
  find_ret_strict_suffix m ;
  fun p ->
    match find_ret m [] p with
    | Some (x, q) -> f x q
    | None -> find_ret_None_noRet m [] p ; cast_node (m p)

(* An ill-formed loop *)
let bad_loop #op #s a : itree op s a =
  fun p -> Some Tau

(** A loop with no events/effects except non-termination *)
let loop #op #s a : itree op s a =
  fun p ->
    match filter (fun c -> c = Tau_choice) p with
    | [] -> Some Tau
    | _ -> None

(** Definition of a co-recursor *)

let cont #op #s #a (n : inode op s a) r =
  match n with
  | Ret x -> unit
  | Call o x -> s.res o -> r
  | Tau -> r

let cont_node op s a r =
  n: inode op s a & cont n r

let rec itree_corec_aux (#op : eqtype) #s #a #b (f : a -> cont_node op s b a) (i : a) (p : ipos op s) :
  Pure (option (inode op s b)) (requires True) (ensures fun r -> True) (decreases p)
= match p with
  | [] ->
    let (| n, _ |) = f i in Some n
  | Tau_choice :: p ->
    begin match f i with
    | (| Tau, next |) -> itree_corec_aux f next p
    | _ -> None
    end
  | Call_choice o x y :: p ->
    begin match f i with
    | (| Call o' x', next |) ->
      if o = o' && x = x'
      then itree_corec_aux f (next y) p
      else None
    | _ -> None
    end

let rec itree_corec_aux_final_ret (#op : eqtype) #s #a #b (f : a -> cont_node op s b a) i p q :
  Lemma
    (ensures isRet (itree_corec_aux f i p) ==> p `strict_suffix_of` q ==> None? (itree_corec_aux f i q))
    (decreases p)
= match p with
  | [] ->
    begin match f i with
    | (| Ret x, n |) -> ()
    | (| Tau,  n |) -> ()
    | (| Call o' x', n |) -> ()
    end
  | Tau_choice :: p ->
    begin match f i with
    | (| Ret x, n |) -> ()
    | (| Tau, n |) ->
      begin match q with
      | [] -> ()
      | Tau_choice :: q -> itree_corec_aux_final_ret f n p q
      | Call_choice o x y :: q -> ()
      end
    | (| Call o' x', n |) -> ()
    end
  | Call_choice o x y :: p ->
    begin match f i with
    | (| Ret x, n |) -> ()
    | (| Tau, n |) -> ()
    | (| Call o' x', n |) ->
      if o = o' && x = x'
      then begin
        match q with
        | [] -> ()
        | Tau_choice :: q -> ()
        | Call_choice oo xx yy :: q ->
          itree_corec_aux_final_ret f (n y) p q
      end
      else ()
    end

let itree_corec (#op : eqtype) #s #a #b (f : a -> cont_node op s b a) (i : a) : itree op s b =
  forall_intro_2 (itree_corec_aux_final_ret f i) ;
  itree_corec_aux f i

(** Some notion of cofixpoint where the function should produce at least one
    constructor before calling itself recursively.

    Sadly, we need the productivity because we have to be able to produce a
    node when given a position.
    The idea is that we only have to unfold the cofixpoint [length p + 1]
    times to be able to get the node at position [p].

*)

(* Unfold the function (n+1) times *)
let rec itree_cofix_unfoldn (#op : eqtype) #s #a #b (ff : (a -> itree op s b) -> a -> itree op s b) (n : nat) : a -> itree op s b =
  if n = 0
  then ff (fun _ -> loop _)
  else ff (itree_cofix_unfoldn ff (n - 1))

unfold
let itree_cofix_guarded (#op : eqtype) #s #a #b (ff : (a -> itree op s b) -> a -> itree op s b) =
  forall (x : a) (n : nat) (p : ipos op s).
    length p <= n ==>
    itree_cofix_unfoldn ff (length p) x p == itree_cofix_unfoldn ff n x p

let itree_cofix (#op : eqtype) #s #a #b (ff : (a -> itree op s b) -> a -> itree op s b) :
  Pure (a -> itree op s b) (requires itree_cofix_guarded ff) (ensures fun _ -> True)
= fun (x : a) p -> itree_cofix_unfoldn ff (length p) x p

// let itree_cofix_isfix (#op : eqtype) #s #a #b (ff : (a -> itree op s b) -> a -> itree op s b) (x : a) p :
//   Lemma (itree_cofix_guarded ff ==> itree_cofix ff x p == ff (itree_cofix ff) x p)
// = assert (itree_cofix_unfoldn ff (length p + 1) x p == ff (itree_cofix_unfoldn ff (length p)) x p) ;
// // WAIT! Capture problem here.
//   assume (itree_cofix_guarded ff ==> ff (itree_cofix_unfoldn ff (length p)) x p == ff (fun x q -> itree_cofix_unfoldn ff (length p) x q) x p) ;
//   assert (itree_cofix_guarded ff ==> ff (itree_cofix ff) x p == ff (fun x p -> itree_cofix_unfoldn ff (length p) x p) x p) ;
//   assert (itree_cofix_guarded ff ==> itree_cofix_unfoldn ff (length p) x p == ff (itree_cofix ff) x p)

let itree_cofix_unfold_1 (#op : eqtype) #s #a #b (ff : (a -> itree op s b) -> a -> itree op s b) (x : a) p :
  Lemma (itree_cofix_guarded ff ==> itree_cofix ff x p == ff (if length p = 0 then (fun _ -> loop _) else itree_cofix_unfoldn ff (length p - 1)) x p)
= ()

(* Trivial cofix *)
let ret' #op #s #a (v : a) : itree op s a =
  itree_cofix (fun (_ : unit -> itree op s a) (_ : unit) -> ret v) ()

(* Alternative def of loop using cofix to test it *)
let loop' #op #s a : itree op s a =
  let ff loop_ _ = tau (loop_ ()) in
  let rec aux p n :
    Lemma
      (ensures length p <= n ==> itree_cofix_unfoldn ff (length p) () p == itree_cofix_unfoldn ff n () p)
      (decreases p)
      [SMTPat ()]
  = match p with
    | Tau_choice :: q ->
      if length q + 1 <= n
      then aux q (n-1)
      else ()
    | _ -> ()
  in
  itree_cofix ff ()

(** Definition of repeat
   Is is achieved using a cofix. For proof purposes we define it in three parts.
*)

let repeat_fix #op #s (body : itree op s unit) repeat_ (_ : unit) : itree op s unit =
  bind body (fun _ -> tau (repeat_ ()))

let rec repeat_fix_guarded #op #s (body : itree op s unit) p n :
  Lemma
    (ensures length p <= n ==> itree_cofix_unfoldn (repeat_fix body) (length p) () p == itree_cofix_unfoldn (repeat_fix body) n () p)
    (decreases p)
= match find_ret body [] p with
  | Some (x, q) ->
    find_ret_smaller body [] p ;
    find_ret_length body [] p ;
    begin match q with
    | Tau_choice :: r ->
      if length r + 1 <= n
      then begin
        repeat_fix_guarded body r (n-1) ;
        repeat_fix_guarded body r (length p - 1)
      end
      else ()
    | _ -> ()
    end
  | None -> ()

let repeat #op #s (body : itree op s unit) : itree op s unit =
  forall_intro_2 (repeat_fix_guarded body) ;
  itree_cofix (repeat_fix body) ()

(* Definition of iter from cofixpoint *)
let iter (#op : eqtype) #s #ind #a (step : ind -> itree op s (either ind a)) : ind -> itree op s a =
  let ff iter_ i =
    bind (step i) (fun ir ->
      begin match ir with
      | Inl j -> tau (iter_ j)
      | Inr r -> ret r
      end
    )
  in
  let rec aux p n x :
    Lemma
      (ensures length p <= n ==> itree_cofix_unfoldn ff (length p) x p == itree_cofix_unfoldn ff n x p)
      (decreases p)
      [SMTPat ()]
  = match find_ret (step x) [] p with
    | Some (Inl j, q) ->
      find_ret_smaller (step x) [] p ;
      find_ret_length (step x) [] p ;
      begin match q with
      | Tau_choice :: r ->
        if length r + 1 <= n
        then begin
          aux r (n-1) j ;
          aux r (length p - 1) j
        end
        else ()
      | _ -> ()
      end
    | Some (Inr r, q) -> ()
    | None -> ()
  in
  itree_cofix ff

(** Monad instance

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

unfold
let iotree a = itree cmds io_op_sig a

unfold
let iopos = ipos cmds io_op_sig

unfold
let iochoice = ichoice cmds io_op_sig

unfold
let ioret #a (x : a) : iotree a =
  ret x

(**
  Spec with trace
  The trace contains the response of the environment, in fact it is a subset of
  positions where Tau steps are ignored.

  This specification if enough to talk about (non-)termination of a program
  with respect to its interaction with the environment. Unfortunately, it is
  still more limited than the Itrees in Coq.
*)

let trace = list (c: iochoice { c <> Tau_choice })

let rec ipos_trace (p : iopos) : trace =
  match p with
  | [] -> []
  | Tau_choice :: p -> ipos_trace p
  | Call_choice o x y :: p -> Call_choice o x y :: ipos_trace p

let rec ipos_trace_append (p q : iopos) :
  Lemma (ensures ipos_trace (p @ q) == ipos_trace p @ ipos_trace q) (decreases p)
= match p with
  | [] -> ()
  | Tau_choice :: p -> ipos_trace_append p q
  | Call_choice o x y :: p -> ipos_trace_append p q

unfold
let tio_post a = trace -> option a -> Type0

let twp a = tio_post a -> Type0

let twp_return #a (x : a) : twp a =
  fun post -> post [] (Some x)

let shift_post #a (tr : trace) (post : tio_post a) : tio_post a =
  fun tr' x -> post (tr @ tr') x

let twp_bind #a #b (w : twp a) (f : a -> twp b) : twp b =
  fun post ->
    w (fun tr v ->
      match v with
      | Some x -> f x (shift_post tr post)
      | None -> post tr None
    )

let stronger_twp #a (wp1 wp2 : twp a) : Type0 =
  forall post. wp1 post ==> wp2 post

let io_twp #a (t : iotree a) =
  fun post ->
    (forall p. isRet (t p) ==> post (ipos_trace p) (Some (ret_val (t p)))) /\
    (forall p. isEvent (t p) ==> post (ipos_trace p) None)

let tio a (w : twp a) =
  t: iotree a { w `stronger_twp` io_twp t }

let tio_return a (x : a) : tio a (twp_return x) =
  ret x

let tio_bind a b w wf (m : tio a w) (f : (x:a) -> tio b (wf x)) : tio b (twp_bind w wf) =
  assert (forall (post : tio_post a). w post ==> io_twp m post) ;
  assert (forall (post : tio_post b) x. wf x post ==> io_twp (f x) post) ;

  // ret
  forall_intro (find_ret_Some_pos m []) ;
  forall_intro_2 ipos_trace_append ;
  forall_intro (find_ret_prefix_val m []) ;
  assert (forall (post : tio_post b) p. twp_bind w wf post ==> isRet (bind m f p) ==> post (ipos_trace p) (Some (ret_val (bind m f p)))) ;

  // event.ret
  assert (forall (post : tio_post b) p. twp_bind w wf post ==> isEvent (bind m f p) ==> Some? (find_ret m [] p) ==> post (ipos_trace p) None) ;

  // event.noret
  assert (forall (post : tio_post b) p.
    twp_bind w wf post ==>
    isEvent (bind m f p) ==>
    None? (find_ret m [] p) ==>
    isEvent (m p)
  ) ;
  assert (forall (post : tio_post b) p. twp_bind w wf post ==> isEvent (bind m f p) ==> None? (find_ret m [] p) ==> post (ipos_trace p) None) ;

  // event
  assert (forall (post : tio_post b) p. twp_bind w wf post ==> isEvent (bind m f p) ==> post (ipos_trace p) None) ;

  assert (forall (post : tio_post b). twp_bind w wf post ==> io_twp (bind m f) post) ;
  bind m f

let twp_tau #a (w : twp a) : twp a =
  fun post -> post [] None /\ w post

let tio_tau #a #w (m : tio a w) : tio a (twp_tau w) =
  tau m

let twp_call #a (o : cmds) (x : io_args o) (w : io_res o -> twp a) : twp a =
  fun post -> post [] None /\ (forall y. w y (shift_post [ Call_choice o x y ] post))

let tio_call #a (o : cmds) (x : io_args o) #w (k : (r : io_res o) -> tio a (w r)) : tio a (twp_call o x w) =
  call o x k

let rec twp_repeat_trunc (w : twp unit) (n : nat) : twp unit =
  if n = 0
  then fun post -> True
  else twp_bind w (fun (_:unit) -> twp_tau (twp_repeat_trunc w (n - 1)))

let twp_repeat (w : twp unit) : twp unit =
  fun post -> forall n. twp_repeat_trunc w n post

let repeat_unfold_1 (body : iotree unit) :
  Lemma (forall p. repeat body p == bind body (fun _ -> tau ((if length p = 0 then (fun _ -> loop _) else itree_cofix_unfoldn (repeat_fix body) (length p - 1)) ())) p)
= forall_intro (itree_cofix_unfold_1 (repeat_fix body) ()) ;
  forall_intro_2 (repeat_fix_guarded body) ;
  assert (forall p. itree_cofix (repeat_fix body) () p == repeat_fix body (if length p = 0 then (fun _ -> loop _) else itree_cofix_unfoldn (repeat_fix body) (length p - 1)) () p) ;
  assert (forall p. itree_cofix (repeat_fix body) () p == bind body (fun _ -> tau ((if length p = 0 then (fun _ -> loop _) else itree_cofix_unfoldn (repeat_fix body) (length p - 1)) ())) p)

let repeat_one_ret (body : iotree unit) :
  Lemma (forall p q. isRet (body p) ==> repeat body (p @ Tau_choice :: q) == repeat body q)
= repeat_unfold_1 body ;
  find_ret_append body ;
  assert (forall p q.
    isRet (body p) ==>
    repeat body (p @ Tau_choice :: q) == itree_cofix_unfoldn (repeat_fix body) (length (p @ Tau_choice :: q) - 1) () q
  ) ;
  forall_intro_2 (repeat_fix_guarded body)

let rec repeat_not_ret (body : iotree unit) p :
  Lemma (~ (isRet (repeat body p)))
= match find_ret body [] p with
  | Some ((), q) ->
    repeat_unfold_1 body ;
    if length p = 0
    then ()
    else begin
      match q with
      | Tau_choice :: r ->
        find_ret_length body [] p ;
        forall_intro_2 (repeat_fix_guarded body) ;
        find_ret_smaller body [] p ;
        repeat_not_ret body r
      | _ :: r -> ()
      | [] -> ()
    end
  | None -> ()

let rec tio_repeat_proof_gen #w (body : tio unit w) (pl : list iopos) p :
  Lemma
    (requires forall pp. mem pp pl ==> isRet (body pp))
    (ensures forall (post : tio_post unit).
      twp_repeat w post ==>
      isEvent (repeat body (flatten pl @ p)) ==> // rather flatten_sep with Tau_choice
      post (ipos_trace (flatten pl @ p)) None
    )
    (decreases p)
= match find_ret body [] p with
  | Some ((), q) ->
    assert (isRet (body (find_ret_prefix body [] p))) ;
    find_ret_Some_pos body [] p ;
    assert (p == find_ret_prefix body [] p @ q) ;
    begin match q with
    | [] -> admit ()
    | Tau_choice :: r ->
      assume (forall pp. mem pp (pl @ [find_ret_prefix body [] p]) ==> isRet (body pp)) ;
      find_ret_smaller body [] p ;
      tio_repeat_proof_gen body (pl @ [find_ret_prefix body [] p]) r ;
      admit ()
    | c :: r -> admit ()
    end
  | None -> admit ()

let rec tio_repeat_proof #w (body : tio unit w) p :
  Lemma (forall (post : tio_post unit).
    twp_repeat w post ==>
    isEvent (repeat body p) ==>
    post (ipos_trace p) None
  )
= tio_repeat_proof_gen body [] p

  // match find_ret body [] p with
  // | Some ((), q) ->
  //   assert (isRet (body (find_ret_prefix body [] p))) ;
  //   find_ret_Some_pos body [] p ;
  //   assert (p == find_ret_prefix body [] p @ q) ;
  //   repeat_unfold_1 body ;
  //   begin match q with
  //   | [] ->
  //     assert (repeat body p == Some Tau) ;
  //     assert (forall (post : tio_post unit). twp_repeat w post ==> twp_repeat_trunc w 1 post) ;
  //     assert (p == find_ret_prefix body [] p) ;
  //     assert (forall (post : tio_post unit).
  //       twp_repeat w post ==>
  //       twp_tau (twp_repeat_trunc w 0) (shift_post (ipos_trace p) post)
  //     ) ;
  //     assert (forall (post : tio_post unit).
  //       twp_tau (twp_repeat_trunc w 0) (shift_post (ipos_trace p) post) ==>
  //       shift_post (ipos_trace p) post [] None
  //     )
  //   | Tau_choice :: r ->
  //     repeat_one_ret body ;
  //     assert (repeat body p == repeat body r) ;
  //     find_ret_smaller body [] p ;
  //     tio_repeat_proof body r ;
  //     assert (forall (post : tio_post unit).
  //       twp_repeat w post ==>
  //       isEvent (repeat body p) ==>
  //       post (ipos_trace r) None
  //     ) ;
  //     // assume (forall (post : tio_post unit).
  //     //   twp_repeat w post ==>
  //     //   isEvent (repeat body p) ==>
  //     //   post (ipos_trace p) None
  //     // )
  //     // Maybe it should be generalised to take a list of previous return positions for body
  //     // maybe using requires, then the recursive call will be the easy bit
  //     // for the other ones, we will need to also use recursion using the thing with n = 1 + length of that list
  //     admit ()
  //   | c :: r -> ()
  //   end
  // | None ->
  //   assert (forall (post : tio_post unit). twp_repeat w post ==> twp_repeat_trunc w 1 post)

let tio_repeat #w (body : tio unit w) : tio unit (twp_repeat w) =
  // assert (forall (post : tio_post unit). w post ==> io_twp body post) ;

  // ret
  forall_intro (repeat_not_ret body) ;

  // event
  forall_intro (tio_repeat_proof body) ;

  assert (forall (post : tio_post unit). twp_repeat w post ==> io_twp (repeat body) post) ;
  repeat body

// We can also "inline" the induction by asking the SMT to prove (p n ==> p (n+1)) which might work sometimes

(**

  Alternatively, we propose a definition of tio_repeat using an invariant.
  The invariant is relative to the predicate transformer of the body.
  It must hold for the empty list / root position because postconditions
  must be downward closed for non-terminating / infinite branches
  (all finite prefixes are considered as long as they don't have future
  returns, so maybe downward-closed is wrong in general. For infinite loops
  however, it is true).

*)

let trace_invariant (w : twp unit) (inv : trace -> Type0) =
  inv [] /\
  (forall tr. inv tr ==> w (fun tr' v -> inv (tr @ tr') /\ Some? v))
  // this forces termination, maybe we can simply remove the Some?

let twp_repeat_with_inv (w : twp unit) (inv : trace -> Type0) : twp unit =
  fun post -> forall tr. inv tr ==> post tr None

// For some reason the identity doesn't work
let rec trace_to_pos (tr : trace) : Pure iopos (requires True) (ensures fun p -> ipos_trace p == tr) =
  match tr with
  | [] -> []
  | c :: tr -> c :: trace_to_pos tr

let on_ipos_trace_enough (pr : trace -> Type0) :
  Lemma ((forall (p : iopos). pr (ipos_trace p)) ==> (forall (tr : trace). pr tr))
= assert ((forall (p : iopos). pr (ipos_trace p)) ==> (forall (tr : trace). pr (ipos_trace (trace_to_pos tr))))

// let tio_repeat_with_inv_proof #w (body : tio unit w) (inv : trace -> Type0) :
//   Lemma
//     (requires trace_invariant w inv)
//     (ensures forall (post : tio_post unit) tr. io_twp (repeat body) post ==> inv tr ==> post tr None)
// = assert (forall (post : tio_post unit). io_twp body post ==> w post) ;

//   // This is not ok... If inv is True, we only know that w terminates holds
//   // Nothing on p... Is the whole approach flawed?
//   assume (forall (post : tio_post unit) p. io_twp (repeat body) post ==> inv (ipos_trace p) ==> isEvent (repeat body p)) ;

//   forall_intro (repeat_not_ret body) ;
//   assert (forall (post : tio_post unit) p. io_twp (repeat body) post ==> inv (ipos_trace p) ==> isEvent (repeat body p) /\ noFutureRet (repeat body) p) ;

//   on_ipos_trace_enough (fun tr -> forall (post : tio_post unit). io_twp (repeat body) post ==> inv tr ==> post tr None) ;
//   assert (forall (post : tio_post unit) p. io_twp (repeat body) post ==> inv (ipos_trace p) ==> post (ipos_trace p) None)

let tio_repeat_with_inv #w (body : tio unit w) (inv : trace -> Type0) :
  Pure
    (tio unit (twp_repeat_with_inv w inv))
    (requires trace_invariant w inv)
    (ensures fun _ -> True)
= // tio_repeat_with_inv_proof body inv ;
  admit () ;
  repeat body

// Some specifications

// Does not make sense at the moment
// let terminates #a : tio_post a =
//   fun tr v -> Some? v

let diverges #a : tio_post a =
  fun tr v -> None? v

// let ret_terminates a (x : a) : Lemma (twp_return x terminates) = ()

// Should be p1 ==> p2 rather than ==
let rec twp_repeat_trunc_ext w n (p1 p2 : tio_post unit) :
  Lemma ((forall tr x. p1 tr x == p2 tr x) ==> twp_repeat_trunc w n p1 == twp_repeat_trunc w n p2)
= if n = 0
  then ()
  else begin
    // twp_repeat_trunc_ext w (n-1) p1 p2 ;
    // assume ((forall tr x. p1 tr x == p2 tr x) ==> twp_bind w (fun _ -> twp_repeat_trunc w (n -1)) p1 == twp_bind w (fun _ -> twp_repeat_trunc w (n -1)) p2)
    // assert (twp_repeat_trunc w n == twp_bind w (fun _ -> twp_repeat_trunc w (n -1))) ; // Isn't this by def??
    assume ((forall tr x. p1 tr x == p2 tr x) ==> twp_repeat_trunc w n p1 == twp_repeat_trunc w n p2)
  end

let repeat_ret_loops () :
  Lemma (twp_repeat (twp_return ()) diverges)
= let rec aux n :
    Lemma (twp_repeat_trunc (twp_return ()) n diverges) [SMTPat ()]
  = if n = 0
    then ()
    else begin
      aux (n - 1) ;
      twp_repeat_trunc_ext (twp_return ()) (n-1) (shift_post [] diverges) (diverges #unit)
    end
  in
  ()

// Much better
let repeat_ret_loops_with_inv () :
  Lemma (twp_repeat_with_inv (twp_return ()) (fun _ -> True) diverges)
= ()

[@@allow_informative_binders]
reifiable total layered_effect {
  IODiv : a:Type -> twp a -> Effect
  with
    repr   = tio ;
    return = tio_return ;
    bind   = tio_bind
    // tau    = tio_tau ; // Universe problems
    // call   = tio_call
}
