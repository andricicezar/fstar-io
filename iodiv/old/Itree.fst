module Itree

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc
open FStar.FunctionalExtensionality
open Util
open Stream

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
  forall p. isRet (t p) ==> (forall q. p `strict_prefix_of` q ==> None? (t q)) // Ret is final
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

let return_of #op #s #a (x : a) (m : itree op s a) =
  exists p. isRet (m p) /\ ret_val (m p) == x

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
  then strict_prefix_or_eq_append pp p
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

let rec find_ret_Event_None #op #s #a (m : itree op s a) (pp p : ipos op s) :
  Lemma
    (requires isEvent (m (pp @ p)))
    (ensures find_ret m pp p == None)
    (decreases p)
= if isRet (m pp)
  then begin
    match p with
    | [] -> ()
    | c :: p -> strict_prefix_or_eq_append pp (c :: p)
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

let rec find_ret_suffix_of #op #s #a (m : itree op s a) (pp p : ipos op s) :
  Lemma (ensures forall x q. find_ret m pp p == Some (x, q) ==> q `suffix_of` p) (decreases p)
= if isRet (m pp)
  then ()
  else begin
    match p with
    | [] -> ()
    | c :: p' -> find_ret_suffix_of m (pp @ [c]) p'
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

let rec find_ret_prefix_prefix_of #op #s #a (m : itree op s a) (pp p : ipos op s) :
  Lemma (ensures
    Some? (find_ret m pp p) ==>
    find_ret_prefix m pp p `prefix_of` (pp @ p)
  ) (decreases p)
= if isRet (m pp)
  then prefix_of_append pp p
  else begin
    match p with
    | [] -> ()
    | c :: p ->
      append_assoc pp [c] p ;
      find_ret_prefix_prefix_of m (pp @ [c]) p
  end

let find_ret_prefix_length #op #s #a (m : itree op s a) (pp p : ipos op s) :
  Lemma
    (requires Some? (find_ret m pp p))
    (ensures length (find_ret_prefix m pp p) <= length (pp @ p))
= find_ret_prefix_prefix_of m pp p ;
  prefix_length (find_ret_prefix m pp p) (pp @ p)

let rec find_ret_strict_prefix #op #s #a (m : itree op s a) pp p q :
  Lemma
    (requires Some? (find_ret m pp p) /\ p `strict_prefix_of` q)
    (ensures Some? (find_ret m pp q) /\ find_ret_val m pp p == find_ret_val m pp q /\ find_ret_pos m pp p `strict_prefix_of` find_ret_pos m pp q)
    (decreases p)
= if isRet (m pp)
  then ()
  else begin
    match p with
    | c :: p ->
      begin
        match q with
        | c' :: q ->
          find_ret_strict_prefix m (pp @ [c]) p q
      end
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
let raw_bind #op #s #a #b (m : itree op s a) (f : (x : a { x `return_of` m }) -> itree op s b) (p : ipos op s) : option (inode op s b) =
  match find_ret m [] p with
  | Some (x, q) -> find_ret_prefix_val m [] p ; f x q
  | None -> find_ret_None_noRet m [] p ; cast_node (m p)

let bind #op #s #a #b (m : itree op s a) (f : (x : a { x `return_of` m }) -> itree op s b) : itree op s b =
  introduce forall p q. isRet (raw_bind m f p) /\ p `strict_prefix_of` q ==> None? (raw_bind m f q)
  with begin
    introduce isRet (raw_bind m f p) /\ p `strict_prefix_of` q ==> None? (raw_bind m f q)
    with _. begin
      find_ret_strict_prefix m [] p q ;
      find_ret_prefix_val m [] p
    end
  end ;
  raw_bind m f

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
    (ensures isRet (itree_corec_aux f i p) ==> p `strict_prefix_of` q ==> None? (itree_corec_aux f i q))
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

(** Definition of iter from cofixpoint *)

let iter_fix (#op : eqtype) #s #ind #a (step : ind -> itree op s (either ind a)) iter_ (i : ind) : itree op s a =
  bind (step i) (fun ir ->
    begin match ir with
    | Inl j -> tau (iter_ j)
    | Inr r -> ret r
    end
  )

let rec iter_fix_guarded (#op : eqtype) #s #ind #a (step : ind -> itree op s (either ind a)) p n x :
  Lemma
    (ensures length p <= n ==> itree_cofix_unfoldn (iter_fix step) (length p) x p == itree_cofix_unfoldn (iter_fix step) n x p)
    (decreases p)
= match find_ret (step x) [] p with
  | Some (Inl j, q) ->
    // find_ret_smaller (step x) [] p ;
    // find_ret_length (step x) [] p ;
    // begin match q with
    // | Tau_choice :: r ->
    //   if length r + 1 <= n
    //   then begin
    //     iter_fix_guarded step r (n-1) j ;
    //     iter_fix_guarded step r (length p - 1) j
    //   end
    //   else ()
    // | _ -> ()
    // end
    admit ()
  | Some (Inr r, q) -> ()
  | None -> ()

let iter (#op : eqtype) #s #ind #a (step : ind -> itree op s (either ind a)) : ind -> itree op s a =
  forall_intro_3 (iter_fix_guarded step) ;
  itree_cofix (iter_fix step)

(** Position streams

   Potentially infinite counterpart to iopos.

*)
let postream op s =
  stream (ichoice op s)

(** Properties on repeat *)

let repeat_unfold_1 #op #s (body : itree op s unit) :
  Lemma (forall p. repeat body p == bind body (fun _ -> tau ((if length p = 0 then (fun _ -> loop _) else itree_cofix_unfoldn (repeat_fix body) (length p - 1)) ())) p)
= forall_intro (itree_cofix_unfold_1 (repeat_fix body) ()) ;
  forall_intro_2 (repeat_fix_guarded body) ;
  assert (forall p. itree_cofix (repeat_fix body) () p == repeat_fix body (if length p = 0 then (fun _ -> loop _) else itree_cofix_unfoldn (repeat_fix body) (length p - 1)) () p) ;
  assert (forall p. itree_cofix (repeat_fix body) () p == bind body (fun _ -> tau ((if length p = 0 then (fun _ -> loop _) else itree_cofix_unfoldn (repeat_fix body) (length p - 1)) ())) p)

let repeat_one_ret #op #s (body : itree op s unit) :
  Lemma (forall p q. isRet (body p) ==> repeat body (p @ Tau_choice :: q) == repeat body q)
= repeat_unfold_1 body ;
  find_ret_append body ;
  assert (forall p q.
    isRet (body p) ==>
    repeat body (p @ Tau_choice :: q) == itree_cofix_unfoldn (repeat_fix body) (length (p @ Tau_choice :: q) - 1) () q
  ) ;
  forall_intro_2 (repeat_fix_guarded body)

let rec repeat_not_ret #op #s (body : itree op s unit) p :
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

let rec repeat_any_ret #op #s (body : itree op s unit) (pl : list (ipos op s)) p :
  Lemma
    (requires forall pp. mem pp pl ==> isRet (body pp))
    (ensures repeat body (flatten_sep [Tau_choice] pl @ p) == repeat body p)
= match pl with
  | [] -> ()
  | pp :: pl ->
    calc (==) {
      repeat body (flatten_sep [Tau_choice] (pp :: pl) @ p) ;
      == {}
      repeat body ((pp @ [Tau_choice] @ flatten_sep [Tau_choice] pl) @ p) ;
      == { forall_intro_3 (append_assoc #(ichoice op s)) }
      repeat body (pp @ Tau_choice :: (flatten_sep [Tau_choice] pl @ p)) ;
      == { repeat_one_ret body }
      repeat body (flatten_sep [Tau_choice] pl @ p) ;
      == { repeat_any_ret body pl p }
      repeat body p ;
    }
