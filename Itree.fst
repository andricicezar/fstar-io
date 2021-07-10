module Itree

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Classical

(* Similar to strict_prefix_of, I believe the names should be swapped but well... *)
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
  Lemma (ensures s `strict_suffix_of` l ==> length s <= length l) (decreases l)
= match l with
  | [] -> ()
  | x :: l ->
    match s with
    | [] -> ()
    | y :: s -> strict_suffix_length s l

noeq
type sig a (b : a -> Type) =
| Dpair : x:a -> b x -> sig a b

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

let cast_node #op #s #a #b (n : (option (inode op s a)) { ~ (isRet n) }) : option (inode op s b) =
  match n with
  | Some Tau -> Some Tau
  | Some (Call o x) -> Some (Call o x)
  | None -> None

let bind #op #s #a #b (m : itree op s a) (f : a -> itree op s b) : itree op s b =
  find_ret_strict_suffix m ;
  fun p ->
    match find_ret m [] p with
    | Some (x, q) -> f x q
    | None -> find_ret_None_noRet m [] p ; cast_node (m p)

(* A loop with no events/effects except non-termination *)
let loop #op #s a : itree op s a =
  fun p -> Some Tau

let cont #op #s #a (n : inode op s a) r =
  match n with
  | Ret x -> unit
  | Call o x -> s.res o -> r
  | Tau -> r

let cont_node op s a r =
  sig (inode op s a) (fun n -> cont n r)

let rec itree_corec_aux (#op : eqtype) #s #a #b (f : a -> cont_node op s b a) (i : a) (p : ipos op s) :
  Pure (option (inode op s b)) (requires True) (ensures fun r -> True) (decreases p)
= match p with
  | [] ->
    let Dpair n _ = f i in Some n
  | Tau_choice :: p ->
    begin match f i with
    | Dpair Tau next -> itree_corec_aux f next p
    | _ -> None
    end
  | Call_choice o x y :: p ->
    begin match f i with
    | Dpair (Call o' x') next ->
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
    | Dpair (Ret x) n -> ()
    | Dpair Tau n -> ()
    | Dpair (Call o' x') n -> ()
    end
  | Tau_choice :: p ->
    begin match f i with
    | Dpair (Ret x) n -> ()
    | Dpair Tau n ->
      begin match q with
      | [] -> ()
      | Tau_choice :: q -> itree_corec_aux_final_ret f n p q
      | Call_choice o x y :: q -> ()
      end
    | Dpair (Call o' x') n -> ()
    end
  | Call_choice o x y :: p ->
    begin match f i with
    | Dpair (Ret x) n -> ()
    | Dpair Tau n -> ()
    | Dpair (Call o' x') n ->
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

// Some notion of cofixpoint where the function should produce at least one constructor
// before calling itself recursively.

// For some reason I have to force Type0 for a and b
noeq
type guarded_gen (#op : eqtype) #s (#a : Type0) (#b : Type0) : ((a -> itree op s b) -> itree op s b) -> Type0 =
| Guarded_ret : u:b -> guarded_gen #op #s #a #b (fun r -> ret u)
| Guarded_tau_rec : x:a -> guarded_gen #op #s #a #b (fun r -> tau (r x))
| Guarded_call_rec : o:op -> arg:(s.args o) -> k:(s.res o -> a) -> guarded_gen #op #s #a #b (fun r -> call o arg (fun z -> r (k z)))
| Guarded_tau : g:((a -> itree op s b) -> itree op s b) -> guarded_gen g -> guarded_gen #op #s #a #b (fun r -> tau (g r))
| Guarded_call : o:op -> arg:(s.args o) -> g:(s.res o -> (a -> itree op s b) -> itree op s b) -> (z:(s.res o) -> guarded_gen (g z)) -> guarded_gen #op #s #a #b (fun r -> call o arg (fun z -> g z r))

type cofix_gen (op : eqtype) s (a : Type0) (b : Type0) =
  g:((a -> itree op s b) -> itree op s b) { guarded_gen g }

let itree_cofix_guarded (#op : eqtype) #s #a #b (ff : (a -> itree op s b) -> a -> itree op s b) =
  forall x. exists (g : cofix_gen op s a b). forall r. ff r x == g r

// Unfold the function (n+1) times
let rec itree_cofix_unfoldn (#op : eqtype) #s #a #b (ff : (r:(a -> itree op s b)) -> a -> itree op s b) (n : nat) : a -> itree op s b =
  if n = 0
  then ff (fun _ -> loop _)
  else ff (itree_cofix_unfoldn ff (n - 1))

let rec guarded_gen_at (#op : eqtype) #s (#a : Type0) (#b : Type0) (g : (a -> itree op s b) -> itree op s b) (h : guarded_gen g) (p : ipos op s) :
  Pure (option (ipos op s * a)) (requires True) (ensures fun o -> match o with | None -> exists c. forall r. g r p == c | Some (q, v) -> q << p /\ length q < length p /\ (forall r. g r p == r v q)) (decreases p)
= match h with
  | Guarded_ret u ->
    exists_intro (fun c -> ret u p == c) (ret u p) ;
    None
  | Guarded_tau_rec u ->
    begin match p with
    | [] -> exists_intro (fun c -> forall (r : (a -> itree op s b)). tau (r u) [] == c) (Some Tau) ; None
    | Tau_choice :: q -> Some (q, u)
    | Call_choice o' arg' y :: q -> exists_intro (fun c -> forall (r : (a -> itree op s b)). tau (r u) p == c) None ; None
    end
  | Guarded_call_rec o arg k ->
    begin match p with
    | [] -> exists_intro (fun c -> forall (r : (a -> itree op s b)). call o arg (fun z -> r (k z)) [] == c) (Some (Call o arg)) ; None
    | Tau_choice :: q -> exists_intro (fun c -> forall (r : (a -> itree op s b)). call o arg (fun z -> r (k z)) p == c) None ; None
    | Call_choice o' arg' y :: q ->
      if o = o' && arg = arg'
      then Some (q, k y)
      else begin exists_intro (fun c -> forall (r : (a -> itree op s b)). call o arg (fun z -> r (k z)) p == c) None ; None end
    end
  | Guarded_tau g' h' ->
    begin match p with
    | [] -> exists_intro (fun c -> forall (r : (a -> itree op s b)). tau (g' r) [] == c) (Some Tau) ; None
    | Tau_choice :: q -> guarded_gen_at g' h' q
    | Call_choice o' arg' y :: q -> exists_intro (fun c -> forall (r : (a -> itree op s b)). tau (g' r) p == c) None ; None
    end
  | Guarded_call o arg g' h' ->
    begin match p with
    | [] -> exists_intro (fun c -> forall (r : (a -> itree op s b)). call o arg (fun z -> g' z r) [] == c) (Some (Call o arg)) ; None
    | Tau_choice :: q -> exists_intro (fun c -> forall (r : (a -> itree op s b)). call o arg (fun z -> g' z r) p == c) None ; None
    | Call_choice o' arg' y :: q ->
      if o = o' && arg = arg'
      then guarded_gen_at (g' y) (h' y) q
      else begin exists_intro (fun c -> forall (r : (a -> itree op s b)). call o arg (fun z -> g' z r) p == c) None ; None end
    end

let rec itree_cofix_unfoldn_enough_aux (#op : eqtype) #s #a #b (g : a -> (a -> itree op s b) -> itree op s b) (h : (x:a) -> guarded_gen (g x)) (x : a) (n : nat) (p : ipos op s) :
  Lemma (ensures length p <= n ==> itree_cofix_unfoldn (fun r x -> g x r) (length p) x p == itree_cofix_unfoldn (fun r x -> g x r) n x p) (decreases p)
= match h x with
  | Guarded_ret u -> ()
  | Guarded_tau_rec u ->
    begin match p with
    | [] -> ()
    | Tau_choice :: p ->
      if length p + 1 <= n
      then itree_cofix_unfoldn_enough_aux g h u (n-1) p
      else ()
    | Call_choice _ _ _ :: p -> ()
    end
  | Guarded_call_rec o arg k ->
    begin match p with
    | [] -> ()
    | Tau_choice :: p -> ()
    | Call_choice o' arg' y :: p ->
      if o = o' && arg = arg'
      then begin
        if length p + 1 <= n
        then itree_cofix_unfoldn_enough_aux g h (k y) (n-1) p
        else ()
      end
      else ()
    end
  | Guarded_tau g' h' ->
    begin match p with
    | [] -> ()
    | Tau_choice :: p ->
      begin match guarded_gen_at g' h' p with
      | None -> ()
      | Some (q, v) ->
        if length p + 1 <= n
        then begin
          itree_cofix_unfoldn_enough_aux g h v (n-1) q ;
          itree_cofix_unfoldn_enough_aux g h v (length p) q
        end
        else ()
      end
    | Call_choice _ _ _ :: p -> ()
    end
  | Guarded_call o arg g' h' ->
    begin match p with
    | [] -> ()
    | Tau_choice :: p -> ()
    | Call_choice o' arg' y :: p ->
      if o = o' && arg = arg'
      then begin
        begin match guarded_gen_at (g' y) (h' y) p with
        | None -> ()
        | Some (q, v) ->
          if length p + 1 <= n
          then begin
            itree_cofix_unfoldn_enough_aux g h v (n-1) q ;
            itree_cofix_unfoldn_enough_aux g h v (length p) q
          end
          else ()
        end
      end
      else ()
    end

// It might be better to let go of this condition and use Tau padding instead
// and find a way to enforce the valid_itree condition rather than productivity.
let rec itree_cofix_unfoldn_enough (#op : eqtype) #s #a #b (ff : (a -> itree op s b) -> a -> itree op s b) (x : a) (n : nat) (p : ipos op s) :
  Lemma
    (ensures itree_cofix_guarded ff ==> length p <= n ==> itree_cofix_unfoldn ff (length p) x p == itree_cofix_unfoldn ff n x p)
= match p with
  | [] ->
    assume (itree_cofix_guarded ff ==> ff (fun _ -> loop _) x [] == itree_cofix_unfoldn ff n x []) ;
    assume (itree_cofix_unfoldn ff 0 == ff (fun _ -> loop _)) ; // why can't the SMT see it?
    assert (itree_cofix_guarded ff ==> itree_cofix_unfoldn ff 0 x [] == itree_cofix_unfoldn ff n x [])
  | c :: p ->
    // assume (itree_cofix_guarded ff ==> length p + 1 <= n ==> itree_cofix_unfoldn ff (length p + 1) x (c :: p) == itree_cofix_unfoldn ff n x (c :: p))
    assume (itree_cofix_guarded ff ==> length p + 1 <= n ==> ff (itree_cofix_unfoldn ff (length p)) x (c :: p) == ff (itree_cofix_unfoldn ff (n-1)) x (c :: p))
    // match ff (fun _ -> loop _) x [] with
    // | Some (Ret y) -> ()
    // | Some (Call o arg) -> admit ()
    // | Some Tau ->
    //   assert (itree_cofix_guarded ff ==> (forall r. exists k. ff r x == tau k)) ;
    //   // We now know how ff will behave on (Tau_choice :: p), it will call k p
    //   // but we don't know anything about the two k that we have, only that they depend on the recursive call
    //   // can we be more precise in itree_productive?
    //   begin match c with
    //   | Tau_choice -> admit ()
    //   | Call_choice _ _ _ -> ()
    //   end
    // | None -> ()

    // if length (c :: p) <= n
    // then begin
    //   itree_cofix_unfoldn_enough ff x (n-1) p ;
    //   admit ()
    // end
    // else ()

let itree_cofix (#op : eqtype) #s #a #b (ff : (r:(a -> itree op s b)) -> a -> itree op s b) (x : a) :
  Pure (itree op s b) (requires itree_cofix_guarded ff) (ensures fun _ -> True)
= forall_intro_2 (itree_cofix_unfoldn_enough ff x) ;
  fun p -> itree_cofix_unfoldn ff (length p) x p

// Coq def:
// Definition iter {E : Type -> Type} {R I: Type}
//            (step : I -> itree E (I + R)) : I -> itree E R :=
//   cofix iter_ i := bind (step i) (fun lr => on_left lr l (Tau (iter_ l))).

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
  For now only simple spec monad without trace.
  For later, the trace can be read from the position + eventually the node it leads to.
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
  find_ret_append m ;
  assert (forall p q. isRet (m p) ==> find_ret m [] (p @ q) == Some (ret_val (m p), q)) ;
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

(*
  Spec with trace
  The trace contains the response of the environment, in fact it is a subset of positions
  where Tau steps are ignored.

  This specification if enough to talk about (non)-termination of a program with respect to
  its interaction with the environmnet.
*)

let trace = list (c: ichoice cmds io_op_sig { c <> Tau_choice })

let rec ipos_trace (p : ipos cmds io_op_sig) : trace =
  match p with
  | [] -> []
  | Tau_choice :: p -> ipos_trace p
  | Call_choice o x y :: p -> Call_choice o x y :: ipos_trace p

let rec ipos_trace_append (p q : ipos cmds io_op_sig) :
  Lemma (ensures ipos_trace (p @ q) == ipos_trace p @ ipos_trace q) (decreases p)
= match p with
  | [] -> ()
  | Tau_choice :: p -> ipos_trace_append p q
  | Call_choice o x y :: p -> ipos_trace_append p q

let twp a = (trace -> option a -> Type0) -> Type0

let twp_return #a (x : a) : twp a =
  fun post -> post [] (Some x)

let shift_post #a (tr : trace) (post : trace -> option a -> Type0) =
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

// let io_twp #a (t : itree cmds io_op_sig a) =
//   fun post -> forall p. Some? (t p) ==> post (ipos_trace p) (match t p with Some (Ret x) -> Some x | _ -> None)

// Equivalent but maybe nicer for the SMT
let io_twp #a (t : itree cmds io_op_sig a) =
  fun post ->
    (forall p. isRet (t p) ==> post (ipos_trace p) (Some (ret_val (t p)))) /\
    (forall p. isEvent (t p) ==> post (ipos_trace p) None)

let tio a (w : twp a) =
  t:itree cmds io_op_sig a { io_twp t `stronger_twp` w }

let tio_return a (x : a) : tio a (twp_return x) =
  assert (isRet (ret #cmds #io_op_sig #a x [])) ;
  ret x

let tio_bind a b w wf (m : tio a w) (f : (x:a) -> tio b (wf x)) : tio b (twp_bind w wf) =
  find_ret_append m ;
  assert (forall p q. isRet (m p) ==> find_ret m [] (p @ q) == Some (ret_val (m p), q)) ;
  assert (forall p q. isRet (m p) ==> isRet (f (ret_val (m p)) q) ==> ret_val (bind m f (p @ q)) == ret_val (f (ret_val (m p)) q)) ;
  assert (forall post p q. io_twp (bind m f) post ==> isRet (m p) ==> isRet (f (ret_val (m p)) q) ==> post (ipos_trace (p @ q)) (Some (ret_val (bind m f (p @ q))))) ;
  assert (forall post p q. io_twp (bind m f) post ==> isRet (m p) ==> isRet (f (ret_val (m p)) q) ==> post (ipos_trace (p @ q)) (Some (ret_val (f (ret_val (m p)) q)))) ;
  assert (forall post p q. io_twp (bind m f) post ==> isRet (m p) ==> isEvent (f (ret_val (m p)) q) ==> post (ipos_trace (p @ q)) None) ;
  assert (forall x. io_twp (f x) `stronger_twp` (wf x)) ;
  forall_intro_2 ipos_trace_append ;
  assert (forall post p. io_twp (bind m f) post ==> isRet (m p) ==> wf (ret_val (m p)) (shift_post (ipos_trace p) post)) ;

  forall_intro (move_requires (find_ret_Event_None m [])) ;
  assert (forall p. isEvent (m p) ==> find_ret m [] p == None) ;
  assert (forall p. isEvent (m p) ==> isEvent (bind m f p)) ;
  assert (forall post p. io_twp (bind m f) post ==> isEvent (m p) ==> post (ipos_trace p) None) ;

  bind m f

[@@allow_informative_binders]
reifiable total layered_effect {
  TIO : a:Type -> twp a -> Effect
  with
    repr   = tio ;
    return = tio_return ;
    bind   = tio_bind
}
