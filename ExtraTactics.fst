module ExtraTactics

open FStar.Tactics

(** This was just a exercise for me. This is equivalent to `:|` operator from Dafny **)
val forall_x_0 :
  (p:    ('a -> Type0)) ->
  (post: (x:'a{p x} -> Type0)) ->
  (f:    (x:'a -> Lemma (requires (p x)) (ensures (post x)))) ->
  (x : 'a{p x}) ->
  Lemma (post x)
let forall_x_0 p post f x = f x

let forall_x_cond p post f :
  Lemma (forall x. post x) = Classical.forall_intro (forall_x_0 p post f)

let forall_x post f :
  Lemma (forall x. post x) = Classical.forall_intro (forall_x_0 (fun _ -> True) post f)

let grewrite_eq (b:binder) : Tac unit =
  match term_as_formula (type_of_binder b) with
  | Comp (Eq _) l r ->
    grewrite l r;
    iseq [idtac; (fun () -> exact (binder_to_term b))]
  | _ -> fail "failed in grewrite_eq"


// let rec extract_nth (n:nat) (l : list 'a) : option ('a * list 'a) =
//   match n, l with
//   | _, [] -> None
//   | 0, hd::tl -> Some (hd, tl)
//   | _, hd::tl -> begin
//     match extract_nth (n-1) tl with
//     | Some (hd', tl') -> Some (hd', hd::tl')
//     | None -> None
//   end

// let bump_nth (n:pos) : Tac unit =
//   // n-1 since goal numbering begins at 1
//   match extract_nth (n - 1) (goals ()) with
//   | None -> fail "bump_nth: not that many goals"
//   | Some (h, t) -> set_goals (h :: t)


private
let rec innermost_sc (t:term) : Tac term =
  match inspect t with
  | Tv_Match s _ _ -> innermost_sc s
  | _ -> t

let get_match_body () : Tac term =
  match FStar.Reflection.Formula.unsquash (cur_goal ()) with
  | None -> fail "Goal is not squashed"
  | Some t -> match inspect t with
             | Tv_Match sc _ _ -> innermost_sc sc
             | _ -> fail "Goal is not a match"

let rec last (x : list 'a) : Tac 'a =
    match x with
    | [] -> fail "last: empty list"
    | [x] -> x
    | _::xs -> last xs

(** When the goal is [match e with | p1 -> e1 ... | pn -> en],
destruct it into [n] goals for each possible case, including an
hypothesis for [e] matching the correposnding pattern. *)

let let_intro () : Tac unit =
    focus (fun () ->
      let x = get_match_body () in
      let _ = t_destruct x in
      iterAll (fun () -> ignore (intro ()); ignore (intro ()); grewrite_eq (intro ()))
    )

let rewrite_lemma n m : Tac unit =
    (** n is for the index of the wp
        m is for the index of the pure_result:unit **)
    let zz = nth_binder n in
    let zz' = nth_binder m in
    let b' = instantiate (binder_to_term zz) (binder_to_term zz') in
    mapply (binder_to_term b');
    ignore (trytac (fun () -> clear b'; clear zz; clear zz'))
    
let rewrite_lemma_2 n m m' : Tac unit =
    (** n is for the index of the wp
        m is for the index of the pure_result:unit **)
    let zz = nth_binder n in
    let zz' = nth_binder m in
    let zz'' = nth_binder m' in
    let b' = instantiate (binder_to_term zz) (binder_to_term zz') in
    let b'' = instantiate (binder_to_term b') (binder_to_term zz'') in
    ignore (trytac (fun () -> mapply (binder_to_term b'')));
    ignore (trytac (fun () -> clear b'; clear zz; clear zz'; clear zz''; clear b''))
 
    // by (explode (); bump_nth 3; 
    // let bs = List.Tot.map (fun (_, b) -> b) (skolem ()) in
    // iter (fun b -> ignore (trytac (fun () -> ignore (destruct_and (binder_to_term b))))) bs;
    // rewrite_eqs_from_context ();
    // let _ = l_intros () in
    // split ();
    // bump_nth 2;
    // explode ();
    // // let f = cur_formula () in
    // // dump (term_to_string (quote f));
     
    // //branch_on_match (); 
    // dump "H") =

let copy_binder (b:binder) : Tac binder =
  focus (fun () ->
    let nb = tcut (type_of_binder b) in
    flip ();
    exact (binder_to_term b);
    nb
  )

  
let rec instantiate_n_times_with_none (b:binder) (n : nat{n>0}) : Tac binder =
  let b' = instantiate b (fresh_uvar None) in
  if n = 1 then b else (
    let r = instantiate_n_times_with_none b' (n-1) in
    clear b';
    r
  )


let rec instantiate_multiple_foralls (b:binder) (l : list term) : Tac binder =
  match l with
  | [] -> b
  | h :: tail ->
    let b' = instantiate (binder_to_term b) h in
    let r = instantiate_multiple_foralls b' tail in
    (if List.length tail = 0 then ()
    else clear b');
    r

let rec blowup_binder (x:term) (x':binder) : Tac unit =
  match term_as_formula' x with
  | And a b ->
    let a', b' = destruct_and (binder_to_term x') in
    clear x';
    blowup_binder a a';
    blowup_binder b b'
  | Comp (Eq _) v _ -> (
    match inspect v with
    | Tv_Var _
    | Tv_BVar _
    | Tv_FVar _ ->
      ignore (trytac (fun () ->
        rewrite x'; norm [iota]))
    | _ -> ())
  | _ -> ()

let rec blowup () : Tac unit =
  let goal = cur_goal () in
  match term_as_formula goal with
  | Forall _ _ -> ignore (forall_intro ()); blowup ()
  | And _ _ ->
      focus (fun () -> split (); iterAll blowup)
  | Implies x _ ->
      let x' = implies_intro () in
      blowup_binder x x';
      blowup ()
  | _  -> ()
  // begin
  //   let goal = FStar.Reflection.Formula.unsquash goal in
  //   match goal with
  //   | None -> ()
  //   | Some goal -> (
  //   print (term_to_string goal);
  //   match inspect goal with
  //   | Tv_Match sc _ ->
  //     print "Este match!";
  //     let x = innermost_sc sc in
  //     focus (fun () ->
  //     ignore (trytac (fun () ->
  //       let _ = t_destruct x in
  //       iterAll (fun () →
  //         let bs = repeat intro in
  //         let b = last bs in (* this one is the equality *)
  //         grewrite_eq b;
  //         // rewrite_eqs_from_context ();
  //         norm [iota];
  //         blowup ()))))
  //   | _ -> print "Nu este match!"; ())
  // end

let branch_on (b:binder) : Tac unit =
    focus (fun () ->
      destruct b;
      iterAll (fun () ->
        let _ = intro () in
        let b = intro () in
        rewrite b;
        norm [iota])
    )


let implies_elim (#p #q: prop)
                 (i: (p ==> q))
                 (j: p)
   : squash q
   = ()
let apply_in (t:term) (b:binder) : Tac binder =
  let p =
   Tv_App (Tv_App (`implies_elim) (t, Q_Explicit))
          (binder_to_term b, Q_Explicit)
  in
  print (term_to_string p);
  pose p
