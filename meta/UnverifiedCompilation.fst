module UnverifiedCompilation

open HelperTactics

type open_stlc_term (g:STLC.env) =
  (e:STLC.exp & t:STLC.typ & STLC.typing g e t)

type open_stlc_term' (g:STLC.env) (t:STLC.typ) =
  (e:STLC.exp & STLC.typing g e t)

let rec make_stlc_nat #g (n:nat) : open_stlc_term' g STLC.TNat = 
  match n with
  | 0 -> (| _, STLC.TyZero |)
  | _ -> 
    let (|_, tyj |) = make_stlc_nat (n-1) in
    (| _, STLC.TySucc tyj |)

let rec unverified_typ_translation
  (gfs:env)
  (qfs:term)
  : TacP STLC.typ
      (requires True)
      (ensures fun _ -> True) =    
  match inspect qfs with
  | Tv_FVar fv -> begin
    match fv_to_string fv with
    | "Prims.int" -> STLC.TNat
    | _ ->
      let qfs' = norm_term_env gfs [delta] qfs in
      (* avoid infinite loop by checking if axiom *)
      if tag_of qfs' <> "Tv_FVar" then unverified_typ_translation gfs qfs'
      else fail (fv_to_string fv ^ " not defined")
  end

  | Tv_Arrow b c ->  begin
    let tbv = unverified_typ_translation gfs b.sort in
    match c with
    | C_Total ret -> 
      let tc = unverified_typ_translation gfs ret in
      STLC.TArr tbv tc
    | _ -> fail ("not a total function type")
  end
  | Tv_Var v -> fail "fvar"

  (** erase refinement **)
  | Tv_Refine b _ -> unverified_typ_translation gfs b.sort

  | Tv_Const c -> fail (print_vconst c)

  | Tv_Unknown -> fail ("an underscore was found in the term")
  | Tv_Unsupp -> fail ("unsupported by F* terms")

  | _ -> fail ("not implemented")

let comp_typ (nm:string) (qfs:term) : dsl_tac_t = fun g ->
  let typ= unverified_typ_translation g qfs in

  let qtyp = quote typ in
  type_dynamically g qtyp (`STLC.typ);

  [
   mk_checked_let g nm qtyp (`STLC.typ);
  ]  

%splice_t[typ1] (comp_typ "typ1" (`(int)))
let _ = assert (typ1 == STLC.TNat)

%splice_t[typ2] (comp_typ "typ2" (`(nat)))
let _ = assert (typ2 == STLC.TNat)

%splice_t[typ3] (comp_typ "typ3" (`(nat -> nat)))
let _ = assert (typ3 == STLC.TArr STLC.TNat STLC.TNat)

let recover_type_of_arrow (gfs:env) (qfs:term) (t:term) : 
  TacP (option binder)
    (requires True) // (exists t'. tot_typing gfs hd (Tv_Arrow t' t)));
    (ensures fun _ -> True) // Some? r ==> tot_typing gfs hd (Tv_Arrow (Some?.v r) t)))
  = 
  match inspect qfs with
  | Tv_Abs b c -> Some b
  | _ -> None

noeq
type fs_var =
| FVar : fv -> fs_var
| Var  : namedv -> fs_var
| Bv   : bv -> fs_var

(* CA: keeping track of the type of the term is important for the logical relation *)
let rec unverified_exp_translation
  (gfs:env)
  (gstlc:STLC.env)
  (vars_mapping:fs_var -> nat -> option (x:STLC.var{Some? (gstlc x)}))
  (qfs:term)
  : TacP (open_stlc_term gstlc)
      (requires True)
      (ensures fun _ -> True) =
  match inspect qfs with
  | Tv_FVar fv -> begin
    match vars_mapping (FVar fv) 0 with
    | Some v -> (| _, _, STLC.TyVar #gstlc v |)
    | None -> fail (fv_to_string fv ^ " not defined")
  end

  | Tv_Var v -> begin
    match vars_mapping (Var v) 0 with
    | Some dbi -> (| STLC.EVar dbi, Some?.v (gstlc dbi), STLC.TyVar #gstlc dbi |)
    | None -> fail (print_nat v.uniq ^ " not defined in STLC env")
  end

  | Tv_App hd (a, q) -> begin
    (** TODO: it seems like we cannot get the type of `hd` or `a` here because
              we don't have the typing judgment of `qfs`.
              Even if we would ask for the F* typing judgement of `qfs`,
              it could be just a token---not helpful.
              Maybe there is a way to recover by normalizing a bit `hd`?
          QA: How would this work with the logical relation? **) 
    // assert (forall t. tot_typing gfs (Tv_App hd (a, _)) qty ==> 
    //           (exists t'. tot_typing gfs a t' /\ tot_typing gfs hd (Tv_Arrow t' qty)));
    // assert (forall t. tot_typing gfs (Tv_App hd (a, _)) qty ==> 
    //           (forall t'. tot_typing gfs hd (Tv_Arrow t' qty) ==> tot_typing gfs a t'));
    let (| _, sa_ty, sa_tyj |) = unverified_exp_translation gfs gstlc vars_mapping a in
    let (| _, shd_ty, shd_tyj |) = unverified_exp_translation gfs gstlc vars_mapping hd in
    match shd_ty with
    | STLC.TArr arg res -> 
      if arg = sa_ty then (| _, res, STLC.TyApp shd_tyj sa_tyj |)
      else fail ("argument type mismatch")
    | _ -> fail ("hd is not an arrow type")
    end

  | Tv_Abs b c -> begin
    let b_ty : STLC.typ = unverified_typ_translation gfs b.sort in
    let gstlc' = STLC.extend b_ty gstlc in
    let vars_mapping': fs_var -> int -> option (x:STLC.var{Some? (gstlc' x)}) =
      (fun x n -> match x with 
          | Var v -> if v.uniq = b.uniq then (admit (); Some n) else (admit (); vars_mapping x (n+1))
          | _ -> (admit (); vars_mapping x (n+1))) in
    let gfs' = extend_env gfs b.uniq b.sort in
    let (| c_e, c_ty, c_tyj |) = unverified_exp_translation gfs' gstlc' vars_mapping' c in
    (| _, _, STLC.TyLam #gstlc b_ty c_tyj |) 
  end

  | Tv_Const (C_Int x) ->
    if (x < 0) then fail ("not supporting ints, only nats") else
    let (| e, tyj |) = make_stlc_nat x in
    (| e, STLC.TNat, tyj |)

  | Tv_Unknown -> fail ("an underscore was found in the term")
  | Tv_Unsupp -> fail ("unsupported by F* terms")

  | _ -> dump (tag_of qfs); fail ("not implemented")

let mk_stlc_typing (g qexp qtyp:term) =
  mk_app (`STLC.typing) [(g, Q_Explicit); (qexp, Q_Explicit); (qtyp, Q_Explicit)]	

let comp_exp (nm:string) (qfs:term) : dsl_tac_t = fun g ->
  let qfs = norm_term_env g [delta] qfs in
  let (| exp, typ, tyj |) : open_stlc_term STLC.empty =
    unverified_exp_translation g STLC.empty (fun _ _ -> None) qfs in
  let qexp = quote exp in
  type_dynamically g qexp (`STLC.exp);
  let qtyp = quote typ in
  type_dynamically g qtyp (`STLC.typ);
  let qtyj = quote tyj in
  let qtyj_ty = mk_stlc_typing (`STLC.empty) qexp qtyp in
  assert (has_type tyj (STLC.typing STLC.empty exp typ));
  // type_dynamically g qtyj qtyj_ty;
  assume (tot_typing g qtyj qtyj_ty);
  [
   mk_checked_let g nm qexp (`STLC.exp);
   mk_checked_let g (nm^"_typ") qtyp (`STLC.typ);
   mk_checked_let g (nm^"_tyj") qtyj qtyj_ty;
  ]



let stlc_sem (#e:STLC.exp) (#t:STLC.typ) (ht:STLC.typing STLC.empty e t) : STLC.elab_typ t = 
  let (| _, ht' |) = STLC.eval ht in
  STLC.elab_exp ht' STLC.vempty

let src1 : nat = 4
%splice_t[tgt1;tgt1_typ;tgt1_tyj] (comp_exp "tgt1" (`src1))
let _ = 
  assert (tgt1 == STLC.ESucc (STLC.ESucc (STLC.ESucc (STLC.ESucc STLC.EZero))));
  assert (stlc_sem tgt1_tyj == src1)

// let src2 : nat = 4+5
// %splice_t[tgt2;tgt2_typ;tgt2_tyj] (comp_exp "tgt2" (`src2))

// let _ = 
//   assert (tgt2 == STLC.EZero)

let src3 : nat -> nat -> nat = fun x y -> x
%splice_t[tgt3;tgt3_typ;tgt3_tyj] (comp_exp "tgt3" (`src3))

let test () =
  assert (tgt3_typ == STLC.TArr STLC.TNat (STLC.TArr STLC.TNat STLC.TNat));
  assert (tgt3 == STLC.ELam STLC.TNat (STLC.ELam STLC.TNat (STLC.EVar 1)));
  assert (forall x y. (stlc_sem tgt3_tyj) x y == src3 x y)