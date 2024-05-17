module UnverifiedCompilation

open HelperTactics

open FStar.Tactics.V2
open FStar.Reflection.Typing
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data

noeq
type fs_var =
| FVar : fv -> fs_var
| BVar : var -> fs_var

type mapping (g:STLC.context) =
  fs_var -> option (x:STLC.var{Some? (g x)})

let incr_option (#g:STLC.context) (#b_ty:STLC.typ) (x:option (y:STLC.var{Some? (g y)})) : 
  option (y:STLC.var{Some? (STLC.extend b_ty g y)}) =
  match x with
  | Some n -> Some (n+1)
  | None -> None

let extend_gmap_binder
  (#gstlc:STLC.context)
  (gmap:mapping gstlc) 
  (b_ty:STLC.typ)
  : mapping (STLC.extend b_ty gstlc) =
  (fun x -> match x with 
      | BVar v -> if v = 0 then Some 0 else incr_option (gmap (BVar (v-1))) //Some v
      | _ -> incr_option (gmap x))

let extend_gmap
  (#gstlc:STLC.context)
  (gmap:mapping gstlc) 
  (b:string)
  (b_ty:STLC.typ)
  : mapping (STLC.extend b_ty gstlc) =
  (fun x -> match x with 
      | FVar v -> if fv_to_string v = b then Some 0 else (incr_option (gmap x))
      | _ -> (incr_option (gmap x)))

type axiom_ty = string & e:STLC.exp{~(STLC.EVar? e)} & ty:STLC.typ & STLC.typing STLC.empty e ty
let axioms_mapping : list axiom_ty = [
  (| "Prims.op_Addition", _, _, STLC.op_add_tyj |);
  (| "Prims.op_LessThanOrEqual", _, _, STLC.op_lte_tyj |)
//  (| "Prims.op_Multiply", STLC.op_mul, STLC.op_mul_ty, STLC.op_mul_tyj |);
//  (| "Prims.op_Negation", STLC.op_neg, STLC.op_neg_ty, STLC.op_neg_tyj |);
//  (| "Prims.op_AmpAmp", STLC.op_and, STLC.op_and_ty, STLC.op_and_tyj |);
//  (| "Prims.op_BarBar", STLC.op_or, STLC.op_or_ty, STLC.op_or_tyj |)
]

type open_stlc_term' (g:STLC.context) (t:STLC.typ) =
  (e:STLC.exp & STLC.typing g e t)

let rec make_stlc_nat #g (n:nat) : open_stlc_term' g STLC.TNat = 
  match n with
  | 0 -> (| _, STLC.TyZero |)
  | _ -> 
    let (|_, tyj |) = make_stlc_nat (n-1) in
    (| _, STLC.TySucc tyj |)

let rec typ_translation (qfs:term) : Tac STLC.typ = 
  match inspect_ln qfs with
  | Tv_FVar fv -> begin
    match fv_to_string fv with
    | "Prims.nat" -> STLC.TNat
    | _ -> fail ("Type " ^ fv_to_string fv ^ " not supported")
  end

  | Tv_Arrow b c ->  begin
    let tbv = typ_translation (binder_sort b) in
    match inspect_comp c with
    | C_Total ret -> 
      let tc = typ_translation ret in
      STLC.TArr tbv tc
    | _ -> fail ("not a total function type")
  end

  (** erase refinement **)
  | Tv_Refine b _ -> 
    let b = inspect_binder b in
    typ_translation b.sort

  | Tv_Unknown -> fail ("an underscore was found in the term")
  | Tv_Unsupp -> fail ("unsupported by F* terms")

  | _ -> fail ("not implemented: " ^ tag_of qfs)

let comp_typ (nm:string) (qfs:term) : dsl_tac_t = fun g ->
  let typ = typ_translation qfs in

  let qtyp = quote typ in
  type_dynamically g qtyp (`STLC.typ);

  [
   mk_checked_let g nm qtyp (`STLC.typ);
  ]  

%splice_t[typ2] (comp_typ "typ2" (`(nat)))
let _ = assert (typ2 == STLC.TNat)

%splice_t[typ3] (comp_typ "typ3" (`(nat -> nat)))
let _ = assert (typ3 == STLC.TArr STLC.TNat STLC.TNat)

let pattern_tag (t:pattern) : string =
  match t with
  | Pat_Var _ _ -> "Pat_Var"
  | Pat_Constant _ -> "Pat_Constant"
  | Pat_Cons _ _ _-> "Pat_Cons"
  | Pat_Dot_Term _ -> "Pat_Dot_Term"

let ptyp #g (s:STLC.open_term g) : STLC.typ = Mkdtuple3?._2 s


(* CA: keeping track of the type of the term is important for the logical relation.
  However, because we lack a proper typing judgement for the F* term, sometimes we don't have
  the type of a subterm (e.g., hd in App and sc in Match branches). 
  However, Guido pointed out that we need this for the logical relation, which is spec, so we
  can make the type and the typing erased and use inversion lemmas **)
let rec exp_translation
  (#gstlc:STLC.context)
  (gmap:mapping gstlc)
  (qfs:term)
  : Tac (STLC.open_term gstlc) =
  print ("      in exp translation: " ^ tag_of qfs);
  match inspect_ln qfs with
  | Tv_FVar fv -> begin
    print ("        looking for fvar: " ^ fv_to_string fv);
    match gmap (FVar fv) with
    | Some v -> (| _, _, STLC.TyVar #gstlc v |)
    | None -> fail (fv_to_string fv ^ " not defined")
  end

  | Tv_BVar v -> begin
    let i = (inspect_bv v).index in
    match gmap (BVar i) with
    | Some i' -> (| _, _, STLC.TyVar #gstlc i' |)
    | None -> fail (print_nat i ^ " not defined")
  end

  // | Tv_Var v -> begin
  //   let v = inspect_namedv v in
  //   match gmap (Var v) with
  //   | Some dbi -> (| _, _, STLC.TyVar #gstlc dbi |)
  //   | None -> fail (print_nat v.uniq ^ " not defined in STLC env")
  // end

  | Tv_App hd (a, q) -> begin
    let (| _, shd_ty, shd_tyj |) = exp_translation gmap hd in
    let (| _, sa_ty, sa_tyj |) = exp_translation gmap a in
    match shd_ty with
    | STLC.TArr arg res -> 
      if arg = sa_ty then (| _, res, STLC.TyApp shd_tyj sa_tyj |)
      else fail ("argument type mismatch")
    | _ -> fail ("hd is not an arrow type")
    end

  | Tv_Abs bin body -> begin
    let bin : binder_view = inspect_binder bin in
    let bin_ty : STLC.typ = typ_translation bin.sort in
    let gmap' = extend_gmap_binder gmap bin_ty in
    let (| _, _, body_tyj |) = exp_translation gmap' body in
    (| _, _, STLC.TyAbs #gstlc bin_ty body_tyj |) 
  end

  | Tv_Const (C_Int x) ->
    if (x < 0) then fail ("not supporting ints, only nats") else
    let (| e, tyj |) = make_stlc_nat x in
    (| e, STLC.TNat, tyj |)
  
  | Tv_Const C_True -> (| _, _, STLC.tyjtrue |)
  | Tv_Const C_False -> (| _, _, STLC.tyjfalse |)

  // | Tv_Let    : recf:bool -> attrs:(list term) -> b:simple_binder -> def:term -> body:term -> named_term_view
  // | Tv_Let recf attr bin def body -> begin
  //   let gfs' = extend_env gfs bin.uniq bin.sort in
  //   let bin_ty : STLC.typ = typ_translation gfs bin.sort in
  //   let (| _, def_ty, def_tyj |) = exp_translation gfs gstlc gmap def in
  //   if def_ty <> bin_ty then fail ("converting let failed because definition type mismatch") else
  //   let (| gstlc', gmap' |) = extend_gmap_binder gstlc gmap bin bin_ty in
  //   let (| _, body_ty, body_tyj |) = exp_translation gfs' gstlc' gmap' body in
  //   (| _, body_ty, STLC.TyApp #gstlc #_ #_ #bin_ty #body_ty (STLC.TyAbs #gstlc bin_ty body_tyj) def_tyj |)
  // end

  | Tv_Match qsc ret brs -> begin
    let sc = exp_translation gmap qsc in
    if List.length brs <> 2 then fail ("only supporting matches with 2 branches") else
    match ptyp sc with
    | STLC.TSum t1 t2 -> begin
      let (pt1, qbr1)::(pt2, qbr2)::[] = brs in
      (** TODO: hack. not even looking at patterns to make sure they are in correct order **)
      let br1 = STLC.abstract_term (exp_translation (extend_gmap_binder gmap t1) qbr1) in
      let br2 = STLC.abstract_term (exp_translation (extend_gmap_binder gmap t2) qbr2) in
      if ptyp br1 <> ptyp br2 then fail ("branches have different types") else
      if STLC.TArr? (ptyp br1) && t1 = STLC.TArr?.int (ptyp br1) &&
         STLC.TArr? (ptyp br2) && t2 = STLC.TArr?.int (ptyp br2) then
        STLC.term_case_sum sc br1 br2
      else fail ("branches have different types")
    end
    | _ -> fail ("only supporting match on sum types")
  end

  | Tv_AscribedC t c _ _ -> begin
    match inspect_comp c with
    | C_Total _ -> exp_translation gmap t
    | _ -> fail ("not a total function type")
  end

  | _ -> fail ("not implemented: " ^ tag_of qfs)
// and branch_translation (gfs:env) (gstlc:STLC.context) (gmap:mapping gstlc) (pt:pattern) (qbr:term) : Tac (STLC.open_term gstlc) =
//   let gfs' = gfs in
//   let gstlc' = extend ? gstlc in
//   let gmap' = gmap in
//   let case = exp_translation gfs' gstlc' gmap' qbr in
//   (| _, _, TyAbs )

let mk_stlc_typing (gfs qexp qtyp:term) =
  mk_app (`STLC.typing) [(gfs, Q_Explicit); (qexp, Q_Explicit); (qtyp, Q_Explicit)]	

let rec def_translation gfs gstlc gmap (qdef:term) : Tac (string * STLC.open_term gstlc) =
  print "  in def translation\n";
  match inspect_ln qdef with
  | Tv_FVar fv -> begin
    let fnm = fv_to_string fv in
    print ("    def: " ^ fnm ^ "\n");
    let qdef' = norm_term_env gfs [delta_only [fnm]; zeta] qdef in
    match inspect_ln qdef' with
    | Tv_FVar fv' ->
      if fnm = fv_to_string fv' then fail (fnm ^ " does not unfold!")
      else def_translation gfs gstlc gmap qdef'
    | _ -> (fnm, exp_translation gmap qdef')
  end
  | _ -> fail ("not top-level definition")

let rec prog_translation gfs gstlc gmap (qdefs:(list term){List.length qdefs > 0}) : Tac (STLC.open_term gstlc) =
  print "in prog translation\n";
  match qdefs with
 | qdef::[] -> snd (def_translation gfs gstlc gmap qdef)
 | qdef::tl ->
    let (def_name, def) = def_translation gfs gstlc gmap qdef in
    let gstlc' = STLC.extend (Mkdtuple3?._2 def) gstlc in
    let gmap' = extend_gmap gmap def_name (Mkdtuple3?._2 def) in
    let prog = prog_translation gfs gstlc' gmap' tl in
    STLC.instantiate_newest_binder def prog

let rec translation gfs gstlc gmap qdefs (axioms:list axiom_ty) : Tac (STLC.open_term gstlc) =
  print "in translation\n";
  match axioms with
  | [] -> prog_translation gfs gstlc gmap qdefs
  | (| axiom_name, axiom, axiom_ty, axiom_tyj |)::tl ->
    print ("  axiom: " ^ axiom_name ^ "\n");
    let gstlc' = STLC.extend axiom_ty gstlc in
    let gmap' = extend_gmap gmap axiom_name axiom_ty in
    let prog = translation gfs gstlc' gmap' qdefs tl in
    admit ();
    STLC.instantiate_newest_binder (| axiom, axiom_ty, axiom_tyj |) prog

let fs_translation gfs (qdefs:(list term){List.length qdefs > 0}) : Tac STLC.closed_term =
  print "\n\n\n================New Translation\n";
  translation gfs STLC.empty (fun _ -> None) qdefs axioms_mapping

let meta_translation (nm:string) (qdefs:(list term){List.length qdefs > 0}) : dsl_tac_t = fun g ->
  let (| exp, typ, tyj |) = fs_translation g qdefs in
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

let src1 : nat = 4+5
%splice_t[tgt1;tgt1_typ;tgt1_tyj] (meta_translation "tgt1" [`src1])
let _ = 
  assert (stlc_sem tgt1_tyj == src1) by (compute ())

let src2 : nat -> nat = fun x -> x + 5
%splice_t[tgt2;tgt2_typ;tgt2_tyj] (meta_translation "tgt2" [`src2])

let _ = 
  assert (stlc_sem tgt2_tyj 4 == src2 4) by (compute ());
  assert (stlc_sem tgt2_tyj 0 == src2 0) by (compute ())

let src2' (x:nat) : nat = x + 5
%splice_t[tgt2p;tgt2p_typ;tgt2p_tyj] (meta_translation "tgt2p" [`src2'])

let _ = 
  assert (stlc_sem tgt2p_tyj 4 == src2' 4) by (compute ());
  assert (stlc_sem tgt2p_tyj 0 == src2' 0) by (compute ())

let src_let (x:nat) : nat = let y = src2 x in src2 y
%splice_t[tgt_let;tgt_let_typ;tgt_let_tyj] (meta_translation "tgt_let" [`src2; `src_let])

let src_if (x:nat) : nat = 
  if x <= 5 then 0 else 1
%splice_t[tgt_if;tgt_if_typ;tgt_if_tyj] (meta_translation "tgt_if" [`src_if])

let _ = 
  assert (stlc_sem tgt_if_tyj 2 == src_if 2) by (compute ());
  assert (stlc_sem tgt_if_tyj 5 == src_if 5) by (compute ());
  assert (stlc_sem tgt_if_tyj 6 == src_if 6) by (compute ())

let src3 : nat -> nat -> nat = fun x y -> x
%splice_t[tgt3;tgt3_typ;tgt3_tyj] (meta_translation "tgt3" [`src3])

let test3 () =
  assert (tgt3_typ == STLC.TArr STLC.TNat (STLC.TArr STLC.TNat STLC.TNat));
  assert (forall x y. (stlc_sem tgt3_tyj) x y == x /\ (stlc_sem tgt3_tyj) x y == src3 x y) by (compute ())

let src4 : nat -> (nat -> nat) -> nat = fun x f -> let y = f x in y
%splice_t[tgt4;tgt4_typ;tgt4_tyj] (meta_translation "tgt4" [`src4])

let test4 () =
  assert (tgt4_typ == STLC.TArr STLC.TNat (STLC.TArr (STLC.TArr STLC.TNat STLC.TNat) STLC.TNat));
  assert (stlc_sem (STLC.TyApp (STLC.TyApp tgt4_tyj tgt1_tyj) tgt2_tyj) == src4 src1 src2) by (compute ())
  // assert (tgt4 == STLC.ELam STLC.TNat
  //                  (STLC.ELam (STLC.TArr STLC.TNat STLC.TNat) (STLC.EApp (STLC.EVar 0) (STLC.EVar 1))))
  // assert (forall x. (stlc_sem tgt4_tyj) x == x /\ (stlc_sem tgt4_tyj) x == src4 x) by (compute ())

let src5 : nat = src2 src1

%splice_t[tgt5;tgt5_typ;tgt5_tyj] (meta_translation "tgt5" [`src1; `src2; `src5])

let test5 () =
  assert (tgt5_typ == STLC.TNat);
  assert (stlc_sem tgt5_tyj == src2 src1) by (compute ())

// let src6 : nat = (src4 src1 src2)

(** CA: this takes long and multiple runs have different logs ??? **)
// %splice_t[tgt6;tgt6_typ;tgt6_tyj] (meta_translation "tgt6" [`src1; `src2; `src4; `src6])
















// let test6 () =
//   assert (tgt6_typ == STLC.TNat);
//   assert (stlc_sem tgt6_tyj == src4 src1 src2) by (compute ())


// let rec src_sum (x:nat) : nat =
//   if x <= 1 then x else x + src_sum (x-1)

// %splice_t[tgt_sum;tgt_sum_typ;tgt_sum_tyj] (meta_translation "tgt_sum" [`src_sum])