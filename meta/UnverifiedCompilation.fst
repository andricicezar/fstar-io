module UnverifiedCompilation

open HelperTactics

noeq
type fs_var =
| FVar : fv -> fs_var
| Var  : namedv -> fs_var
| Bv   : bv -> fs_var

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
  (b:binder)
  (b_ty:STLC.typ)
  : mapping (STLC.extend b_ty gstlc) =
  (fun x -> match x with 
      | Var v -> if v.uniq = b.uniq then Some 0 else (incr_option (gmap x))
      | _ -> (incr_option (gmap x)))

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
  (| "Prims.op_Addition", STLC.op_add, STLC.op_add_ty, STLC.op_add_tyj |)
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

let rec typ_translation (gfs:env) (qfs:term) : Tac STLC.typ = 
  match inspect qfs with
  | Tv_FVar fv -> begin
    match fv_to_string fv with
    | "Prims.int" -> STLC.TNat
    | _ ->
      let qfs' = norm_term_env gfs [delta] qfs in
      (* avoid infinite loop by checking if axiom *)
      if tag_of qfs' <> "Tv_FVar" then typ_translation gfs qfs'
      else fail (fv_to_string fv ^ " not defined")
  end

  | Tv_Arrow b c ->  begin
    let tbv = typ_translation gfs b.sort in
    match c with
    | C_Total ret -> 
      let tc = typ_translation gfs ret in
      STLC.TArr tbv tc
    | _ -> fail ("not a total function type")
  end
  | Tv_Var v -> fail "fvar"

  (** erase refinement **)
  | Tv_Refine b _ -> typ_translation gfs b.sort

  | Tv_Const c -> fail (print_vconst c)

  | Tv_Unknown -> fail ("an underscore was found in the term")
  | Tv_Unsupp -> fail ("unsupported by F* terms")

  | _ -> fail ("not implemented: " ^ tag_of qfs)

let comp_typ (nm:string) (qfs:term) : dsl_tac_t = fun g ->
  let typ = typ_translation g qfs in

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

(* CA: keeping track of the type of the term is important for the logical relation *)
let rec exp_translation
  (gfs:env)
  (gstlc:STLC.context)
  (gmap:mapping gstlc)
  (qfs:term)
  : Tac (STLC.open_term gstlc) =
  print ("      in exp translation: " ^ tag_of qfs);
  match inspect qfs with
  | Tv_FVar fv -> begin
    print ("        looking for fvar: " ^ fv_to_string fv);
    match gmap (FVar fv) with
    | Some v -> (| _, _, STLC.TyVar #gstlc v |)
    | None -> fail (fv_to_string fv ^ " not defined")
  end

  | Tv_Var v -> begin
    match gmap (Var v) with
    | Some dbi -> (| STLC.EVar dbi, Some?.v (gstlc dbi), STLC.TyVar #gstlc dbi |)
    | None -> fail (print_nat v.uniq ^ " not defined in STLC env")
  end

  | Tv_App hd (a, q) -> begin
    (** TODO: it seems like we cannot get the type of `hd` or `a` here because
              we don't have the typing judgment of `qfs`.
              Even if we would ask for the F* typing judgement of `qfs`,
              it could be just a token---not helpful.
              Maybe there is a way to recover by normalizing a bit `hd`? See: recover_type_of_arrow
          QA: How would this work with the logical relation? **) 
    // assert (forall t. tot_typing gfs (Tv_App hd (a, _)) qty ==> 
    //           (exists t'. tot_typing gfs a t' /\ tot_typing gfs hd (Tv_Arrow t' qty)));
    // assert (forall t. tot_typing gfs (Tv_App hd (a, _)) qty ==> 
    //           (forall t'. tot_typing gfs hd (Tv_Arrow t' qty) ==> tot_typing gfs a t'));
    let (| _, shd_ty, shd_tyj |) = exp_translation gfs gstlc gmap hd in
    let (| _, sa_ty, sa_tyj |) = exp_translation gfs gstlc gmap a in
    match shd_ty with
    | STLC.TArr arg res -> 
      if arg = sa_ty then (| _, res, STLC.TyApp shd_tyj sa_tyj |)
      else fail ("argument type mismatch")
    | _ -> fail ("hd is not an arrow type")
    end

  | Tv_Abs bin body -> begin
    let gfs' = extend_env gfs bin.uniq bin.sort in
    let bin_ty : STLC.typ = typ_translation gfs bin.sort in
    (* TODO: don't I have to prove termination here? *)
    let gstlc' = STLC.extend bin_ty gstlc in
    let gmap' = extend_gmap_binder gmap bin bin_ty in
    let (| _, _, body_tyj |) = exp_translation gfs' gstlc' gmap' body in
    (| _, _, STLC.TyLam #gstlc bin_ty body_tyj |) 
  end

  | Tv_Const (C_Int x) ->
    if (x < 0) then fail ("not supporting ints, only nats") else
    let (| e, tyj |) = make_stlc_nat x in
    (| e, STLC.TNat, tyj |)

  // | Tv_Let    : recf:bool -> attrs:(list term) -> b:simple_binder -> def:term -> body:term -> named_term_view
  // | Tv_Let recf attr bin def body -> begin
  //   let gfs' = extend_env gfs bin.uniq bin.sort in
  //   let bin_ty : STLC.typ = typ_translation gfs bin.sort in
  //   let (| _, def_ty, def_tyj |) = exp_translation gfs gstlc gmap def in
  //   if def_ty <> bin_ty then fail ("converting let failed because definition type mismatch") else
  //   let (| gstlc', gmap' |) = extend_gmap_binder gstlc gmap bin bin_ty in
  //   let (| _, body_ty, body_tyj |) = exp_translation gfs' gstlc' gmap' body in
  //   (| _, body_ty, STLC.TyApp #gstlc #_ #_ #bin_ty #body_ty (STLC.TyLam #gstlc bin_ty body_tyj) def_tyj |)
  // end

  | Tv_AscribedC t (C_Total _) _ _ -> exp_translation gfs gstlc gmap t

  | Tv_Unknown -> fail ("an underscore was found in the term")
  | Tv_Unsupp -> fail ("unsupported by F* terms")

  | _ -> fail ("not implemented: " ^ tag_of qfs)

let mk_stlc_typing (gfs qexp qtyp:term) =
  mk_app (`STLC.typing) [(gfs, Q_Explicit); (qexp, Q_Explicit); (qtyp, Q_Explicit)]	

let rec def_translation gfs gstlc gmap (qdef:term) : Tac (string * STLC.open_term gstlc) =
  print "  in def translation\n";
  match inspect qdef with
  | Tv_FVar fv -> begin
    let fnm = fv_to_string fv in
    print ("    def: " ^ fnm ^ "\n");
    let qdef' = norm_term_env gfs [delta_only [fnm]] qdef in
    match inspect qdef' with
    | Tv_FVar fv' ->
      if fnm = fv_to_string fv' then fail (fnm ^ " does not unfold!")
      else def_translation gfs gstlc gmap qdef'
    | _ -> (fnm, exp_translation gfs gstlc gmap qdef')
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

let src_if (x:nat) : nat = 
  if x <= 5 then 0 else 1
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

let src6 : nat = (src4 src1 src2)

(** CA: this takes long and multiple runs have different logs ??? **)
%splice_t[tgt6;tgt6_typ;tgt6_tyj] (meta_translation "tgt6" [`src1; `src2; `src4; `src6])

let test6 () =
  assert (tgt6_typ == STLC.TNat);
  assert (stlc_sem tgt6_tyj == src4 src1 src2) by (compute ())
