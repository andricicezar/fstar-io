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

let rec print_nat (n:nat) : string =
  match n with
  | 0 -> "0"
  | 1 -> "1"
  | 2 -> "2"
  | 3 -> "3"
  | 4 -> "4"
  | 5 -> "5"
  | 6 -> "6"
  | 7 -> "7"
  | 8 -> "8"
  | 9 -> "9"
  | _ -> print_nat (n/10) ^ print_nat (n % 10)

let print_vconst (c:vconst) : string =
  match c with
  | C_Unit -> "C_Unit"
  | C_Int _ -> "C_Int"
  | C_True -> "C_True"
  | C_False -> "C_False"
  | C_String s -> "C_String" ^ s
  | C_Range r -> "C_Range"
  | C_Reify -> "C_Reify"
  | C_Reflect nm -> "C_Reflect"


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

let rec unverified_exp_translation
  (gfs:env)
  (gstlc:STLC.env)
  (mapping_fv:fv -> option (x:STLC.var{Some? (gstlc x)}))
  (mapping_v:namedv -> option (x:STLC.var{Some? (gstlc x)}))
  (qfs:term)
  : TacP (open_stlc_term gstlc)
      (requires True)
      (ensures fun _ -> True) =
  match inspect qfs with
  | Tv_FVar fv -> begin
    match mapping_fv fv with
    | Some v -> (| _, _, STLC.TyVar #gstlc v |)
    | None -> fail (fv_to_string fv ^ " not defined")
  end

  | Tv_Var v -> begin
    match mapping_v v with
    | Some v -> (| _, _, STLC.TyVar #gstlc v |)
    | None -> fail (print_nat v.uniq ^ " not defined in STLC env")
  end

  | Tv_App hd (a, _) -> begin
    (** TODO: it seems like we cannot get the type of `hd` or `a` here because
              we don't have the typing judgment of `qfs`.
              Even if we would ask for the F* typing judgement of `qfs`,
              it could be just a token---not helpful.
          QA: How would this work with the logical relation? **) 
    let (| _, a_t, a_tyj |) = unverified_exp_translation gfs gstlc mapping_fv mapping_v a in
    let (| _, hd_t, hd_tyj |) = unverified_exp_translation gfs gstlc mapping_fv mapping_v hd in
    match hd_t with
    | STLC.TArr arg res -> 
      if arg = a_t then (| _, res, STLC.TyApp hd_tyj a_tyj |)
      else fail ("argument type mismatch")
    | _ -> fail ("hd is not an arrow type")
  end

  | Tv_Abs b c -> begin
    let gfs' = extend_env gfs b.uniq b.sort in
    (match inspect b.sort with
    | Tv_Refine b' ref -> dump (tag_of ref)
    | _ -> fail ("not a refinement type"));
    (** TODO: 
        * convert b.sort into a STLC type
        * extend gstlc and mapping **)
    unverified_exp_translation gfs' gstlc mapping_fv mapping_v c
  end

  | Tv_Const (C_Int x) ->
    if (x < 0) then fail ("not supporting ints, only nats") else
    let (| e, tyj |) = make_stlc_nat x in
    (| e, STLC.TNat, tyj |)

  | Tv_Unknown -> fail ("an underscore was found in the term")
  | Tv_Unsupp -> fail ("unsupported by F* terms")

  | _ -> dump (tag_of qfs); fail ("not implemented")

let comp_exp (nm:string) (qfs:term) : dsl_tac_t = fun g ->
  let qfs = norm_term_env g [delta] qfs in
  let (| exp, typ, tyj |) = unverified_exp_translation g STLC.empty (fun _ -> None) (fun _ -> None) qfs in
  
  let qexp = quote exp in
  type_dynamically g qexp (`STLC.exp);
  let qtyp = quote typ in
  type_dynamically g qtyp (`STLC.typ);
  let qtyj = quote tyj in
  type_dynamically g qtyj (`STLC.typing STLC.empty (`#qexp) (`#qtyp));

  [
   mk_checked_let g nm qexp (`STLC.exp);
   mk_checked_let g (nm^"_typ") qtyp (`STLC.typ);
   mk_checked_let g (nm^"_tyj") qtyj (`STLC.typing STLC.empty (`#qexp) (`#qtyp));
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

let src3 : nat -> nat = fun x -> x
%splice_t[tgt3;tgt3_typ;tgt3_tyj] (comp_exp "tgt3" (`src3))

