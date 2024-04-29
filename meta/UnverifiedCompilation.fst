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

let rec unverified_term_translation
  (gfs:env)
  (gstlc:STLC.env)
  (mapping:fv -> option (x:STLC.var{Some? (gstlc x)}))
  (qfs:term)
  : TacP (open_stlc_term gstlc)
      (requires True)
      (ensures fun _ -> True) =
  match inspect qfs with
  | Tv_FVar fv -> begin
    match mapping fv with
    | Some v -> (| _, _, STLC.TyVar #gstlc v |)
    | None -> fail (fv_to_string fv ^ " not implemented")
  end    
  | Tv_App hd (a, _) -> begin
    (** TODO: it seems like we cannot get the type of `hd` or `a` here because
              we don't have the typing judgment of `qfs`.
              Even if we would ask for the F* typing judgement of `qfs`,
              it could be just a token---not helpful.
          QA: How would this work with the logical relation? **) 
    let (| _, a_t, a_tyj |) = unverified_term_translation gfs gstlc mapping a in
    let (| _, hd_t, hd_tyj |) = unverified_term_translation gfs gstlc mapping hd in
    match hd_t with
    | STLC.TArr arg res -> 
      if arg = a_t then (| _, res, STLC.TyApp hd_tyj a_tyj |)
      else fail ("argument type mismatch")
    | _ -> fail ("hd is not an arrow type")
  end

  | Tv_Const (C_Int x) ->
    if (x < 0) then fail ("not supporting ints, only nats") else
    let (| e, tyj |) = make_stlc_nat x in
    (| e, STLC.TNat, tyj |)

  | Tv_Unknown -> fail ("an underscore was found in the term")
  | Tv_Unsupp -> fail ("unsupported by F* terms")

  | _ -> fail ("not implemented")

let specialize (nm:string) (qfs:term) : dsl_tac_t = fun g ->
  let qfs = norm_term_env g [delta] qfs in
  let (| exp, typ, tyj |) = unverified_term_translation g STLC.empty (fun _ -> None) qfs in
  
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
%splice_t[tgt1;tgt1_typ;tgt1_tyj] (specialize "tgt1" (`src1))
let _ = 
  assert (tgt1 == STLC.ESucc (STLC.ESucc (STLC.ESucc (STLC.ESucc STLC.EZero))));
  assert (stlc_sem tgt1_tyj == src1)

let src2 : nat = 4+5
%splice_t[tgt2;tgt2_typ;tgt2_tyj] (specialize "tgt2" (`src2))

let _ = 
  assert (tgt2 == STLC.EZero)
