module RQ.Metaprogram.Utils

open FStar.Tactics.V2
open FStar.Reflection.Typing
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data

let must (x : ret_t 'a) : Tac 'a =
  match x with
  | Some v, _ -> v
  | None, [] ->
    fail ("must failed, no issues?")
  | None, i::_ ->
    fail ("must failed: " ^ FStar.Issue.render_issue i)

(** ** Help with quotations **)
let qunit : term = `()

(** ** Static Typing **)
let valid (g:env) (phi:term) : prop =
  squash (tot_typing g qunit (mk_squash phi))

let same_typing (t0 t1 : term) : prop =
  forall g c typ. typing g t0 (c, typ) ==> typing g t1 (c, typ)

let same_valid (t0 t1 : term) : prop =
  forall g. valid g t0 ==> valid g t1

let mk_eq2 (ty t1 t2 : term) : Tot term =
  mk_app (`Prims.eq2) [(ty, Q_Implicit); (t1, Q_Explicit); (t2, Q_Explicit)]

(** ** Dynamic Typing **)
let dyn_typing (#g #ty #t : _) () : Tac (tot_typing g t ty) =
  let tok = must <| core_check_term g t ty E_Total in
  T_Token _ _ _ (Squash.return_squash tok)

let type_dynamically g ty t : TacH unit (requires True) (ensures fun _ -> tot_typing g t ty) =
  let ht : tot_typing g t ty = dyn_typing () in
  Squash.return_squash ht

let assert_dynamically g phi : TacH unit (requires True) (ensures fun _ -> valid g phi) =
  let ht : tot_typing g qunit (mk_squash phi) = dyn_typing () in
  Squash.return_squash ht


let lem_retype_expression g e (t:typ{tot_typing g e t}) (desired_t:typ) :
  Lemma (requires tot_typing g e t /\ sub_typing g t desired_t)
        (ensures tot_typing g e desired_t) =
  Squash.bind_squash #(typing g e (E_Total, t)) () (fun d_typing ->
    Squash.bind_squash #(sub_typing g t desired_t) () (fun d_sub ->
      let d_sub_comp = Relc_typ g t desired_t E_Total R_Sub d_sub in
      let d_res = T_Sub g e (E_Total, t) (E_Total, desired_t) d_typing d_sub_comp in
      Squash.return_squash d_res))


let token_as_typing (g:env) (e:term) (eff:tot_or_ghost) (ty:typ)
  : Lemma
    (requires typing_token g e (eff, ty))
    (ensures typing g e (eff, ty)) =
    assert (typing_token g e (eff, ty));
    Squash.return_squash (T_Token _ _ _ (Squash.get_proof (typing_token g e (eff, ty))))

let lem_retype_token (g:env) (e:term) (ty:typ) (desired_ty:typ)
  : Lemma
    (requires typing_token g e (E_Total, ty) /\ equiv_token g desired_ty ty)
    (ensures typing_token g e (E_Total, desired_ty)) =
  Squash.bind_squash #(typing_token g e (E_Total, ty)) () (fun ty_tok ->
    Squash.bind_squash #(equiv_token g desired_ty ty) () (fun eq_tok ->
      let d_eq : related g desired_ty R_Eq ty =
        Rel_eq_token g desired_ty ty (Squash.return_squash eq_tok) in
      let d_eq_sym : related g ty R_Eq desired_ty =
        Rel_sym g desired_ty ty d_eq in
      let d_sub : related g ty R_Sub desired_ty =
        Rel_equiv g ty desired_ty R_Sub d_eq_sym in
      let d_sub_comp : related_comp g (E_Total, ty) R_Sub (E_Total, desired_ty) =
        Relc_typ g ty desired_ty E_Total R_Sub d_sub in
      let d_typ : typing g e (E_Total, ty) =
        T_Token g e (E_Total, ty) (Squash.return_squash ty_tok) in
      let d_res : typing g e (E_Total, desired_ty) =
        T_Sub g e (E_Total, ty) (E_Total, desired_ty) d_typ d_sub_comp in
      let d_res_tok : typing_token g e (E_Total, desired_ty) =
        typing_to_token d_res in
      Squash.return_squash d_res_tok))

let rec fold_left (f:'a -> 'b -> 'a) (acc:'a) (l:list 'b) : Tot 'a (decreases l)=
  match l with
  | [] -> acc
  | hd::tl -> fold_left f (f acc hd) tl

let fv_to_string (fv:fv) : string =
  match inspect_fv fv with
  | [] -> ""
  | h::[] -> h
  | h::tl -> fold_left (fun x y -> x ^ "." ^ y) h tl


let get_fv (head:term) : option string =
  match inspect_ln head with
  | Tv_FVar fv -> Some (fv_to_string fv)
  | Tv_UInst fv _ -> Some (fv_to_string fv)
  | _ -> None

(** Extract the fully-qualified name of a top-level definition referenced by a
    term (an [FVar]/[UInst]). *)
let fv_name_of_term (t:term) : option name =
  match inspect_ln t with
  | Tv_FVar fv | Tv_UInst fv _ -> Some (inspect_fv fv)
  | _ -> None

(** Read the declared (possibly refined) F* type of a top-level symbol out of
    the environment [g] with [lookup_typ] (we do NOT re-typecheck anything). *)
let lookup_fstar_type (g:env) (nm:name) : option typ =
  match lookup_typ g nm with
  | Some se ->
    (match FStar.Stubs.Reflection.V2.Builtins.inspect_sigelt se with
     | FStar.Stubs.Reflection.V2.Data.Sg_Val _ _ ty -> Some ty
     | FStar.Stubs.Reflection.V2.Data.Sg_Let _ lbs ->
       let rec find (ls:list FStar.Stubs.Reflection.Types.letbinding) : option typ =
         match ls with
         | [] -> None
         | lb :: rest ->
           let lbv = FStar.Stubs.Reflection.V2.Builtins.inspect_lb lb in
           if inspect_fv lbv.lb_fv = nm then Some lbv.lb_typ
           else find rest
       in
       find lbs
     | _ -> None)
  | None -> None

(** Recover the (possibly refined) declared F* type of a term that is either a
    bound variable or a top-level name. For a bound variable the metaprogram
    never pushes binders into the reflection env, so its type comes from its own
    [sort]; for a top-level (closed) name the declared type is read out of the
    environment [g] (see [lookup_fstar_type]). Used both to thread an application
    head's refined domain onto its argument (otherwise the argument's refinement
    defaults to [trivial_ref0], i.e. [fun _ -> True]) and to obtain the type of
    the top-level program being derived.

    The [Tac] effect is needed solely for [unseal] in the bound-variable case
    (the binder's [sort] is a [sealed typ]); the top-level lookup is pure. *)
let head_fstar_type (g:env) (hd:term) : Tac (option typ) =
  match inspect_ln hd with
  | Tv_BVar v -> Some (unseal (inspect_bv v).sort)
  | _ ->
    (match fv_name_of_term hd with
     | Some nm -> lookup_fstar_type g nm
     | None -> None)

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

let print_vconst (c:FStar.Stubs.Reflection.V2.Data.vconst) : string =
  match c with
  | C_Unit -> "C_Unit"
  | C_Int _ -> "C_Int"
  | C_True -> "C_True"
  | C_False -> "C_False"
  | C_String s -> "C_String" ^ s
  | C_Range r -> "C_Range"
  | C_Reify -> "C_Reify"
  | C_Reflect nm -> "C_Reflect"
  | C_Real s -> "C_Real" ^ s
  | C_Char _ -> "C_Char"


let pat_to_string (p:pattern) : string =
  match p with
  | Pat_Constant c -> "Pat_Constant " ^ (print_vconst c)
  | Pat_Cons head univs subpats ->
      // let subpats : list ((p: pattern{p << p}) & bool) = FStar.List.Tot.map #(pattern & bool) #((p: pattern{p << p}) & bool)
      //   (fun (x, y) -> (x, y)) subpats in
     "Pat_Cons " ^ fv_to_string head //^ " (" ^ FStar.List.Tot.fold_left (fun acc (p, b) -> acc ^ ", " ^ pat_to_string p) "" subpats  ^ ")"
  | Pat_Var v sort -> "Pat_Var"
  | Pat_Dot_Term _ -> "Pat_Dot_Term"

let branch_to_string (b:branch) : Tac string =
  let (p, t) = b in
  "(" ^ pat_to_string p ^ ", " ^ term_to_string t ^ ")"

let branches_to_string (brs:list branch) : Tac string =
  FStar.Tactics.Util.fold_left (fun acc b -> acc ^ (branch_to_string b) ^ "; ") "" brs

let unk = pack_ln Tv_Unknown
