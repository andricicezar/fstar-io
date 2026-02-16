module HelperTactics

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

let valid_wtf (g:env) (phi:term)
  : Lemma (requires valid g phi)
          (ensures squash (tot_typing g qunit (mk_squash phi)))
  = let goal = squash (tot_typing g qunit (mk_squash phi)) in
    assert (valid g phi ==> goal) by (compute ()); /// WHY????
    () // ????

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