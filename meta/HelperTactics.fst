module HelperTactics

include FStar.Tactics.V2
include FStar.Reflection.Typing

let must (x : ret_t 'a) : Tac 'a =
  match x with
  | Some v, _ -> v
  | None, [] ->
    fail ("must failed, no issues?")
  | None, i::_ ->
    fail ("must failed: " ^ FStar.Issue.render_issue i)

(* Metaprograms with partial correctness *)
effect TacP (a:Type) (pre:prop) (post : a -> prop) =
  TacH a (requires (fun _ -> pre))
         (ensures (fun _ps r ->
           match r with
           | FStar.Stubs.Tactics.Result.Success v ps -> post v
           | _ -> True))

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

(** ** Normalize **)
val typed_norm_term_env :
  ty:typ ->
  g:env ->
  list norm_step ->
  t0:term{tot_typing g t0 ty} ->
  Tac (t1:term{same_typing t0 t1 /\ valid g (mk_eq2 ty t0 t1)})
let typed_norm_term_env ty g steps t0 =
  let t1 = norm_term_env g steps t0 in
  admit(); // can't prove this, we should strengthen norm_term_env in F* library
  t1

(** ** Dynamic Typing **)
let dyn_typing (#g #ty #t : _) () : Tac (tot_typing g t ty) =
  let tok = must <| core_check_term g t ty E_Total in
  T_Token _ _ _ (Squash.return_squash tok)

let type_dynamically g ty t : TacP unit (requires True) (ensures fun _ -> squash (tot_typing g ty t)) =
  let ht : tot_typing g ty t = dyn_typing () in
  Squash.return_squash ht

let assert_dynamically g phi : TacP unit (requires True) (ensures fun _ -> squash (valid g phi)) =
  let ht : tot_typing g qunit (mk_squash phi) = dyn_typing () in
  Squash.return_squash ht



let rec fold_left (f:'a -> 'b -> 'a) (acc:'a) (l:list 'b) : Tot 'a (decreases l)=
  match l with
  | [] -> acc
  | hd::tl -> fold_left f (f acc hd) tl

let fv_to_string (fv:fv) : string =
  match inspect_fv fv with
  | [] -> ""
  | h::[] -> h
  | h::tl -> fold_left (fun x y -> x ^ "." ^ y) h tl

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
