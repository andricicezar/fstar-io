module VerifiedTransform3

open FStar.Tactics.V2
open FStar.Reflection.Typing

let must (x : ret_t 'a) : Tac 'a =
  match x with
  | Some v, _ -> v
  | None, [] ->
    fail ("must failed, no issues?")
  | None, i::_ ->
    fail ("must failed: " ^ FStar.Issue.render_issue i)

let mk_squash (phi:term) : Tot term = pack (Tv_App (`squash) (phi, Q_Explicit))

let t_unit = `()

let valid (g:env) (phi:term) : prop =
  squash (tot_typing g t_unit (mk_squash phi))

let valid_wtf (g:env) (phi:term) 
  : Lemma (requires valid g phi)
          (ensures squash (tot_typing g t_unit (mk_squash phi)))
  = let goal = squash (tot_typing g t_unit (mk_squash phi)) in
    assert (valid g phi ==> goal) by (compute ()); /// WHY????
    () // ????

let same_typing (t0 t1 : term) : prop =
  forall g c typ. typing g t0 (c, typ) ==> typing g t1 (c, typ)

let same_valid (t0 t1 : term) : prop =
  forall g. valid g t0 ==> valid g t1

let mk_eq2 (ty t1 t2 : term) : Tot term =
  mk_app (`Prims.eq2) [(ty, Q_Implicit); (t1, Q_Explicit); (t2, Q_Explicit)]	

val norm_term_env :
  ty:typ ->
  g:env ->
  list norm_step ->
  t0:term{tot_typing g t0 ty} ->
  Tac (t1:term{same_typing t0 t1 /\ valid g (mk_eq2 ty t0 t1)})
let norm_term_env ty g steps t0 =
  let t1 = norm_term_env g steps t0 in
  admit(); // can't prove this, we should strengthen norm_term_env in F* library
  t1

(* Metaprograms with partial correctness *)
effect TacP (a:Type) (pre:prop) (post : a -> prop) =
  TacH a (requires (fun _ -> pre))
         (ensures (fun _ps r ->
           match r with
           | FStar.Stubs.Tactics.Result.Success v ps -> post v
           | _ -> True))

let object_eq2_refl (x:'a) : Lemma (x == x) = ()

let eq2_refl (g:env) (ty:term) (t:term)
  : TacP unit
         (requires squash (tot_typing g t ty))
         (ensures fun _ -> valid g (mk_eq2 ty t t))
  = (* currently this just calls the typechecker/solver, but it could
    be done statically from the type of Refl *)
    let goal = mk_squash (mk_eq2 ty t t) in
    let tok = must <| core_check_term g (`()) goal E_Total in
    let _ : valid g (mk_eq2 ty t t) = 
        Squash.return_squash (T_Token _ _ _ (Squash.return_squash tok)) in
    assert (valid g (mk_eq2 ty t t));
    ()

let eq2_trans (g:env) (ty:term) (t0 t1 t2:term)
  : TacP unit
         (requires valid g (mk_eq2 ty t0 t1) /\ valid g (mk_eq2 ty t1 t2))
         (ensures fun _ -> valid g (mk_eq2 ty t0 t2))
= admit() // could prove, it's a lift of the eq2_trans object-level lemma

let dyn_typing (#g #ty #t : _) () : Tac (tot_typing g t ty) =
  let tok = must <| core_check_term g t ty E_Total in
  T_Token _ _ _ (Squash.return_squash tok)


(** A small language to sum natural numbers **)
type ast_typ =
  | TInt    : ast_typ

type ast_exp =
  | EC_Int : int -> ast_exp                        // TODO: OCaml ints are not the same as F* ints
  | EAdd  : e1:ast_exp -> e2:ast_exp -> ast_exp    // TODO: OCaml addition is not the same as F* addition

(** we do not have free variables yet, so we do not need an env **)
// assume type ast_env

(** we only have one type, so probably this is not very useful **)
type ast_typing : (e:ast_exp) -> (t:ast_typ) -> Type =
  | C_IntTyping : x:int -> ast_typing (EC_Int x) TInt
  | AddTyping   : #e1:ast_exp -> #e2:ast_exp -> ast_typing e1 TInt -> ast_typing e2 TInt -> ast_typing (EAdd e1 e2) TInt

let t : ast_exp = EAdd (EC_Int 2) (EC_Int 1)

let rec sem (e:ast_exp) : int =
  match e with
  | EC_Int x -> x
  | EAdd e1 e2 -> sem e1 + sem e2

let _ = assert (sem t == 3)

let c_int_typing (g:env) (x : int) : Tac (tot_typing g (pack (Tv_Const (C_Int x))) (`int)) =
  dyn_typing ()

let mk_ec_int (g:env) (x:int) : e:term{
  tot_typing g e (`ast_exp) /\ 
  valid g (`(ast_typing (`#e) TInt)) /\ 
  valid g (mk_eq2 (`int) (pack (Tv_Const (C_Int x))) (`(sem (`#e))))
} =
  let e = pack (
      Tv_App 
        (`EC_Int)
        (pack (Tv_Const (C_Int x)), Q_Explicit)) in
  assume (tot_typing g e (`ast_exp));
  assume (valid g (`(ast_typing (`#e) TInt)));
  assume (valid g (mk_eq2 (`int) (pack (Tv_Const (C_Int x))) (`(sem (`#e)))));
  e

let mk_eapp (g:env) (x:term{tot_typing g x (`ast_exp)}) (y:term{tot_typing g y (`ast_exp)}) : e:term{
  tot_typing g e (`ast_exp) /\
  valid g (`(ast_typing (`#e) TInt)) /\
  valid g (mk_eq2 (`int) (`((sem (`#x)) + (sem (`#y)))) (`(sem (`#e))))
} =
  let e = pack (
    Tv_App 
      (Tv_App (`EAdd) (x, Q_Explicit))
      (y, Q_Explicit)) in
  assume (tot_typing g e (`ast_exp));
  assume (valid g (`(ast_typing (`#e) TInt)));
  assume (valid g (mk_eq2 (`int) (`((sem (`#x)) + (sem (`#y)))) (`(sem (`#e)))));
  e

let compose_add (a b c d:int) : Lemma (requires (a == b /\ c == d)) (ensures (a+c == b+d)) = ()

let rec compile_to_ast (g:env) (t0:term{tot_typing g t0 (`int)})
  : TacP term (requires True)
              (ensures fun t1 -> 
                tot_typing g t1 (`ast_exp) /\                // AST syntax
                valid g (`(ast_typing (`#t1) TInt)) /\       // well typed AST syntax
                valid g (mk_eq2 (`int) t0 (`(sem (`#t1)))))  // equivalent semantics
= 
  match inspect t0 with
  | Tv_FVar _ ->
    (* inline the top-level definition *)
    let t1 = norm_term_env (`int) g [delta] t0 in
    let t2 = compile_to_ast g t1 in
    eq2_trans g (`int) t0 t1 (`(sem (`#t2)));
    t2
  
  | Tv_Const (C_Int x) ->
    let t1 = mk_ec_int g x in
    assume (valid g (mk_eq2 (`int) t0 (`(sem (`#t1)))));
    t1

  (* detect ((op_Plus a) b) *)
  | Tv_App hd (a2, Q_Explicit) ->
    begin match inspect hd with
      | Tv_App op (a1, Q_Explicit) ->
        begin match inspect op with
        | Tv_FVar fv ->
          if inspect_fv fv = ["Prims"; "op_Addition"]
          then begin
            assume (tot_typing g a1 (`int)); // need inversion lemma
            assume (tot_typing g a2 (`int)); // need inversion lemma
            let lhs = compile_to_ast g a1 in
            let rhs = compile_to_ast g a2 in
            let t1 = mk_eapp g lhs rhs in
            // TODO:quotations and anti quotations are not stable
            //  refactor this to use other techniques
            //assert (valid g (mk_eq2 (`int) a1 (`(sem (`#rhs)))));
            //assert (valid g (mk_eq2 (`int) a2 (`(sem (`#lhs)))));
            assume (valid g (mk_eq2 (`int) (`((`#a1)+(`#a2))) (`(sem (`#lhs) + sem (`#rhs)))));
            //assert (valid g (mk_eq2 (`int) (`(sem (`#lhs) + sem (`#rhs))) (`(sem (`#t1)))));
            eq2_trans g (`int) (`((`#a1)+(`#a2))) (`(sem (`#lhs) + sem (`#rhs))) (`(sem (`#t1)));
            assume (valid g (mk_eq2 (`int) t0 (`((`#a1)+(`#a2)))));
            //assert (valid g (mk_eq2 (`int) (`((`#a1)+(`#a2))) (`(sem (`#t1)))));
            admit (); //TODO: calling this lemma fails, which is weird. 
            eq2_trans g (`int) t0 (`((`#a1)+(`#a2))) (`(sem (`#t1)));
            assert (valid g (mk_eq2 (`int) t0 (`(sem (`#t1)))));
            t1
          end else fail ("not implemented")
        | _ -> fail ("not implemented")
        end
      | _ -> fail ("not implemented")
    end

  | _ -> fail ("not implemented")

let specialize (nm':string) (e0:term) : dsl_tac_t = fun g ->
  let typ0 : tot_typing g e0 (`int) = dyn_typing () in
  FStar.Squash.return_squash typ0;
  let e1 = compile_to_ast g e0 in
  let phi = mk_eq2 (`int) e0 (`(sem (`#e1))) in
  valid_wtf g phi;
  [
   mk_checked_let g nm' e1 (`ast_exp);
   mk_checked_let g (nm'^"_pf")
                    (`())
                    (mk_squash phi);
  ]
  
let src1 : int = 4 + 5 + 6

%splice_t[tgt1;tgt1_pf] (specialize "tgt1" (`src1))

// TODO: @Guido, here there is a universe problem. any tip on how to fix this?
// let _ =
//   FStar.Squash.give_proof tgt1_pf

let _ = 
  assert (tgt1 == EAdd (EAdd (EC_Int 4) (EC_Int 5)) (EC_Int 6));
  assert (sem tgt1 == src1);
  assert (sem tgt1 == 15) 

[@expect_failure]
let _ = 
  assert (tgt1 == EAdd (EC_Int 5) (EC_Int 4))
