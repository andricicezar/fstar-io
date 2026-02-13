module STLCToLambdaBox

(** Compiler from STLC expressions to LambdaBox terms. *)

open STLC
open LambdaBox
open Sexp
open LambdaBoxToSexp
open FStar.List.Tot

(** Module path for our STLC types - using a simple file path *)
let stlc_modpath : modpath = MPfile ["STLC"]

(** Predefined inductive type identifiers *)

(** Unit type: single constructor tt *)
let unitTyId : inductive = {
  inductive_mind = (stlc_modpath, "unit");
  inductive_ind = 0;
}

(** Bool type: constructors true (0) and false (1) *)
let boolTyId : inductive = {
  inductive_mind = (stlc_modpath, "bool");
  inductive_ind = 0;
}

(** Pair type: constructor pair (0) with 2 arguments *)
let pairTyId : inductive = {
  inductive_mind = (stlc_modpath, "prod");
  inductive_ind = 0;
}

(** Sum type: constructors inl (0) and inr (1), each with 1 argument *)
let sumTyId : inductive = {
  inductive_mind = (stlc_modpath, "sum");
  inductive_ind = 0;
}

(** Nat type: constructors zero (0) and succ (1) *)
let natTyId : inductive = {
  inductive_mind = (stlc_modpath, "nat");
  inductive_ind = 0;
}

(** Inductive declarations for the base environment *)

let unit_decl : mutual_inductive_body = {
  ind_npars = 0;
  ind_bodies = [{
    ind_name = "unit";
    ind_propositional = false;
    ind_ctors = [{
      cstr_name = "tt";
      cstr_nargs = 0;
    }];
  }];
}

let bool_decl : mutual_inductive_body = {
  ind_npars = 0;
  ind_bodies = [{
    ind_name = "bool";
    ind_propositional = false;
    ind_ctors = [
      { cstr_name = "true"; cstr_nargs = 0; };
      { cstr_name = "false"; cstr_nargs = 0; }
    ];
  }];
}

let prod_decl : mutual_inductive_body = {
  ind_npars = 0;  (* We erase type parameters *)
  ind_bodies = [{
    ind_name = "prod";
    ind_propositional = false;
    ind_ctors = [{
      cstr_name = "pair";
      cstr_nargs = 2;
    }];
  }];
}

let sum_decl : mutual_inductive_body = {
  ind_npars = 0;  (* We erase type parameters *)
  ind_bodies = [{
    ind_name = "sum";
    ind_propositional = false;
    ind_ctors = [
      { cstr_name = "inl"; cstr_nargs = 1; };
      { cstr_name = "inr"; cstr_nargs = 1; }
    ];
  }];
}

let nat_decl : mutual_inductive_body = {
  ind_npars = 0;
  ind_bodies = [{
    ind_name = "nat";
    ind_propositional = false;
    ind_ctors = [
      { cstr_name = "zero"; cstr_nargs = 0; };
      { cstr_name = "succ"; cstr_nargs = 1; }
    ];
  }];
}

(** The base environment containing declarations for Unit, Bool, Pair, Sum, Nat *)
let base_env : global_env = [
  ((stlc_modpath, "unit"), InductiveDecl unit_decl);
  ((stlc_modpath, "bool"), InductiveDecl bool_decl);
  ((stlc_modpath, "prod"), InductiveDecl prod_decl);
  ((stlc_modpath, "sum"), InductiveDecl sum_decl);
  ((stlc_modpath, "nat"), InductiveDecl nat_decl);
]

(** Module path and kernel name for the IO runtime *)
let runtime_modpath : modpath = MPfile ["Runtime"]
let print_result_kn : kername = (runtime_modpath, "print_result")

(** Abstract runtime declarations — no body → Peregrine emits (global $Axioms ...) *)
let runtime_env : global_env = [
  (print_result_kn, ConstantDecl { cst_body = None })
]

(** Main compilation function: STLC expression to LambdaBox term *)
let rec compile (e: exp) : Tot term (decreases e) =
  match e with
  (* Unit and boolean constructors *)
  | EUnit -> TConstruct unitTyId 0 []
  | ETrue -> TConstruct boolTyId 0 []
  | EFalse -> TConstruct boolTyId 1 []
  | EString s -> TPrim (PrimString s)

  (* Variables and lambdas *)
  | EVar x -> TRel x
  | ELam b -> TLambda NAnon (compile b)
  | EApp f x -> TApp (compile f) (compile x)

  (* Pair operations *)
  | EPair e1 e2 -> TConstruct pairTyId 0 [compile e1; compile e2]
  | EFst e' ->
      (* case e' of pair x y => x *)
      (* Branch binds 2 variables, returns the first (index 1 since de Bruijn) *)
      TCase (pairTyId, 0) (compile e') [([NAnon; NAnon], TRel 1)]
  | ESnd e' ->
      (* case e' of pair x y => y *)
      (* Branch binds 2 variables, returns the second (index 0) *)
      TCase (pairTyId, 0) (compile e') [([NAnon; NAnon], TRel 0)]

  (* Sum operations *)
  | EInl e' -> TConstruct sumTyId 0 [compile e']
  | EInr e' -> TConstruct sumTyId 1 [compile e']
  | ECase s l r ->
      (* case s of inl x => l x | inr y => r y *)
      (* l and r are already lambdas in STLC, so we apply them to the bound variable *)
      TCase (sumTyId, 0) (compile s) [
        ([NAnon], TApp (compile l) (TRel 0));
        ([NAnon], TApp (compile r) (TRel 0))
      ]

  (* Natural number constructors *)
  | EZero -> TConstruct natTyId 0 []
  | ESucc e' -> TConstruct natTyId 1 [compile e']

  (* Natural number recursion: ENRec n base step *)
  (* Semantics: ENRec 0 base step => base; ENRec (succ v) base step => ENRec v (step base) step *)
  (* TCase is a simple match (succ binds only [pred], no IH); recursion requires TFix. *)
  (* All three args are passed into the fix to avoid shifting free variables: *)
  (*   (fix (λ self. λ n. λ base. λ step. case n of ...)) e1 e2 e3            *)
  (* After λ n, λ base, λ step:                                               *)
  (*   step=TRel 0, base=TRel 1, n=TRel 2, self=TRel 3                        *)
  (* Zero branch (0 bindings):  base = TRel 1.                                *)
  (* Succ branch [pred]:  pred=0, step=1, base=2, n=3, self=4.                *)
  (*   body: step (self pred base step)                                       *)
  (* rarg=0 because the first argument (n) is the one that decreases *)
  | ENRec e1 e2 e3 ->
      TApp (TApp (TApp
        (TFix [(NAnon,
          TLambda NAnon  (* n *)
            (TLambda NAnon  (* base *)
              (TLambda NAnon  (* step *)
                (TCase (natTyId, 0) (TRel 2)  (* n *)
                  [
                    ([], TRel 1);  (* zero: base *)
                    ([NAnon],      (* succ [pred]: step (self pred base step) *)
                      TApp (TRel 1)
                        (TApp (TApp (TApp (TRel 4) (TRel 0))  (* self pred *)
                          (TRel 2))  (* base *)
                          (TRel 1))) (* step *)
                  ]))),
          0)]  (* rarg = 0: first argument (n) is recursive *)
        0)
        (compile e1))   (* n *)
        (compile e2))   (* base *)
        (compile e3)    (* step *)

  (* Conditional *)
  | EIf c t e ->
      (* case c of true => t | false => e *)
      (* Bool constructors have 0 arguments *)
      TCase (boolTyId, 0) (compile c) [
        ([], compile t);
        ([], compile e)
      ]

(** Compile a full program with the base environment *)
let compile_program (e: exp) : program = (base_env, compile e)

(** Compile a program with named top-level constants.
    [modpath] is the module path for the definitions.
    [defs] is a list of (name, STLC expression) pairs — each becomes a ConstantDecl.
    [main_name] names which def is the entry point; the main term will be (TConst (modpath, main_name)).
    The definitions are compiled independently (no cross-references via TConst at the STLC level).
    base_env inductive declarations are included. *)
let compile_program_with_consts (modpath: modpath)
  (defs: list (string & exp))
  (main_name: string)
  : program =
  let compile_one (name_and_exp: string & exp) : kername & global_decl =
    let (name, e) = name_and_exp in
    ((modpath, name), ConstantDecl { cst_body = Some (compile e) })
  in
  let const_decls : global_env = List.Tot.map compile_one defs in
  (* IMPORTANT: Peregrine requires inductives AFTER constants that use them *)
  (const_decls @ base_env, TConst (modpath, main_name))

(** Compile an IO program: [main_name] must be a unit->nat function.
    The main term is (print_result main_fn), which prints the result. *)
let compile_io_program (modpath: modpath)
  (defs: list (string & exp))
  (main_name: string)
  : program =
  let compile_one (name_and_exp: string & exp) : kername & global_decl =
    let (name, e) = name_and_exp in
    ((modpath, name), ConstantDecl { cst_body = Some (compile e) })
  in
  let const_decls : global_env = List.Tot.map compile_one defs in
  let main_term = TApp (TConst print_result_kn) (TConst (modpath, main_name)) in
  (const_decls @ base_env @ runtime_env, main_term)

(** Serialize a program to its LambdaBox s-expression string (used by run-io.py) *)
let red_prog (p: program) : string = sexp_to_string (serialize_program p)
