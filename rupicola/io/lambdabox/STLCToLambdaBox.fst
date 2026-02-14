module STLCToLambdaBox

(** Compiler from STLC expressions (with IO) to LambdaBox terms. *)

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

(** Sum type: constructors inl (0) and inr (1), each with 1 argument.
    Also used for resexn = either a unit. *)
let sumTyId : inductive = {
  inductive_mind = (stlc_modpath, "sum");
  inductive_ind = 0;
}

(** Nat type: constructors zero (0) and succ (1).
    Used to represent file_descr values (file_descr = nat). *)
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

(** The base environment containing declarations for Unit, Bool, Pair, Sum, Nat.
    Nat is kept for representing file_descr values (file_descr = nat). *)
let base_env : global_env = [
  ((stlc_modpath, "unit"), InductiveDecl unit_decl);
  ((stlc_modpath, "bool"), InductiveDecl bool_decl);
  ((stlc_modpath, "prod"), InductiveDecl prod_decl);
  ((stlc_modpath, "sum"), InductiveDecl sum_decl);
  ((stlc_modpath, "nat"), InductiveDecl nat_decl);
]

(** Module path and kernel names for the IO runtime *)
let runtime_modpath : modpath = MPfile ["Runtime"]
let io_read_kn  : kername = (runtime_modpath, "io_read")
let io_write_kn : kername = (runtime_modpath, "io_write")
let io_open_kn  : kername = (runtime_modpath, "io_open")
let io_close_kn : kername = (runtime_modpath, "io_close")
let run_main_kn : kername = (runtime_modpath, "run_main")

(** Abstract runtime declarations — no body → Peregrine emits (global $Axioms ...) *)
let runtime_env : global_env = [
  (io_read_kn,  ConstantDecl { cst_body = None });
  (io_write_kn, ConstantDecl { cst_body = None });
  (io_open_kn,  ConstantDecl { cst_body = None });
  (io_close_kn, ConstantDecl { cst_body = None });
  (run_main_kn, ConstantDecl { cst_body = None });
]

(** Compile a file_descr (nat) literal to a Church-encoded LambdaBox nat term.
    file_descr = nat, so fd 0 = zero, fd 1 = succ zero, etc. *)
let rec compile_nat (n: nat) : Tot term (decreases n) =
  if n = 0 then TConstruct natTyId 0 []
  else TConstruct natTyId 1 [compile_nat (n - 1)]

(** Main compilation function: STLC expression (with IO) to LambdaBox term *)
let rec compile (e: exp) : Tot term (decreases e) =
  match e with
  (* Unit and boolean constructors *)
  | EUnit  -> TConstruct unitTyId 0 []
  | ETrue  -> TConstruct boolTyId 0 []
  | EFalse -> TConstruct boolTyId 1 []

  (* Variables and lambdas *)
  | EVar x   -> TRel x
  | ELam b   -> TLambda NAnon (compile b)
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

  (* Sum operations (also covers resexn = either a unit) *)
  | EInl e' -> TConstruct sumTyId 0 [compile e']
  | EInr e' -> TConstruct sumTyId 1 [compile e']
  | ECase s l r ->
      (* case s of inl x => l x | inr y => r y *)
      (* l and r are already lambdas in STLC, so we apply them to the bound variable *)
      TCase (sumTyId, 0) (compile s) [
        ([NAnon], TApp (compile l) (TRel 0));
        ([NAnon], TApp (compile r) (TRel 0))
      ]

  (* Conditional *)
  | EIf c t e ->
      (* case c of true => t | false => e *)
      (* Bool constructors have 0 arguments *)
      TCase (boolTyId, 0) (compile c) [
        ([], compile t);
        ([], compile e)
      ]

  (* File descriptor literal: compile nat value to Church-encoded nat *)
  | EFileDescr fd -> compile_nat fd

  (* IO operations: compiled as calls to runtime axioms.
     The monad is erased: ERead/EWrite/EOpen/EClose are direct calls that return values.
     Sequencing (bind) has been compiled away to EApp (ELam k) m at the STLC level. *)
  | ERead fd ->
      TApp (TConst io_read_kn) (compile fd)
  | EWrite fd msg ->
      TApp (TApp (TConst io_write_kn) (compile fd)) (compile msg)
  | EOpen fnm ->
      TApp (TConst io_open_kn) (compile fnm)
  | EClose fd ->
      TApp (TConst io_close_kn) (compile fd)

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

(** Compile an IO program: [main_name] must be a (unit -> resexn unit) function.
    The main term is (run_main main_fn), which executes the IO computation. *)
let compile_io_program (modpath: modpath)
  (defs: list (string & exp))
  (main_name: string)
  : program =
  let compile_one (name_and_exp: string & exp) : kername & global_decl =
    let (name, e) = name_and_exp in
    ((modpath, name), ConstantDecl { cst_body = Some (compile e) })
  in
  let const_decls : global_env = List.Tot.map compile_one defs in
  let main_term = TApp (TConst run_main_kn) (TConst (modpath, main_name)) in
  (const_decls @ base_env @ runtime_env, main_term)

(** Serialize a program to its LambdaBox s-expression string (used by run-io.py) *)
let red_prog (p: program) : string = sexp_to_string (serialize_program p)
