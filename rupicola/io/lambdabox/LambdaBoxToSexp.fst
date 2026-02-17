module LambdaBoxToSexp

(** Serialize LambdaBox terms to S-expressions following the Peregrine format.
    Reference: https://github.com/peregrine-project/peregrine-tool/blob/ast-format/doc/format.md *)

open LambdaBox
open Sexp
open FStar.List.Tot

(** Serialize an identifier *)
let serialize_ident (i: ident) : sexp = str i

(** Serialize a directory path *)
let serialize_dirpath (dp: dirpath) : sexp =
  slist (List.Tot.map str dp)

(** Serialize a module path *)
let rec serialize_modpath (mp: modpath) : Tot sexp (decreases mp) =
  match mp with
  | MPfile dp -> slist [raw "MPfile"; serialize_dirpath dp]
  | MPbound dp id n -> slist [raw "MPbound"; serialize_dirpath dp; str id; num n]
  | MPdot mp' id -> slist [raw "MPdot"; serialize_modpath mp'; str id]

(** Serialize a kernel name *)
let serialize_kername (kn: kername) : sexp =
  let (mp, id) = kn in
  slist [serialize_modpath mp; str id]

(** Serialize a name (binder name) *)
let serialize_name (n: name) : sexp =
  match n with
  | NAnon -> raw "nAnon"
  | NNamed id -> slist [raw "nNamed"; str id]

(** Serialize an inductive reference *)
let serialize_inductive (ind: inductive) : sexp =
  slist [raw "inductive"; serialize_kername ind.inductive_mind; num ind.inductive_ind]

(** Serialize a primitive value *)
let serialize_prim_val (pv: prim_val) : sexp =
  match pv with
  | PrimString s -> slist [raw "primString"; str s]
  (* Future: PrimFloat, PrimArray *)

(** Serialize a list of names (for branch binders) *)
let serialize_names (ns: list name) : sexp =
  slist (List.Tot.map serialize_name ns)

(** Serialize a term - uses explicit recursion for lists to help termination checker *)
let rec serialize_term (t: term) : Tot sexp (decreases t) =
  match t with
  | TBox -> raw "tBox"
  | TRel n -> slist [raw "tRel"; num n]
  | TLambda na body -> slist [raw "tLambda"; serialize_name na; serialize_term body]
  | TApp f x -> slist [raw "tApp"; serialize_term f; serialize_term x]
  | TConst kn -> slist [raw "tConst"; serialize_kername kn]
  | TConstruct ind n args ->
      slist [raw "tConstruct"; serialize_inductive ind; num n;
             slist (serialize_terms args)]
  | TCase (ind, npars) scrut brs ->
      slist [raw "tCase";
             slist [serialize_inductive ind; num npars];
             serialize_term scrut;
             slist (serialize_branches brs)]
  | TLetIn na v body ->
      slist [raw "tLetIn"; serialize_name na; serialize_term v; serialize_term body]
  | TFix defs i ->
      slist [raw "tFix"; slist (serialize_fixpoint_defs defs); num i]
  | TPrim pv ->
      slist [raw "tPrim"; serialize_prim_val pv]

and serialize_terms (ts: list term) : Tot (list sexp) (decreases ts) =
  match ts with
  | [] -> []
  | t :: rest -> serialize_term t :: serialize_terms rest

and serialize_branches (brs: list (list name & term)) : Tot (list sexp) (decreases brs) =
  match brs with
  | [] -> []
  | (names, body) :: rest ->
      slist [serialize_names names; serialize_term body] :: serialize_branches rest

and serialize_fixpoint_defs (defs: list (name & term & nat)) : Tot (list sexp) (decreases defs) =
  match defs with
  | [] -> []
  | (n, body, rarg) :: rest ->
      slist [raw "def"; serialize_name n; serialize_term body; num rarg] :: serialize_fixpoint_defs rest

(** Serialize a constructor body *)
let serialize_constructor_body (cb: constructor_body) : sexp =
  slist [raw "constructor_body"; str cb.cstr_name; num cb.cstr_nargs]

(** Serialize one inductive body *)
let serialize_one_inductive_body (oib: one_inductive_body) : sexp =
  slist [
    raw "one_inductive_body";
    str oib.ind_name;
    raw (if oib.ind_propositional then "true" else "false");
    raw "IntoAny";
    slist (List.Tot.map serialize_constructor_body oib.ind_ctors);
    slist []
  ]

(** Serialize a mutual inductive body *)
let serialize_mutual_inductive_body (mib: mutual_inductive_body) : sexp =
  slist [
    raw "mutual_inductive_body";
    raw "Finite";
    num mib.ind_npars;
    slist (List.Tot.map serialize_one_inductive_body mib.ind_bodies)
  ]

(** Serialize a constant body *)
let serialize_constant_body (cb: constant_body) : sexp =
  match cb.cst_body with
  | None -> slist [raw "constant_body"; raw "None"]
  | Some t -> slist [raw "constant_body"; slist [raw "Some"; serialize_term t]]

(** Serialize a global declaration *)
let serialize_global_decl (gd: global_decl) : sexp =
  match gd with
  | ConstantDecl cb -> slist [raw "ConstantDecl"; serialize_constant_body cb]
  | InductiveDecl mib -> slist [raw "InductiveDecl"; serialize_mutual_inductive_body mib]

(** Serialize a global environment entry *)
let serialize_global_entry (entry: kername & global_decl) : sexp =
  let (kn, gd) = entry in
  slist [serialize_kername kn; serialize_global_decl gd]

(** Serialize a global environment *)
let serialize_global_env (env: global_env) : sexp =
  slist (List.Tot.map serialize_global_entry env)

(** Serialize a complete program (environment + main term) *)
let serialize_program (p: program) : sexp =
  let (env, t) = p in
  slist [serialize_global_env env; serialize_term t]
