module LambdaBox

(** LambdaBox term representation based on MetaRocq's erasure AST.
    References:
    - https://github.com/MetaRocq/metarocq/blob/9.1/common/theories/Kernames.v
    - https://github.com/MetaRocq/metarocq/blob/9.1/erasure/theories/EAst.v
    - https://github.com/MetaRocq/metarocq/blob/9.1/common/theories/BasicAst.v *)

open FStar.List.Tot

(** Identifiers and names *)
type ident = string

(** Directory path - reversed list: ["C";"B";"A"] represents A.B.C *)
type dirpath = list ident

(** Module path *)
type modpath =
  | MPfile : dirpath -> modpath
  | MPbound : dirpath -> ident -> nat -> modpath
  | MPdot : modpath -> ident -> modpath

(** Kernel name = module path + identifier *)
type kername = modpath & ident

(** Name for binders *)
type name =
  | NAnon : name
  | NNamed : ident -> name

(** Inductive type reference *)
noeq type inductive = {
  inductive_mind : kername;
  inductive_ind : nat;
}

(** Primitive values - based on MetaRocq EPrimitive.v *)
type prim_val =
  | PrimString : string -> prim_val     (* String / byte string *)
  (* Future: PrimFloat, PrimArray *)

(** Terms - subset of MetaRocq EAst.term needed for STLC *)
noeq type term =
  | TBox : term                                              (* Proofs/irrelevant terms *)
  | TRel : nat -> term                                       (* de Bruijn index *)
  | TLambda : name -> term -> term                           (* Lambda abstraction *)
  | TApp : term -> term -> term                              (* Application *)
  | TConst : kername -> term                                 (* Reference to a constant *)
  | TConstruct : inductive -> nat -> list term -> term       (* Constructor with index and args *)
  | TCase : (inductive & nat) -> term -> list (list name & term) -> term  (* Pattern match *)
  | TLetIn : name -> term -> term -> term                                (* Let-in: name, value, body *)
  | TFix : list (name & term & nat) -> nat -> term                       (* Fixpoint: defs (name, body, rarg), index *)
  | TPrim : prim_val -> term                                             (* Primitive values *)

(** Constructor body for inductive declarations *)
noeq type constructor_body = {
  cstr_name : ident;
  cstr_nargs : nat;
}

(** One inductive body in a mutual block *)
noeq type one_inductive_body = {
  ind_name : ident;
  ind_propositional : bool;  (* True iff the inductive lives in Prop *)
  ind_ctors : list constructor_body;
}

(** Mutual inductive body *)
noeq type mutual_inductive_body = {
  ind_npars : nat;
  ind_bodies : list one_inductive_body;
}

(** Constant body - wraps an optional term definition *)
noeq type constant_body = {
  cst_body : option term;
}

(** Global declaration - constant or inductive *)
noeq type global_decl =
  | ConstantDecl : constant_body -> global_decl
  | InductiveDecl : mutual_inductive_body -> global_decl

(** Global environment - list of declarations *)
type global_env = list (kername & global_decl)

(** A program is an environment plus a main term *)
type program = global_env & term
