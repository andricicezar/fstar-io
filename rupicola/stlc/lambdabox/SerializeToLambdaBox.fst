module SerializeToLambdaBox

open STLC

(** Lambda Box term **)

(**

https://github.com/MetaRocq/metarocq/blob/9.1/common/theories/Kernames.v
https://github.com/MetaRocq/metarocq/blob/9.1/erasure/theories/EAst.v

Definition kername := modpath × ident. // string * string

Record inductive : Set := mkInd { inductive_mind : kername ;
                                  inductive_ind : nat }.

1. Define the inductive types in Lambda Box.
  1.a Define the identifier
  let pairTyID : inductive = { inductive_mind = "Common" * "Pair", inductive_ind = 0 }
  Program = Env * Term

  1.b

  let pairTy : inductive_decl = // stored in the environment
(MPfile ["Datatypes"; "Init"; "Corelib"], "prod",
          EAst.InductiveDecl
            {|
              ExtractionCorrectness.E.ind_finite := Finite;
              ExtractionCorrectness.E.ind_npars := 0;
              ExtractionCorrectness.E.ind_bodies :=
                [{|
                   ExtractionCorrectness.E.ind_name := "prod";
                   ExtractionCorrectness.E.ind_propositional := false;
                   ExtractionCorrectness.E.ind_kelim := IntoAny;
                   ExtractionCorrectness.E.ind_ctors :=
                     [{|
                        ExtractionCorrectness.E.cstr_name := "pair";
                        ExtractionCorrectness.E.cstr_nargs := 2
                      |}];
                   ExtractionCorrectness.E.ind_projs := []
                 |}]
            |})

Record one_inductive_body : Set := {
  ind_name : ident;
  ind_propositional : bool; (* True iff the inductive lives in Prop *)
  ind_kelim : allowed_eliminations; (* Allowed eliminations *)
  ind_ctors : list constructor_body;
  ind_projs : list projection_body (* names of projections, if any. *) }.
Derive NoConfusion for one_inductive_body.

(** See [mutual_inductive_body] from [declarations.ml]. *)
Record mutual_inductive_body := {
  ind_finite : recursivity_kind;
  ind_npars : nat;
  ind_bodies : list one_inductive_body }.


Inductive term : Set :=
// | tBox (* Represents all proofs *) // for computationally irrelevant
| tRel (n : nat)
// | tVar (i : ident) (* For free variables (e.g. in a goal) *)
// | tEvar (n : nat) (l : list term)
| tLambda (na : name) (t : term)
// | tLetIn (na : name) (b t : term) (* let na := b : B in t *)
| tApp (u v : term)
// | tConst (k : kername)
| tConstruct (ind : inductive) (n : nat) (args : list term)
| tCase (indn : inductive * nat (* # of parameters *)) (c : term  (* discriminee *)) (brs : list (list name * term) (* branches *))
// | tProj (p : projection) (c : term)
// | tFix (mfix : mfixpoint term) (idx : nat)
// | tCoFix (mfix : mfixpoint term) (idx : nat)
| tPrim (prim : prim_val term) // for Rocq primitives -- arrays, strings, machine integers
// | tLazy (t : term)
// | tForce (t : term).

name defined in https://github.com/MetaRocq/metarocq/blob/9.1/common/theories/BasicAst.v

val stlc_to_lbox : exp -> term
let rec stlc_to_lbox e =
  match e with
  (** Constructors **)
  | EPair fst snd -> tConstruct pairTyId 0 [stlc_to_lbox fst; stlc_to_lbox snd]
  (** Lambdas **)
  | EVar x -> tRel x
  | ELam b -> tLambda tAnon (stlc_to_lbox b)
  | EApp f x -> tApp (stlc_to_lbox f) (stlc_to_lbox x)
  (** Pattern matching **)
  | EIf c t e -> tCase (pairTyId, 0) (stlc_to_lbox c) [([], stlc_to_lbox t); ([], stlc_to_lbox e)]
  | ECase  : exp -> exp -> exp -> exp


So one file with topological sorted top-level definitions: https://github.com/peregrine-project/peregrine-tool/blob/ast-format/doc/format.md
Pair of two things:
1. Environment -- list of declarations (primitive to Ceres, (1 2 3))
2. Just a term


https://github.com/agda/agda2lambox/tree/master/test
https://github.com/peregrine-project/peregrine-tool/tree/ast-format/test/agda
**)



(** Following Ceres **)

type atom =
| Num : int -> atom  (* Integers. *)
| Str : string -> atom  (* Literal strings. *)
| Raw : string -> atom  (* Simple atoms (e.g., ADT tags). *)
                           (* Should fit in this alphabet:
                           [A-Za-z0-9'=+*/:!?@#$%^&<>.,|_~-]. *)

type sexp =
| Atom : atom -> sexp
| List : list sexp -> sexp

val serialize : exp -> sexp
let rec serialize e =
  match e with
  (** Unary construtors **)
  | EUnit -> Atom (Raw "()")
  | ETrue -> Atom (Raw "true")
  | EFalse -> Atom (Raw "false")
  (** Constructors **)
  | EPair  : fst:exp -> snd:exp -> exp
  | EInl   : exp -> exp
  | EInr   : exp -> exp
  | EFst   : exp -> exp
  | ESnd   : exp -> exp
  (** Lambdas **)
  | EVar x -> List [Atom "tEvar"; Raw (Num x)]
  | ELam b -> List [Atom "tLambda"; serialize b]
  | EApp f x -> List [Atom "tApp"; serialize f; serialize x]
  (** Pattern matching **)
  | EIf c t e -> List [Atom "tCase"; ]
  | ECase  : exp -> exp -> exp -> exp
