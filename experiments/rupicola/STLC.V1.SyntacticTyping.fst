(* Based on file FStar/examples/metatheory/StlcStrongDbParSubst.fst *)

module STLC.V1.SyntacticTyping

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Calc
open FStar.List.Tot

type typ =
  | TArr  : typ -> typ -> typ
  | TUnit : typ

let rec elab_typ (t:typ) : Type0 =
  match t with
  | TUnit -> unit
  | TArr t1 t2 -> (elab_typ t1 -> elab_typ t2)

class compile_typ (s:Type) = {
  [@@@no_method] t : (t:typ{elab_typ t == s}) // this could already create universe problems when using monads `u -> max 1 u`
}

instance compile_typ_unit : compile_typ unit = { t = TUnit }
instance compile_typ_arrow s1 s2 {| c1:compile_typ s1 |} {| c2:compile_typ s2 |} : compile_typ (s1 -> s2) =
  { t = begin
    let t = (TArr c1.t c2.t) in
    assert (elab_typ t == (elab_typ c1.t -> elab_typ c2.t))
      by (norm [delta_only [`%elab_typ];zeta;iota]);
    assert (s1 == elab_typ c1.t);
    assert (s2 == elab_typ c2.t);
    assert ((s1 -> s2) == elab_typ t) by (
      rewrite (nth_binder (-1));
      rewrite (nth_binder (-3))
    );
    t
   end }

// Some tests
let test0 : compile_typ (unit) = solve
let _ = assert (test0.t == TUnit)
let test1 : compile_typ (unit -> unit) = solve
let _ = assert (test1.t == (TArr TUnit TUnit))
let test2 : compile_typ ((unit -> unit) -> (unit -> unit)) = solve
let _ = assert (test2.t == TArr (TArr TUnit TUnit) (TArr TUnit TUnit))
// stress test
let test3 : compile_typ ((unit -> unit) -> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)-> (unit -> unit)) = solve

type var = nat

type exp =
  | EUnit : exp
  | ELam  : typ -> exp -> exp
  | EVar  : var -> exp
  | EApp  : exp -> exp -> exp

(* Type system; as inductive relation (not strictly necessary for STLC) *)

type env = var -> Tot (option typ)

val empty : env
let empty _ = None

(* we only need extend at 0 *)
val extend : typ -> env -> Tot env
let extend t g y = if y = 0 then Some t
                   else g (y-1)

noeq type typing : env -> exp -> typ -> Type =
  | TyVar : #g:env ->
             x:var{Some? (g x)} ->
             typing g (EVar x) (Some?.v (g x))
  | TyLam : #g :env ->
             t :typ ->
            #e1:exp ->
            #t':typ ->
            $hbody:typing (extend t g) e1 t' ->
                   typing g (ELam t e1) (TArr t t')
  | TyApp : #g:env ->
            #e1:exp ->
            #e2:exp ->
            #t11:typ ->
            #t12:typ ->
            $h1:typing g e1 (TArr t11 t12) ->
            $h2:typing g e2 t11 ->
                typing g (EApp e1 e2) t12
  | TyUnit : #g:env ->
             typing g EUnit TUnit


class compile_exp (#a:Type0) {| ca: compile_typ a |} (s:a) (varn:nat) = {
  [@@@no_method] t : exp
}

assume val get_v : y:var -> a:Type0 -> a
(** CA: this is an abstraction that helps with dealing with
   variables **)

instance compile_exp_unit n : compile_exp #unit #solve () n = {
  t = EUnit
}

let test_unit : compile_exp () 0 = solve

instance compile_exp_var (#a:Type) {| ca: compile_typ a |} n (i:nat{i <= n}) : compile_exp (get_v i a) n = {
    t = EVar (n-i)
  }

instance compile_exp_lambda
  (n:nat)
  (#a:Type) {| ca: compile_typ a |}
  (#b:Type) {| cb: compile_typ b |}
  (f:a -> b) {| cf: (compile_exp #_ #cb (f (get_v (n+1) a)) (n+1)) |}
  : compile_exp #_ #solve (fun x -> f x) n = {
  t = ELam ca.t cf.t
}

let test1_exp : compile_exp #(unit -> unit) (fun x -> ()) 0 =
  solve
let _ = assert (test1_exp.t == ELam TUnit (EUnit))

let test2_exp : compile_exp #(unit -> unit) (fun x -> x) 0 =
  solve
let _ = assert (test2_exp.t == ELam TUnit (EVar 0))

let test3_exp : compile_exp #(unit -> unit -> unit) (fun x y -> x) 0 =
  solve
let _ = assert (test3_exp.t == ELam TUnit (ELam TUnit (EVar 1)))

let test4_exp : compile_exp #(unit -> unit -> unit) (fun x y -> y) 0 =
  solve
let _ = assert (test4_exp.t == ELam TUnit (ELam TUnit (EVar 0)))

instance compile_exp_app
  (n:nat)
  (#a:Type) {| ca: compile_typ a |}
  (#b:Type) {| cb: compile_typ b |}
  (f:a -> b) {| cf: compile_exp #_ #solve f n |}
  (x:a)     {| cx: compile_exp #_ #ca x n |}
  : compile_exp #_ #cb (f x) n = {
  t = EApp (cf.t) (cx.t)
}

let test0_fapp : compile_exp #unit #solve ((fun x y -> y) () ()) 0 =
  solve
let _ = assert (test0_fapp.t == EUnit)

(** How to deal with top level definitions? **)

val myf : unit -> unit
let myf () = ()

(* It seems that it just unfolds the definition of myf, which is pretty cool **)
let test1_topf : compile_exp (myf ()) 0 =
  solve
//let _ = assert (test1_topf.t == EApp (ELam TUnit EUnit) EUnit) by (dump "H")

val myf2 : unit -> unit -> unit
let myf2 x y = x

(* Also handles partial application. Pretty amazing! *)
let test2_topf : compile_exp (myf2 ()) 0 =
  solve
//let _ = assert (test2_topf.t == EApp (ELam TUnit (ELam TUnit (EVar 1))) EUnit)
