(** Syntactic representation of F* types that we can compile. **)

module SyntacticTypes

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC

type typ =
  | TUnit : typ
  | TBool : typ
  | TArr  : typ -> typ -> typ

(** We have to very careful on how we define this elaboration of types.
    We'll face universe problems when using monads `Type u#a -> Type u#(max 1 a)`.
    See also: https://fstar.zulipchat.com/#narrow/stream/214975-fstar-ml-interop/topic/Language.20characterization **)
let rec elab_typ (t:typ) : Type0 =
  match t with
  | TUnit -> unit
  | TBool -> bool
  | TArr t1 t2 -> (elab_typ t1 -> elab_typ t2)

(** Typing environment **)
type env = var -> option typ

let empty : env = fun _ -> None

(* we only need extend at 0 *)
let extend (t:typ) (g:env)
  : env
  = fun y -> if y = 0 then Some t
          else g (y-1)

let fv_in_env (g:env) (e:exp) : Type0 =
  forall (fv:var). fv `memP` free_vars e ==> Some? (g fv)

let lem_no_fv_is_closed (e:exp) : Lemma
  (requires fv_in_env empty e)
  (ensures is_closed e)
  [SMTPat (is_closed e)] =
  ()

(** STLC Evaluation Environment : variable -> value **)
let gsub (g:env) (b:bool{b ==> (forall x. None? (g x))}) = (** CA: this b is polluting **)
  s:(sub b){forall x. Some? (g x) ==> is_value (s x)}

let gsub_empty : gsub empty true =
  (fun v -> EVar v)

let gsub_extend (#g:env) #b (s:gsub g b) (t:typ) (v:value) : gsub (extend t g) false =
  let f = fun (y:var) -> if y = 0 then v else s (y-1) in
  introduce exists (x:var). ~(EVar? (f x)) with 0 and ();
  f

let gsubst (#g:env) #b (s:gsub g b) (e:exp{fv_in_env g e}) : closed_exp =
  lem_subst_freevars_closes_exp s e 0;
  subst s e

let lem_substitution #g #b (s:gsub g b) (t:typ) (v:value) (e:exp)
  : Lemma (
    (subst (sub_beta v) (subst (sub_elam s) e)) == (subst (gsub_extend s t v) e))
  = admit () (** common lemma **)

let lem_gsubst_empty_identity (e:closed_exp) :
  Lemma (gsubst gsub_empty e == e)
  [SMTPat (gsubst gsub_empty e)] =
  admit ()
