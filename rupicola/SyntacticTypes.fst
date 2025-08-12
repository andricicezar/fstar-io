(** Syntactic representation of F* types that we can compile. **)

module SyntacticTypes

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC

type typ =
  | TUnit : typ
  | TArr  : typ -> typ -> typ

(** We have to very careful on how we define this elaboration of types.
    We'll face universe problems when using monads `Type u#a -> Type u#(max 1 a)`.
    See also: https://fstar.zulipchat.com/#narrow/stream/214975-fstar-ml-interop/topic/Language.20characterization **)
let rec elab_typ (t:typ) : Type0 =
  match t with
  | TUnit -> unit
  | TArr t1 t2 -> (elab_typ t1 -> elab_typ t2)

(** Common definition of typing environment **)
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
