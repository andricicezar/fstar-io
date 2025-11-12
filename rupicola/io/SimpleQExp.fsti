module SimpleQExp

open FStar.Tactics
open FStar.Universe
open IO

(** typ_env is a typing environment: variables to F* types **)
type typ_env = nat -> option Type0
val empty : typ_env
val extend : Type0 -> typ_env -> typ_env

(** eval_env is an evaluation environment: variables to F* values **)
val eval_env (g:typ_env) : Type
val hd : #t:Type0 -> #g:_ -> eval_env (extend t g) -> t
val tail : #t:Type0 -> #g:_ ->  eval_env (extend t g) -> eval_env g

type fs_oexp (g:typ_env) (a:Type0) =
  eval_env g -> a

noeq
type exp_quotation : #a:Type0 -> g:typ_env -> fs_oexp g a -> Type =
| Qtt : #g:typ_env -> exp_quotation g (fun _ -> ())
| QFalse : #g:typ_env -> exp_quotation g (fun _ -> false)

| QTrue : #g:typ_env -> exp_quotation g (fun _ -> true)

| QIf : #g:typ_env ->
        #a:Type0 ->
        #cond:fs_oexp g bool -> #b1:fs_oexp g a -> #b2:fs_oexp g a ->
        exp_quotation g cond -> exp_quotation g b1 -> exp_quotation g b2 ->
        exp_quotation #a g (fun fsG -> if cond fsG then b1 fsG else b2 fsG)

| QVar0  : #g:typ_env -> #a:Type0 -> exp_quotation (extend a g) (fun fsG -> hd fsG)

| QVar1  : #g:typ_env -> #a:Type0 -> #b:Type0 -> exp_quotation (extend b (extend a g)) (fun fsG -> hd (tail fsG))

(** ... we need a case for each deBrujin variable **)
| QApp : #g:_ -> #a:Type0 -> #b:Type0 ->
        #f:fs_oexp g (a -> b) -> #x:fs_oexp g a ->
        exp_quotation g f -> exp_quotation g x ->
        exp_quotation #b g (fun fsG -> (f fsG) (x fsG))

| QLambda : #g:_ -> #a:Type0 -> #b:Type0 ->
        #f:fs_oexp g (a -> b) ->
        exp_quotation #b (extend a g) (fun fsG -> (f (tail fsG)) (hd fsG)) ->
        exp_quotation g f

| QReturn :
        #g:typ_env ->
        #a:Type0 ->
        #x:fs_oexp g a ->
        exp_quotation g x ->
        exp_quotation #(io a) g (fun fsG -> io_return #a (x fsG))

| QBind :
        #g:typ_env ->
        #a:Type0 ->
        #b:Type0 ->
        #m:fs_oexp g (io a) ->
        #k:fs_oexp g (a -> io b) ->
        exp_quotation g m ->
        exp_quotation g k ->
        exp_quotation #(io b) g (fun fsG -> io_bind #a #b (m fsG) (k fsG))

(** Return and Bind as functions:
| QReturn :
        #g:typ_env ->
        #a:Type0 ->
        exp_quotation #(a -> io a) g (fun _ -> io_return #a)

| QBind :
        #g:typ_env ->
        #a:Type0 ->
        #b:Type0 ->
        exp_quotation #(io a -> (a -> io b) -> io b) g (fun _ -> io_bind #a #b)
**)

(** Read & Write as functions **)
| QRead :
        #g:typ_env ->
        exp_quotation #(unit -> io bool) g (fun _ -> read)

| QWrite :
        #g:typ_env ->
        exp_quotation #(bool -> io unit) g (fun _ -> write)

open ExamplesIO

type closed_exp_quotation (a:Type0) (x:a) =
  exp_quotation #a empty (fun _ -> x)

#push-options "--no_smt"

let test_u_return
  : closed_exp_quotation _ u_return
  = QReturn QTrue

(**
let test_papply_io_return
  : closed_exp_quotation _ papply_io_return
  = QReturn
**)

let test_apply_io_return
  : closed_exp_quotation _ apply_io_return
  = QLambda (QReturn QVar0)

let test_apply_read
  : closed_exp_quotation _ apply_read
  = QApp QRead Qtt

let test_apply_write_const
  : closed_exp_quotation _ apply_write_const
  = QApp QWrite QTrue

let test_apply_write
  : closed_exp_quotation _ apply_write
  = QLambda (QApp QWrite QVar0)

let test_apply_io_bind_const
  : closed_exp_quotation _ apply_io_bind_const
  = QBind
      (QReturn QTrue)
      (QLambda (QReturn QVar0))

let test_apply_io_bind_identity
  : closed_exp_quotation _ apply_io_bind_identity
  = QLambda
      (QBind
        (QReturn QVar0)
        (QLambda #_ #_ #_ #(fun fsG y -> io_return y) (QReturn QVar0)))

let test_apply_io_bind_pure_if
  : closed_exp_quotation _ apply_io_bind_pure_if
  = QLambda
      (QBind
        (QReturn QVar0)
        (QLambda #_ #_ #_ #(fun fsG y -> if y then io_return false else io_return true)
          (QIf QVar0
            (QReturn QFalse)
            (QReturn QTrue))))

let test_apply_io_bind_write
  : closed_exp_quotation _ apply_io_bind_write
  = QLambda (
      QBind
         (QReturn QVar0)
         (QLambda #_ #_ #_ #(fun fsG y -> write y)
           (QApp QWrite QVar0)))

let test_apply_io_bind_read_write
  : closed_exp_quotation _ apply_io_bind_read_write
  = QBind
     (QApp QRead Qtt)
     (QLambda
       (QApp QWrite QVar0))

let test_apply_io_bind_read_write'
  : closed_exp_quotation _ apply_io_bind_read_write'
  = QBind (QApp QRead Qtt) QWrite

let test_apply_io_bind_read_if_write
  : closed_exp_quotation _ apply_io_bind_read_if_write
  = QBind
      (QApp QRead Qtt)
      (QLambda (** TODO: weird that this does not require the lambda as the other examples **)
        (QIf QVar0
          (QApp QWrite QFalse)
          (QApp QWrite QTrue)))
