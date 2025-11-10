module QExp

open FStar.Tactics
open FStar.Universe
open Free

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

| QFreeReturn :
        #g:typ_env ->
        #a:Type0 ->
        exp_quotation #(a -> free a) g (fun _ -> free_return #a)

| QFreeBind :
        #g:typ_env ->
        #a:Type0 ->
        #b:Type0 ->
        exp_quotation #(free a -> (a -> free b) -> free b) g (fun _ -> free_bind #a #b)

| QFreeRead :
        #g:typ_env ->
        exp_quotation #(unit -> free bool) g (fun _ -> free_read)

| QFreeWrite :
        #g:typ_env ->
        exp_quotation #(bool -> free unit) g (fun _ -> free_write)

open ExamplesIO

type closed_exp_quotation (a:Type0) (x:a) =
  exp_quotation #a empty (fun _ -> x)

#push-options "--no_smt"

let test_u_return
  : closed_exp_quotation _ u_return
  = QApp QFreeReturn QTrue

let test_papply_free_return
  : closed_exp_quotation _ papply_free_return
  = QFreeReturn

let test_apply_free_return
  : closed_exp_quotation _ apply_free_return
  = QLambda (QApp QFreeReturn QVar0)

let test_apply_free_read
  : closed_exp_quotation _ apply_free_read
  = QApp QFreeRead Qtt

let test_apply_free_write_const
  : closed_exp_quotation _ apply_free_write_const
  = QApp QFreeWrite QTrue

let test_apply_free_write
  : closed_exp_quotation _ apply_free_write
  = QLambda (QApp QFreeWrite QVar0)

let test_apply_free_bind_pure_if ()
  : closed_exp_quotation _ apply_free_bind_pure_if
  = magic ()
//    QLambda
//       (QApp
//         (QApp 
//           QFreeBind
//           (QApp QFreeReturn QVar0))
//         (QLambda
//           (QIf QVar0
//             (QApp QFreeReturn QFalse)
//             (QApp QFreeReturn QTrue))))

let test_apply_free_bind_write
  : closed_exp_quotation _ apply_free_bind_write
  = magic ()
//   = QLambda (
//       QApp 
//         (QApp 
//           QFreeBind
//           (QApp QFreeReturn QVar0))
//         (QLambda
//           (QApp QFreeWrite QVar0)))