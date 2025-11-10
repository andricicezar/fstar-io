module QExp

open Free

(** typ_env is a typing environment: variables to F* types **)
type typ_env = nat -> option Type
val empty : typ_env
val extend : Type -> typ_env -> typ_env
(** eval_env is an evaluation environment: variables to F* values **)
type eval_env (g:typ_env) = x:nat{Some? (g x)} -> Some?.v (g x)
val hd : #g:_ -> #t:Type -> eval_env (extend t g) -> t
val tail : #g:_ -> #t:Type -> eval_env (extend t g) -> eval_env g

type fs_oexp (g:typ_env) (a:Type) = eval_env g -> a

open FStar.Universe

noeq
type exp_quotation : #a:Type u#1 -> g:typ_env -> fs_oexp g a -> Type =
| Qtt : #g:typ_env -> exp_quotation #(raise_t u#0 u#1 unit) g (fun _ -> raise_val ())
| QFalse : #g:typ_env -> exp_quotation #(raise_t u#0 u#1 bool) g (fun _ -> raise_val false)
| QTrue : #g:typ_env -> exp_quotation #(raise_t u#0 u#1 bool) g (fun _ -> raise_val true)
| QIf : #g:typ_env ->
        #a:Type ->
        #cond:fs_oexp g (raise_t u#0 u#1 bool) -> #b1:fs_oexp g a -> #b2:fs_oexp g a ->
        exp_quotation g cond -> exp_quotation g b1 -> exp_quotation g b2 ->
        exp_quotation g (fun fsG -> if downgrade_val (cond fsG) then b1 fsG else b2 fsG)
| QVar0  : #g:typ_env -> #a:Type -> exp_quotation (extend a g) (fun fsG -> hd fsG)
| QVar1  : #g:typ_env -> #a:Type -> #b:Type -> exp_quotation (extend b (extend a g)) (fun fsG -> hd (tail fsG))
(** ... we need a case for each deBrujin variable **)
| QApp : #g:_ -> #a:Type -> #b:Type ->
        #f:fs_oexp g (a -> b) -> #x:fs_oexp g a ->
        exp_quotation g f -> exp_quotation g x ->
        exp_quotation #b g (fun fsG -> (f fsG) (x fsG))
| QAbs : #g:_ -> #a:Type -> #b:Type ->
        #f:fs_oexp g (a -> b) ->
        exp_quotation #b (extend a g) (fun fsG -> (f (tail fsG)) (hd fsG)) ->
        exp_quotation g f
| QFreeReturn :
        #g:typ_env ->
        #a:Type ->
        exp_quotation #(a -> free a) g (fun _ -> free_return #a)
| QFreeBind :
        #g:typ_env ->
        #a:Type ->
        #b:Type ->
        exp_quotation #(free a -> (a -> free b) -> free b) g (fun _ -> free_bind #a #b)
| QFreeRead :
        #g:typ_env ->
        exp_quotation #(unit -> free bool) g (fun _ -> free_read)
| QFreeWrite :
        #g:typ_env ->
        exp_quotation #(bool -> free unit) g (fun _ -> free_write)

open ExamplesIO

type closed_exp_quotation (a:Type) (x:a) =
  exp_quotation #a empty (fun _ -> x)

let test_u_return
  : closed_exp_quotation _ (free_return (raise_val true))
  = QApp QFreeReturn QTrue
