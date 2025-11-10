module PredicateQuotation

(** typ_env is a typing environment: variables to F* types **)
type typ_env = nat -> option Type
val empty : typ_env
val extend : Type -> typ_env -> typ_env
(** eval_env is an evaluation environment: variables to F* values **)
type eval_env (g:typ_env) = x:nat{Some? (g x)} -> Some?.v (g x)
val hd : #g:_ -> #t:Type -> eval_env (extend t g) -> t
val tail : #g:_ -> #t:Type -> eval_env (extend t g) -> eval_env g

type fs_oexp (g:typ_env) (a:Type) = eval_env g -> a

noeq
type rq : #a:Type -> g:typ_env -> fs_oexp g a -> Type =
| CFalse : #g:typ_env -> rq g (fun _ -> false)
| CTrue : #g:typ_env -> rq g (fun _ -> true)
| CIf : #g:typ_env ->
        #a:Type ->
        #cond:fs_oexp g bool -> #b1:fs_oexp g a -> #b2:fs_oexp g a ->
        rq g cond -> rq g b1 -> rq g b2 ->
        rq g (fun fsG -> if cond fsG then b1 fsG else b2 fsG)
| CVar0  : #g:typ_env -> #a:Type -> rq (extend a g) (fun fsG -> hd fsG)
| CVar1  : #g:typ_env -> #a:Type -> #b:Type -> rq (extend b (extend a g)) (fun fsG -> hd (tail fsG))
(** ... we need a case for each deBrujin variable **)
| CApp : #g:_ -> #a:Type -> #b:Type ->
        #f:fs_oexp g (a -> b) -> #x:fs_oexp g a ->
        rq g f -> rq g x ->
        rq #b g (fun fsG -> (f fsG) (x fsG))
| CAbs : #g:_ -> #a:Type -> #b:Type ->
        #f:fs_oexp g (a -> b) ->
        rq #b (extend a g) (fun fsG -> (f (tail fsG)) (hd fsG)) ->
        rq g f

let somep : rq empty (fun _ -> if true then false else true) =
  CIf CTrue CFalse CTrue

let neg_pred (p:bool -> bool) : bool -> bool =
  fun x -> if p x then false else true

let cnp : rq empty (fun _ -> neg_pred) =
  CAbs (CAbs (CIf (CApp CVar1 CVar0) CFalse CTrue))

open FStar.Tactics
open FStar.Tactics.Typeclasses

class rq_tc (#a:Type) (g:typ_env) (e: fs_oexp g a) = { prf: rq g e }

instance rq_CFalse (#g:typ_env) : rq_tc #bool g (fun _ -> false) = { prf = CFalse }
instance rq_CTrue  (#g:typ_env) : rq_tc #bool g (fun _ -> true)  = { prf = CTrue }

instance rq_CIf
        (#g:typ_env) (#a:Type)
        (cond: fs_oexp g bool) (b1: fs_oexp g a) (b2: fs_oexp g a)
        (ic: rq_tc #bool g cond) (ib1: rq_tc g b1) (ib2: rq_tc g b2)
        : rq_tc g (fun fsG -> if cond fsG then b1 fsG else b2 fsG) =
        { prf = CIf ic.prf ib1.prf ib2.prf }

instance rq_CVar0 (#g:typ_env) (#a:Type) : rq_tc (extend a g) (fun fsG -> hd fsG) =
        { prf = CVar0 }

instance rq_CVar1 (#g:typ_env) (#a:Type) (#b:Type) :
        rq_tc (extend b (extend a g)) (fun fsG -> hd (tail fsG)) =
        { prf = CVar1 }

instance rq_CApp
        (#g:typ_env) (#a:Type) (#b:Type)
        (#f: fs_oexp g (a -> b)) (#x: fs_oexp g a)
        (ifn: rq_tc g f) (ix: rq_tc g x)
        : rq_tc g (fun fsG -> (f fsG) (x fsG)) =
        { prf = CApp ifn.prf ix.prf }

instance rq_CAbs
        (#g:typ_env) (#a:Type) (#b:Type)
        (#f: fs_oexp g (a -> b))
        (ibody: rq_tc (extend a g) (fun fsG -> (f (tail fsG)) (hd fsG)))
        : rq_tc g f =
        { prf = CAbs ibody.prf }

let somep' : rq_tc empty (fun _ -> if true then false else true) = solve

let test_var0 : rq_tc #(bool -> bool) empty (fun _ -> (fun x -> x)) = solve

#set-options "--debug Tac"
// Cezar: automation fails when applying a deBrujin variable
let _ : rq_tc #((bool -> bool) -> bool ) empty (fun _ p  -> p false) =
  solve // TODO: why does this fail?
 // rq_CAbs (rq_CApp rq_CVar0 rq_CFalse)

let cnp' : rq_tc empty (fun _ -> neg_pred) = solve
