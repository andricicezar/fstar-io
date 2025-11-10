module QExp

open FStar.Tactics
open FStar.Universe
open Free

noeq
type uType : Type u#2 =
| U0 : Type u#0 -> uType
| U1 : Type u#1 -> uType

let (^->) (a b:uType) : uType =
  match a, b with
  | U0 a, U0 b -> U0 (a -> b)
  | U0 a, U1 b -> U1 (a -> b)
  | U1 a, U0 b -> U1 (a -> b)
  | U1 a, U1 b -> U1 (a -> b)

let get_Type (a:uType) : Type u#1 =
  match a with
  | U0 a -> ((raise_t unit) -> a)
  | U1 a -> ((raise_t unit) -> a)

(** typ_env is a typing environment: variables to F* types **)
type typ_env = nat -> option uType
val empty : typ_env
val extend : uType -> typ_env -> typ_env

(** eval_env is an evaluation environment: variables to F* values **)
val eval_env (g:typ_env) : Type
val hd : #t:uType -> #g:_ -> eval_env (extend t g) -> get_Type t
val tail : #t:uType -> #g:_ ->  eval_env (extend t g) -> eval_env g

type fs_oexp (g:typ_env) (a:uType) =
  eval_env g -> get_Type a

#push-options "--print_implicits --print_universes"

(**
val myf : (#g:typ_env) -> #a:uType -> fs_oexp g a -> eval_env g -> (match a with | U0 b -> b | U1 b -> b)

let myf (#g:typ_env) (#a:uType) (s:fs_oexp g a) (fsG:eval_env g) =
  match a with
  | U0 b -> (let s' : eval_env g -> b = s in s' fsG)
  | U1 b -> (let s' : eval_env g -> b = s in s' fsG)
**)

let fapp (a b:uType) (f:get_Type (a ^-> b)) (x:get_Type a) : get_Type b =
  match a ^-> b, a, b with
  | U0 ab, U0 a, U0 b -> begin
    let f : get_Type (U0 ab) = f in
    let f : raise_t unit -> a -> b = f in
    let x : raise_t unit -> _ = x in
    (fun tt -> (f tt) (x tt))
  end
  | U1 ab, U0 a, U1 b
  | U1 ab, U1 a, U0 b
  | U1 ab, U1 a, U1 b -> begin
    let f : get_Type (U1 ab) = f in
    let f : raise_t unit -> a -> b = f in
    let x : raise_t unit -> _ = x in
    (fun tt -> (f tt) (x tt))
  end

noeq
type exp_quotation : #a:uType -> g:typ_env -> fs_oexp g a -> Type =
| Qtt : #g:typ_env -> exp_quotation #(U0 unit) g (fun _ _ -> ())
| QFalse : #g:typ_env -> exp_quotation #(U0 bool) g (fun _ _ -> false)

| QTrue : #g:typ_env -> exp_quotation #(U0 bool) g (fun _ _ -> true)

| QIf : #g:typ_env ->
        #a:uType ->
        #cond:fs_oexp g (U0 bool) -> #b1:fs_oexp g a -> #b2:fs_oexp g a ->
        exp_quotation g cond -> exp_quotation g b1 -> exp_quotation g b2 ->
        exp_quotation #a g (fun fsG -> if cond fsG (raise_val ()) then b1 fsG else b2 fsG)

| QVar0  : #g:typ_env -> #a:uType -> exp_quotation (extend a g) (fun fsG -> hd fsG)

| QVar1  : #g:typ_env -> #a:uType -> #b:uType -> exp_quotation (extend b (extend a g)) (fun fsG -> hd (tail fsG))

(** ... we need a case for each deBrujin variable **)
| QApp : #g:_ -> #a:uType -> #b:uType ->
        #f:fs_oexp g (a ^-> b) -> #x:fs_oexp g a ->
        exp_quotation g f -> exp_quotation g x ->
        exp_quotation #b g (fun fsG -> fapp a b (f fsG) (x fsG))

| QLambda : #g:_ -> #a:uType -> #b:uType ->
        #f:fs_oexp g (a ^-> b) ->
        exp_quotation #b (extend a g) (fun fsG -> fapp a b (f (tail fsG)) (hd fsG)) ->
        exp_quotation g f

| QFreeReturn :
        #g:typ_env ->
        #a:Type0 ->
        exp_quotation #(U1 (a -> free a)) g (fun _ _ -> free_return #a)

// | QFreeBind :
//         #g:typ_env ->
//         #a:Type0 ->
//         #b:Type0 ->
//         exp_quotation #(U1 (free a -> (a -> free b) -> free b)) g (fun _ _ -> free_bind #a #b)

// | QFreeRead :
//         #g:typ_env ->
//         exp_quotation #(U1 (unit -> free bool)) g (fun _ _ -> free_read)

// | QFreeWrite :
//         #g:typ_env ->
//         exp_quotation #(U1 (bool -> free unit)) g (fun _ _ -> free_write)

open ExamplesIO

type closed_exp_quotation0 (a:Type u#0) (x:a) =
  exp_quotation #(U0 a) empty (fun _ _ -> x)

type closed_exp_quotation1 (a:Type u#1) (x:a) =
  exp_quotation #(U1 a) empty (fun _ _ -> x)

#push-options "--no_smt"

let test_u_return ()
  : Tot (closed_exp_quotation1 _ u_return)
  by (norm [delta_only [`%u_return; `%fapp; `%op_Hat_Subtraction_Greater]; iota])
  = QApp QFreeReturn QTrue

let test_papply_free_return ()
  : Tot (closed_exp_quotation1 _ papply_free_return)
  by (norm [delta_only [`%papply_free_return; `%fapp; `%op_Hat_Subtraction_Greater]])
  = QFreeReturn

// TODO: why doesn't this work?
let test_apply_free_return ()
  : Tot (closed_exp_quotation1 _ apply_free_return)
  by (norm [delta_only [`%apply_free_return; `%fapp; `%op_Hat_Subtraction_Greater]];
    dump "H")
  = QLambda #_ #(U0 bool) #(U1 (free bool)) (QApp QFreeReturn QVar0)
