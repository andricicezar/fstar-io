module Compilable

open FStar.Tactics

open STLC
open Compiler

type fs_oexp (g:env) (a:Type) =
  fsG:fs_env g -> a

noeq
type compilable : #a:Type -> g:env -> fs_oexp g a -> Type =
| CUnit       : #g:env -> compilable g (fun _ -> ())
| CTrue       : #g:env -> compilable g (fun _ -> true)
| CFalse      : #g:env -> compilable g (fun _ -> false)
(** The following three rules for variables should be generalized. What would be an elegant solution? **)
| CVar        : #g:env ->
                #a:Type ->
                #x:var{Some? (g x) /\ a == Some?.v (g x)} ->
                compilable #a g (fun fsG -> get_v fsG x)
| CVarShrink1 : #g:env ->
                #a:Type ->
                #b:Type ->
                #x:var{Some? (g x) /\ a == Some?.v (g x)} ->
                compilable #a (extend b g) (fun fsG -> get_v fsG (x+1)) ->
                compilable #a (extend b g) (fun fsG -> get_v (fs_shrink #b fsG) x)
| CVarShrink2 : #g:env ->
                #a:Type ->
                #b:Type ->
                #c:Type ->
                #x:var{Some? (g x) /\ a == Some?.v (g x)} ->
                compilable #a (extend c (extend b g)) (fun fsG -> get_v fsG (x+2)) ->
                compilable #a (extend c (extend b g)) (fun fsG -> get_v (fs_shrink #b (fs_shrink #c fsG)) x)
| CLambda     : #g :env ->
                #a :Type ->
                #b :Type ->
                #f :fs_oexp g (a -> b) ->
                cf:compilable #b (extend a g) (fun fsG -> f (fs_shrink fsG) (get_v fsG 0)) ->
                compilable g f
| CApp        : #g :env ->
                #a :Type ->
                #b :Type ->
                #f :fs_oexp g (a -> b) ->
                cf:compilable g f ->
                #x :fs_oexp g a ->
                cx:compilable g x ->
                compilable g (fun fsG -> (f fsG) (x fsG))
| CIf         : #g :env ->
                #a :Type ->
                #c :fs_oexp g bool ->
                cc:compilable g c ->
                #t :fs_oexp g a ->
                ct:compilable g t ->
                #e :fs_oexp g a ->
                ce:compilable g e ->
                compilable g (fun fsG -> if c fsG then t fsG else e fsG)

unfold let compilable_closed #a (x:a) = compilable empty (fun _ -> x)

let test2_var
  : compilable (extend unit (extend unit empty)) (fun fsG -> get_v (fs_shrink fsG) 0)
  = CVarShrink1 CVar

let test4_exp'
  : compilable_closed #(unit -> unit -> unit -> unit) (fun x y z -> y)
  = CLambda (CLambda (CLambda (CVarShrink1 (CVar))))

let test1_hoc
  : compilable_closed #((bool -> bool) -> bool) (fun f -> f false)
  = CLambda (CApp CVar CFalse)

let test2_if
  : compilable_closed #(bool -> bool) (fun x -> if x then false else true)
  = CLambda (CIf CVar CFalse CTrue)

let test1_if
  : compilable_closed #(bool -> bool -> bool) (fun x y -> if x then false else y)
  = CLambda (CLambda (CIf (CVarShrink1 CVar) CFalse CVar))

let test1_comp_ref
  : compilable_closed #(x:bool{x == true} -> x:bool{x == true}) (fun x -> x)
  = CLambda CVar

[@expect_failure]
let test_pm2
  : compilable_closed
      #(bool -> y:bool{y == false})
      (fun x -> if x then if x then false else true else false)
  = CLambda (CIf CVar (CIf CVar CFalse CTrue) CFalse)

[@expect_failure]
let test1_erase_ref
  : compilable_closed #(x:bool{x == true} -> bool) (fun x -> x)
  = CLambda CVar

[@expect_failure]
let test1_add_ref
  : compilable_closed #(bool -> (x:bool{x == true})) (fun x -> true)
  = CLambda CTrue

#set-options "--print_implicits"

noeq
type compilable_ref : #a:Type -> g:env -> fs_oexp g a -> Type =
| CRRefErase  : #g:env ->
                #a:Type ->
                p:(a -> Type0) ->
                #v:fs_oexp g (x:a{p x}) ->
                compilable_ref g v ->
                compilable_ref #a g (fun fsG -> v fsG)
| CRUnit      : #g:env -> compilable_ref g (fun _ -> ())
| CRTrue      : #g:env -> compilable_ref g (fun _ -> true)
| CRFalse     : #g:env -> compilable_ref g (fun _ -> false)
(** The following three rules for variables should be generalized. What would be an elegant solution? **)
| CRVar       : #g:env ->
                #a:Type ->
                #x:var{Some? (g x) /\ a == Some?.v (g x)} ->
                compilable_ref #a g (fun fsG -> get_v fsG x)
| CRVarShrink1: #g:env ->
                #a:Type ->
                #b:Type ->
                #x:var{Some? (g x) /\ a == Some?.v (g x)} ->
                compilable_ref #a (extend b g) (fun fsG -> get_v fsG (x+1)) ->
                compilable_ref #a (extend b g) (fun fsG -> get_v (fs_shrink #b fsG) x)
| CRVarShrink2: #g:env ->
                #a:Type ->
                #b:Type ->
                #c:Type ->
                #x:var{Some? (g x) /\ a == Some?.v (g x)} ->
                compilable_ref #a (extend c (extend b g)) (fun fsG -> get_v fsG (x+2)) ->
                compilable_ref #a (extend c (extend b g)) (fun fsG -> get_v (fs_shrink #b (fs_shrink #c fsG)) x)
| CRLambda    : #g :env ->
                #a :Type ->
                #b :Type ->
                #f :fs_oexp g (a -> b) ->
                cf:compilable_ref #b (extend a g) (fun fsG -> f (fs_shrink fsG) (get_v fsG 0)) ->
                compilable_ref g f
| CRApp       : #g :env ->
                #a :Type ->
                #b :Type ->
                #f :fs_oexp g (a -> b) ->
                cf:compilable_ref g f ->
                #x :fs_oexp g a ->
                cx:compilable_ref g x ->
                compilable_ref g (fun fsG -> (f fsG) (x fsG))
| CRIf        : #g :env ->
                #a :Type ->
                #c :fs_oexp g bool ->
                cc:compilable_ref g c ->
                #t :fs_oexp g a ->
                ct:compilable_ref g t ->
                #e :fs_oexp g a ->
                ce:compilable_ref g e ->
                compilable_ref g (fun fsG -> if c fsG then t fsG else e fsG)

unfold let compilable_ref_closed #a (x:a) = compilable_ref empty (fun _ -> x)

let test1_erase_ref
  : compilable_ref_closed #(x:bool{x == true} -> bool) (fun x -> x)
  = CRLambda (CRRefErase (fun x -> x == true) CRVar)
