module Compilable

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Calc
open FStar.List.Tot

open STLC
open Compiler

type fs_oexp (g:env) (a:Type) =
  fsG:fs_env g -> a (** this works better than using PURE **)

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
                #x :fs_oexp g a ->
                cx:compilable g x ->
                #f :fs_oexp g (a -> b) ->
                cf:compilable g f ->
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
  = CVarShrink1 (CVar)

let test4_exp'
  : compilable_closed #(unit -> unit -> unit -> unit) (fun x y z -> y)
  = CLambda (CLambda (CLambda (CVarShrink1 (CVar))))

let test1_hoc
  : compilable_closed #((bool -> bool) -> bool) (fun f -> f false)
  = CLambda (CApp (CFalse) (CVar))

let test2_if
  : compilable_closed #(bool -> bool) (fun x -> if x then false else true)
  = CLambda (CIf (CVar) (CFalse) (CTrue))

let test1_if
  : compilable_closed #(bool -> bool -> bool) (fun x y -> if x then false else y)
  = CLambda (CLambda (CIf (CVarShrink1 (CVar)) (CFalse) (CVar)))
