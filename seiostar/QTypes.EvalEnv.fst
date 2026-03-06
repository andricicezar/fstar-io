module QTypes.EvalEnv

module FE = FStar.FunctionalExtensionality

open LambdaIO
open IOStar

include QTypes.TypEnv

(** Evaluation Environment for IOStar: variable -> F* values **)
type eval_env g =
  FE.restricted_t (x:var{Some? (g x)}) (fun x -> get_Type (Some?.v (g x)))
let empty_eval : eval_env empty =
  FE.on_dom
    (x:var{Some? (empty x)})
    #(fun x -> get_Type (Some?.v (empty x)))
    (fun _ -> assert False)
val hd : #t:qType -> #g:_ -> eval_env (extend t g) -> get_Type t
let hd #g fsG = fsG 0
val stack : #g:_ -> fsG:eval_env g -> #t:qType -> get_Type t -> eval_env (extend t g)
let stack #g fsG #t fs_v =
  FE.on_dom
    (x:var{Some? ((extend t g) x)})
    #(fun x -> get_Type (Some?.v ((extend t g) x)))
    (fun y ->
      if y = 0 then fs_v else fsG (y-1))
val tail : #t:qType -> #g:_ -> eval_env (extend t g) -> eval_env g
let tail #t #g fsG =
  FE.on_dom
    (x:var{Some? (g x)})
    #(fun x -> get_Type (Some?.v (g x)))
    (fun y -> fsG (y+1))
val index : #g:_ -> eval_env g -> x:LambdaIO.var{Some? (g x)} -> get_Type (Some?.v (g x))
let index #g fsG x = fsG x

val lem_hd_stack #t #g (fsG:eval_env g) (v:get_Type t)
  : Lemma (
 // (fs_hd fsG == fs_hd (fs_tail (fs_stack fsG v))) /\
   hd (stack fsG v) == v)
  [SMTPat (hd (stack fsG v))]
let lem_hd_stack fsG v = ()

val lem_stack_index #g (fsG:eval_env g) #t (v:get_Type t) : Lemma (
  (forall (x:var). Some? (g x) ==>  index fsG x == index (stack fsG v) (x+1)) /\
  index (stack fsG v) 0 == v)
  [SMTPat (stack fsG v)]
let lem_stack_index fsG v = ()

val lem_index_tail #g #t (fsG:eval_env (extend t g)) : Lemma (
  (forall (x:var). Some? (g x) ==>  index fsG (x+1) == index (tail fsG) x))
  [SMTPat (tail fsG)]
let lem_index_tail fsG = ()

val lem_tail_stack_inverse #g (fsG:eval_env g) #t (x:get_Type t)
  : Lemma (tail (stack fsG x) == fsG)
  [SMTPat (tail (stack fsG x))]
let lem_tail_stack_inverse #g fsG #t v =
  let fsG' : eval_env g = tail (stack fsG v) in
  assert (forall x. fsG' x == fsG x);
  assert (FE.feq fsG' fsG);
  FE.extensionality (x:var{Some? (g x)}) (fun x -> get_Type (Some?.v (g x))) fsG' fsG;
  assert (fsG' == fsG)

val lem_index_0_hd #g #t (fsG:eval_env (extend t g))
  : Lemma (index fsG 0 == hd fsG)
let lem_index_0_hd fsG = ()
