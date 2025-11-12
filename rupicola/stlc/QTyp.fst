module QTyp

open FStar.FunctionalExtensionality

type eval_env g =
  restricted_t (x:var{Some? (g x)}) (fun x -> get_Type (Some?.v (g x)))

let empty_eval : eval_env empty =
  on_dom
    (x:var{Some? (empty x)})
    #(fun x -> get_Type (Some?.v (empty x)))
    (fun _ -> assert False)

let hd #g fsG = fsG 0

let stack #g fsG #t fs_v =
  on_dom
    (x:var{Some? ((extend t g) x)})
    #(fun x -> get_Type (Some?.v ((extend t g) x)))
    (fun y ->
      if y = 0 then fs_v else fsG (y-1))

let tail #t #g fsG =
  on_dom
    (x:var{Some? (g x)})
    #(fun x -> get_Type (Some?.v (g x)))
    (fun y -> fsG (y+1))

let index #g fsG x = fsG x

let lem_stack_hd fsG v = ()
let lem_stack_index fsG v = ()
let lem_index_tail fsG = ()

let tail_stack_inverse #g fsG #t v =
  let fsG' : eval_env g = tail (stack fsG v) in
  assert (forall x. fsG' x == fsG x);
  assert (feq fsG' fsG);
  extensionality (x:var{Some? (g x)}) (fun x -> get_Type (Some?.v (g x))) fsG' fsG;
  assert (fsG' == fsG)

let index_0_hd fsG = ()
