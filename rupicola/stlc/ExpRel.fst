module ExpRel

open FStar.FunctionalExtensionality

type fs_env g =
  restricted_t (x:var{Some? (g x)}) (fun x -> get_Type (Some?.v (g x)))

let fs_empty : fs_env empty =
  on_dom
    (x:var{Some? (empty x)})
    #(fun x -> get_Type (Some?.v (empty x)))
    (fun _ -> assert False)

let fs_stack #g fsG #t fs_v =
  on_dom
    (x:var{Some? ((extend t g) x)})
    #(fun x -> get_Type (Some?.v ((extend t g) x)))
    (fun y ->
      if y = 0 then fs_v else fsG (y-1))

let fs_hd #g fsG = fsG 0

let fs_tail #t #g fsG =
  on_dom
    (x:var{Some? (g x)})
    #(fun x -> get_Type (Some?.v (g x)))
    (fun y -> fsG (y+1))

let get_v #g fsG x = fsG x

let lem_fs_stack_hd fsG v = ()
let lem_fs_stack_get_v fsG v = ()
let lem_fs_tail fsG = ()

let tail_stack_inverse #g fsG #t v =
  let fsG' : fs_env g = fs_tail (fs_stack fsG v) in
  assert (forall x. fsG' x == fsG x);
  assert (feq fsG' fsG);
  extensionality (x:var{Some? (g x)}) (fun x -> get_Type (Some?.v (g x))) fsG' fsG;
  assert (fsG' == fsG)
