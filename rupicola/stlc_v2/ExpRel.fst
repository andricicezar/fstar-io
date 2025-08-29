module ExpRel

open FStar.FunctionalExtensionality

type fs_env g =
  restricted_t (x:var{Some? (g x)}) (fun x -> get_Type (Some?.v (g x)))

let fs_empty : fs_env empty =
  on_dom
    (x:var{Some? (empty x)})
    #(fun x -> get_Type (Some?.v (empty x)))
    (fun _ -> assert False)

let get_v #g fs_s x = fs_s x

let fs_extend #g fs_s #t fs_v =
  on_dom
    (x:var{Some? ((extend t g) x)})
    #(fun x -> get_Type (Some?.v ((extend t g) x)))
    (fun y ->
      if y = 0 then fs_v else fs_s (y-1))

let fs_shrink #t #g fs_s =
  on_dom
    (x:var{Some? (g x)})
    #(fun x -> get_Type (Some?.v (g x)))
    (fun y -> fs_s (y+1))

let lem_fs_extend fs_s v = ()
let lem_fs_shrink fs_s = ()

let shrink_extend_inverse #g fs_s #t v =
  let fs_s' : fs_env g = fs_shrink (fs_extend fs_s v) in
  assert (forall x. fs_s' x == fs_s x);
  assert (feq fs_s' fs_s);
  extensionality (x:var{Some? (g x)}) (fun x -> get_Type (Some?.v (g x))) fs_s' fs_s;
  assert (fs_s' == fs_s)
