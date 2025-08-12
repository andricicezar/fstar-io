module EquivRel

open FStar.FunctionalExtensionality

type fs_env #g g_card =
  restricted_t (x:var{x < g_card}) (fun x -> elab_typ (Some?.v (g x)))

let fs_empty : fs_env #empty 0 =
  on_dom
    (x:var{x < 0})
    #(fun x -> elab_typ (Some?.v (empty x)))
    (fun _ -> assert False)

let get_v #g #g_card fs_s i =
  fs_s (fs_to_var g_card i)

let fs_extend #g #g_card fs_s #t fs_v =
  on_dom
    (x:var{x < g_card+1})
    #(fun x -> elab_typ (Some?.v ((extend t g) x)))
    (fun y ->
      if y = 0 then fs_v else fs_s (y-1))

let fs_shrink #t #g #g_card fs_s =
  on_dom
    (x:var{x < g_card})
    #(fun x -> elab_typ (Some?.v (g x)))
    (fun y -> fs_s (y+1))

let lem_fs_extend fs_s v = ()
let lem_fs_shrink fs_s = ()

let shrink_extend_inverse #g #g_card fs_s #t v =
  let fs_s' : fs_env g_card = fs_shrink (fs_extend fs_s v) in
  assert (forall x. fs_s' x == fs_s x);
  assert (feq fs_s' fs_s);
  extensionality (x:var{x < g_card}) (fun x -> elab_typ (Some?.v (g x))) fs_s' fs_s;
  assert (fs_s' == fs_s)
