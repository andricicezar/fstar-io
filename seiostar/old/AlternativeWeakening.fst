module AlternativeWeakening

(*
type finite_typ_env (n:nat) = g:typ_env{forall (x:var{x > n}). None? (g x)}

let comp_typ_env #n (g1:typ_env) (g2:finite_typ_env n) : (g:typ_env{(forall (x:var{x >= n}). (g x) == (g1 (x-n))) /\ (forall (x:var{x < n}). (g x) == (g2 x))}) = admit ()

val tail' : #n:nat -> #t:qType -> #g1:typ_env -> #g2:finite_typ_env n -> eval_env (comp_typ_env #n (extend t g1) g2) -> eval_env (comp_typ_env g1 g2)
let tail' #n #t #g1 #g2 fsG =
  FE.on_dom 
    (x:var{Some? ((comp_typ_env g1 g2) x)})
    #(fun x -> get_Type (Some?.v ((comp_typ_env g1 g2) x)))
    (fun y -> if y < n then (fsG y) else (fsG (y+1)))

val lem_index_tail' #n #g1 (#g2:finite_typ_env n) #t (fsG:eval_env (comp_typ_env (extend t g1) g2)) : Lemma (
  (forall (x:var{x>=n}). Some? ((comp_typ_env g1 g2) x) ==> index fsG (x+1) == index (tail' fsG) x) /\ forall (x:var{x<n}). Some? ((comp_typ_env g1 g2) x) ==> index fsG x == index (tail' fsG) x)
  [SMTPat (tail' fsG)]
let lem_index_tail' fsG = ()

let sub_inc' (n:nat)
  : sub true
  = fun y -> if y < n then EVar y else EVar (y+1)

let sub_inc_many (n:nat)
  : sub true
  = fun y -> EVar (y+n)
*)
