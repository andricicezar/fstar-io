module Effect.Axioms

open FStar.Universe

type axiom (w:Type u#a -> Type u#b) =
  argT:Type u#c & res:(argT -> Type u#a) & (x:argT -> w (res x))

let require_axiom : axiom pure_wp =
  let theta (req:Type0) : pure_wp (raise_t unit) =
    reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
    (fun p -> req ==> p (raise_val ())) in
  (| Type0, (fun _ -> raise_t unit), theta |)

let assume_axiom : axiom pure_wp =
  let theta (assumption:Type0) : pure_wp (raise_t unit) =
    reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
    (fun p -> assumption /\ p (raise_val ())) in
  (| Type0, (fun _ -> raise_t unit), theta |)

let axioms w = string -> option (axiom w)

noeq
type myfree (w:Type u#a -> Type u#b) (a:Type u#a) (m:axioms u#a u#b u#c w) : Type u#(max a c) =
| Return : a -> myfree w a m
| Axiom : op:string{Some? (m op)} -> arg:(Mkdtuple3?._1 (Some?.v (m op))) -> ((Mkdtuple3?._2 (Some?.v (m op))) arg -> myfree w a m) -> myfree w a m

let pure_precond_assume (a:Type u#a) : Type u#(max 1 a) = myfree pure_wp a (fun nm -> if nm = "Require" then Some require_axiom else (if nm = "Assume" then Some assume_axiom else None))
