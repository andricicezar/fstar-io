module Compiler

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Calc
open FStar.List.Tot

open STLC

(** Typing environment **)
type typsr = Type0
let get_Type (t:typsr) = t
type env = var -> option typsr
let empty : env = fun _ -> None

(* we only need extend at 0 *)
let extend (t:typsr) (g:env)
  : env
  = fun y -> if y = 0 then Some t
          else g (y-1)

(** F* evaluation environment **)
assume val fs_env (g:env) : Type u#0
assume val fs_empty : fs_env empty
assume val get_v : #g:env -> fs_env g -> x:var{Some? (g x)} -> get_Type (Some?.v (g x))
assume val fs_extend : #g:env -> fs_s:fs_env g -> #t:typsr -> get_Type t -> fs_env (extend t g)
assume val fs_shrink : #t:typsr -> #g:env -> fs_env (extend t g) -> fs_env g

assume val lem_fs_extend #g (fs_s:fs_env g) #t (v:get_Type t) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fs_s x == get_v (fs_extend fs_s v) (x+1)) /\
  get_v (fs_extend fs_s v) 0 == v)
  [SMTPat (fs_extend fs_s v)]

assume val lem_fs_shrink #g #t (fs_s:fs_env (extend t g)) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fs_s (x+1) == get_v (fs_shrink fs_s) x))
  [SMTPat (fs_shrink fs_s)]

assume val shrink_extend_inverse #g (fs_s:fs_env g) #t (x:get_Type t) : Lemma (fs_shrink (fs_extend fs_s x) == fs_s)
  [SMTPat (fs_shrink (fs_extend fs_s x))]

(** Definition of open FStar expressions **)
type fs_oexp (g:env) (a:Type) =
  fs_s:fs_env g -> a

(** Compiling open expressions **)
class compile_exp (#a:Type0) (g:env) (fs_e:fs_oexp g a) = {
  [@@@no_method] e : exp; (** expression is closed by g *)
}

(** Just a helper typeclass **)
unfold let compile_closed (#a:Type0) (s:a) =
  compile_exp #a empty (fun _ -> s)

instance unit_elim #g : compile_exp g (fun _ -> ()) = {
  e = EUnit;
}

instance true_elim #g : compile_exp g (fun _ -> true) = {
  e = ETrue;
}

instance false_elim #g : compile_exp g (fun _ -> false) = {
  e = EFalse;
}

let test_unit : compile_closed () = solve
let test_true : compile_closed true = solve
let test_false : compile_closed false = solve

(** get_v' works better with typeclass resolution than get_v **)
[@"opaque_to_smt"] (** not sure if it is the right pragma to prevent F* unfolding get_v' during type class resolution **)
val get_v' : #g:env -> fs_env g -> x:var{Some? (g x)} -> a:Type{a == get_Type (Some?.v (g x))} -> a
let get_v' #g fs_s i a =
  get_v #g fs_s i

instance var_elim
  (#g:env)
  (a:Type)
  (x:var{Some? (g x) /\ a == Some?.v (g x)})
  : compile_exp #a g (fun fs_s -> get_v' fs_s x a) = {
    e = EVar x;
}

let test1_var : compile_exp (extend unit empty) (fun fs_s -> get_v' fs_s 0 unit) = solve

instance var_elim_shrink1 (** CA: how to make this general? **)
  (g':env)
  (a:Type)
  (t:typsr)
  (g:env{g' == extend t g})
  (x:var{Some? (g x) /\ a == Some?.v (g x)})
  {| ce:compile_exp g' (fun fs_s -> get_v' #g' fs_s (x+1) a) |} (** this is not necessary. I am hoping that it can be modified to be recursive **)
  : compile_exp g' (fun (fs_s:fs_env g') -> get_v' #g (fs_shrink #t #g fs_s) x a) = {
    e = ce.e;
  }

instance var_elim_shrink2 (** CA: how to make this general? **)
  (g':env)
  (a:Type)
  (t1 t2:typsr)
  (g:env{g' == extend t1 (extend t2 g)})
  (x:var{Some? (g x) /\ a == Some?.v (g x)})
  {| ce:compile_exp g' (fun fs_s -> get_v' #g' fs_s (x+2) a) |} (** this is not necessary. I am hoping that it can be modified to be recursive **)
  : compile_exp g' (fun (fs_s:fs_env g') -> get_v' #g (fs_shrink #t2 (fs_shrink #t1 fs_s)) x a) = {
    e = ce.e;
  }

let test2_var : compile_exp (extend unit (extend unit empty)) (fun fs_s -> get_v' (fs_shrink fs_s) 0 unit) =
  solve

let test3_var : compile_exp (extend unit (extend unit (extend unit empty))) (fun fs_s -> get_v' (fs_shrink (fs_shrink fs_s)) 0 unit) =
  solve

instance lambda_elim
  #g
  (a:Type)
  (b:Type)
  (f:fs_oexp g (a -> b))
  {| cf: compile_exp #b (extend a g) (fun fs_s -> f (fs_shrink #a fs_s) (get_v' fs_s 0 a)) |}
  : compile_exp g f = {
  e = ELam cf.e;
}

let test1_exp : compile_closed (fun (x:unit) -> ()) = solve
let _ = assert (test1_exp.e == ELam (EUnit))

let test2_exp : compile_closed #(unit -> unit) (fun x -> x) = solve
let _ = assert (test2_exp.e == ELam (EVar 0))

let test3_exp : compile_closed #(unit -> unit -> unit) (fun x y -> x) = solve
let _ = assert (test3_exp.e == ELam (ELam (EVar 1)))

let test3_exp' : compile_closed #(unit -> unit -> unit) (fun x y -> y) = solve
let _ = assert (test3_exp'.e == ELam (ELam (EVar 0)))

let test4_exp : compile_closed #(unit -> unit -> unit -> unit) (fun x y z -> x) =
  solve
let _ = assert (test4_exp.e == ELam (ELam (ELam (EVar 2))))

let test4_exp' : compile_closed #(unit -> unit -> unit -> unit) (fun x y z -> y) = solve
let _ = assert (test4_exp'.e == ELam (ELam (ELam (EVar 1))))

let test4_exp'' : compile_closed #(unit -> unit -> unit -> unit) (fun x y z -> z) = solve
let _ = assert (test4_exp''.e == ELam (ELam (ELam (EVar 0))))


instance app_elim
  #g
  (a:Type)
  (b:Type)
  (f:fs_oexp g (a -> b)) {| cf: compile_exp g f |}
  (x:fs_oexp g a)       {| cx: compile_exp g x |}
  : compile_exp g (fun fs_s -> (f fs_s) (x fs_s)) = {
  e = EApp cf.e cx.e;
}

(** TODO: why does this not work automatically **)
let test1_hoc : compile_closed
  #((bool -> bool) -> bool)
  (fun f -> f false) =
  lambda_elim _ _ _ #(app_elim _ _ (fun fs_s -> get_v' fs_s 0 (bool -> bool)) _)

instance if_elim
  #g
  (co:fs_oexp g bool)  {| cco: compile_exp g co |}

  (a:Type)
  (th:fs_oexp g a)     {| cth: compile_exp g th |}
  (el:fs_oexp g a)     {| cel: compile_exp g el |}
  : compile_exp #_ g (fun fs_s -> if co fs_s then th fs_s else el fs_s) = {
  e = EIf cco.e cth.e cel.e;
}

let test1_if : compile_closed #(bool -> bool -> bool) (fun x y -> if x then false else y) = solve
let _ = assert (test1_if.e == ELam (ELam (EIf (EVar 1) EFalse (EVar 0))))

let myt = true

let test2_if : compile_closed #bool (if myt then false else true) = solve
let _ = assert (test2_if.e == EIf ETrue EFalse ETrue)

instance pair_elim
  #g
  (a:Type)
  (b:Type)
  (l:fs_oexp g a)     {| cl: compile_exp g l |}
  (r:fs_oexp g b)     {| cr: compile_exp g r |}
  : compile_exp #(a & b) g (fun fs_s -> (l fs_s, r fs_s)) = {
  e = EPair cl.e cr.e;
}

let test1_pair : compile_closed #(bool -> bool -> bool & bool) (fun x y-> (x,y)) = solve
let _ = assert (test1_pair.e == ELam (ELam (EPair (EVar 1) (EVar 0))))

let test2_pair : compile_closed #((bool -> bool) & (bool -> bool -> bool)) ((fun x -> x), (fun y x -> y)) = solve
let _ = assert (test2_pair.e == EPair (ELam (EVar 0)) (ELam (ELam (EVar 1))))

let test3_pair : compile_closed #((bool -> bool) & (bool -> bool)) ((fun x -> x), (fun x -> if x then false else true)) = solve

instance fst_elim
  #g
  (a:Type)
  (b:Type)
  : compile_exp #(a & b -> a) g (fun _ -> fst #a #b) = {
  e = ELam (EFst (EVar 0));
}

val test4_pair : compile_closed (fst (true, ()))
let test4_pair = solve

val test5_pair : compile_closed #((bool & bool) -> bool) (fun p -> fst p)
let test5_pair = solve

val test4_pair_fst' : compile_closed #(bool & unit -> bool) (fst #bool #unit)
let test4_pair_fst' = solve

val test4_pair' : compile_closed #bool (fst (true, ()))
let test4_pair' = solve

instance snd_elim
  #g
  (a:Type)
  (b:Type)
  : compile_exp #(a & b -> b) g (fun _ -> snd #a #b) = {
  e = ELam (ESnd (EVar 0));
}

val test6_pair : compile_closed #unit (snd (true, ()))
let test6_pair = solve

val test7_pair : compile_closed #((bool & unit) -> unit) (fun p -> snd p)
let test7_pair = solve
