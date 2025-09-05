module Compiler

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Calc
open FStar.List.Tot

open STLC

(** We're stuck at defining a compiler that is able
    to compile the following programs that make use of false_elim.
**)

let test_false_elim0
  : bool -> bool
  = fun x -> if x then if x then true else false_elim () else true

let test_false_elim1
  : x:unit{False} -> Tot bool
  = fun x -> false_elim ()

let test_false_elim2
  : f:(unit -> x:bool{x == true}) -> Tot bool
  = fun f -> if f () then true else false_elim ()

(** What other examples should we add to the list? **)

(** Helpers to deal with Monotonicity of Pure **)
module M = FStar.Monotonic.Pure

let intro_pure_wp_monotonicity (#a:Type) (wp:pure_wp' a)
  : Lemma
      (requires M.is_monotonic wp)
      (ensures pure_wp_monotonic a wp)
    [SMTPat (pure_wp_monotonic a wp)]
  = M.intro_pure_wp_monotonicity wp

let pure_wp (a: Type) = wp:pure_wp' a{M.is_monotonic wp}

unfold
let pure_trivial #a : pure_wp a =
  fun p -> forall r. p r

unfold let (<=) #a (wp1 wp2:pure_wp a) = pure_stronger a wp1 wp2
unfold let ret #a x : pure_wp a = pure_return a x

(** Compiling types, helps with recursion of the other type class **)
class compile_typ (s:Type) = {  [@@@no_method] r : unit; }
instance compile_typ_unit : compile_typ unit = { r = () }
instance compile_typ_bool : compile_typ bool = { r = () }
instance compile_typ_arrow (s1:Type) (s2:Type) {| c1:compile_typ s1 |} {| c2:compile_typ s2 |} : compile_typ (s1 -> s2) = { r = () }
instance compile_typ_refinement (s1:Type) {| c1:compile_typ s1 |} (p:s1 -> Type0) : compile_typ (x:s1{p x}) = { r = (); }

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
assume val fs_extend : #g:env -> fsG:fs_env g -> #t:typsr -> get_Type t -> fs_env (extend t g)
assume val fs_shrink : #t:typsr -> #g:env -> fs_env (extend t g) -> fs_env g

assume val lem_fs_extend #g (fsG:fs_env g) #t (v:get_Type t) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fsG x == get_v (fs_extend fsG v) (x+1)) /\
  get_v (fs_extend fsG v) 0 == v)
  [SMTPat (fs_extend fsG v)]

assume val lem_fs_shrink #g #t (fsG:fs_env (extend t g)) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fsG (x+1) == get_v (fs_shrink fsG) x))
  [SMTPat (fs_shrink fsG)]

assume val shrink_extend_inverse #g (fsG:fs_env g) #t (x:get_Type t) : Lemma (fs_shrink (fs_extend fsG x) == fsG)
  [SMTPat (fs_shrink (fs_extend fsG x))]

type spec_env (g:env) (a:Type) =
  fsG:fs_env g -> pure_wp a

(** Definition of open FStar expressions **)
type fs_oexp (g:env) (a:Type) (wpG:spec_env g a) =
  fsG:fs_env g -> x:a{wpG fsG <= ret x} (** this works better than using PURE **)

(** Compiling open expressions **)
class compile_exp (#a:Type0) {| compile_typ a |} (g:env) (wpG:spec_env g a) (fs_e:fs_oexp g a wpG) = {
  [@@@no_method] e : exp; (** expression is closed by g *)
}

(** Just a helper typeclass **)
unfold let compile_closed (#a:Type0) {| compile_typ a |} (s:a) =
  compile_exp #a empty (fun _ -> pure_trivial) (fun _ -> s)

instance unit_elim
  #g
  (#wpG:spec_env g unit)
  (_:squash (forall fsG. wpG fsG <= ret ()))
  : compile_exp g wpG (fun _ -> ())
  = { e = EUnit; }

instance true_elim
  #g
  (#wpG:spec_env g bool)
  (_:squash (forall fsG. wpG fsG <= ret true))
  : compile_exp g wpG (fun _ -> true)
  = { e = ETrue; }

instance fals_elim
  #g
  (#wpG:spec_env g bool)
  (_:squash (forall fsG. wpG fsG <= ret false))
  : compile_exp g wpG (fun _ -> false)
  = { e = EFalse; }

let test_unit : compile_closed () = solve
let test_true : compile_closed true = solve
let test_false : compile_closed false = solve

(** get_v' works better with typeclass resolution than get_v **)
[@"opaque_to_smt"] (** not sure if it is the right pragma to prevent F* unfolding get_v' during type class resolution **)
val get_v' : #g:env -> fs_env g -> x:var{Some? (g x)} -> a:Type{a == get_Type (Some?.v (g x))} -> a
let get_v' #g fsG i a =
  get_v #g fsG i

instance var_elim
  (#g:env)
  (a:Type) {| compile_typ a |}
  (#wpG:spec_env g a)
  (x:var{Some? (g x) /\ a == Some?.v (g x)})
  (_:squash (forall fsG. wpG fsG <= ret (get_v' fsG x a)))
  : compile_exp #a g wpG (fun fsG -> get_v' fsG x a)
  = { e = EVar x; }

let test1_var
  : compile_exp (extend unit empty) (fun _ -> pure_trivial) (fun fsG -> get_v' fsG 0 unit)
  = solve

instance var_elim_shrink1 (** CA: how to make this general? **)
  (g':env)
  (a:Type) {| compile_typ a |}
  (#wpG:spec_env g' a)
  (t:typsr)
  (g:env{g' == extend t g})
  (x:var{Some? (g x) /\ a == Some?.v (g x)})
  (_:squash (forall fsG. wpG fsG <= ret (get_v' fsG (x+1) a)))
  {| ce:compile_exp g' wpG (fun fsG -> get_v' #g' fsG (x+1) a) |} (** this is not necessary. I am hoping that it can be modified to be recursive **)
  (_:squash (forall fsG. wpG fsG <= ret (get_v' #g (fs_shrink #t fsG) x a)))
  : compile_exp g' wpG (fun fsG -> get_v' #g (fs_shrink #t fsG) x a)
  = { e = ce.e; }

instance var_elim_shrink2 (** CA: how to make this general? **)
  (g':env)
  (a:Type) {| compile_typ a |}
  (#wpG:spec_env g' a)
  (t1 t2:typsr)
  (g:env{g' == extend t1 (extend t2 g)})
  (x:var{Some? (g x) /\ a == Some?.v (g x)})
  (_:squash (forall fsG. wpG fsG <= ret (get_v' fsG (x+2) a)))
  {| ce:compile_exp g' wpG (fun fsG -> get_v' #g' fsG (x+2) a) |} (** this is not necessary. I am hoping that it can be modified to be recursive **)
  (_:squash (forall fsG. wpG fsG <= ret (get_v' #g (fs_shrink #t2 (fs_shrink #t1 fsG)) x a)))
  : compile_exp g' wpG (fun fsG -> get_v' #g (fs_shrink #t2 (fs_shrink #t1 fsG)) x a) = {
    e = ce.e;
  }

let test2_var
  : compile_exp (extend unit (extend unit empty)) (fun _ -> pure_trivial) (fun fsG -> get_v' (fs_shrink fsG) 0 unit)
  = solve

let test3_var
  : compile_exp (extend unit (extend unit (extend unit empty))) (fun _ -> pure_trivial) (fun fsG -> get_v' (fs_shrink (fs_shrink fsG)) 0 unit)
  = solve

unfold
let lambda_body_wp
  #g
  (#a:Type)
  (#b:Type)
  (#wpG:spec_env g (a -> b))
  (f:fs_oexp g (a -> b) wpG)
  : spec_env (extend a g) b
  = fun fsG ->
    fun p -> wpG (fs_shrink fsG) (fun f' -> f (fs_shrink fsG) == f' /\ p (f (fs_shrink fsG) (get_v' fsG 0 a)))

instance lambda_elim
  #g
  (a:Type) {| compile_typ a |}
  (b:Type) {| compile_typ b |}
  (#wpG:spec_env g (a -> b))
  (f:fs_oexp g (a -> b) wpG)
  {| cf: compile_exp #b
           (extend a g)
           (lambda_body_wp f)
           (fun fsG -> f (fs_shrink fsG) (get_v' fsG 0 a)) |}
  (_:squash (forall fsG. wpG fsG <= ret (f fsG)))
  : compile_exp #(a -> b) g wpG f
  = { e = ELam cf.e; }

let test1_exp
  : compile_closed (fun (x:unit) -> ())
  = solve
let _ = assert (test1_exp.e == ELam (EUnit))

let test2_exp
  : compile_closed #(unit -> unit) (fun x -> x)
  = solve
let _ = assert (test2_exp.e == ELam (EVar 0))

#set-options "--timing"
let test3_exp // 450ms
  : compile_closed #(unit -> unit -> unit) (fun x y -> x)
  = solve

let _ = assert (test3_exp.e == ELam (ELam (EVar 1)))

let test3_exp'
  : compile_closed #(unit -> unit -> unit) (fun x y -> y)
  = solve
let _ = assert (test3_exp'.e == ELam (ELam (EVar 0)))

let test4_exp
  : compile_closed #(unit -> unit -> unit -> unit) (fun x y z -> x)
  = solve
let _ = assert (test4_exp.e == ELam (ELam (ELam (EVar 2))))

let test4_exp'
  : compile_closed #(unit -> unit -> unit -> unit) (fun x y z -> y)
  = solve
let _ = assert (test4_exp'.e == ELam (ELam (ELam (EVar 1))))

let test4_exp''
  : compile_closed #(unit -> unit -> unit -> unit) (fun x y z -> z)
  = solve
let _ = assert (test4_exp''.e == ELam (ELam (ELam (EVar 0))))

unfold
let fapp_x_wp
  #g
  (#b:Type)
  (wpG:spec_env g b)
  (a:Type)
  : spec_env g a
  = fun fsG ->
    fun p -> wpG fsG (fun _ -> forall r. p r)

unfold
let fapp_f_wp
  #g
  (#b:Type)
  (wpG:spec_env g b)
  (#a:Type)
  (x:fs_oexp g a (fapp_x_wp wpG a))
  : spec_env g (a -> b)
  = fun fsG ->
      fun p -> wpG fsG (fun r -> forall (f:a -> b). f (x fsG) == r ==> p f)

instance app_elim
  #g
  (b:Type) {| compile_typ b |}
  (#wpG:spec_env g b)
  (a:Type) {| compile_typ a |}
  (x:fs_oexp g a (fapp_x_wp wpG a))         {| cx: compile_exp _ _ x |}
  (f:fs_oexp g (a -> b) (fapp_f_wp wpG x))   {| cf: compile_exp _ _ f |}
  (_:squash (forall fsG. wpG fsG <= ret ((f fsG) (x fsG))))
  : compile_exp g wpG (fun fsG -> (f fsG) (x fsG)) = {
  e = EApp cf.e cx.e;
}

(** TODO: why does this not work automatically **)
let test1_hoc : compile_closed
  #((bool -> bool) -> bool)
  (fun f -> f false) =
  lambda_elim _ _ _ #(app_elim _ _ _ (fun fsG -> get_v' fsG 0 (bool -> bool)) _) _

instance false_elim_elim
  #g
  (a:Type) {| compile_typ a |}
  (#wpG:spec_env g (_:unit{False} -> a))
  (_:squash (forall fsG. wpG fsG <= ret (false_elim #a)))
  : compile_exp g wpG (fun _ -> false_elim #a)
  = { e = EUnit; } (** an error, or smth that makes it obvious that it gets stuck
                       would be more informative **)


unfold
let if_co_wp
  #g
  (#a:Type)
  (wpG:spec_env g a)
  : spec_env g bool =
  fun fsG ->
    fun p -> wpG fsG (fun _ -> forall b. p b)

unfold
let if_th_wp
  #g
  (#a:Type)
  (#wpG:spec_env g a)
  (co:fs_oexp g bool (if_co_wp wpG))
  : spec_env g a =
  fun fsG ->
    fun p -> wpG fsG (fun r -> co fsG /\ p r)

unfold
let if_el_wp
  #g
  (#a:Type)
  (#wpG:spec_env g a)
  (co:fs_oexp g bool (if_co_wp wpG))
  : spec_env g a =
  fun fsG ->
    fun p -> wpG fsG (fun r -> ~(co fsG) /\ p r)

instance if_elim
  #g
  (a:Type) {| compile_typ a |}
  (#wpG:spec_env g a)
  (co:fs_oexp g bool (if_co_wp wpG))  {| cco: compile_exp _ _ co |}

  (th:fs_oexp g a (if_th_wp co))      {| cth: compile_exp _ _ th |}
  (el:fs_oexp g a (if_el_wp co))      {| cel: compile_exp _ _ el |}
  (_:squash (forall fsG. wpG fsG <= ret (if co fsG then th fsG else el fsG)))
  : compile_exp g wpG (fun fsG -> if co fsG then th fsG else el fsG) = {
  e = EIf cco.e cth.e cel.e;
}

let myt = true
let test2_if
  : compile_closed #bool (if myt then false else true)
  = if_elim _ _ _ (fun _ -> true) #_ ()

let _ = assert (test2_if.e == EIf ETrue EFalse ETrue)

let test1_if
  : compile_closed #(bool -> bool -> bool) (fun x y -> if x then false else y)
  = solve
let _ = assert (test1_if.e == ELam (ELam (EIf (EVar 1) EFalse (EVar 0))))

let test3_if
  : compile_closed #(bool -> bool) (fun x -> if x then if x then true else false else true)
  = solve

unfold
let ref_wp
  #g
  (#a:Type) {| compile_typ a |}
  (#ref:a -> Type0)
  (wpG:spec_env g (x:a{ref x}))
  : spec_env g a =
  fun fsG ->
    fun p -> wpG fsG (fun r -> ref r /\ p r)

instance refinement_elim
  #g
  (#a:Type) {| compile_typ a |}
  (ref:a -> Type0)
  (#wpG:spec_env g (x:a{ref x}))
  (v:fs_oexp g (x:a{ref x}) wpG)
  {| cv: compile_exp #a g (ref_wp wpG) (fun fsG -> v fsG) |}
  : compile_exp #(x:a{ref x}) g wpG v
  = { e = cv.e; }

let refbool : (t:bool{t == true}) = true

let test1_ref
  : compile_closed refbool
  = solve
let _ = assert (test1_ref.e == ETrue)

let test2_ref : compile_closed (fun (x:bool{False}) -> x) =
  solve

let _ = assert (test2_ref.e == ELam (EVar 0))

let test_false_elim99
  : x:unit{False} -> Tot bool
  = fun x -> false_elim x

let test_false_elim99'
  : compile_closed test_false_elim99
  = lambda_elim _ _ _ #(app_elim _ _ _ _ #(false_elim_elim bool ()) ()) ()

(**
let test_false_elim1'
  : compile_closed test_false_elim1
  =
  lambda_elim _ _ _ #(app_elim _ #_ (_:unit{False}) (fun _ -> ()) #_ _ #(false_elim_elim bool ()) ()) _
**)
