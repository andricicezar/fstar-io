module Metaprogram

open FStar.Tactics
open FStar.Tactics.Typeclasses

open QTyp
open QExp

(** fs_hd' works better with typeclass resolution than fs_hd **)
[@"opaque_to_smt"] (** not sure if it is the right pragma to prevent F* unfolding get_v' during type class resolution **)
val hd' : #g:typ_env -> #t:qType -> eval_env (extend t g) -> a:Type{a == get_Type t} -> a
let hd' #g fsG a =
  hd fsG

class quotable_typ (s:Type) = {
  [@@@no_method] q : type_quotation s;
}

let pack #s (c:quotable_typ s) : qType = (| s, c.q |)

instance quotable_typ_unit : quotable_typ unit = { q = QUnit }
instance quotable_typ_bool : quotable_typ bool = { q = QBool }
instance quotable_typ_arrow
  (s1:Type)
  (s2:Type)
  {| c1:quotable_typ s1 |}
  {| c2:quotable_typ s2 |} :
  quotable_typ (s1 -> s2) = { q = QArr c1.q c2.q }
instance quotable_typ_pair (s1:Type) (s2:Type) {| c1:quotable_typ s1 |} {| c2:quotable_typ s2 |} : quotable_typ (s1 & s2) = { q = QPair c1.q c2.q }

class quotable_exp (#a:Type0) {| ca: quotable_typ a |} (g:typ_env) (s:eval_env g -> a) = { (** using fs_oexp g (pack ca) complicates the instances of the type class **)
  [@@@no_method] q : exp_quotation #(pack ca) g s;
}

unfold let quotable (#a:Type0) {| ca: quotable_typ a |} (s:a) =
  quotable_exp #a empty (fun _ -> s)

instance quotable_tt g : quotable_exp #unit #solve g (fun _ -> ()) = {
  q = Qtt;
}

instance quotable_true g : quotable_exp #bool #solve g (fun _ -> true) = {
  q = QTrue;
}

instance quotable_false g : quotable_exp #bool #solve g (fun _ -> false) = {
  q = QFalse;
}

instance quotable_var0
  (g:typ_env)
  (a:Type)
  {| qa:quotable_typ a |}
  : quotable_exp #a #qa (extend (pack qa) g) (fun fsG -> hd' fsG a) = {
    q = magic (); //QVar0;
}

let test1_var : quotable_exp (extend qUnit empty) (fun fsG -> hd fsG) = solve

instance quotable_var1
  (g:typ_env)
  (a:Type)
  (b:Type)
  {| qa:quotable_typ a |}
  {| qb:quotable_typ b |}
  : quotable_exp #a #qa (extend (pack qb) (extend (pack qa) g))
    (fun fsG -> hd' (tail fsG) a) = {
    q = magic (); // QVar1;
}

instance quotable_var2
  (g:typ_env)
  (a:Type)
  (b:Type)
  (c:Type)
  {| qa:quotable_typ a |}
  {| qb:quotable_typ b |}
  {| qc:quotable_typ c |}
  : quotable_exp #a #qa (extend (pack qc) (extend (pack qb) (extend (pack qa) g)))
    (fun fsG -> hd' (tail (tail fsG)) a) = {
    q = magic (); // QVar2;
}

(**
let test2_var : quotable_exp (extend qUnit (extend qUnit empty)) (fun fsG -> hd' (tail fsG) unit) =
  solve

let test3_var : compile_exp (extend tunit (extend tunit (extend tunit empty))) (fun fsG -> hd' (tail (tail fsG)) unit) =
  solve
**)

instance quotable_lambda
  g
  (a:Type) {| qa: quotable_typ a |}
  (b:Type) {| qb: quotable_typ b |}
  (f:eval_env g -> a -> b)
  {| cf: quotable_exp #b #qb (extend (pack qa) g) (fun fsG -> f (tail #(pack qa) fsG) (hd' fsG a)) |}
  : quotable_exp g f = {
  q = magic ();
}

instance quotable_app
  g
  (a:Type) {| qa: quotable_typ a |}
  (b:Type) {| qb: quotable_typ b |}
  (f:eval_env g -> a -> b) {| qf: quotable_exp #_ #solve g f |}
  (x:eval_env g -> a)     {| qx: quotable_exp #_ #qa g x |}
  : quotable_exp #_ #qb g (fun fsG -> (f fsG) (x fsG)) = {
  q = QApp qf.q qx.q;
}

instance quotable_if
  g
  (co:eval_env g -> bool)  {| qco: quotable_exp #_ #solve g co |}

  (a:Type) {| qa: quotable_typ a |}
  (th:eval_env g -> a)     {| qth: quotable_exp #_ #qa g th |}
  (el:eval_env g -> a)     {| qel: quotable_exp #_ #qa g el |}
  : quotable_exp #_ #qa g (fun fsG -> if co fsG then th fsG else el fsG) = {
  q = QIf qco.q qth.q qel.q
}
