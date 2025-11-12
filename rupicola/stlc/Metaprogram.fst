module Metaprogram

open FStar.Tactics
open FStar.Tactics.Typeclasses

open QTyp
open QExp

(** hd' works better with typeclass resolution than hd,
    but not sure how to integrate it **)
[@"opaque_to_smt"]
val hd' : #g:typ_env -> #t:qType -> eval_env (extend t g) -> a:Type{a == get_Type t} -> a
let hd' #g fsG a =
  hd fsG

class quotable_typ (s:Type) = {
  [@@@no_method] q : type_quotation s;
}

let pack #s (c:quotable_typ s) : qType = (| s, c.q |)

instance q_unit : quotable_typ unit = { q = QUnit }
instance q_bool : quotable_typ bool = { q = QBool }
instance q_arr
  (s1:Type)
  (s2:Type)
  {| c1:quotable_typ s1 |}
  {| c2:quotable_typ s2 |} :
  quotable_typ (s1 -> s2) = { q = QArr c1.q c2.q }

instance q_pair (s1:Type) (s2:Type) {| c1:quotable_typ s1 |} {| c2:quotable_typ s2 |} : quotable_typ (s1 & s2) = { q = QPair c1.q c2.q }

class quotable_exp (#a:Type0) {| ca: quotable_typ a |} (g:typ_env) (s:eval_env g -> a) = { (** using fs_oexp g (pack ca) complicates the instances of the type class **)
  [@@@no_method] q : exp_quotation #(pack ca) g s;
}

unfold let quotable (#a:Type0) {| ca: quotable_typ a |} (s:a) =
  quotable_exp #a empty (fun _ -> s)

instance q_tt g : quotable_exp #unit #solve g (fun _ -> ()) = {
  q = Qtt;
}

instance q_true g : quotable_exp #bool #solve g (fun _ -> true) = {
  q = QTrue;
}

instance q_false g : quotable_exp #bool #solve g (fun _ -> false) = {
  q = QFalse;
}

instance q_var0
  (g:typ_env)
  (a:Type)
  {| qa:quotable_typ a |}
  : quotable_exp #a #qa (extend (pack qa) g) (fun fsG -> hd fsG) = {
    q = QVar0;
}

instance q_varS
  (g:typ_env)
  (a:Type)
  (b:Type)
  {| qa:quotable_typ a |}
  {| qb:quotable_typ b |}
  (x:eval_env g -> a)
  {| qx:quotable_exp g x |}
  : quotable_exp #a #qa (extend (pack qb) g)
    (fun fsG -> x (tail fsG)) = {
    q = QVarS qx.q;
}

let test1_var : quotable_exp (extend qUnit empty) (fun fsG -> hd fsG) =
  solve

val test2_var : quotable_exp (extend qUnit (extend qUnit empty)) (fun fsG -> hd (tail fsG))
let test2_var =
 q_varS _ _ _ _ #(q_var0 _ _)
 // TODO: solve

let test3_var : quotable_exp (extend qUnit (extend qUnit (extend qUnit empty))) (fun fsG -> hd (tail (tail fsG))) =
  q_varS _ _ _ _ #(q_varS _ _ _ _ #(q_var0 _ _))
 // TODO: solve

instance q_lambda
  g
  (a:Type) {| qa: quotable_typ a |}
  (b:Type) {| qb: quotable_typ b |}
  (f:eval_env g -> a -> b)
  {| cf: quotable_exp #b #qb (extend (pack qa) g) (fun fsG -> f (tail #(pack qa) fsG) (hd fsG)) |}
  : quotable_exp #(a -> b) #(q_arr a b) g f = {
  q = QLambda #g #(pack qa) #(pack qb) #f cf.q;
}

instance q_app
  g
  (a:Type) {| qa: quotable_typ a |}
  (b:Type) {| qb: quotable_typ b |}
  (f:eval_env g -> a -> b) {| qf: quotable_exp #_ #solve g f |}
  (x:eval_env g -> a)     {| qx: quotable_exp #_ #qa g x |}
  : quotable_exp #_ #qb g (fun fsG -> (f fsG) (x fsG)) = {
  q = QApp qf.q qx.q;
}

instance q_if
  g
  (co:eval_env g -> bool)  {| qco: quotable_exp #_ #solve g co |}

  (a:Type) {| qa: quotable_typ a |}
  (th:eval_env g -> a)     {| qth: quotable_exp #_ #qa g th |}
  (el:eval_env g -> a)     {| qel: quotable_exp #_ #qa g el |}
  : quotable_exp #_ #qa g (fun fsG -> if co fsG then th fsG else el fsG) = {
  q = QIf qco.q qth.q qel.q
}

(** When using solve, one should also use the pre-processor **)
