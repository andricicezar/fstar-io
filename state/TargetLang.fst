module TargetLang

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Ref

type tfootprint = Set.set nat

(** target_lang is a shallow embedding of STLC **)
class target_lang (t:Type) = {
    footprint : t -> heap -> GTot tfootprint
}

instance target_lang_unit : target_lang unit = {
    footprint = fun _ _ -> Set.empty
}

instance target_lang_int : target_lang int = {
    footprint = fun _ _ -> Set.empty
}

instance target_lang_pair (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (t1 * t2) = {
    footprint = fun (x1, x2) h -> 
        (c1.footprint x1 h) `Set.union` 
        (c2.footprint x2 h)
}

instance target_lang_sum (t1:Type) (t2:Type) {| c1:target_lang t1 |} {| c2:target_lang t2 |} : target_lang (either t1 t2) = {
    footprint = fun x h -> 
        match x with
        | Inl x1 -> c1.footprint x1 h
        | Inr x2 -> c2.footprint x2 h
}

instance target_lang_ref (t:Type) {| c:target_lang t |} : target_lang (ref t) = {
    footprint = fun x h -> 
        (only x) `Set.union`
        (c.footprint (sel h x) h) // <--- following x in h
}

let mk_tgt_arrow  
  (t1:Type)
  {| target_lang t1 |}
  (t2:t1 -> Type) 
  (#tscope:Type)
  (scope:tscope)
  {| target_lang tscope |}
  {| c2 : (x:t1 -> target_lang (t2 x)) |}
=
  x:t1 -> ST (t2 x) 
     (requires (fun _ -> True))
     (ensures (fun h0 r h1 -> 
        let fp = (target_lang_pair tscope t1).footprint (scope, x) h0 in
        (modifies fp h0 h1) /\
        (forall z. Set.mem z ((c2 x).footprint r h1) ==> Set.mem z fp \/ addr_unused_in z h0) // <-- returned references either are already in scope or are fresh
 ))

instance target_lang_arrow 
    (t1:Type)
    {| target_lang t1 |}
    (t2:t1 -> Type) 
    (#tscope:Type)
    (scope:tscope)
    {| target_lang tscope |}
    {| (x:t1 -> target_lang (t2 x)) |}
    : 
    target_lang (mk_tgt_arrow t1 t2 scope)  = {
    footprint = fun _ _ -> Set.empty
}

open STLC

(** *** Elaboration of types to F* *)
let rec elab_typ' (t:typ) (#tscope:Type) (scope:tscope) (c_scope:target_lang tscope) : tt:Type & target_lang tt =
  match t with
  | TArr t1 t2 -> begin
     let (| tt1, c_tt1 |) = elab_typ' t1 scope c_scope in
     let tt2 (x:tt1) = elab_typ' t2 (scope, x) (target_lang_pair tscope tt1 #c_scope #c_tt1) in
     (| mk_tgt_arrow      tt1 #c_tt1 (fun x -> dfst (tt2 x)) scope #c_scope #(fun x -> dsnd (tt2 x)),
        target_lang_arrow tt1 #c_tt1 (fun x -> dfst (tt2 x)) scope #c_scope #(fun x -> dsnd (tt2 x))
     |)
  end 
  | TUnit -> (| unit, target_lang_unit |)
  | TNat -> (| int, target_lang_int |)
  | TSum t1 t2 ->
     let (| tt1, c_tt1 |) = elab_typ' t1 scope c_scope in
     let (| tt2, c_tt2 |) = elab_typ' t2 scope c_scope in
     (| either tt1 tt2, target_lang_sum tt1 tt2 #c_tt1 #c_tt2 |)
  | TPair t1 t2 ->
     let (| tt1, c_tt1 |) = elab_typ' t1 scope c_scope in
     let (| tt2, c_tt2 |) = elab_typ' t2 scope c_scope in
     (| (tt1 * tt2), target_lang_pair tt1 tt2 #c_tt1 #c_tt2 |)
  | TRef t ->
     let (| tt, c_tt |) = elab_typ' t scope c_scope in
     (| ref tt, target_lang_ref tt #c_tt |)

let elab_typ (t:typ) : Type =
  dfst (elab_typ' t () target_lang_unit)

val elab_typ_test1 : elab_typ (TArr (TRef (TRef TNat)) (TArr (TRef TNat) TUnit))
let elab_typ_test1 (x:ref (ref int)) (y:ref int) =
  let ix = !x in
  ix := !ix + 1;
  x := y;
  y := !y + 5;
  ()

val elab_typ_test2 : elab_typ (TArr TUnit (TRef TNat))
let elab_typ_test2 () = alloc 0
  
val elab_typ_test2' : elab_typ (TArr (TRef TNat) (TRef TNat))
let elab_typ_test2' x = x

val elab_typ_test3 : elab_typ (TArr (TArr TUnit (TRef TNat)) TUnit)
let elab_typ_test3 f =
  let x:ref int = f () in
  x := !x + 1;
  ()
