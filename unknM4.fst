module UnknM4

open FStar.Tactics
open FStar.Tactics.Typeclasses
open M4
class ml (t:Type) = { mldummy : unit }

instance ml_int : ml int = { mldummy = () }
instance ml_mlarrow t1 t2 {| ml t1 |} {| ml t2 |} : ml (t1 -> M4 t2) = { mldummy = () }

class importable (t : Type) = { itype : Type; import : itype -> M4 t; ml_itype : ml itype }

let mk_importable (t1 #t2 : Type) {|ml t1|} (imp : t1 -> M4 t2) : importable t2 =
  { itype = t1; import = imp;  ml_itype = solve }

instance ml_importable (#t : Type) (d : importable t) : ml (d.itype) = d.ml_itype

instance importable_ml t {| ml t|} : importable t = mk_importable t (fun x -> x)

class checkable2 (#t1 #t2:Type) (p : t1 -> t2 -> Type0) = { check2 : (x1:t1 -> x2:t2 -> b:bool{b ==> p x1 x2}) }
instance general_is_checkeable2 t1 t2 (p : t1 -> t2 -> bool) : checkable2 (fun x y -> p x y) = { check2 = fun x y -> p x y}
  
exception Contract_failure
instance importable_darrow_refined t1 t2 (p:t1->t2->Type0)
  {| d1:ml t1 |} {| d2:ml t2 |} {| d3:checkable2 p |} : importable (x:t1 -> M4 (y:t2{p x y})) =
  mk_importable (t1 -> M4 t2) #(x:t1 -> M4 (y:t2{p x y}))
    (fun (f:(t1 -> M4 t2)) -> 
      (fun (x:t1) -> 
        let y : t2 = f x in
        (if check2 #t1 #t2 #p x y then y 
         else raise Contract_failure) <: M4 (y:t2{p x y})))

// Example 
let incr (x:int) : M4 int = x + 1
//(Error) user tactic failed: Typeclass resolution failed: could not solve constraint: UnknM4.importable (x: Prims.int -> M4.M4 (y: Prims.int{y = x + 1}))
// Related location (C-c C-' to visit, M-, to come back): FStar/ulib/FStar.Tactics.Derived.fst(358,4-360,16) 
let incr' : (x:int) -> M4 (y:int{y = x + 1}) = import incr
