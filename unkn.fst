module Unkn

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.All

class ml (t:Type) = { mldummy : unit }

instance ml_int : ml int = { mldummy = () }
instance ml_mlarrow t1 t2 {| ml t1 |} {| ml t2 |} : ml (t1 -> ML t2) = { mldummy = () }
instance ml_pair t1 t2 {| ml t1 |} {| ml t2 |} : ml (t1 * t2) = { mldummy = () }

class importable (t : Type) = { itype : Type; import : itype -> ML t; ml_itype : ml itype }

let mk_importable (t1 #t2 : Type) {|ml t1|} (imp : t1 -> ML t2) : importable t2 =
  { itype = t1; import = imp;  ml_itype = solve }

instance ml_importable (#t : Type) (d : importable t) : ml (d.itype) = d.ml_itype

instance importable_ml t {| ml t|} : importable t = mk_importable t (fun x -> x)

class checkable2 (#t1 #t2:Type) (p : t1 -> t2 -> Type0) = { check2 : (x1:t1 -> x2:t2 -> b:bool{b ==> p x1 x2}) }
instance general_is_checkeable2 t1 t2 (p : t1 -> t2 -> bool) : checkable2 (fun x y -> p x y) = { check2 = fun x y -> p x y}
  
exception Contract_failure
instance importable_darrow_refined t1 t2 (p:t1->t2->Type0)
  {| d1:ml t1 |} {| d2:ml t2 |} {| d3:checkable2 p |} : importable (x:t1 -> ML (y:t2{p x y})) =
  mk_importable (t1 -> ML t2) #(x:t1 -> ML (y:t2{p x y}))
    (fun (f:(t1 -> ML t2)) -> 
      (fun (x:t1) -> 
        let y : t2 = f x in
        (if check2 #t1 #t2 #p x y then y 
         else raise Contract_failure) <: ML (y:t2{p x y})))

// Example 
let incr (x:int) : ML int = x + 1
let incr' : (x:int) -> ML (y:int{y = x + 1}) = import incr

instance importable_dpair_refined t1 t2 (p:t1 -> t2 -> Type0)
  {| d1:importable t1 |} {| d2:importable t2 |} {| d3:checkable2 p |} : importable (x:t1 & y:t2{p x y}) =
  mk_importable (d1.itype & d2.itype) #(x:t1 & y:t2{p x y})
    (fun ((x', y')) ->
        let (x : t1) = import x' in
        let (y : t2) = import y' in
        (if check2 #t1 #t2 #p x y then (| x, y |) 
        else raise Contract_failure) <: (x:t1 & y:t2{p x y}))

let test_dpair_refined : (a:int & b:int{b = a + 1}) = import (10, 11)
