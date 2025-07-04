module Rupicola

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.List.Tot

type t_op = | TPush : int -> t_op | TPopAdd : t_op | TIfThenElse: bool -> tgt -> tgt -> t_op
and tgt = list t_op

let sem_top (zs:list int) (op:t_op) : list int =
  match op, zs with
  | TPush z, zs -> z :: zs
  | TPopAdd, z2::z1::zs -> (z1+z2) :: zs
  | _, zs -> zs

let sem_t (t:tgt) (zs:list int) =
  fold_left (sem_top) zs t

let equiv (t:tgt) (z:int) =
  forall zs. sem_t t zs = z :: zs

class compile (s:int) = { t:(t:tgt(* {equiv t s} *)) }

instance compile_int (s:int) : compile s = { t = [TPush s] }

instance compile_add s1 s2 {| c1:compile s1 |} {| c2:compile s2 |}  : compile (s1+s2) = {
  t = c1.t @ c2.t @ [TPopAdd]
}

 val f : int -> int
 let f x = x+1

instance compile_if_then_else (b:bool) s1 s2 {| c1:compile s1 |} {| c2:compile s2 |} :
  compile (if b then s1 else s2) = {
  t = [TIfThenElse b c1.t c2.t]
  }

let test : compile (10 + 4) = solve

[@expect_failure]
let _ = assert (test.t == []) by (compute (); dump "H")

val g : bool -> bool
let g x = x

let test2 : compile (if g true then f 10 else 4) = solve

[@expect_failure]
let _ = assert (test2.t == []) by (compute (); dump "H")
