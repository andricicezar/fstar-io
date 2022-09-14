module Poly

noeq type monad = {
  m    : Type u#a -> Type u#(max 1 a);
  ret  : #a:Type -> a -> m a;
  bind : #a:Type u#a -> #b:Type u#a -> m a -> (a -> m b) -> m b;
}

assume type acts (mon:monad)

assume val free : monad
assume val free_acts : acts free

type int1 : Type u#1 = Universe.raise_t int

type src_ctx1 = ((int1 -> free.m int1) -> free.m int1) -> free.m (int1 -> free.m int1)
type tgt_ctx1 = mon:monad -> acts mon -> ((int1 -> mon.m int1) -> mon.m int1) -> mon.m (int1 -> mon.m int1)

val backtranslate : tgt_ctx1 -> src_ctx1
let backtranslate (tgt_ctx:tgt_ctx1) (pprog_cb:((int1 -> free.m int1) -> free.m int1)) : free.m (int1 -> free.m int1) = 
  let src_ctx : ((int1 -> free.m int1) -> free.m int1) -> free.m (int1 -> free.m int1) = tgt_ctx free free_acts in
  let r : free.m (int1 -> free.m int1) = src_ctx pprog_cb in 
  r
  
let src_prog1 : Type = src_ctx1 -> free.m int1
let tgt_prog1 : Type = tgt_ctx1 -> free.m int1

val compile : src_prog1 -> tgt_prog1
let compile src_prog tgt_ctx : free.m int1 = 
  src_prog (backtranslate tgt_ctx)

open FStar.Tactics
open FStar.Tactics.Typeclasses

class some (kleisi_typ:Type) = {
  [@@@no_method]
  poly_typ : Type 
}

instance some_c (a:Type) {| d1: some a |} (b:Type) {| d2: some b |} : some (a -> free.m b) = {
  poly_typ = mon:monad -> acts:acts mon -> a -> mon.m b 
}

class some_ho (kleisi_typ:Type) = {
  [@@@no_method]
  poly_typ : Type 
}

// Problem to solve: how to derive the type of the program in the target from the type in the source
// Two initial ideas: 
// 1. have something that gives us the type in the source and the target (Kleisli/Code)
// 2. use TypeClasses.
