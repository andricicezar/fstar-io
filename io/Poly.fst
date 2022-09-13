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

let src_ctx1 : Type = ((int1 -> free.m int1) -> free.m int1) -> free.m (int1 -> free.m int1)
let tgt_ctx1 : Type = mon:monad -> acts mon -> ((int1 -> mon.m int1) -> mon.m int1) -> mon.m (int1 -> mon.m int1)

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
