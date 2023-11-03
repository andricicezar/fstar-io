module DeeperShallowEmbedding

open FStar.Tactics
open FStar.Universe

#set-options "--print_universes"

val ctx : Type u#(4+1)
let ctx = Type u#4

val typ : ctx -> Type u#(4+1)
let typ (cs :ctx) = cs -> Type u#4

let typ0 = fun (cs:ctx) -> cs -> Type u#0
let typ1 = fun (cs:ctx) -> cs -> Type u#1
let typ2 = fun (cs:ctx) -> cs -> Type u#2
let typ3 = fun (cs:ctx) -> cs -> Type u#3

val term : (cs : ctx) -> typ cs -> Type u#4
let term cs t = (c:cs) -> t c

val empty_ctx : ctx
let empty_ctx : ctx = raise_t empty // or true?
val cons : (cs : ctx) -> typ cs -> ctx
let cons cs t = 
  cs * (c:cs -> t c)

val var : (cs : ctx)  -> typ cs -> Type u#4
let var cs t = (c:cs) -> t c

val weakenT : (#cs : ctx)  -> (#t : typ cs) -> typ cs -> typ (cons cs t)
let weakenT t (c, _) = t c

val same : (#cs : ctx)  -> (#t : typ cs) -> var (cons cs t) (weakenT t)
let same = 
  // TODO: fails here
  fun (c, small_t) -> small_t
