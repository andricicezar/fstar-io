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

val var : (cs : ctx)  -> typ cs -> Type u#4
let var cs t = (c:cs) -> t c

val term : (cs : ctx) -> typ cs -> Type u#4
let term cs t = (c:cs) -> t c

val empty_ctx : ctx
let empty_ctx : ctx = raise_t empty // or true?

val cons : (cs : ctx) -> typ cs -> ctx
let cons cs t = 
  // TODO: why is this failing?
  either u#4 u#4 cs t

