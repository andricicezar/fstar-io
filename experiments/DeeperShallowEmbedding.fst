module DeeperShallowEmbedding

open FStar.Tactics
open FStar.Universe

#set-options "--print_universes"

val ctx : Type u#(4+1)
let ctx = Type u#4

val typ : ctx -> Type u#(4+1)
let typ cs = cs -> Type u#4

(**
let typ0 = fun (cs:ctx) -> cs -> Type u#0
let typ1 = fun (cs:ctx) -> cs -> Type u#1
let typ2 = fun (cs:ctx) -> cs -> Type u#2
let typ3 = fun (cs:ctx) -> cs -> Type u#3
**)

val empty_ctx : ctx
let empty_ctx : ctx = raise_t unit // or true?

val cons : cs:ctx -> typ cs -> ctx
let cons cs t = 
  c:cs & t c

val var : cs:ctx  -> typ cs -> Type u#4
let var cs t = (c:cs) -> t c

val weakenT : #cs:ctx -> #t:(typ cs) -> typ cs -> typ (cons cs t)
let weakenT t (| c, _ |) = t c

val same : #cs:ctx -> #at:(typ cs) -> var (cons cs at) (weakenT at)
let same = fun (| _, a |) -> a

val next : #cs:ctx -> #t:(typ cs) -> #at:(typ cs) -> var cs at -> var (cons cs t) (weakenT at)
let next x = fun (| c, _ |) -> x c

val dt : #cs:ctx -> at:(typ cs) -> bt:(typ (cons cs at)) -> typ cs
let dt #cs at bt = fun (c:cs) -> ((a : at c) -> bt (| c, a |))

val u : #cs:ctx -> typ cs
let u c = Type

val term : cs:ctx -> typ cs -> Type u#4
let term cs t = (c:cs) -> t c

val lookup : #cs:ctx -> #t:(typ cs) -> icx:(var cs t) -> term cs t
let lookup x = x

val lambda : #cs:ctx -> #at:(typ cs) -> #bt:(typ (cons cs at)) -> term (cons cs at) bt -> term cs (dt at bt)
let lambda e = fun c a -> e (| c, a |)

val app : #cs:ctx -> #at:(typ cs) -> #bt:(typ (cons cs at)) -> term cs (dt at bt) -> (a : term cs at) -> term cs (fun c -> bt (| c, a c |))
let app e1 e2 = fun c -> (e1 c) (e2 c)
