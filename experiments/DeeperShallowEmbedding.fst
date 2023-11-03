module DeeperShallowEmbedding

open FStar.Tactics
open FStar.Universe

#set-options "--print_universes"

(** Shallow Embedding of DTT in F* - Figure 2 *)

val ctx : Type u#(a+1)
let ctx = Type u#a

val typ : ctx u#a -> Type u#(a+1)
let typ cs = cs -> Type u#a

val empty_ctx : ctx
let empty_ctx : ctx = raise_t unit // or true?

val cons : cs:ctx u#a -> typ u#a cs -> ctx u#a
let cons cs t = 
  c:cs & t c

val var : cs:ctx u#a -> typ u#a cs -> Type u#a
let var cs t = (c:cs) -> t c

val weakenT : #cs:ctx -> #t:(typ cs) -> typ cs -> typ (cons cs t)
let weakenT t (| c, _ |) = t c

val same : #cs:ctx -> #at:(typ cs) -> var (cons cs at) (weakenT at)
let same = fun (| _, a |) -> a

val next : #cs:ctx -> #t:(typ cs) -> #at:(typ cs) -> var cs at -> var (cons cs t) (weakenT at)
let next x = fun (| c, _ |) -> x c

val dt : #cs:ctx -> at:(typ cs) -> bt:(typ (cons cs at)) -> typ cs
let dt #cs at bt = fun (c:cs) -> ((a : at c) -> bt (| c, a |))

val term : cs:ctx u#a -> typ u#a cs -> Type u#a
let term cs t = (c:cs) -> t c

val lookup : #cs:ctx -> #t:(typ cs) -> icx:(var cs t) -> term cs t
let lookup x = x

val lambda : #cs:ctx -> #at:(typ cs) -> #bt:(typ (cons cs at)) -> term (cons cs at) bt -> term cs (dt at bt)
let lambda e = fun c a -> e (| c, a |)

val app : #cs:ctx -> #at:(typ cs) -> #bt:(typ (cons cs at)) -> term cs (dt at bt) -> (a : term cs at) -> term cs (fun c -> bt (| c, a c |))
let app e1 e2 = fun c -> (e1 c) (e2 c)


(** Deeper shallow embedding - Figure 3 **)
let typ0 (cs:ctx u#4) : Type u#4 = cs -> Type u#0
let typ1 (cs:ctx u#4) : Type u#4 = cs -> Type u#1
let typ2 (cs:ctx u#4) : Type u#4 = cs -> Type u#2
let typ3 (cs:ctx u#4) : Type u#4 = cs -> Type u#3

val u0 : #cs:ctx u#4 -> typ1 cs
let u0 c = Type u#0

val u1 : #cs:ctx u#4 -> typ2 cs
let u1 c = Type u#1

val u2 : #cs:ctx u#4 -> typ3 cs
let u2 c = Type u#2

let lift0 (#cs:ctx u#4) (x:typ0 cs) : typ cs = fun c -> raise_t (x c)
let lift1 (#cs:ctx u#4) (x:typ1 cs) : typ cs = fun c -> raise_t u#1 u#4 (x c)
let lift2 (#cs:ctx u#4) (x:typ2 cs) : typ cs = fun c -> raise_t u#2 u#4 (x c)
let lift3 (#cs:ctx u#4) (x:typ3 cs) : typ cs = fun c -> raise_t u#3 u#4 (x c)

let vlift0 (#cs:ctx u#4) (x:typ0 cs) : term cs (lift1 u0) = fun c -> raise_val (x c)
let vlift1 (#cs:ctx u#4) (x:typ1 cs) : term cs (lift2 u1) = fun c -> raise_val (x c)
let vlift2 (#cs:ctx u#4) (x:typ2 cs) : term cs (lift3 u2) = fun c -> raise_val (x c)
  
val dt0 : #cs:ctx u#4 -> at:(typ0 cs) -> bt:(typ0 (cons cs (lift0 at))) -> typ0 cs
let dt0 #cs at bt = fun (c:cs) -> ((a : at c) -> bt (| c, raise_val a |))

val dt1 : #cs:ctx u#4 -> at:(typ1 cs) -> bt:(typ1 (cons cs (lift1 at))) -> typ1 cs
let dt1 #cs at bt = fun (c:cs) -> ((a : at c) -> bt (| c, raise_val a |))

noeq
type dctx : (cs:ctx u#a) -> Type u#(a+1) =
| Empty : dctx empty_ctx
| Extend : (#cs:ctx) -> dctx cs -> t:(typ cs) -> dctx (cons cs t)

noeq
type dvar : #cs:ctx u#a -> dcs:(dctx cs) -> t:(typ cs) -> var cs t -> Type u#(a+1) =
| Same : #cs:ctx -> #t:typ cs -> #dcs:dctx cs -> dvar (Extend dcs t) (weakenT t) same
| Next : #cs:ctx -> #dcs:dctx cs -> #t:typ cs -> #at:_ -> #s:_ -> dvar #cs dcs at s -> dvar (Extend dcs t) (weakenT at) (next s)

noeq
type dterm : #cs:ctx u#4 -> dcs:dctx cs -> t:typ cs -> term cs t -> Type u#5 =
| Lambda : #cs:ctx -> #dcs:dctx cs -> #at:typ cs -> #bt:typ (cons cs at) -> #s:_ -> dterm (Extend dcs at) bt s -> dterm dcs (dt at bt) (lambda s)
| Var    : #cs:ctx -> #dcs:dctx cs -> #t:typ cs -> #s:term cs t -> dvar dcs t s -> dterm #cs dcs t s
| App    : #cs:ctx -> #dcs:dctx cs -> #at:typ cs -> #bt:typ (cons cs at) -> #s1:_ -> #s2:_ -> dterm dcs (dt at bt) s1 -> x:(dterm dcs at s2) -> dterm dcs (fun c -> bt (| c, s2 c |)) (app s1 s2)
| Dt0    : #cs:ctx -> #dcs:dctx cs -> #at:typ0 cs -> #bt:_ -> dterm dcs (lift1 u0) (vlift0 at) -> dterm (Extend dcs (lift0 at)) (lift1 u0) (vlift0 bt) -> dterm dcs (lift1 u0) (vlift0 (dt0 at bt))
| Dt1    : #cs:ctx -> #dcs:dctx cs -> #at:typ1 cs -> #bt:_ -> dterm dcs (lift2 u1) (vlift1 at) -> dterm (Extend dcs (lift1 at)) (lift2 u1) (vlift1 bt) -> dterm dcs (lift2 u1) (vlift1 (dt1 at bt))
| U0     : #cs:ctx -> #dcs:dctx cs -> dterm dcs (lift2 u1) (vlift1 u0)
| U1     : #cs:ctx -> #dcs:dctx cs -> dterm dcs (lift3 u2) (vlift2 u1)


val identity : dterm Empty (dt (lift1 u0) (lift1 u0)) (lambda (lookup same))
let identity = Lambda (Var Same)

val extract : #cs:ctx -> #dcs:dctx cs -> #at:typ cs -> #a:term cs at -> dterm dcs at a -> term cs at
let extract #cs #dcs #at #a e = a

val consistency : #t:_ -> dterm #empty_ctx Empty (fun _ -> raise_t u#0 u#4 empty) t -> raise_t u#0 u#4 empty
let consistency e = (extract e) (raise_val ())
