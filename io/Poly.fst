module Poly

#set-options "--print_universes"

noeq type monad = {
  m    : Type u#a -> Type u#(max 1 a);
  ret  : #a:Type -> a -> m a;
  bind : #a:Type u#a -> #b:Type u#a -> m a -> (a -> m b) -> m b;
}

assume type io_ops : Type u#0

noeq
type op_sig (op:Type u#a) = {
  args : op -> Type u#b;
  res : (cmd:op) -> (args cmd) -> Type u#c;
}

(* TODO: the type of the signature in Free.fst is polymorphic just in one universe.
   TODO: since io_ops is in univese 0 and we have to be at least in universe 1, we have to raise *)
assume val io_sig : op_sig u#a u#a u#a (Universe.raise_t io_ops)

type acts (mon:monad) = op:(Universe.raise_t io_ops) -> arg:io_sig.args op -> mon.m (io_sig.res op arg)

assume val free : monad
assume val free_acts : acts free

type int1 : Type u#1 = Universe.raise_t int

type src_ctx1 = ((int1 -> free.m int1) -> free.m int1) -> free.m (int1 -> free.m int1)
type tgt_ctx1 = mon:monad -> acts mon -> ((int1 -> mon.m int1) -> mon.m int1) -> mon.m (int1 -> mon.m int1)
  
let src_prog1 : Type = src_ctx1 -> free.m int1
let tgt_prog1 : Type = tgt_ctx1 -> free.m int1

val compile1 : src_prog1 -> tgt_prog1
let compile1 src_prog tgt_ctx : free.m int1 = 
  let src_ctx = tgt_ctx free free_acts in
  src_prog src_ctx

(* Conclusion until now, it is that we do not need to do 
   recursively compile/instrument things. It is enough to
   have the context as an effectful polymorphic type and 
   instantiate with free and the actions **)

(** *** Try new idea **)
assume type w (a:Type)
assume val theta : (#a:Type) -> (c:free.m a) -> w a
assume val w_ord : w 'a -> (w 'a) -> Type0

assume type pi_type
assume val pi_as_w : (#a:Type) -> pi_type -> w a

type dm (pi:pi_type) (a:Type) = c:(free.m a){pi_as_w pi `w_ord` theta c} 

(* this is easy to prove since ret produces the empty trace *)
assume val lemma_return_dm (pi:pi_type) (x:'a) :
  Lemma (pi_as_w pi `w_ord` theta (free.ret x))

(* this is also easy to prove based on how enforced_locally is defined *)
assume val lemma_bind_dm (pi:pi_type) (m:dm pi 'a) (k:'a -> dm pi 'b) :
  Lemma (pi_as_w pi `w_ord` theta (free.bind m k))

let dm_mon (pi:pi_type) : monad = {
  m = dm pi;
  ret = (fun (x:'a) -> 
    lemma_return_dm pi x;
    free.ret x);
  bind = (fun (m:dm pi 'a) (k:'a -> dm pi 'b) -> 
    lemma_bind_dm pi m k;
    free.bind m k)
}

assume val dm_acts (pi:pi_type) : acts (dm_mon pi)

assume type ct (m:Type u#a -> Type u#(max 1 a))

type src_ctx2 (pi:pi_type) = ct u#a (dm_mon pi).m
type tgt_ctx2 = mon:monad -> acts mon -> ct mon.m

let src_prog2 (ipi:pi_type) (vpi:pi_type) : Type = src_ctx2 u#a ipi -> (dm_mon vpi).m int1
let tgt_prog2 : Type = tgt_ctx2 -> free.m int1

val compile2 : (#ipi:pi_type) -> (#vpi:pi_type) -> src_prog2 u#a ipi vpi -> tgt_prog2 u#a
let compile2 #ipi src_prog tgt_ctx : free.m int1 = 
  let src_ctx = tgt_ctx (dm_mon ipi) (dm_acts ipi) in 
  src_prog src_ctx

(* Problem to solve: how to derive the type of the program in the target from the type in the source
   Two initial ideas: 
   1. have something that gives us the type in the source and the target (Kleisli/Code)
   2. use TypeClasses.*)

(* TODO Next: do compilation from RILang to MLang *)
