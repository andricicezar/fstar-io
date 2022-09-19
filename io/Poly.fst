module Poly

noeq type monad = {
  m    : Type u#a -> Type u#(max 1 a);
  ret  : #a:Type -> a -> m a;
  bind : #a:Type u#a -> #b:Type u#a -> m a -> (a -> m b) -> m b;
}

assume type io_ops

noeq
type op_sig (op:Type u#a) = {
  args : op -> Type u#b;
  res : (cmd:op) -> (args cmd) -> Type u#c;
}

assume val io_sig : op_sig io_ops

type acts (mon:monad) = op:io_ops -> arg:io_sig.args op -> mon.m (io_sig.res op arg)

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

(* Conclusion until now, it is that we do not need to do 
   recursively compile/instrument things. It is enough to
   have the context as an effectful polymorphic type and 
   instantiate with free and the actions **)

(* Problem to solve: how to derive the type of the program in the target from the type in the source
   Two initial ideas: 
   1. have something that gives us the type in the source and the target (Kleisli/Code)
   2. use TypeClasses.*)

(* Next challenge is to have Dijkstra Monads at all positions, instead of the free monad. 
   My intuition says we should get this from parametricity. *)
assume type w (a:Type)
assume val theta : (#a:Type) -> (c:free.m a) -> w a
assume val w_ord : w 'a -> (w 'a) -> Type0

type dm a (wp:w a) = c:(free.m a){wp `w_ord` theta c} 

assume type pi_type
assume val pi_as_w : (#a:Type) -> pi_type -> w a

(** *** Parametricity **)
noeq
type monad_p (mon:monad) = {
  m_p : a:Type -> a_p:(a -> Type) -> x:(mon.m a) -> Type;
  ret_p : a:Type -> a_p:(a -> Type) -> (x:a) -> x_p:(a_p x) -> Lemma (m_p a a_p (mon.ret x));
}

[@@ "opaque_to_smt"]
type io_cmds_p (cmd:io_ops) = True

[@@ "opaque_to_smt"]
type io_sig_args_p (op:io_ops) (arg:io_sig.args op) = True

[@@ "opaque_to_smt"]
type io_sig_res_p (op:io_ops) (arg:io_sig.args op) (res:io_sig.res op arg) = True

type acts_p (mon:monad) (mon_p:monad_p mon) (theActs:acts mon) = 
  op:io_ops -> op_p : (io_cmds_p op) -> 
  arg:io_sig.args op -> arg_p : (io_sig_args_p op arg) ->
  Lemma (mon_p.m_p (io_sig.res op arg) (io_sig_res_p op arg) (theActs op arg))


(** **** Parametricity - instances **)
let free_p (pi:pi_type) : monad_p free = {
  m_p = (fun a a_p tree -> pi_as_w pi `w_ord` theta tree);
  ret_p = (fun a a_p tree tree_p -> (* This was unit before *) admit ());
}

assume val wrap : pi_type -> acts free -> acts free

val wrap_p : (pi:pi_type) -> (ca:(acts free)) -> acts_p free (free_p pi) (wrap pi ca)
let wrap_p pi ca (op:io_ops) op_p (arg:io_sig.args op) arg_p : 
  Lemma ((free_p pi).m_p (io_sig.res op arg) (io_sig_res_p op arg) ((wrap pi ca) op arg)) = 
  (* this was proved before *)
  admit ()

type ct_p 
  (mon:monad) (mon_p:monad_p mon)
  (a b:Type)
  (c:a -> mon.m b) =
  squash (forall x. mon_p.m_p b (fun x -> True) (c x))

type ctx_p 
  (mon:monad) (mon_p:monad_p mon) 
  (theActs:acts mon) (theActs_p:acts_p mon mon_p theActs)
  (a:Type)
  (b:Type) 
  (c:(mon:monad -> acts mon -> a -> mon.m b)) =
  ct_p mon mon_p a b (c mon theActs)

assume val ctx_param : 
  (mon:monad) -> (mon_p:monad_p mon) ->
  (theActs:acts mon) -> (theActs_p:acts_p mon mon_p theActs) ->
  (a:Type) ->
  (b:Type) ->
  (c:(mon:monad -> acts mon -> a -> mon.m b)) ->
  Lemma (ctx_p mon mon_p theActs theActs_p a b c)

open FStar.Tactics

val cast_to_dm_iio  : 
  (#a:Type) -> 
  (#b:Type) -> 
  ipi:pi_type ->
  (mon:monad -> acts mon -> a -> mon.m b) ->
  (x:a -> dm b (pi_as_w ipi))
let cast_to_dm_iio #a #b ipi c x : _ by (norm [delta_only [`%Mkmonad_p?.m_p;`%free_p]]; norm [iota]; explode ()) =
  let c' : a -> free.m b = c free (wrap ipi free_acts) in
  let tree : free.m _ = c' x in
  ctx_param free (free_p ipi) (wrap ipi free_acts) (wrap_p ipi free_acts) a b c;
  assert (pi_as_w ipi `w_ord` theta tree);
  tree


