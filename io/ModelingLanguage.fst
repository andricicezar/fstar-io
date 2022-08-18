module ModelingLanguage

open FStar.Classical.Sugar
open FStar.Tactics
open FStar.List.Tot
open FStar.Tactics.Typeclasses

open Common
open Free
open IO
open IO.Sig
open TC.Monitorable.Hist
open IIO

(* TODO : think about higher-order **)

noeq type monad = {
  m    : Type u#a -> Type u#(max 1 a);
  ret  : #a:Type -> a -> m a;
  (* TODO: bind should be polymorphic in two universes *)
  bind : #a:Type u#a -> #b:Type u#a -> m a -> (a -> m b) -> m b;
  (* TODO: merge acts into monad **)
  (* TODO: make acts more general? **)
  // acts : op:io_cmds -> arg:io_sig.args op -> m (Universe.raise_t (io_sig.res op arg))
}

val free : monad
let free = { 
  m = iio; 
  ret = iio_return; 
  bind = iio_bind; 
 // acts = (fun cmd arg -> iio_bind (IO.Sig.Call.iio_call cmd arg) (fun x -> Universe.raise_val x))
}

type acts (mon:monad) = op:io_cmds -> arg:io_sig.args op -> mon.m (io_sig.res op arg)

(** **** Free Actions **)
val free_acts : acts free
let free_acts cmd arg = IO.Sig.Call.iio_call cmd arg

let spec_free_acts (ca:acts free) =
  (forall (cmd:io_cmds) (arg:io_sig.args cmd). iio_wps cmd arg `hist_ord` dm_iio_theta (ca cmd arg))

let lemma_free_acts () : Lemma (spec_free_acts free_acts) = 
  assert (forall (cmd:io_cmds) (arg:io_sig.args cmd). iio_wps cmd arg `hist_ord` dm_iio_theta (free_acts cmd arg));
  assert (spec_free_acts free_acts) by (assumption ())

let pi_type = pi:monitorable_prop{forall h op arg. pi op arg h ==> io_pre op arg h}

(** * Arrow Types **)
type styp = (Type -> Type) -> Type
(* I use styp here to be able to write HO types. Not sure if standard practice,
   or if there is another way to do it. Or maybe a better name since a kleisli arrow
   has the simpler form.
   By using styp, I can write things like: kleisli (kleisli a b) c m. that stands
   for (a -> m b) -> m c.
   
   Also, from what I have read, a kleisli arrow actually has access to bind/return
   and other monad operations. In our case, that it is not true.*)
type kleisli (t1:styp) (t2:styp) (m:Type->Type) = t1 m -> m (t2 m)
let (--->) = kleisli

let wstyp (a:Type) : styp = fun m -> a
let (~~) = wstyp

let kleisli_fish
  (#m:Type->Type)
  (#m_bind:(a:Type -> b:Type -> m a -> (a -> m b) -> m b))
  (f:kleisli 'a 'b m)
  (g:kleisli 'b 'c m) : 
  kleisli 'a 'c m = 
  fun (x:'a m) -> m_bind _ _ (f x) g

(* effectpoly is the type of effect polymorphic kleisli arrows 
   Q: I am confused if kleisli arrows are already effectful polymorphic and if the
      names I use are correct **)
type effectpoly (t1:styp) (t2:styp) = mon:monad -> acts mon -> kleisli t1 t2 mon.m 
let (--><*>) = effectpoly
let effectpoly_fish (f:'a --><*> 'b) (g:'b --><*> 'c) : ('a --><*> 'c) = 
  fun (mon:monad) (acts:acts mon) (x:'a mon.m) -> 
    mon.bind (f mon acts x) (g mon acts)

(* About the --><*> notation:
   I saw this notation in: Effects as Capabilities: Effect Handlers and Lightweight
   Effect Polymorphism 

  In the mentioned paper they use this notation actually to highlight the effect of the 
  arrow.
  --> <> means that the arrow is in the pure effect
  --> <exception, IO> means that the arrow is in exception/IO

  Since I thought it is fun to use symbols for operators, I tried to find one and
  I thought this one looks decent.

  I read `a --><*> b` as: the arrow `a --> b` can accept any effect.
**)

(* My guess is that statically verified programs have to be compiled to
   effectful polymorphic functions. However, we don't want that. So, one idea 
   I had was to use a refinement that only accepts the free monad. *)
(* if --><*> means that the arrow accepts any effect, 
   --><> means that this arrow does not accept any effect.
   that is not really true. this arrow accepts only the free effect. *)
type effectpoly_hack (t1:styp) (t2:styp) = mon:monad{mon == free} -> acts mon -> kleisli t1 t2 mon.m 
let (--><>) = effectpoly_hack
let effectpoly_hack_fish (f:'a --><> 'b) (g:'b --><*> 'c) : ('a --><> 'c) = 
  fun mon (acts:acts mon) (x:'a mon.m) -> 
    mon.bind (f mon acts x) (g mon acts)

//let convert_free_to_effectpoly (f:'a -> free.m 'b) : (~~'a --><> ~~'b) =
//  fun mon acts x -> f x

(** * MLang **)
class mlang (t:Type u#a) = { mldummy : unit }

(** *** FO instances **)
instance mlang_unit : mlang unit = { mldummy = () }

instance mlang_bool : mlang bool = { mldummy = () }
instance mlang_int : mlang int = { mldummy = () }

instance mlang_pair t1 t2 {| d1:mlang t1 |} {| d2:mlang t2 |} : mlang (t1 * t2) = 
  { mldummy = () }
instance mlang_either t1 t2 {| d1:mlang t1 |} {| d2:mlang t2 |} : mlang (either t1 t2) =
  { mldummy = () }

(** TODO: is this one neeeded? *)
(* instance mlang_tree #t1 (d1:mlang t1) : mlang (free.m t1) =
  { mldummy = () } *)
  
(* TODO: I am not sure if we want arrows in any effect to be part of our language. *)
instance mlang_kleisli #t1 #t2 (m:Type->Type) (d1:mlang t1) (d2:mlang t2) : mlang (kleisli (~~t1) (~~t2) m) =
  { mldummy = () }

instance mlang_kleisli_lhs_ho (#t1:styp) #t2 (m:Type->Type) (d1:mlang (t1 m)) (d2:mlang t2) : mlang (kleisli t1 (~~t2) m) =
  { mldummy = () }

instance mlang_kleisli_rhs_ho #t1 (#t2:styp) (m:Type->Type) (d1:mlang t1) (d2:mlang (t2 m)) : mlang (kleisli (~~t1) t2 m) =
  { mldummy = () }

instance mlang_kleisli_ho (#t1:styp) (#t2:styp) (m:Type->Type) (d1:mlang (t1 m)) (d2:mlang (t2 m)) : mlang (kleisli t1 t2 m) =
  { mldummy = () }

(* TODO: in practice, I don't think we need this case *)
instance mlang_effectpoly (#t1:Type) (#t2:Type) (d1:mlang t1) (d2:mlang t2) : mlang (~~t1 --><*> ~~t2) =
  { mldummy = () }

instance mlang_effectpoly_lhs_ho (#t1:styp) (#t2:Type) (d1:(m:(Type -> Type) -> mlang (t1 m))) (d2:mlang t2) : mlang (t1 --><*> ~~t2) =
  { mldummy = () }
  
instance mlang_effectpoly_ho (#t1:styp) (#t2:styp) (d1:(m:(Type -> Type) -> mlang (t1 m))) (d2:(m:(Type -> Type) -> mlang (t1 m))) : mlang (t1 --><*> t2) =
  { mldummy = () }

(**
instance mlang_effectpoly_hack #t1 #t2 (d1:mlang t1) (d2:mlang t2) : mlang (~~t1 --><> ~~t2) =
  { mldummy = () }

(** Since the effectpolymorphic arrow here only accepts the free monad, we can instantiate the HO input and output with free **)
instance mlang_effectpoly_hack_lhs_ho (#t1:styp) #t2 (d1:mlang (t1 free.m)) (d2:mlang t2) : mlang (t1 --><> ~~t2) =
  { mldummy = () }
**)

(** Manual tests of MLang. 
    Types of programs that should be part of MLang:
   - [v] int -> free.m int
   - [ ] int -> free.m (int -> free.m int)
   - [v] (int -> free.m int) -> free.m int (?)
   - [v] mon:monad -> acts mon -> int -> mon.m int 
   - [v] mon:monad -> acts mon -> (int -> mon.m int) -> mon.m int 
   - [ ] mon:monad -> acts mon -> int -> mon.m (int -> mon.m int)
   - [v] (mon:monad -> acts mon -> int -> mon.m int) -> free.m int
   - [v] (mon:monad -> acts mon -> (int -> mon.m int) -> mon.m int) -> free.m int 

   Types of programs that should not be part of MLang:
   - [ ] how can I identify such cases?
**)

let test_mlang_kleisli : mlang (kleisli ~~int ~~int free.m) =
  mlang_kleisli free.m mlang_int mlang_int

(** Cannot be typed because universe problems
let test_mlang_kleisli_rhs_ho : mlang (kleisli ~~int (kleisli ~~int ~~int) free.m) =
  mlang_kleisli free.m mlang_int (mlang_kleisli free.m mlang_int mlang_int)
 **)

let test_mlang_kleisli_lhs_ho : mlang (kleisli (kleisli ~~int ~~int) ~~int free.m) =
  mlang_kleisli free.m (mlang_kleisli free.m mlang_int mlang_int) mlang_int

let test_mlang_fo_effectpoly : mlang (~~int --><*> ~~int) =
  mlang_effectpoly
    mlang_int
    mlang_int

let test_mlang_lhs_ho_effectpoly : mlang (~~int ---> ~~int --><*> ~~int) =
  mlang_effectpoly_lhs_ho
    (fun m -> mlang_kleisli m mlang_int mlang_int)
    mlang_int

(** This can not be typed because universe problems: 
let test_mlang_rhs_ho_effectpoly : mlang (~~int --><*> (~~int ---> ~~int)) = **)

let test_mlang_prog1 : mlang (kleisli ~~(~~int --><*> ~~int) ~~int free.m) =
  mlang_kleisli_lhs_ho
    free.m
    (mlang_effectpoly mlang_int mlang_int)
    mlang_int

let test_mlang_prog2 : mlang (kleisli ~~(~~int ---> ~~int --><*> ~~int) ~~int free.m) =
  mlang_kleisli_lhs_ho
    free.m
    (mlang_effectpoly_lhs_ho
        (fun m -> mlang_kleisli m mlang_int mlang_int)
        mlang_int)
    mlang_int

   

(* Exercise: 
   Be prog of type: ctx:( cb:(a -> IIOpi b pi) -> IIOpi c psi) -> IIOpi d phi
   the expected type after compilation of prog should be:
     ctx:(cb:(a ---> b) --><*> c) ---> free.m d  

   The cb is a verified program, and even if we can compile it directly to
   a -> free.m b, we don't want because then the ctx can not use it inside.
   Thus, the cb should have the same monad as the ctx.

   However, cb only works only with the free monad. So even if it accepts the
   monad passed by the context, it should have as pre-condition that the monad
   should be free.

   Another thing to notice is that prog and cb should be compiled by the same
   compilation function and from the start we expect two different outputs.

   Maybe we can compile prog as it is, but then when doing backtranslation to treat
   the case when on the left is an arrow by abstracting that further.
*)

(** *** Parametricity **)
noeq
type monad_p (mon:monad) = {
  m_p : a:Type -> a_p:(a -> Type) -> x:(mon.m a) -> Type;
  ret_p : a:Type -> a_p:(a -> Type) -> (x:a) -> x_p:(a_p x) -> Lemma (m_p a a_p (mon.ret x));
}

(* TODO: *)
[@@ "opaque_to_smt"]
type io_cmds_p (cmd:io_cmds) =
  True

(* TODO: *)
[@@ "opaque_to_smt"]
type io_sig_args_p (op:io_cmds) (arg:io_sig.args op) =
  True

(* TODO: *)
[@@ "opaque_to_smt"]
type io_sig_res_p (op:io_cmds) (arg:io_sig.args op) (res:io_sig.res op arg) =
  True

type acts_p (mon:monad) (mon_p:monad_p mon) (theActs:acts mon) = 
  op:io_cmds -> op_p : (io_cmds_p op) -> 
  arg:io_sig.args op -> arg_p : (io_sig_args_p op arg) ->
  Lemma (mon_p.m_p (io_sig.res op arg) (io_sig_res_p op arg) (theActs op arg))

(* TODO: check if we need parametricity for the interface **)
type ct_p (a b:Type) (mon:monad) (mon_p:monad_p mon) (c:a -> mon.m b) =
  squash (forall x. mon_p.m_p b (fun x -> True) (c x))

type ctx_p (a b:Type) (mon:monad) (mon_p:monad_p mon) (theActs:acts mon) (theActs_p:acts_p mon mon_p theActs) (c:~~a --><*> ~~b) =
  ct_p a b mon mon_p (c mon theActs)

(* TODO: check with others -- since this is assumed, it represents a risk **)
(* Parametricity Assumption about the Context **)
assume val ctx_param : 
  (a:Type) -> 
  (b:Type) ->
  (mon:monad) -> (mon_p:monad_p mon) ->
  (theActs:acts mon) -> (theActs_p:acts_p mon mon_p theActs) ->
  (c:(~~a --><*> ~~b)) -> 
  Lemma (ctx_p a b mon mon_p theActs theActs_p c)

(** **** Parametricity - instances **)
let free_p (pi:pi_type) : monad_p free = {
  m_p = (fun a a_p tree -> ILang.pi_hist #a pi `hist_ord` dm_iio_theta tree);
  ret_p = (fun a a_p tree tree_p -> ());
}

unfold val check_get_trace : pi_type -> cmd:io_cmds -> io_sig.args cmd -> free.m bool

[@@ "opaque_to_smt"]
let check_get_trace pi cmd arg = 
  iio_bind (IO.Sig.Call.iio_call GetTrace ()) (fun h -> Return (pi cmd arg h))

val wrap : pi_type -> acts free -> acts free
[@@ "opaque_to_smt"]
let wrap pi theActs cmd arg =
  iio_bind
    (check_get_trace pi cmd arg)
    (fun b -> if b then theActs cmd arg else free.ret #(io_sig.res cmd arg) (Inr Common.Contract_failure))

#set-options "--split_queries"
val wrap_p : (pi:pi_type) -> (ca:(acts free){spec_free_acts ca}) -> acts_p free (free_p pi) (wrap pi ca)
let wrap_p pi ca (op:io_cmds) op_p (arg:io_sig.args op) arg_p : 
  Lemma ((free_p pi).m_p (io_sig.res op arg) (io_sig_res_p op arg) ((wrap pi ca) op arg)) = 
  assert (spec_free_acts ca);
  assert (iio_wps op arg `hist_ord` dm_iio_theta (ca op arg)) by (
    let lem = nth_binder 9 in
    let lem = instantiate lem (nth_binder 2) in
    let lem = instantiate lem (nth_binder 4) in
    assumption ()
  );
  introduce forall p h. ILang.pi_hist pi p h ==> dm_iio_theta ((wrap pi ca) op arg) p h with begin
    introduce ILang.pi_hist pi p h ==> dm_iio_theta ((wrap pi ca) op arg) p h with _. begin
      calc (==>) {
        ILang.pi_hist pi p h;
        ==> {
          assert (pi op arg h ==> io_pre op arg h);
          assert (iio_wps op arg p h ==> dm_iio_theta (ca op arg) p h)
        }
        if pi op arg h then
          dm_iio_theta (ca op arg) p h
        else 
          dm_iio_theta (Return (Inr Common.Contract_failure)) p h;
        ==> {}
        if pi op arg h then
          dm_iio_theta (ca op arg) (fun lt' r -> p lt' r) h
        else 
          dm_iio_theta (Return (Inr Common.Contract_failure)) (fun lt' r -> p lt' r) h;
        ==> {}
        dm_iio_theta (if pi op arg h then ca op arg
          else Return (Inr Common.Contract_failure))
        (fun lt' r -> p lt' r)
        h;
        == { _ by (
          norm [delta_only [`%hist_bind;`%hist_post_bind;`%hist_post_shift];zeta;iota];
          l_to_r [`List.Tot.Properties.append_nil_l]
        )}
        hist_bind
          (fun p h -> p [] (pi op arg h))
          (fun b -> dm_iio_theta (if b then ca op arg else free.ret #(io_sig.res op arg) (Inr Common.Contract_failure)))
          p h;
        == { _ by (compute ()) }
        hist_bind
          (dm_iio_theta (check_get_trace pi op arg))
          (fun b -> dm_iio_theta (if b then ca op arg else free.ret #(io_sig.res op arg) (Inr Common.Contract_failure)))
          p h;
        ==> { 
          let m1 = (check_get_trace pi op arg) in
          let m2 = fun b -> (if b then ca op arg else free.ret #(io_sig.res op arg) (Inr Common.Contract_failure)) in 
          DMFree.lemma_theta_is_lax_morphism_bind iio_wps m1 m2;
          assert (hist_bind (dm_iio_theta m1) (fun b -> dm_iio_theta (m2 b)) p h ==>
            dm_iio_theta (iio_bind m1 m2) p h)
        }
        dm_iio_theta (
          iio_bind
            (check_get_trace pi op arg)
            (fun b -> if b then ca op arg else free.ret #(io_sig.res op arg) (Inr Common.Contract_failure)))
         p h;
        == { _ by (norm [delta_only [`%wrap]; zeta]) }
        dm_iio_theta ((wrap pi ca) op arg) p h;
      }
    end
  end
#reset-options

val cast_to_dm_iio  : (#a:Type) -> (#b:Type) -> ipi:pi_type -> (~~a --><*> ~~b) -> (x:a) -> dm_iio b (ILang.pi_hist ipi)
let cast_to_dm_iio #a #b ipi c x : _ by (norm [delta_only [`%ctx_p;`%ct_p;`%Mkmonad_p?.m_p;`%free_p]]; norm [iota]; explode ()) =
  lemma_free_acts ();
  let c' : a -> free.m b = c free (wrap ipi free_acts) in
  let tree : iio b = c' x in
  ctx_param a b free (free_p ipi) (wrap ipi free_acts) (wrap_p ipi free_acts) c;
  assert (ILang.pi_hist ipi `hist_ord` dm_iio_theta tree);
  tree

(** * Type Classes **)
class compilable (icomp:Type u#a) (pi:pi_type) = {
  [@@@no_method]
  mcomp : Type u#b;

  compile: icomp -> mcomp;

  [@@@no_method]
  ilang_icomp : ILang.ilang icomp pi;
  [@@@no_method]
  mlang_mcomp : mlang mcomp;
}

class backtranslateable (ibtrans:Type u#a) (pi:pi_type) = {
  [@@@no_method]
  mbtrans : Type u#b;

  backtranslate: mbtrans -> ibtrans;

  [@@@no_method]
  ilang_ibtrans : ILang.ilang ibtrans pi;
  [@@@no_method]
  mlang_mbtrans : mlang mbtrans;
}

class instrumentable (iinst_in iinst_out:Type) (pi:pi_type) = {
 // [@@@no_method]
  minst_in: Type;
  minst_out : Type;

  instrument: ~~minst_in --><*> ~~minst_out -> Tot (ILang.ilang_arrow_typ iinst_in iinst_out pi); 

  [@@@no_method]
  mlang_iinst : mlang (~~minst_in --><*> ~~minst_out);
  [@@@no_method]
  ilang_minst : ILang.ilang (ILang.ilang_arrow_typ iinst_in iinst_out pi) pi;
}

instance instrumentable_is_backtranslateable #t1 #t2 #ipi (d1: instrumentable t1 t2 ipi) : backtranslateable (ILang.ilang_arrow_typ t1 t2 ipi) ipi = {
  mbtrans = ~~d1.minst_in --><*> ~~d1.minst_out;
  mlang_mbtrans = d1.mlang_iinst;
  backtranslate = d1.instrument;
  ilang_ibtrans = d1.ilang_minst;
}

assume val reify_IIOwp (#a:Type) (#wp:hist a) ($f:unit -> IIOwp a wp) : dm_iio a wp

instance compile_verified_marrow
  (vpi #pi1 #pi2:pi_type)
  (t1:Type) {| d1:backtranslateable t1 pi1 |} 
  (t2:Type) {| d2:compilable t2 pi2 |}:
  Tot (compilable (ILang.ilang_arrow_typ t1 t2 vpi) vpi) =
  {
  ilang_icomp = ILang.ilang_arrow vpi t1 #d1.ilang_ibtrans t2 #d2.ilang_icomp;

  mcomp = kleisli ~~d1.mbtrans ~~d2.mcomp free.m;

  mlang_mcomp = mlang_ver_arrow d1.mlang_mbtrans d2.mlang_mcomp;

  compile = (fun (f:ILang.ilang_arrow_typ t1 t2 vpi) (x:d1.mbtrans) ->
    let r : unit -> ILang.IIOpi _ vpi = fun () -> (f (d1.backtranslate x)) in
    let tree : dm_iio _ _ = reify_IIOwp r in
    iio_bind tree (fun x -> free.ret (d2.compile x))
  );
}

(** *** Instrumentable arrows **)
instance instrumentable_unverified_marrow 
  ipi #pi1 #pi2
  t1 {| d1:compilable t1 pi1 |}
  t2 {| d2:backtranslateable t2 pi2 |} : 
  instrumentable t1 t2 ipi = {
  minst_in = d1.mcomp;
  minst_out = d2.mbtrans;

  mlang_iinst = mlang_unv_arrow d1.mlang_mcomp d2.mlang_mbtrans;
  ilang_minst = ILang.ilang_arrow ipi t1 #(d1.ilang_icomp) t2 #(d2.ilang_ibtrans);

  instrument = (fun f (x:t1) -> 
    let x' = d1.compile x in
    let dm_tree : dm_iio _ (ILang.pi_hist ipi) = 
      cast_to_dm_iio ipi f x' in
    let r : d2.mbtrans = IIOwp?.reflect dm_tree in
    d2.backtranslate r
  )
}


(** * Model of Secure Interop *)

noeq
type interface = {
  (* intermediate level *)
  ictx_in : Type u#a;
  ictx_out : Type u#b;
  iprog_out : Type u#c; 

  vpi : pi_type;

  (* target level *)
  ctx_in : compilable ictx_in vpi;
  ctx_out : backtranslateable ictx_out vpi;
  prog_out : compilable iprog_out vpi; 
}


(** *** Intermediate Lang **)
type ictx (i:interface) (ipi:pi_type) =  x:i.ictx_in -> ILang.IIOpi i.ictx_out ipi
type iprog (i:interface)  = ictx i i.vpi -> ILang.IIOpi i.iprog_out i.vpi
type iwhole (i:interface) = unit -> ILang.IIOpi i.iprog_out i.vpi

//  vpi  : pi_type; (* the statically verified monitorable property (part of partial program's spec) *)
//  ipi : pi_type;  (* the instrumented monitorable property (part of context's spec) *)

type r_vpi_ipi (vpi ipi:pi_type) = squash (forall h lt. enforced_locally ipi h lt ==> enforced_locally vpi h lt)

(* The interesting thing here is that the context can have a different (stronger) pi than the partial program. *)
let ilink 
  (#i:interface) 
  (#ipi:pi_type) 
  (#_ : r_vpi_ipi i.vpi ipi)
  (ip:iprog i) 
  (ic:ictx i ipi) : 
  iwhole i = 
  fun () -> ip ic

(** *** Target Lang **)
(* will eventually need a signature and what not;
   I think we need to pass the abstract monad inside is we want to support higher-order types.
   in this case I conflated alpha + beta = ct, and gamma + delta = pt *)
type ct (i:interface) (mon:monad) = i.ctx_in.mcomp -> mon.m i.ctx_out.mbtrans
type pt (i:interface) (mon:monad) = mon.m i.prog_out.mcomp

type ctx (i:interface) = mon:monad -> acts mon -> ct i mon
type prog (i:interface) = ctx i -> pt i free

type whole (i:interface) = unit -> iio i.prog_out.mcomp
let link (#i:interface) (p:prog i) (c:ctx i) : whole i = 
  fun () -> p c

(** *** Backtranslate **)
(* Possible issue: backtranslation may be difficult if we allow m at arbitrary places,
   while in F* effects are only allowed at the right or arrows;
   make such kleisli arrows the abstraction instead of m? *)

(** *** Compilation **)
(**[@@ "opaque_to_smt"]
let compile_body  
  (#i:interface)
  (ip:iprog i)
  (ipi:pi_type)
  (#_: r_vpi_ipi i.vpi ipi) 
  (c:ctx i) :
  dm_iio i.iprog_out (ILang.pi_hist i.vpi) = 
  let f : unit -> IIOwp i.iprog_out (ILang.pi_hist i.vpi) = 
    fun () -> ip (backtranslate ipi c) in
  reify_IIOwp f **)

let ctx_instrumentable (i:interface) (ipi:pi_type) : instrumentable i.ictx_in i.ictx_out ipi =
  instrumentable_unverified_marrow
    ipi
    i.ictx_in #i.ctx_in
    i.ictx_out #i.ctx_out

let ctx_backtranslateable (i:interface) (ipi:pi_type) : backtranslateable (ictx i ipi) ipi =
  instrumentable_is_backtranslateable (ctx_instrumentable i ipi)

let ctx_backtranslateable' (i:interface) (ipi:pi_type) : backtranslateable (ictx i i.vpi) ipi =
  admit ();
  ctx_backtranslateable i ipi

let prog_compilable (i:interface) (ipi:pi_type) : compilable (iprog i) i.vpi =
  compile_verified_marrow
    i.vpi
    (ictx i i.vpi) #(ctx_backtranslateable' i ipi)
    i.iprog_out #i.prog_out

let model_compile
  (#i:interface)
  (ip:iprog i)
  (ipi:pi_type)
  (#_: r_vpi_ipi i.vpi ipi) :
  prog i = 
  compile #_ #i.vpi #(prog_compilable i ipi) ip

(** *** Case Studies **)

instance compilable_int #pi : compilable int pi = {
  ilang_icomp = ILang.ilang_int pi;
  mcomp = int;
  mlang_mcomp = mlang_int;
  compile = (fun x -> x);
}

instance backtranslate_int #pi : backtranslateable int pi = {
  mbtrans = int;

  backtranslate = (fun x -> x);

  ilang_ibtrans = ILang.ilang_int pi;
  mlang_mbtrans = mlang_int;
}

assume val thePi : pi_type

let test1 : interface = {
  vpi = thePi;

  (* intermediate level *)
  ictx_in = int;
  ictx_out = int;
  iprog_out = int; 

  ctx_in = compilable_int;
  ctx_out = backtranslate_int;
  prog_out = compilable_int;
}

let iprog1 : iprog test1 = fun c -> (c 5) + 1
let mprog1 : prog test1 = compile #_ #thePi #(prog_compilable test1 thePi) iprog1 
val mctx1 : ctx test1  
let mctx1 (mon:monad) (acts:acts mon) (x:int) : mon.m int =
  mon.ret (x+2)

let mwhole1 = mprog1 `link` mctx1

let _ = mwhole1 () == Return 8

(** new test where ctx accepts an f from prog **)
type icbt = ILang.ilang_arrow_typ int int thePi
type ictxt = ILang.ilang_arrow_typ icbt int thePi

let icbt_comp : compilable icbt thePi = 
  compile_verified_marrow thePi int #(backtranslate_int #thePi) int #(compilable_int #thePi)

let ictxt_instrum : instrumentable icbt int thePi = 
  instrumentable_unverified_marrow thePi icbt #icbt_comp int #(backtranslate_int #thePi) 

let ictxt_btrans : backtranslateable ictxt thePi =
  instrumentable_is_backtranslateable ictxt_instrum

type iprogt = ictxt -> ILang.IIOpi int thePi

let prog_comp : compilable iprogt thePi =
  compile_verified_marrow thePi ictxt #ictxt_btrans int #(compilable_int #thePi)
let someProg : iprogt = fun c -> (c (fun x -> x + 5)) + 1

let mprog : prog_comp.mcomp = compile #_ #thePi #prog_comp someProg

(** TODO: problem!! f's output type should be mon.m int, not free.m. **)
val mctx : ictxt_btrans.mbtrans
let mctx (mon:monad) (acts:acts mon) (f:int -> mon.m int) : mon.m int =
  mon.ret (f 2)


(** ** Criterias **)
(** *** Behaviors **)
(* A trace property is a set of pairs between a trace and a result. 
   The trace is a complete trace. *)

(* `hist_post a` is the type of post-condtions over the local trace and the final result.
   Since, it has the same type as our definition of a trace property, we use 
   hist_post a as the type for trace properties. *)
type trace_property (a:Type) = hist_post #event a

(* We define `beh` that returns the set of traces produced by a whole program.
   Since whole programs start with the empty trace, thus, the
   local trace that the post-condtion describes is the complete trace.

   `theta` is a weakest precondtion monad, and we need it to be
   a post-condition. Looking at Kenji's thesis, we can apply the
   'backward predicate transformer 2.3.4' and the 
   'pre-/postcondition transformer 2.3.2' to obtain
   the 'set' of traces produces by the whole program. *)
let _beh  #a (d:iio a) : trace_property a = 
  fun lt (r:a) -> 
   (* We verify specs of whole programs, thus, instead of having
      properties forall histories, we can specialize it for the
      empty history *)
    forall p. dm_iio_theta d p [] ==> p lt r

(* TODO: the two sets have the same type, which is a limitation since:
         1) our traces do not contain the result
         2) the type between target and source can be different *)
let subset_of (s1:trace_property 'a) (s2:trace_property 'a) =
  (* TODO: using hist_post_ord implies that the trace and the result are part of s2.
           maybe we can simply our life for now by having just the trace **)
  s1 `hist_post_ord` s2

let included_in (tr:trace * 'a) (s1:trace_property 'a) =
  s1 (fst tr) (snd tr) 
  
let _produces (d:iio 'a) (tr:trace * 'a) =
  tr `included_in` (_beh d)

let pi_to_set #a (pi:pi_type) : trace_property a = fun lt _ -> enforced_locally pi [] lt

(** **** Helpers **)
let ibeh (#i:interface) (d:iwhole i) : trace_property i.iprog_out = 
  _beh (reify_IIOwp d)

(* d has this type to accomodate both whole and iwhole programs. **)
let beh  #a (d:unit -> iio a) : trace_property a = 
  _beh (d ())

let produces (d:unit -> iio 'a) (tr:trace * 'a) =
  (d ()) `_produces` tr

let iproduces (#i:interface) (d:iwhole i) (tr:trace * i.prog_out.mcomp) =
  exists r'. compile #_ #_ #i.prog_out r' == snd tr /\ (reify_IIOwp d) `_produces` (fst tr, r')

(** *** Soundness *)
let soundness (i:interface) (ip:iprog i) (c:ctx i) : Type0 =
  lemma_free_acts ();
  beh (model_compile ip i.vpi `link` c) `subset_of` (pi_to_set i.vpi)

let lemma_dm_iio_theta_is_lax_morphism_bind (#a:Type u#a) (#b:Type u#b) (m:iio a) (f:a -> iio b) :
  Lemma
    (hist_bind (dm_iio_theta m) (fun x -> dm_iio_theta (f x)) `hist_ord` dm_iio_theta (iio_bind m f)) = 
    DMFree.lemma_theta_is_lax_morphism_bind iio_wps m f

let soundness_proof (i:interface) (ip:iprog i) (c:ctx i) : Lemma (soundness i ip c) = 
  let lhs : dm_iio i.iprog_out (ILang.pi_hist i.vpi) = (compile_body ip i.vpi #_ c) in
  let rhs : x:i.iprog_out -> dm_iio i.prog_out (hist_return (compile'' i x))  = fun x -> Mkmonad?.ret free (compile'' i x) in
  let p1 : hist_post i.iprog_out = (fun lt _ -> enforced_locally i.vpi [] lt) in
  let p1' : hist_post i.prog_out = (fun lt _ -> enforced_locally i.vpi [] lt) in

  assert (dm_iio_theta lhs p1 []);
  calc (==>) {
    dm_iio_theta lhs p1 [];
    ==> {  
      let p2 : hist_post i.iprog_out = 
      	(fun lt r ->
	   dm_iio_theta (Mkmonad?.ret free (compile'' i r))
	     (fun lt' (_:i.prog_out) -> enforced_locally i.vpi [] (lt @ lt'))
             (rev lt @ [])) in
      assert (p1 `hist_post_ord` p2) (* using monotonicity **)
    }
    dm_iio_theta 
       lhs
       (fun lt r ->
         dm_iio_theta (rhs r)
           (fun lt' _ -> enforced_locally i.vpi [] (lt @ lt'))
           (rev lt @ []))
       [];
    == { _ by (norm [delta_only [`%hist_bind;`%hist_post_bind;`%hist_post_shift]; iota]) }
    hist_bind (dm_iio_theta lhs) (fun x -> dm_iio_theta (rhs x)) (fun lt (_:i.prog_out) -> enforced_locally i.vpi [] lt) [];
    == {}
    hist_bind (dm_iio_theta lhs) (fun x -> dm_iio_theta (rhs x)) p1' [];
    ==> { lemma_dm_iio_theta_is_lax_morphism_bind lhs rhs }
    dm_iio_theta #i.prog_out (iio_bind lhs rhs) p1' [];
  };
  assert (dm_iio_theta (iio_bind lhs rhs) p1' []);
  introduce forall lt r. (forall p. dm_iio_theta (iio_bind lhs rhs) p [] ==> p lt r) ==> enforced_locally i.vpi [] lt with begin
    introduce (forall p. dm_iio_theta (iio_bind lhs rhs) p [] ==> p lt r) ==> enforced_locally i.vpi [] lt with q1. begin
      eliminate forall p. dm_iio_theta (iio_bind lhs rhs) p [] ==> p lt r with p1';
      assert (p1' lt r);
      assert (enforced_locally i.vpi [] lt)
    end
  end;
  assert (soundness i ip c) by (assumption ())


let lemma_beh_bind_of_tot (m:iio 'a) (f:'a -> Tot 'b) (tr:trace * 'b) :
  Lemma 
    (requires (iio_bind m (fun x -> Return (f x))) `_produces` tr)
    (ensures  (exists r'. f r' == snd tr /\ m `_produces` (fst tr, r'))) =
    admit ()

let lemma_beh_bind_of_tot_dual (m:iio 'a) (f:'a -> Tot 'b) (tr:trace * 'b) :
  Lemma 
    (requires  (exists r'. f r' == snd tr /\ m `_produces` (fst tr, r')))
    (ensures ((iio_bind m (fun x -> Return (f x))) `_produces` tr)) =
    admit ()

(** *** RTC **)
let rtc (i:interface) (ip:iprog i) (c:ctx i) (tr:trace * i.prog_out) =
  ((compile ip i.vpi) `link` c) `produces` tr ==> 
    (exists (ic:ictx i i.vpi). (ip `ilink` ic) `iproduces` tr)

let rtc_proof (i:interface) (ip:iprog i) (c:ctx i) (tr:trace * i.prog_out) : Lemma (rtc i ip c tr) =
  let ws = (compile ip i.vpi) `link` c in
  let wt = fun ic -> (ip `ilink` ic) in
  introduce ws `produces` tr ==> (exists (ic:ictx i i.vpi). wt ic `iproduces` tr) with s. begin
    let ic = (backtranslate i.vpi c) in
    introduce exists (ic:ictx i i.vpi). wt ic `iproduces` tr with ic and begin
      let m = compile_body ip i.vpi c in
      assert (ws `produces` tr);
      assert (iio_bind m (fun x -> Return (compile'' i x)) `_produces` tr) by (assumption ());
      lemma_beh_bind_of_tot m (compile'' i) tr;
      assert (wt ic `iproduces` tr) by (
        norm [delta_only [`%iproduces;`%produces;`%beh;`%link;`%ilink]; iota];
        binder_retype (nth_binder (-1));
          norm [delta_only [`%compile_body];iota];
        trefl ();
       assumption ()
      )
    end
  end

(** *** RrHC **)
let r_pi (pi:pi_type) : squash (r_vpi_ipi pi pi) by (compute ()) = ()

(* stronger criterion; for which our backtranslation should also work *)
let rrhc (i:interface) (c:ctx i) =
  (exists (ic:ictx i i.vpi).
    (forall (ip:iprog i) (tr:trace * i.prog_out.mcomp).
      ((model_compile ip i.vpi #(r_pi i.vpi)) `link` c) `produces` tr <==>
         (ip `ilink` ic) `iproduces` tr))

let rrhc_proof (i:interface) (c:ctx i) : Lemma (rrhc i c) =
  let ic = backtranslate i.vpi c in
  introduce exists (ic:ictx i i.vpi).
    (forall (ip:iprog i) (tr:trace * i.prog_out).
      ((compile ip i.vpi #(r_pi i.vpi)) `link` c) `produces` tr <==> (ip `ilink #_ #_ #(r_pi i.vpi)` ic) `iproduces` tr)
  with ic and 
  begin
    introduce forall (ip:iprog i) (tr:trace * i.prog_out). 
      ((compile ip i.vpi #(r_pi i.vpi)) `link` c) `produces` tr ==> (ip `ilink #i #_ #(r_pi i.vpi)` ic) `iproduces` tr
    with 
    begin
      rtc_proof i ip c tr
    end;

    introduce forall (ip:iprog i) (tr:trace * i.prog_out). 
      (ip `ilink #i #_ #(r_pi i.vpi)` ic) `iproduces` tr ==> ((compile ip i.vpi #(r_pi i.vpi)) `link` c) `produces` tr
    with 
    begin
      introduce (ip `ilink #i #_ #(r_pi i.vpi)` ic) `iproduces` tr ==>
        ((compile ip i.vpi #(r_pi i.vpi)) `link` c) `produces` tr
      with _.
      begin
        let ws = (compile ip i.vpi) `link` c in
        let wt = fun ic -> (ip `ilink` ic) in
        let m = compile_body ip i.vpi c in
        assert (wt ic `iproduces` tr);
        assert (exists r'. compile'' i r' == snd tr /\ m `_produces` (fst tr, r')) by (assumption ());
        lemma_beh_bind_of_tot_dual m (compile'' i) tr;
        assert (ws `produces` tr) by (
            norm [delta_only [`%iproduces;`%produces;`%beh;`%link;`%ilink]; iota];
            binder_retype (nth_binder (-1));
            norm [delta_only [`%compile_body];iota];
            trefl ();
            assumption ()
        )
      end
    end
  end

(** *** RrHP **)
(* To state RrHP we need relations between the results and I am not sure if it is worth 
   doing that since we proved RrHC *)
type hyperproperty (a:Type) = trace_property a -> Type0

let rel (#i:interface) (p:trace_property i.iprog_out) : trace_property i.prog_out =
  fun t (r:i.prog_out) -> exists r'. compile'' i r' == r /\ p t r'
  
let rrhp (i:interface) (h:hyperproperty i.prog_out) (ip:iprog i) =
  (forall (ic:ictx i i.vpi). (h (rel (ibeh (ip `ilink` ic))))) ==> 
    (forall c. (h (beh ((compile ip i.vpi) `link` c))))

let rrhc_g (i:interface) = forall c. rrhc i c
let rrhp_g (i:interface) = forall h ip. rrhp i h ip

let lemma_rrhc_eq_rrhp (i:interface) : Lemma (rrhc_g i <==> rrhp_g i) = 
  introduce rrhc_g i ==> rrhp_g i with _. begin
    admit ()
  end;
  introduce rrhp_g i ==> rrhc_g i with _. begin
    admit ()
  end

(** *** Transparency **)
let transparency (i:interface) (ip:iprog i) (c:ctx i) (tr:trace * i.prog_out.mcomp) (ipi:pi_type) (r:r_vpi_ipi i.vpi ipi) =
  ((model_compile ip i.vpi) `link` c) `produces` tr /\ tr `included_in` (pi_to_set #i.prog_out.mcomp ipi) ==>
    ((model_compile ip ipi #r) `link` c) `produces` tr
(* ip:iprog i weakest_pi = the partial program has the weakest spec, thus, it produces any trace 
                           and accepts contexts that also produce any trace that respect the weakest_pi.
   compile ip weakest_pi = compilation gives to the context the free_acts wrapped with minimal checks
   compile ip ipi        = compilation gives to the context the free_acts wrapped with ipi 
   The trick of this statement is that we can instrument the context with any spec stronger than weakest_pi
   because the partial program accepts all of them. This is possible because a context must be instrumented with a pi
   stronger than the one used as spec for the partial program. *)

let lemma_transparency_without_reify (i:interface) (ip:ictx i i.vpi -> dm_iio i.iprog_out (ILang.pi_hist i.vpi)) (c:ctx i) (ipi:pi_type) (r:r_vpi_ipi i.vpi ipi) (p:hist_post i.iprog_out) :
  Lemma
    (requires (dm_iio_theta (ip (backtranslate ipi c)) p []))
    (ensures (dm_iio_theta (ip (backtranslate i.vpi c)) p [])) =
  (* TODO: why is this easy? my first intuition was that it would be easy, but I can not figure out the proof *)
  () 

let lemma_transparency_without_tot (i:interface) (ip:iprog i) (c:ctx i) (ipi:pi_type) (r:r_vpi_ipi i.vpi ipi) (p:hist_post i.iprog_out) :
  Lemma
    (requires (dm_iio_theta (compile_body ip ipi c) p []))
    (ensures (dm_iio_theta (compile_body ip i.vpi c) p [])) by (
    norm [delta_only [`%compile_body];iota];
    ExtraTactics.blowup ();
    bump_nth 4;
    ExtraTactics.rewrite_lemma (-4) (-2);
    assumption ();
    bump_nth 3;
    assumption ()
  )=
  (* TODO: unexpected that I could prove this using tactics. probably unsound since reify is opaque to the SMT *)
  lemma_transparency_without_reify i (fun x -> reify_IIOwp (fun () -> ip x)) c ipi r p

let lemma_iio_theta_bind_of_tot (m:iio 'a) (f:'a -> Tot 'b) (p:hist_post 'b) h :
  Lemma 
    (requires (dm_iio_theta (iio_bind m (fun x -> Return (f x))) p h))
    (ensures  (dm_iio_theta m (fun lt r -> exists r'. f r == r' /\ p lt r') h)) =
    admit ()

let lemma_iio_theta_bind_of_tot_dual (m:iio 'a) (f:'a -> Tot 'b) (p:hist_post 'b) h :
  Lemma 
    (requires  (dm_iio_theta m (fun lt r -> exists r'. f r == r' /\ p lt r') h))
    (ensures (dm_iio_theta (iio_bind m (fun x -> Return (f x))) p h)) =
    admit ()

let lemma_transparency_tot
  (i:interface)
  (ip:iprog i)
  (c:ctx i)
  (ipi:pi_type)
  (r:r_vpi_ipi i.vpi ipi)
  (p:hist_post i.prog_out)
  (f:i.iprog_out -> Tot i.prog_out) :
  Lemma
    (requires (dm_iio_theta (iio_bind (compile_body ip ipi c) (fun x -> Return (f x))) p []))
    (ensures (dm_iio_theta (iio_bind (compile_body ip i.vpi c)( fun x -> Return (f x))) p [])) =
  let p' : hist_post i.iprog_out = (fun lt r -> exists r'. f r == r' /\ p lt r') in
  lemma_iio_theta_bind_of_tot (compile_body ip ipi c) f p [];
  lemma_transparency_without_tot i ip c ipi r p';
  lemma_iio_theta_bind_of_tot_dual (compile_body ip i.vpi c) f p []
  
let lemma_transparency_unfolded 
  (i:interface)
  (ip:iprog i)
  (c:ctx i)
  (ipi:pi_type)
  (r:r_vpi_ipi i.vpi ipi)
  (p:hist_post i.prog_out) :
  Lemma
    (requires (dm_iio_theta (iio_bind (compile_body ip ipi c) (fun x -> Return (compile'' i x))) p []))
    (ensures (dm_iio_theta (iio_bind (compile_body ip i.vpi c)( fun x -> Return (compile'' i x))) p [])) =
  lemma_transparency_tot i ip c ipi r p (compile'' i)
  
let transparency_proof (i:interface) (ip:iprog i) (c:ctx i) (tr:trace * i.prog_out) (ipi:pi_type) (r:r_vpi_ipi i.vpi ipi) : Lemma (transparency i ip c tr ipi r) =
  introduce ((compile ip i.vpi) `link` c) `produces` tr /\ tr `included_in` (pi_to_set #i.prog_out ipi) ==>
    ((compile ip ipi #r) `link` c) `produces` tr
  with q1. 
  begin
    introduce forall (p: hist_post i.prog_out).
      dm_iio_theta (link (compile ip ipi) c ()) p [] ==> p (fst tr) (snd tr)
    with
    begin
      introduce dm_iio_theta (link (compile ip ipi) c ()) p [] ==> 
        p (fst tr) (snd tr)
      with _. 
      begin
        eliminate dm_iio_theta (link (compile ip i.vpi) c ()) p [] ==> 
          p (fst tr) (snd tr)
        with
        begin
          assert (dm_iio_theta (iio_bind (compile_body ip ipi c) (fun x -> Return (compile'' i x))) p []) by (assumption ());
          lemma_transparency_unfolded i ip c ipi r p;
          assert (dm_iio_theta (link (compile ip i.vpi) c ()) p []) by (assumption ())
        end
      end
    end
  end
