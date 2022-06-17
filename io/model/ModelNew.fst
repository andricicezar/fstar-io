module ModelNew

open FStar.List.Tot
open FStar.Calc
open FStar.Tactics

open IO.Sig
open Common
open ExtraTactics
open TC.Monitorable.Hist
open ILang
open MLang
open ILang.CompileTo.MLang
open MLang.InstrumentTo.ILang

noeq type model_type = {
  interface : Type;

  prog_s  : i:interface -> Type;
  ctx_s   : i:interface -> Type;
  whole_s : i:interface -> Type;
  link_s  : (#i:interface) ->
            ctx_s i -> prog_s i -> Tot (whole_s i);

  prog_t  : i:interface -> Type;
  ctx_t   : interface -> Type;
  whole_t : interface -> Type;
  link_t  : (#i:interface) ->
            ctx_t i -> prog_t i -> Tot (whole_t i);

  compile_prog  : (#i:interface) ->
                  prog_s i -> Tot (prog_t i);
}

noeq type interface = {
  ctx_arg : Type;
  ctx_ret : Type;

  pi : monitorable_prop;
  piprop : squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h);

  compilable_ctx_arg : compilable ctx_arg pi;
  backtranslateable_ctx_ret : backtranslateable ctx_ret pi; 

  ret : Type u#0;
  compilable_ret : compilable ret pi;
}

type whole_s (i:interface) =
  x:unit -> IIOpi (resexn i.ret) i.pi

type whole_t (i:interface) =
  unit -> MIIO (resexn i.compilable_ret.comp_out)

type ctx_t (i:interface) =
  unverified_arrow i.compilable_ctx_arg.comp_out i.backtranslateable_ctx_ret.btrans_in i.pi

type ctx_s (i:interface) =
  (x:i.ctx_arg) -> IIOpi (resexn i.ctx_ret) i.pi

type prog_s (i:interface) =
  ctx_s i -> IIOpi (resexn i.ret) i.pi

type prog_t (i:interface) =
  ctx_t i -> MIIO (resexn i.compilable_ret.comp_out)

val link_s  : (#i:interface) -> ctx_s i ->
              prog_s i -> Tot (whole_s i)
let link_s = (fun c p -> (fun _ -> p c))

(** during linking, p expects a context of type ctx_s, but link_t 
gets a context of type ctx_t, therefore, the linker must instrument 
the context. **)
val link_t  : (#i:interface) -> ctx_t i ->
              prog_t i -> Tot (whole_t i)
let link_t #i c p : whole_t i =
  (fun _ -> p c)
  //(instrument #_ #_ #_ #(instrumentable_unverified_arrow _ _ i.pi #i.compilable_ctx_arg #i.backtranslateable_ctx_ret) c))

let backtranslateable_ctx_s (#i:interface) : backtranslateable (ctx_s i) i.pi = 
  instrumentable_is_backtranslateable (
    instrumentable_unverified_arrow 
      i.pi 
      i.ctx_arg 
      #i.compilable_ctx_arg
      i.ctx_ret 
      #i.backtranslateable_ctx_ret)

(** TODO: universe problems. it seems that the fact that 
compile is in universe 0 bites us **)
val compile_prog : (#i:interface) -> prog_s i -> Tot (prog_t i)
let compile_prog #i p : prog_t i =
  compile #(prog_s i) #_ #(
    compile_verified_arrow
      i.pi 
      (ctx_s i) #(backtranslateable_ctx_s #i)
      i.ret #i.compilable_ret
    ) p

let model : model_type = { 
  interface = interface;

  prog_s  = prog_s;
  ctx_s   = ctx_s;
  whole_s = whole_s;
  link_s  = link_s;

  prog_t  = prog_t;
  ctx_t   = ctx_t;
  whole_t = whole_t;
  link_t  = link_t;

  compile_prog = compile_prog; 
}
