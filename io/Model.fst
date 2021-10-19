module Model

open FStar.List.Tot
open FStar.Calc
open FStar.Tactics


open Free.IO
open Common
open ExtraTactics
open Checkable
open DM
open Instrument

noeq type compiler = {
  interface : Type;
  set_of_traces : Type -> Type;
  monitorable_prop : Type;

  prog_s  : interface -> monitorable_prop -> Type;
  ctx_s   : interface -> monitorable_prop -> Type;
  whole_s : interface -> monitorable_prop -> Type;
  link_s  : (#i:interface) -> (#pi:monitorable_prop) ->
            ctx_s i pi -> prog_s i pi -> Tot (whole_s i pi);

  prog_t  : interface -> monitorable_prop -> Type;
  ctx_t   : interface -> Type;
  whole_t : interface -> Type;
  link_t  : (#i:interface) -> (#pi:monitorable_prop) ->
            ctx_t i -> prog_t i pi -> Tot (whole_t i);

  compile_prog  : (#i:interface) -> (#pi:monitorable_prop) ->
                  prog_s i pi -> Tot (prog_t i pi);
}

noeq type interface = {
  ctx_arg : Type;
  ctx_ret : Type;
  ctx_post :
    ctx_arg -> trace -> maybe ctx_ret -> trace -> Type0;
  ctx_post_c : checkable4 ctx_post;

  ret : Type;
}

(** The whole program does not need a pre-condition. 

Also, a post-condition would be useless since the system/
environment can not use it. **)

val whole_pre' : unit -> trace -> bool
let whole_pre' _ h = true 

val whole_pre : unit -> trace -> Type0
let whole_pre x h = whole_pre' x h

let whole_pre_cc : checkable2 whole_pre =
  general_is_checkable2 unit trace whole_pre'

type whole_s (i:interface) (pi:monitorable_prop) =
  x:unit -> IIO i.ret pi (whole_pre x) (fun _ _ _ -> True)
type whole_t (i:interface) = unit -> MIIO (maybe i.ret)

(** Having a pre-condition for the context is not necessary,
because the context would not know about it. 
If we set a pre-condition for the context, the pre-condition 
is more of a promise that the partial-program has to fulfil.

We make the following remarks about a context's post-condition:
* If the post-condition is only about the returned result, then
  the post-condition should be written as a refinement on the type
  of the result.
* At runtime, the post-condition is verified after the execution of
  the context is over. Therefore, a safety property stated
  in the post-condition would lose its 'safety' when checked at runtime,
  because unsafe behavior could happen before the check happens.
* a post-condition is needed. e.g.:
  if the returned value is a file descriptor and the 
  post-condition guarantees: "the returned file descriptor is open".
**)

let tpre : (i:interface) -> (i.ctx_arg -> trace -> bool) = fun i x h -> true
type ctx_t (i:interface) = i.ctx_arg -> MIO i.ctx_ret
(** The ctx_s stands for the instrumented context, therefore the
    output type is different compared to ctx_t.
    ctx_t has the output type `i.ctx_ret`, but ctx_s has `maybe i.ctx_ret`.
    This is needed to accomodate the possibility of failure during 
    instrumentation when a contract is violated. **)
type ctx_s (i:interface) (pi:monitorable_prop) =
  (x:i.ctx_arg) -> IIO (maybe i.ctx_ret) pi (fun h -> tpre i x h) (i.ctx_post x)

(** The partial program does not need a pre- or a post-condition because
    it is the starting point of the execution in this model. **)
type prog_s (i:interface) (pi:monitorable_prop) =
  ctx_s i pi -> IIO i.ret pi (fun _ -> True) (fun _ _ _ -> True)
(** compared to prog_s, prog_t can fail because it has to check the
    history with which it starts. prog_t is prog_s wrapped in a new 
    function which adds a runtime check for verifying if pi was 
    respected until now **)
type prog_t (i:interface) (pi:monitorable_prop) =
  ctx_s i pi -> MIIO (maybe i.ret)

let extract_local_trace (h:trace) (pi:monitorable_prop) :
  IIO trace pi
    (requires (fun h' -> True)) // suffix_of h h'))
    (ensures (fun h' r lt ->
      lt == [] /\
      h' == (apply_changes h r)))
  =
  admit ();
  let h' = get_trace () in
  suffix_of_length h h';
  let n : nat = (List.length h') - (List.length h) in
  let (lt, ht) = List.Tot.Base.splitAt n h' in
  assume (lt @ ht == h');
  assume (ht == h);
  List.Tot.Properties.rev_involutive lt;
  assert (h' == apply_changes h (List.rev lt));
  List.rev lt

(** CA: The body of this function was inlined in `instrument` but the block
if-then-else added some extra weird goals which did not make sense,
therefore a fast fix was extracting the block in a different function. **)
let enforce_post
  (#t1:Type)
  (#t2:Type)
  (post:t1 -> trace -> maybe t2 -> trace -> Type0)
  {| d4:checkable4 post |}
  (x:t1)
  (h:trace)
  (r:maybe t2)
  (lt:trace) :
  IIOwp (maybe t2) (fun _ p ->
    let b = check4 #t1 #trace #(maybe t2) #trace #post x h r lt in
    (b ==>  p r []) /\
    (~b ==>  p (Inr Contract_failure) [])) =
  if check4 #t1 #trace #(maybe t2) #trace #post x h r lt
  then r
  else (Inr Contract_failure)

let instrument
  (#i  : interface)
  (#pi : monitorable_prop)
  (ct : ctx_t i) :
  Tot (ctx_s i pi) =
  fun (x:i.ctx_arg) ->
    admit ();
    let h : trace = get_trace () in
    let r : maybe i.ctx_ret =
      instrument_MIIO
        (cast_io_iio ((* MIIO.*)reify (ct x) [] (fun _ _ -> True))) pi in
    let lt : trace = extract_local_trace h pi in
    enforce_post #i.ctx_arg #i.ctx_ret i.ctx_post #i.ctx_post_c x h r lt

(**
  Context: During compilation, p is wrapped in a new function
  that first does a runtime check. The runtime check verifies if the 
  history respects pi. 
  
  One possible assumption: Since the partial program is our starting
  point, the history is always empty, and the result of the runtime 
  check is always true. This assumption would simplify the compilation
  since we do not need to add the runtime check.
  But, I do not think that this is a good assumption. I do not think
  that it can be guaranteed that when the partial program starts, the 
  history is empty. 
        let compile_prog'
        (#i  : interface)
        (#pi : monitorable_prop)
        (p  : prog_s i pi) 
        (c : ctx_s i pi) :
        MIIO i.ret by (iio_tactic ()) = 
        assume (get_trace () == []);
        p c
**)

let compile_prog
  (#i  : interface)
  (#pi : monitorable_prop)
  (p  : prog_s i pi) :
  Tot (prog_t i pi) =
  _IIOwp_as_MIIO
    (fun _ -> iio_pre pi)
    (fun _ h r lt -> iio_post pi h r lt)
    p

val link_s  : (#i:interface) -> (#pi:monitorable_prop) -> ctx_s i pi ->
              prog_s i pi -> Tot (whole_s i pi)
let link_s = (fun #i #pi c p -> (fun _ -> p c))

(** during linking, p expects a context of type ctx_s, but link_t 
gets a context of type ctx_t, therefore, the linker must instrument 
the context. **)
val link_t  : (#i:interface) -> (#pi:monitorable_prop) -> ctx_t i ->
              prog_t i pi -> Tot (whole_t i)
let link_t #i #pi c p : whole_t i = (fun _ -> p (instrument #i #pi c))

type set_of_traces (a:Type) = trace * a -> Type0

let comp : compiler = {
  interface = interface;
  set_of_traces = set_of_traces;
  monitorable_prop = monitorable_prop;

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
