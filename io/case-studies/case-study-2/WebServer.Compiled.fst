module WebServer.Compiled

open FStar.Tactics
open FStar.All
open FStar.List.Tot

open Common
open DM
open Model
open Shared
open TC.MLify.MIIO
open WebServer

let extract_local_trace (h':trace) (pi:monitorable_prop) :
  IIO trace pi
    (requires (fun h -> h' `suffix_of` h))
    (ensures (fun h lt' lt ->
      lt == [] /\
      h == (apply_changes h' lt'))) =
  let h = get_trace () in
  suffix_of_length h' h;
  let n : nat = (List.length h) - (List.length h') in
  let (lt', ht) = List.Tot.Base.splitAt n h in
  lemma_splitAt_equal n h;
  lemma_splitAt_suffix h h';
  List.Tot.Properties.rev_involutive lt';
  assert (h == apply_changes h' (List.rev lt'));
  List.rev lt'

let enforce_post
  (#i:interface)
  (#pi:monitorable_prop)
  (f:i.ctx_arg -> IIO (maybe i.ctx_ret) pi (fun _ -> True) (fun _ _ _ -> true))
  (x:i.ctx_arg) :
  IIO (maybe i.ctx_ret) pi (fun _ -> True) (i.ctx_post x)  =
  let h = get_trace () in
  let r : maybe i.ctx_ret = f x in
  Classical.forall_intro (lemma_suffixOf_append h);
  let lt = extract_local_trace h pi in
  Classical.forall_intro_2 (Classical.move_requires_2 (lemma_append_equals h));
  if i.ctx_post_c.check4 x h r lt then r
  else Inr Contract_failure

let compiled_webserver : prog_t i pi = comp.compile_prog #i #pi webserver
val compiled_webserver' : (file_descr -> Tot (maybe unit)) -> MIIO (maybe unit)
let compiled_webserver' f = compiled_webserver (enforce_post #i #pi f)

let compiled_webserver'' : (Types.file_descr -> Tot (maybe unit)) -> ML (maybe unit) = 
  mlify
    #((Types.file_descr -> Tot (maybe unit)) -> MIIO (maybe unit))
    #(mlifyable_tot_miio file_descr (maybe unit) (maybe unit) #TC.Export.ml_file_descr)
    compiled_webserver'
