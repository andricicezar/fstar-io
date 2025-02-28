module Examples.CooperativeMultiThreadingWithIndexT

open FStar.Tactics
open FStar.Tactics.Typeclasses

open SharedRefs
open Witnessable
open TargetLang
open SpecTree
open TargetLang
open HigherOrderContracts
open Compiler
open CooperativeMultiThreadingWithIndexT


(* Calling SecRef* on it *)

instance witnessable_atree (r:ref int) t {| c:witnessable t |} : witnessable (atree r t) = {
  satisfy = (fun _ pred -> pred r);
}

instance witnessable_continuation (r:ref int) t {| c:witnessable t |} : witnessable (continuation r t) = {
  satisfy = (fun _ pred -> pred r);
}

instance witnessable_rcontinuation t {| c:witnessable t |} : witnessable (r:ref int -> continuation r t) = {
  satisfy = (fun _ pred -> True);
}

instance targetlang_atree pspec (r:ref int) t {| c:targetlang pspec t |} : targetlang pspec (atree r t) = {
  wt = witnessable_atree r t #c.wt;
}

instance targetlang_continuation pspec (r:ref int) t {| c:targetlang pspec t |} : targetlang pspec (continuation r t) = {
  wt = witnessable_continuation r t #c.wt;
}

instance targetlang_rcontinuation pspec t {| c:targetlang pspec t |} : targetlang pspec (r:ref int -> continuation r t) = {
  wt = witnessable_rcontinuation t #c.wt;
}

let tgt_typ_run pspec =
  mk_targetlang_arrow pspec ((int * int) * list (r:(ref int) -> (continuation r unit))) (resexn int)

instance targetlang_run pspec
  : targetlang pspec (tgt_typ_run pspec) =
  targetlang_arrow pspec ((int * int) * list (r:(ref int) -> (continuation r unit))) (resexn int)
    #(targetlang_pair pspec (int * int) (list (r:(ref int) -> (continuation r unit)))
      #solve
      #(targetlang_list pspec (r:(ref int) -> (continuation r unit)) #solve))
    #(targetlang_sum pspec int err #solve #(targetlang_err pspec))

let src_run_type (pspec:targetlang_pspec) =
  (mk_targetlang_arrow pspec ((nat * int) * l:(list (r:(ref int) -> (continuation r unit))){List.Tot.length l > 0})
    #(witnessable_pair (nat * int) (l:(list (r:(ref int) -> (continuation r unit))){List.Tot.length l > 0})
      #(witnessable_pair nat int #(witnessable_refinement int (fun x -> x >= 0))) #solve)
    (resexn int) #solve)

let exportable_run_type (pspec) : exportable_from pspec (src_run_type pspec) Leaf = {
  c_styp = solve;
  ityp = tgt_typ_run pspec;
  c_ityp = targetlang_run pspec;
  export = (fun _ (f:src_run_type pspec) ((fuel, init), tasks) ->
    if fuel >= 0 && List.Tot.Base.length tasks > 0 then
      (f ((fuel, init), tasks))
    else Inr (Contract_failure "fuel, or tasks not good")
  );
  lemma_export_preserves_prref = (fun _ _ _ -> ())
}

let sit : src_interface2 = {
  specs = (fun _ -> Leaf);
  hocs = Leaf;
  pt = (fun pspec -> src_run_type pspec);
  c_pt = (fun pspec -> exportable_run_type pspec);
}

val run' : prog_src2 sit
let run' args = Inl (run args)

let compiled_prog = compile_pprog2 #sit run'

val some_ctx : ctx_tgt2 (comp_int_src_tgt2 sit)
let some_ctx inv prref hrel read write alloc run =
  admit (); (* TODO: continuation has to be refactored to be polymorphic in pspec *)
  let res_a (r : ref int) : continuation r unit = (fun () ->
    let () = write r 42 in
    Return ()) in

  let res_b (r : ref int) : continuation r unit = (fun () ->
    let j = read r in
    let m = alloc #SNat 42 in
    Yield (fun () ->
        let () = write r j in
        Return ())) in

  match run ((5000,0),[res_a; res_b]) with
  | Inl _ -> 0
  | Inr _ -> -1

let whole : whole_tgt2 =
  link_tgt2 compiled_prog some_ctx

let r = whole ()
let _ =
  match r with
  | 0 -> FStar.IO.print_string "Success\n"
  | _ -> FStar.IO.print_string "Something went wrong!\n"
