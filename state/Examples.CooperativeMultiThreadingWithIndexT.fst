module Examples.CooperativeMultiThreadingWithIndexT

open FStar.Tactics
open FStar.Tactics.Typeclasses

open SharedRefs
open Witnessable
open PolyIface
open SpecTree
open HigherOrderContracts
open Compiler
open CooperativeMultiThreadingWithIndexT


(* Calling SecRef* on it *)

(**
instance witnessable_atree a3p t {| c:witnessable t |} : witnessable (atree a3p t) = {
  satisfy = (fun _ pred -> True);
}**)

instance poly_iface_atree a3p t {| c:poly_iface a3p t |} : poly_iface a3p (atree a3p t) = {
  wt = witnessable_atree a3p t #c.wt;
}

instance witnessable_continuation a3p t {| c:witnessable t |} : witnessable (continuation a3p t) =
  witnessable_arrow unit (atree a3p t) _ _

instance poly_iface_continuation a3p t {| c:poly_iface a3p t |} : poly_iface a3p (continuation a3p t) =
  poly_iface_arrow a3p unit (atree a3p t #c.wt)

let tgt_typ_run (a3p:threep) =
  mk_poly_arrow a3p ((int * int) * list (t_task a3p)) #(witnessable_pair _ _ #(witnessable_list _ #(witnessable_arrow (ref int) _ _ _))) (resexn int)

instance poly_iface_t_task a3p : poly_iface a3p (t_task a3p) =
  poly_iface_arrow a3p (ref int) #(poly_iface_ref a3p int) (continuation a3p unit) #(poly_iface_continuation a3p unit)

(** stuck here: **)
instance poly_iface_run (a3p:threep) : poly_iface a3p (tgt_typ_run a3p) =
  poly_iface_arrow
    a3p
    ((int * int) * list (t_task a3p))
    #(poly_iface_pair a3p
      (int * int) #(poly_iface_pair a3p int #solve int #solve)
      (list (t_task a3p))
      #(poly_iface_list a3p (t_task a3p) #(poly_iface_t_task a3p)))
    (resexn int)
    #(poly_iface_resexn a3p int #(poly_iface_int a3p))

let src_run_type (a3p:threep) =
  mk_poly_arrow a3p
    ((nat * int) * l:(list (t_task a3p)){List.Tot.length l > 0})
    #(witnessable_pair
      (nat * int)
      #(witnessable_pair nat #(witnessable_refinement int (fun x -> x >= 0)) int)
      (l:(list (t_task a3p)){List.Tot.length l > 0})
      #solve)
    (resexn int) #solve

let exportable_run_type (a3p) : exportable_from a3p (src_run_type a3p) Leaf = {
  c_styp = solve;
  ityp = tgt_typ_run a3p;
  c_ityp = poly_iface_run a3p;
  export = (fun _ (f:src_run_type a3p) ((fuel, init), tasks) ->
    if fuel >= 0 && List.Tot.Base.length tasks > 0 then
      (f ((fuel, init), tasks))
    else Inr (Contract_failure "fuel, or tasks not good")
  );
  lemma_export_preserves_prref = (fun _ _ -> ())
}

let sit : src_interface2 = {
  specs = (fun _ -> Leaf);
  hocs = Leaf;
  pt = (fun a3p -> src_run_type a3p);
  c_pt = (fun a3p -> exportable_run_type a3p);
}

val run' : prog_src2 sit
let run' args = Inl (run args)

let compiled_prog = compile_pprog2 #sit run'

val some_ctx : ctx_tgt2 (comp_int_src_tgt2 sit)
let some_ctx read write alloc run =
  admit (); (* TODO: continuation has to be refactored to be polymorphic in a3p *)
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
