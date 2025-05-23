module Examples.CooperativeMultiThreadingWithIndexT

open FStar.Tactics
open FStar.Tactics.Typeclasses

open LabeledRefs
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

instance witnessable_t_task a3p : witnessable (t_task a3p) =
  witnessable_arrow (ref int) (continuation a3p unit) _ _

instance poly_iface_t_task a3p : poly_iface a3p (t_task a3p) =
  poly_iface_arrow a3p (ref int) #(poly_iface_ref a3p int) (continuation a3p unit) #(poly_iface_continuation a3p unit)

type arg_type a3p =
  ((nat * int) * l:(list (t_task a3p)){List.Tot.length l > 0})

type wit_arg_type a3p : witnessable (arg_type a3p) =
  (witnessable_pair
    (nat * int)
    #(witnessable_pair nat #(witnessable_refinement int (fun x -> x >= 0)) int)
    (l:(list (t_task a3p)){List.Tot.length l > 0})
    #(witnessable_refinement
      _
      #(witnessable_list _ #(witnessable_t_task a3p))
      (fun l -> List.Tot.length l > 0)))

let src_run_type (a3p:threep) =
  mk_poly_arrow
    a3p
    (arg_type a3p)
    #(wit_arg_type a3p)
    (resexn int)
    #(witnessable_resexn int #witnessable_int)

let run_type_spec (a3p:threep) : spec =
  Spec true true
    (arg_type a3p)
    (importable_pair a3p

      (nat & int)
      (EmptyNode Leaf Leaf)
      #(importable_pair a3p
        nat
        Leaf
        #(importable_refinement a3p int Leaf #(safe_importable_is_importable a3p _ Leaf #(safe_importable_int a3p)) (fun n -> n >= 0) (fun n -> n >= 0))
        int
        Leaf
        #(safe_importable_is_importable a3p _ Leaf #(safe_importable_int a3p)))
      (l: list (t_task a3p) {List.Tot.Base.length l > 0})
      Leaf
      #(importable_refinement a3p
        (list (t_task a3p))
        Leaf
        #(safe_importable_is_importable a3p _ Leaf #(poly_iface_is_safely_importable a3p _ #(poly_iface_list a3p _ #(poly_iface_t_task a3p))))
        (fun l -> List.Tot.length l > 0)
        (fun l -> List.Tot.length l > 0))).c_styp
    (pre_poly_arrow a3p #_ #(witnessable_pair (nat & int) #(witnessable_pair nat #(witnessable_refinement int (fun n -> n >= 0)) int) (l: list (t_task a3p) {List.Tot.Base.length l > 0})))
    int
    witnessable_int
    (fun _ -> post_poly_arrow a3p)

let run_type_st a3p : spec_tree =
  (Node (U10 (run_type_spec a3p))
    (EmptyNode (EmptyNode Leaf Leaf) Leaf)
    Leaf)

let exportable_run_type (a3p:threep) : exportable_from a3p (src_run_type a3p) (run_type_st a3p) =
  exportable_arrow_err10 a3p
    ((nat * int) * l:(list (t_task a3p)){List.Tot.length l > 0})
    _
    #(importable_pair a3p
      _ _
      #(importable_pair a3p
        _ _
        #(importable_refinement a3p int Leaf #(safe_importable_is_importable a3p _ Leaf #(safe_importable_int a3p)) (fun n -> n >= 0) (fun n -> n >= 0))
        _ _
        #(safe_importable_is_importable a3p _ Leaf #(safe_importable_int a3p)))
      (l: list (t_task a3p) {List.Tot.Base.length l > 0})
      _
      #(importable_refinement a3p
        (list (t_task a3p))
        Leaf
        #(safe_importable_is_importable a3p _ Leaf #(poly_iface_is_safely_importable a3p _ #(poly_iface_list a3p _ #(poly_iface_t_task a3p))))
        (fun l -> List.Tot.length l > 0)
        (fun l -> List.Tot.length l > 0)))
    _ _ #(exportable_int a3p)
    _
    _

let rec lemma_always_satisfy_list_t_task a3p (l:(list (t_task a3p))) :
  Lemma ((witnessable_list _ #(witnessable_t_task a3p)).satisfy l (prref a3p)) =
  match l with
  | [] -> ()
  | hd::tl -> lemma_always_satisfy_list_t_task a3p tl

let lemma_always_satisfy_arg_type a3p (x:arg_type a3p) :
  Lemma ((wit_arg_type a3p).satisfy x (prref a3p)) =
  let (_, l) = x in
  lemma_always_satisfy_list_t_task a3p l

let hoc_check : hoc c3p (run_type_spec c3p) =
 EnforcePre
   (fun x ->
     let eh0 = get_heap () in
     let check : cb_check c3p _ _ (pre_poly_arrow c3p #((run_type_spec c3p).argt) #(run_type_spec c3p).wt_argt) (fun x _ _ h1 -> (run_type_spec c3p).pre x h1) x eh0 =
       (fun () ->
         lemma_always_satisfy_arg_type c3p x;
         Inl ()) in
     (| eh0, check |)   )
   (fun x r -> ())

let hoc_check_pck : pck_uhoc c3p =
  (| U10 (run_type_spec c3p), U10hoc hoc_check |)

let sit : src_interface2 = {
  specs = run_type_st;
  hocs = Node hoc_check_pck (EmptyNode (EmptyNode Leaf Leaf) Leaf) Leaf;
  pt = src_run_type;
  c_pt = exportable_run_type;
}

val run' : prog_src2 sit
let run' args = Inl (run args)

let compiled_prog = compile_pprog2 #sit run'

let rec lemma_forall_in_list_true (l:list 'a) :
  Lemma (forall_in_list l (fun _ -> True)) =
  match l with
  | [] -> ()
  | _::tl -> lemma_forall_in_list_true tl

let res_a #a3p
  (read :  ttl_read a3p)
  (write : ttl_write a3p)
  (alloc : ttl_alloc a3p)
: t_task a3p =
  fun r () ->
    let () = write r 42 in
    Return ()

let res_b #a3p
  (read :  ttl_read a3p)
  (write : ttl_write a3p)
  (alloc : ttl_alloc a3p)
: t_task a3p =
  fun r () ->
    let j = read r in
    let m = alloc #SNat 42 in
    Yield (fun () ->
        let () = write r j in
        Return ())

val some_ctx : ctx_tgt2 (comp_int_src_tgt2 sit)
let some_ctx #a3p read write alloc my_run =

  let myargs : ((int & int) & list (t_task a3p)) = ((5000,0), [res_a read write alloc; res_b read write alloc]) in
  let h0 = get_heap () in

  match my_run myargs with
  | Inl _ -> 0
  | Inr _ -> -1

let whole : whole_tgt2 =
  link_tgt2 compiled_prog some_ctx

let r = whole ()
let _ =
  match r with
  | 0 -> FStar.IO.print_string "Success\n"
  | _ -> FStar.IO.print_string "Something went wrong!\n"
