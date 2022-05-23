module IIO.CompileTo.ILang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open IO.Sig
open DM.IIO
open TC.Monitorable.Hist
open ILang
open TC.Checkable

class exportable (t : Type u#a) (pi:monitorable_prop) = {
  etype : Type u#a;
  c_etype : ilang etype pi;
  export : t -> etype;
}

class safe_importable (t : Type u#a) (pi:monitorable_prop) = {
  sitype : Type u#a;
  c_sitype : ilang sitype pi;
  safe_import : sitype -> t; 
}


class importable (t : Type u#a) (pi:monitorable_prop) = {
  itype : Type u#a; 
  c_itype : ilang itype pi;
  import : itype -> resexn t;
}


(** *** Exportable instances **)

let mk_exportable (#t1 t2 : Type) {| d1:ilang t2 'pi |} (exp : t1 -> t2) : exportable t1 'pi =
  { etype = t2; c_etype = d1; export = exp; }

instance ilang_is_exportable t {| ilang t 'pi |} : exportable t 'pi =
  mk_exportable t (fun x -> x)

instance exportable_refinement t {| d:exportable t 'pi |} (p : t -> Type0) : exportable (x:t{p x}) 'pi =
  mk_exportable d.etype #d.c_etype export

instance exportable_option
  t1 {| d1:exportable t1 'pi |} :
  Tot (exportable (option t1) 'pi) =
  mk_exportable (option d1.etype) #(ilang_option 'pi d1.etype #d1.c_etype)
    (fun x -> match x with | Some x' -> Some (export x') | None -> None)

instance exportable_pair
  t1 {| d1:exportable t1 'pi |} t2 {| d2:exportable t2 'pi |} :
  Tot (exportable (t1 * t2) 'pi) =
  mk_exportable (d1.etype * d2.etype) #(ilang_pair 'pi d1.etype #d1.c_etype d2.etype #d2.c_etype) (fun (x,y) -> (export x, export y))

instance exportable_either
  t1 {| d1:exportable t1 'pi |} t2 {| d2:exportable t2 'pi |} :
  Tot (exportable (either t1 t2) 'pi) =
  mk_exportable
    (either d1.etype d2.etype)
    #(ilang_either 'pi d1.etype #d1.c_etype d2.etype #d2.c_etype) 
    (fun x -> 
      match x with | Inl x -> Inl (export x) | Inr x -> Inr (export x))

instance ilang_resexn (pi:monitorable_prop) t1 {| d1:ilang t1 pi |} : ilang (resexn t1) pi = { mldummy = () }

(** *** Exportable arrows **)

instance exportable_arrow_with_no_pre_and_no_post
  t1 {| d1:importable t1 'pi |}
  t2 {| d2:exportable t2 'pi |} :
  exportable (t1 -> IIOpi (resexn t2) 'pi) 'pi =
  mk_exportable #_
    #(t1 -> IIOpi (resexn t2) 'pi)
    (d1.itype -> IIOpi (resexn d2.etype) 'pi)
    #(ilang_arrow 'pi d1.itype #d1.c_itype d2.etype #d2.c_etype)
    (fun f (x:d1.itype) -> 
      match import x with
      | Inl x' -> begin
        match f x' with 
        | Inl x'' -> Inl (export x'') 
        | Inr err -> Inr err
      end
      | Inr err -> Inr err)

(** This case does not talk about a post that depends on the input. **)
instance exportable_arrow_with_post
  t1 {| d1:importable t1 'pi |}
  t2 {| d2:exportable t2 'pi |}
  post
  {| d3: monitorable_hist (fun _ _ -> True) post 'pi |} :
  exportable (x:t1 -> DM.IIO.IIO (resexn t2) (fun _ -> True) (post x)) 'pi =
  mk_exportable #_
    #(x:t1 -> DM.IIO.IIO (resexn t2) (fun _ -> True) (post x))
    (d1.itype -> IIOpi (resexn d2.etype) 'pi)
    #(ilang_arrow 'pi d1.itype #d1.c_itype d2.etype #d2.c_etype)
    (fun f -> 
      assume (forall (x: t1) (h: IO.Sig.trace) (lt: IO.Sig.trace) (r':resexn t2).
        (post x h r' lt /\
         (enforced_locally 'pi h lt ==> (exists (r: resexn t2). post x h r lt))) ==>
         enforced_locally 'pi h lt);
      let f' : t1 -> IIOpi (resexn t2) 'pi = f in
      export #_ #'pi #(exportable_arrow_with_no_pre_and_no_post t1 #d1 t2 #d2) f')

let trivialize_new_post_maybe
  (pre:'a -> trace -> bool)
  (post:'a -> trace -> resexn 'b -> trace -> Type0) :
  Tot ('a -> trace -> resexn 'b -> trace -> Type0) =
    fun x h r lt -> 
      (~(pre x h) ==> r == (Inr Contract_failure)) /\
      (pre x h ==> post x h r lt) 
  
let trivialize
  t1 t2
  (pre : t1 -> trace -> Type0) {| d:checkable2 pre |}
  (post : t1 -> trace -> (resexn t2) -> trace -> Type0)
  (f:((x:t1) -> IIO (resexn t2) (pre x) (post x)))
  (x:t1) : 
  IIO (resexn t2) (fun _ -> True) (trivialize_new_post_maybe d.check2 post x) =
  let h = get_trace () in
  if d.check2 x h then f x
  else Inr Contract_failure

let convert222
  #t1
  #t2
  pre {| d3: checkable2 pre |}
  (post:t1 -> trace -> resexn t2 -> trace -> Type0) 
  pi
  (x:squash (forall (x:t1) (h lt:trace). pre x h /\ enforced_locally pi h lt ==> (exists r. post x h r lt))) :
  squash (forall x h lt. enforced_locally pi h lt ==> (exists r. (trivialize_new_post_maybe d3.check2 post) x h r lt)) = 
  introduce forall (x:t1) (h lt:trace). enforced_locally pi h lt ==> (exists r. (trivialize_new_post_maybe d3.check2 post) x h r lt) with begin
    introduce enforced_locally pi h lt ==> (exists r. (trivialize_new_post_maybe d3.check2 post) x h r lt) with _. begin
      assert (pre x h /\ enforced_locally pi h lt ==> (exists r. post x h r lt)) by (
        ignore (ExtraTactics.instantiate_multiple_foralls (nth_binder 6) [binder_to_term (nth_binder 7)]));
      assert (enforced_locally pi h lt);
      assert (pre x h ==> (exists r. post x h r lt));
      admit ()
    end
  end

let convert2
  #t1
  #t2
  pre {| d3: checkable2 pre |}
  (post:t1 -> trace -> resexn t2 -> trace -> Type0) 
  pi (x:monitorable_hist pre post pi) :
  monitorable_hist (fun _ _ ->True) (trivialize_new_post_maybe d3.check2 post) pi = {
    c1post = convert222 pre post pi x.c1post
  }

instance exportable_arrow_with_pre_post
  t1 {| d1:importable t1 'pi |}
  t2 {| d2:exportable t2 'pi |}
  pre {| d3:checkable2 pre |}
  post
  {| d4: monitorable_hist pre post 'pi |} :
  exportable (x:t1 -> DM.IIO.IIO (resexn t2) (pre x) (post x)) 'pi =
  mk_exportable #_
    #(x:t1 -> DM.IIO.IIO (resexn t2) (pre x) (post x))
    (d1.itype -> IIOpi (resexn d2.etype) 'pi)
    #(ilang_arrow 'pi d1.itype #d1.c_itype d2.etype #d2.c_etype)
    (fun f -> 
      export #_ #'pi
        #(exportable_arrow_with_post t1 #d1 t2 #d2 (trivialize_new_post_maybe d3.check2 post) #(convert2 pre post 'pi d4))
        (trivialize t1 t2 pre post f)
    )
    


(** *** Safe importable instances **)
let mk_safe_importable
  (t1 #t2 : Type) {| d1:ilang t1 'pi |}
  (imp : t1 -> t2) :
  Tot (safe_importable t2 'pi) =
  { sitype = t1; c_sitype = d1; safe_import = imp; }

let ilang_is_safely_importable #t (_:ilang t 'pi) : safe_importable t 'pi =
  mk_safe_importable t (fun x -> x)

(** *** Importable instances **)

let mk_importable
  (t1 #t2 : Type) {| d1: ilang t1 'pi |}
  (imp : t1 -> resexn t2) :
  Tot (importable t2 'pi) =
  { itype = t1; import = imp; c_itype = d1 }

instance safe_importable_is_importable t {| d:safe_importable t 'pi |} : importable t 'pi =
  mk_importable d.sitype #t #d.c_sitype
    (fun (x:d.sitype) -> Inl (safe_import x))

instance importable_refinement
  t {| d:importable t 'pi |}
  (rp : t -> Type0) {| checkable rp |} :
  Tot (importable (x:t{rp x}) 'pi) =
  mk_importable
    d.itype
    #_
    #d.c_itype
    (fun (x:d.itype) ->
      (match import x with
      | Inl x ->
        if check #t #rp x then Inl x 
        else Inr Contract_failure
      | Inr err -> Inr err) <: resexn (x:t{rp x}))

instance importable_option
  t {| d:importable t 'pi |} :
  Tot (importable (option t) 'pi) =
  mk_importable
    (option d.itype)
    #_
    #(ilang_option 'pi d.itype #d.c_itype)
    (fun (x:option d.itype) ->
      match x with
      | Some x' -> begin
        match import x' with
        | Inl x'' -> Inl (Some x'')
        | Inr err -> Inr err
      end
      | None -> Inr Contract_failure)

instance importable_pair
  t1 t2 {| d1:importable t1 'pi |} {| d2:importable t2 'pi |} :
  Tot (importable (t1 * t2) 'pi) =
  mk_importable
    (d1.itype * d2.itype)
    #_
    #(ilang_pair 'pi d1.itype #d1.c_itype d2.itype #d2.c_itype)
    (fun (x,y) ->
      match (import x, import y) with
      | (Inl x, Inl y) -> Inl (x, y)
      | _ -> Inr Contract_failure)

instance importable_either
  t1 t2 {| d1:importable t1 'pi |} {| d2:importable t2 'pi |} :
  Tot (importable (either t1 t2) 'pi) =
  mk_importable
    (either d1.itype d2.itype)
    #_
    #(ilang_either 'pi d1.itype #d1.c_itype d2.itype #d2.c_itype)
    (fun x ->
      match x with
      | Inl x' -> begin
        match import x' with
        | Inl x'' -> Inl (Inl x'')
        | Inr err -> Inr err
      end
      | Inr y -> begin
        match import y with
        | Inl y' -> Inl (Inr y')
        | Inr err -> Inr err
      end)

instance importable_dpair_refined
  t1 t2 (p:t1 -> t2 -> Type0)
  {| d1:importable t1 'pi |} {| d2:importable t2 'pi |} {| d3:checkable2 p |} :
  Tot (importable (x:t1 & y:t2{p x y}) 'pi) =
  mk_importable
    (d1.itype & d2.itype)
    #(x:t1 & y:t2{p x y})
    #(ilang_pair 'pi d1.itype #d1.c_itype d2.itype #d2.c_itype)
    (fun ((x', y')) ->
      match (import x', import y') with
       | (Inl x, Inl y) ->
            if check2 #t1 #t2 #p x y then Inl (| x, y |) else Inr Contract_failure
       | _ -> Inr Contract_failure) 


(** *** Safe importable arrows **)
instance safe_importable_resexn
  t1 {| d1:importable t1 'pi |} :
  Tot (safe_importable (resexn t1) 'pi) =
  mk_safe_importable
    (resexn d1.itype)
    #_
    #(ilang_resexn 'pi d1.itype #d1.c_itype)
    (fun x ->
      match x with
      | Inl x' -> import x' 
      | Inr y -> Inr y)

instance safe_importable_arrow
  (t1:Type) {| d1:exportable t1 'pi |}
  (t2:Type) {| d2:importable t2 'pi |} : 
  safe_importable ((x:t1) -> IIOpi (resexn t2) 'pi) 'pi =
  mk_safe_importable
    (d1.etype -> IIOpi (resexn d2.itype) 'pi)
    #((x:t1) -> IIOpi (resexn t2) 'pi)
    #(ilang_arrow 'pi d1.etype #d1.c_etype d2.itype #d2.c_itype)
    (fun f (x:t1) -> 
      (let x' = export x in 
      safe_import #_ #'pi #(safe_importable_resexn t2 #d2) (f x')))

let extract_local_trace (h':trace) (pi:monitorable_prop) :
  IIO trace
    (requires (fun h -> h' `suffix_of` h))
    (ensures (fun h lt' lt ->
      lt == [] /\
      enforced_locally pi h lt /\
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
  (#t1 #t2:Type)
  (pi:monitorable_prop)
  (pre:t1 -> trace -> Type0)
  (post:t1 -> trace -> (r:resexn t2) -> trace -> Type0)
  {| post_c:checkable_hist_post #t1 #t2 pre post pi |}
  (f:t1 -> IIOpi (resexn t2) pi)
  (x:t1) :
  IIO (resexn t2) (pre x) (post x) =
  let h = get_trace () in
  let r : resexn t2 = f x in
  Classical.forall_intro (lemma_suffixOf_append h);
  let lt = extract_local_trace h pi in
  Classical.forall_intro_2 (Classical.move_requires_2 (lemma_append_rev_inv_tail h));
  if post_c.result_check x h r lt then r
  else Inr Contract_failure

instance safe_importable_arrow_pre_post
  (t1:Type) {| d1:exportable t1 'pi |}
  (t2:Type) {| d2:importable t2 'pi |}
  (pre : t1 -> trace -> Type0)
  (** it must be `resexn t2` because needs the ability to fail **)
  (post : t1 -> trace -> (r:resexn t2) -> trace -> Type0)
  {| post_c:checkable_hist_post #t1 #t2 pre post 'pi |} : 
  safe_importable ((x:t1) -> IIO (resexn t2) (pre x) (post x)) 'pi =
  mk_safe_importable
    (d1.etype -> IIOpi (resexn d2.itype) 'pi)
    #((x:t1) -> IIO (resexn t2) (pre x) (post x))
    #(ilang_arrow 'pi d1.etype #d1.c_etype d2.itype #d2.c_itype)
    (fun f -> 
      let f' = safe_import #_ #'pi #(safe_importable_arrow t1 #d1 t2 #d2) f in
      enforce_post 'pi pre post #post_c f')
