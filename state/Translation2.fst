module Translation2

open FStar.Universe

noeq type linkedList (ref: (([@@@ strictly_positive] _:Type0 -> Type0))) (a: Type0) : Type0 =
| Nil : linkedList ref a
| Cons : v:a -> next:ref (linkedList ref a) -> linkedList ref a

noeq
type free (ref:Type0 -> Type0) (a:Type u#a) : Type u#(max 1 a) = (* because of the references *)
| Alloc : b:Type0 -> b -> (ref b -> free ref a) -> free ref a
| Read : b:Type0 -> ref b -> (b -> free ref a) -> free ref a
| Write : b:Type0 -> ref b -> b -> (unit -> free ref a) -> free ref a
| Return : a -> free ref a

let free_return #ref (x:'a) : free ref 'a = Return x

let rec free_bind #ref (m:free ref 'a) (k:'a -> free ref 'b) : free ref 'b =
  match m with
  | Return x -> k x
  | Alloc b x cont -> Alloc b x (fun x -> free_bind (cont x) k)
  | Read b r cont -> Read b r (fun x -> free_bind (cont x) k)
  | Write b r v cont -> Write b r v (fun x -> free_bind (cont x) k)

open STLC

let rec elab_typ0 (t:typ0) (ref: (([@@@ strictly_positive] _:Type0 -> Type0))) : Type u#0 = 
  match t with
  | TUnit -> unit
  | TNat -> int
  | TSum t1 t2 -> either (elab_typ0 t1 ref) (elab_typ0 t2 ref)
  | TPair t1 t2 -> elab_typ0 t1 ref * elab_typ0 t2 ref
  | TRef t -> ref (elab_typ0 t ref)
  | TLList t -> linkedList ref (elab_typ0 t ref)

let rec elab_typ (t:typ) (ref: (([@@@ strictly_positive] _:Type0 -> Type0))) : Type u#1 =
  match t with
  | TArr t1 t2 -> begin
    let tt1 = elab_typ t1 ref in
    let tt2 = elab_typ t2 ref in
    tt1 -> free ref tt2
  end 
  | TUnit -> raise_t unit
  | TNat -> raise_t int
  | TSum t1 t2 ->
    let tt1 = elab_typ t1 ref in
    let tt2 = elab_typ t2 ref in
    either tt1 tt2
  | TPair t1 t2 ->
    let tt1 = elab_typ t1 ref in
    let tt2 = elab_typ t2 ref in
    tt1 * tt2
  | TRef _ ->
    let tt = elab_typ0 t ref in
    raise_t tt
  | TLList t ->
    let tt = elab_typ0 t ref in
    raise_t (linkedList ref tt)

type vcontext (g:context) ref = 
  vx:var{Some? (g vx)} -> elab_typ (Some?.v (g vx)) ref

let vempty ref : vcontext empty ref = fun _ -> assert false

let vextend #t #ref (x:elab_typ t ref) (#g:context) (ve:vcontext g ref) : vcontext (extend t g) ref =
  fun y -> if y = 0 then x else ve (y-1)

let rec downgrade_typ (#t:typ0) #ref (x:elab_typ t ref) : elab_typ0 t ref =
  match t with
  | TSum t1 t2 -> begin
    let x : either (elab_typ t1 ref) (elab_typ t2 ref) = x in
    (match x with
    | Inl x1 -> Inl (downgrade_typ x1)
    | Inr x2 -> Inr (downgrade_typ x2)) <: either (elab_typ0 t1 ref) (elab_typ0 t2 ref)
  end
  | TPair t1 t2 -> begin
    let x : elab_typ t1 ref * elab_typ t2 ref = x in
    let (x1, x2) = x in
    (downgrade_typ #t1 x1, downgrade_typ #t2 x2) <: elab_typ0 t1 ref * elab_typ0 t2 ref
  end
  | _ -> downgrade_val x

let downgrade (#t:typ0) (#ref: (([@@@ strictly_positive] _:Type0 -> Type0))) (m:free ref (elab_typ t ref)) : free ref (elab_typ0 t ref) =
  free_bind m (fun (x:elab_typ t ref) -> 
    free_return (downgrade_typ x))

let rec raise_typ #t #ref (x:elab_typ0 t ref) : elab_typ t ref =
  match t with
  | TSum t1 t2 -> begin
    let x : either (elab_typ0 t1 ref) (elab_typ0 t2 ref) = x in
    (match x with
    | Inl x1 -> Inl (raise_typ x1)
    | Inr x2 -> Inr (raise_typ x2)) <: either (elab_typ t1 ref) (elab_typ t2 ref)
  end
  | TPair t1 t2 -> begin
    let x : elab_typ0 t1 ref * elab_typ0 t2 ref = x in
    let (x1, x2) = x in
    (raise_typ #t1 x1, raise_typ #t2 x2) <: elab_typ t1 ref * elab_typ t2 ref
  end
  | _ -> raise_val x

let raise (#t:typ0) (#ref: (([@@@ strictly_positive] _:Type0 -> Type0))) (m:free ref (elab_typ0 t ref)) : free ref (elab_typ t ref) =
  free_bind m (fun (x:elab_typ0 t ref) -> 
    free_return (raise_typ x))

let rec elab_exp 
  (#g:context)
  (#e:exp) 
  (#t:typ)
  #ref
  (tyj:typing g e t)
  (ve:vcontext g ref)
  : free ref (elab_typ t ref) =
  match tyj with
  | TyUnit -> free_return (raise_val ())
  | TyZero -> free_return (raise_val 0)
  | TySucc tyj_s -> 
    let ms = elab_exp tyj_s ve in
    free_bind ms (fun s -> free_return (raise_val (1 + downgrade_val s)))
  
  | TyAllocRef #_ #_ #t tyj_e -> begin
    let tt : Type0 = elab_typ0 t ref in
    let mv : free ref tt = downgrade (elab_exp tyj_e ve) in
    free_bind mv (fun (v:tt) -> 
      Alloc tt v (fun (r:ref tt) -> free_return (raise_val r)))
  end
  | TyReadRef #_ #_ #t tyj_e -> begin
    let tt : Type0 = elab_typ0 t ref in
    let mr : free ref (ref tt) = downgrade (elab_exp tyj_e ve) in
    free_bind mr (fun (r:ref tt) -> 
      Read tt r (fun (v:tt) -> raise (free_return v)))
  end
  | TyWriteRef #_ #_ #_ #t tyj_ref tyj_v -> begin
    let tt : Type0 = elab_typ0 t ref in
    let mr : free ref (ref tt) = downgrade (elab_exp tyj_ref ve) in
    let mv : free ref tt = downgrade (elab_exp tyj_v ve) in
    free_bind mr (fun (r:ref tt) -> 
      free_bind mv (fun (v:tt) -> 
        Write tt r v (fun () -> free_return (raise_val ()))))
  end

  | TyAbs tx #_ #tres tyj_body ->
    let w : elab_typ tx ref -> free ref (elab_typ tres ref) =
      fun x -> elab_exp tyj_body (vextend #tx x ve) in
    free_return w
  | TyVar vx -> free_return (ve vx)
  | TyApp #_ #_ #_ #tx #tres tyj_f tyj_x -> begin
    let mf = elab_exp tyj_f ve in
    let mx = elab_exp tyj_x ve in
    free_bind mf (fun f -> 
      free_bind mx (fun x -> 
        f x))
  end

  | TyInl #_ #_ #t1 #t2 tyj_1 -> begin
    let mv : free ref (elab_typ t1 ref) = elab_exp tyj_1 ve in
    free_bind mv (fun v -> 
      free_return (Inl #_ #(elab_typ t2 ref) v))
  end
  | TyInr #_ #_ #t1 #t2 tyj_2 -> begin
    let mv : free ref (elab_typ t2 ref) = elab_exp tyj_2 ve in
    free_bind mv (fun v -> 
      free_return (Inr #(elab_typ t1 ref) #_ v))
  end
  | TyCaseSum #_ #_ #_ #_ #tl #tr #tres tyj_c tyj_l tyj_r -> begin
    let mvc : free ref (either (elab_typ tl ref) (elab_typ tr ref)) = elab_exp tyj_c ve in
    free_bind mvc (fun vc ->
      match vc with
      | Inl x ->
        let mf = elab_exp tyj_l ve in
        free_bind mf (fun f -> f x)
      | Inr y ->
        let mf = elab_exp tyj_r ve in
        free_bind mf (fun f -> f y))
  end

  | TyFst #_ #_ #tf #ts tyj_e ->
    let mv : free ref (elab_typ (TPair tf ts) ref) = elab_exp tyj_e ve in
    free_bind mv (fun v -> 
      free_return (fst v))

  | TySnd #_ #_ #tf #ts tyj_e ->
    let mv : free ref (elab_typ (TPair tf ts) ref) = elab_exp tyj_e ve in
    free_bind mv (fun v -> 
      free_return (snd v))

  | TyPair #_ #_ #_ #tf #ts tyj_f tyj_s -> 
    let mvf : free ref (elab_typ tf ref) = elab_exp tyj_f ve in
    let mvs : free ref (elab_typ ts ref) = elab_exp tyj_s ve in
    free_bind mvf (fun f -> 
      free_bind mvs (fun s -> 
        free_return (f, s)))
