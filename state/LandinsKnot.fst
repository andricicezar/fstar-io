module LandinsKnot

open FStar.Tactics
open FStar.Tactics.Typeclasses

open FStar.HyperStack
open FStar.HyperStack.ST 

open STLC
open TargetLangHS

let landins_knot_fs () : St nat = 
  let id : nat -> St nat = fun x -> x in
  let r : ref (nat -> St nat) = ralloc root id in
  let f : nat -> St nat = (fun x -> !r x) in
  r := f;
  f 0

let landins_knot : exp =
     EApp
          (EAbs (TRef (TArr TUnit TUnit)) (* r *)
               (EApp
                 (EAbs (TArr TUnit TUnit) (* f *)
                    (EApp
                         (EAbs TUnit (EApp (EVar 1) EUnit)) (* f () *)  
                         (EWriteRef (EVar 1) (EVar 0)) (* r := f *)
                    ))
                 (EAbs TUnit (EApp (EReadRef (EVar 1)) EUnit)))) (* f = fun () -> r () *)
          (EAlloc (EAbs TUnit (EVar 0))) (* alloc r (fun () -> ()) *)

let ty_landins_knot : typing empty landins_knot TUnit =
     TyApp (TyAbs (TRef (TArr TUnit TUnit))
                  (TyApp (TyAbs (TArr TUnit TUnit) 
                               (TyApp (TyAbs TUnit (TyApp (TyVar 1) TyUnit))
                                       (TyWriteRef (TyVar 1) (TyVar 0))))
                         (TyAbs TUnit (TyApp (TyReadRef (TyVar 1)) TyUnit))))
           (TyAllocRef (TyAbs TUnit (TyVar 0)))


let landins_knot3 () : St unit =
  let rrs = new_region root in
  elab_exp rrs ty_landins_knot (vempty rrs)