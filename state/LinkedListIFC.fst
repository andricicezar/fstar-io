module LinkedListIFC

open FStar.Tactics
open FStar.Tactics.Typeclasses
open Monotonic.IFC.Heap
open IFC.Heap.ST

open STLC
open TargetLangIFC

// noeq type linkedList (a: Type0) : Type0 =
//    | Nil
//    | Cons of a * ref (linkedList a)

type node (#t:Type) {| c:target_lang t |} (v:t) (r: ref t) = (v, r)

// val empty_ll: IST (ref int) (requires _ -> True) (ensures _ _ _ -> True)
// let empty = 
//     let head: option (ref int) = alloc 0 in
//     head := None;
//     head

// val insert