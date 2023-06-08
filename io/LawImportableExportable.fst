(* For SCC we want ∀P. ∀C. ∀t. Beh(C↓[P↓]) ⊆ Beh(C[P])
C↓ = fun p -> C (import p)
P↓ = export P
then C↓[P↓] = C↓ (P↓) = C↓ (export P) = C (import (export P))
so in the end we want Beh(C (import (export P))) ⊆ Beh(C P) *)

module LawImportableExportable

open FStar.Tactics
open FStar.Tactics.Typeclasses
open BeyondCriteria
open MIO.Behavior
open MIO

let beh' (f : dm_gmio int AllActions (to_hist (fun _ -> True) (fun _ _ _ -> True))) =
  beh_gmio f []

class exportable (styp : Type u#a) = {
  [@@@no_method]
  wtyp : Type u#a;
  [@@@no_method]
  export : styp -> wtyp;
}

class importable (styp : Type u#a) = {
  [@@@no_method]
  wtyp : Type u#a;

  [@@@no_method]
  import : wtyp -> styp;

  c_exportable : t:(exportable styp){t.wtyp == wtyp};

  law : squash (forall ctx (x:styp) t. t `member_of` beh' (ctx (import (c_exportable.export x))) ==> t `member_of` beh' (ctx x));
}




(* assume val lemma1 : #a:Type -> #b:Type -> pre:(a -> bool) -> $f:(a -> Tot b) -> $g:(a -> Tot b) ->
  Lemma (
    let v1 : (x:a -> Pure b (pre x) (fun _ -> True)) = (fun x -> f x) in
    let v2 : (x:a -> Pure b (pre x) (fun _ -> True)) = (fun x -> if pre x then f x else g x) in
    v2 == v1) *)

(**
val lemma11 : #a:Type -> #b:Type -> pre:(a -> bool) -> f:(x:a -> Pure (option b) (pre x) (fun _ -> True)) -> (x:a) ->
  Lemma (requires (pre x))
  (ensures (((if pre x then f x else None) <: option b) == f x))
let lemma11 #a #b pre f x = ()

assume val lemma1 : #a:Type -> #b:Type -> pre:(a -> bool) -> f:(x:a -> Pure (option b) (pre x) (fun _ -> True)) ->
  Lemma (
    let g :(x:a -> Pure (option b) (pre x) (fun _ -> True)) = (fun (x:a) -> if pre x then f x else None) in
    f == g)

let lemma1 #a #b pre f =
    let g :(x:a -> Pure (option b) (pre x) (fun _ -> True)) = (fun (x:a) -> if pre x then f x else None) in
    assert (f == g) by (l_to_r [`lemma11]; smt (); dump "h")
**)

(* assume val lemma2 : #a:Type -> #b:Type -> post:(a -> option b -> bool) -> f:(x:a -> Pure (option b) True (fun r -> post x r)) ->
  Lemma (f == (fun (x:a) -> let r = f x in if post x r then r else None)) *)



type strg_test = (x:int -> Pure (option int) (x > 5) (fun r -> match r with | Some r -> r < x | None -> True))
type weak_test = int -> Tot (option int)

instance test_exportable : exportable strg_test = {
  wtyp = weak_test;
  export = (fun (f:strg_test) x -> if x > 5 then f x else None);
}

let _import = (fun (f:weak_test) (x:int) ->
    (let r : option int = f x in
    match r with
    | Some r -> if r < x then Some r else None
    | None -> None) <: Pure (option int) (x > 5) (fun r -> match r with | Some r -> r < x | None -> True))


let law_test () : Lemma (
  forall ctx (x : strg_test) t.
    t `member_of` beh' (ctx (_import (test_exportable.export x))) ==>
    t `member_of` beh' (ctx x)
)
= introduce forall ctx (x : strg_test) t.
    t `member_of` beh' (ctx (_import (test_exportable.export x))) ==>
    t `member_of` beh' (ctx x)
  with begin
    introduce
      t `member_of` beh' (ctx (_import (test_exportable.export x))) ==>
      t `member_of` beh' (ctx x)
    with _. begin
      assert (beh' (ctx (_import (test_exportable.export x))) t) ;
      begin match t with
      | Infinite_trace _ -> ()
      | Finite_trace lt res ->
        assert (forall p. dm_gmio_theta (ctx (_import (test_exportable.export x))) p [] ==> p lt res) ;
        // assume (forall p. dm_gmio_theta (ctx x) p [] ==> p lt res)
        introduce forall p. dm_gmio_theta (ctx x) p [] ==> p lt res
        with begin
          introduce dm_gmio_theta (ctx x) p [] ==> p lt res
          with _. begin
            eliminate forall p. dm_gmio_theta (ctx (_import (test_exportable.export x))) p [] ==> p lt res
            with p ;
            (* Up till now the proof is generic so we could direclty ask for
              some property about dm_gmio_theta, ie
              dm_gmio_theta (ctx x) p [] ==>
              dm_gmio_theta (ctx (_import (test_exportable.export x))) p []
              The issue is how to proceed from here. Without inspecting ctx it
              sounds difficult.
              If it helps we can pick a different p to instantiate the
              hypothesis but it's unclear how it would help bypass the ctx
              thing.
            *)
            assume (dm_gmio_theta (ctx (_import (test_exportable.export x))) p []) ;
            assert (p lt res)
          end
        end
      end ;
      assert (beh' (ctx x) t)
    end
  end

(* let law_test (f:strg_test) : Lemma (_import (test_exportable.export f) == f) =
  calc (==) {
    _import (test_exportable.export f);
    == { _ by (compute ()) }
    _import (fun x -> if x > 5 then f x else None);
    == { _ by (compute ()) }
    (fun (x:int) ->
      (let r : option int = if x > 5 then f x else None in
      match r with
      | Some r -> if r < x then Some r else None
      | None -> None)) <: x:int -> Pure (option int) (x > 5) (fun r -> match r with | Some r -> r < x | None -> True);
    == { (** the pre-condition x > 5 makes the if trivial **) _ by (l_to_r [`(lemma1 (fun x -> x > 5))]; dump "H") }
    (fun (x:int) ->
      (let r : option int = f x in
      match r with
      | Some r -> if r < x then Some r else None
      | None -> None)) <: x:int -> Pure (option int) (x > 5) (fun r -> match r with | Some r -> r < x | None -> True);
    == { (** f has the post-condition, so the if is trivial **) _ by (tadmit ()) }
    (fun (x:int) -> f x);
    == { (** function extensionality may be needed **) _ by (tadmit ()) }
    f;
  } *)

instance test_importable : importable strg_test = {
  wtyp = weak_test;
  import = _import;
  c_exportable = (
    let r : exportable strg_test = test_exportable in
    assert (weak_test == r.wtyp);
    r
  );
  law = law_test ();
}
