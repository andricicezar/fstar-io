module LawImportableExportable

open FStar.Tactics
open FStar.Tactics.Typeclasses

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

  law : squash (forall (x:styp). import (c_exportable.export x) == x);
}

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

assume val p : int -> bool
  
let f (x:int) : Pure int (p x) (fun _ -> True) = if p x then 0 else 1
let g (x:int) : Pure int (p x) (fun _ -> True) = 0

let lemma (x:int) : Lemma (requires (p x)) (ensures (p x == true)) = ()

let _ = assert (f == g) by (norm [delta_only [`%f;`%g]]; l_to_r [`lemma]; smt (); dump "h")


let law_test (f:strg_test) : Lemma (_import (test_exportable.export f) == f) =
  let f' : strg_test = (fun (x:int) -> 
      (let r : option int = if x > 5 then f x else None in
      match r with
      | Some r -> if r < x then Some r else None
      | None -> None)) in

  let f'' : strg_test = (fun (x:int) -> 
      (let r : option int = f x in
      match r with
      | Some r -> if r < x then Some r else None
      | None -> None)) in

  assert (f' == f'');
  
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
    == { (** the pre-condition x > 5 makes the if trivial **) _ by (tadmit ()) }
    (fun (x:int) -> 
      (let r : option int = f x in
      match r with
      | Some r -> if r < x then Some r else None
      | None -> None)) <: x:int -> Pure (option int) (x > 5) (fun r -> match r with | Some r -> r < x | None -> True);
    == { (** f has the post-condition, so the if is trivial **) _ by (tadmit ()) }
    (fun (x:int) -> f x);
    == { (** function extensionality may be needed **) _ by (tadmit ()) }
    f;
  }

instance test_importable : importable strg_test = {
  wtyp = weak_test;
  import = _import;
  c_exportable = (
    let r : exportable strg_test = test_exportable in
    assert (weak_test == r.wtyp);
    r
  );
  law = Classical.forall_intro law_test;
}
