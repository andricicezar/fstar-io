module MLify.MIIO

open FStar.All
open Common
open Free
open Free.IO
open DM
open Export

exception Something_went_really_bad

let mlify_MIIO
  (#t1:Type) {| d1:importable t1 |}
  (#t2:Type) {| d2:exportable t2 |}
  (f:t1 -> MIIO t2)
  (x:d1.itype) :
  ML d2.etype =
  match import x with
  | Some x -> begin
     let tree : iio t2 = reify (f x) [] (fun _ _ -> True) in
     match tree with
     | Return y -> export y
     | _ -> FStar.All.raise Something_went_really_bad
  end
  | None -> FStar.All.raise Contract_failure
