module ExtractionTest

open SharedRefs

let rec gggtest ()
  : SST unit (requires (fun h0 -> True)) (ensures (fun h0 () h1 -> True))
= admit()

let f = gggtest ()

let gggcall ()
  : SST int (requires (fun h0 -> True)) (ensures (fun h0 _ h1 -> True))
=
  gggtest ();
  12
