module Test

open FStar.Tactics
open FStar.Tactics.Typeclasses

class mytc (#a:Type0) (s:a) = {
  e : unit;
}

let f #a #b : a & b -> a = fst #a #b

instance compile_lec_rec
  (#a #b:Type)
  : mytc ()
  = { e = () }
