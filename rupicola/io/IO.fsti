module IO

(** we only have bools in STLC right now **)

(** I would like quotation to happen at the interface level
    and not at the representation level. I think this way
    one could produce code as close as the one written usin the
    do notation. **)

include BaseTypes
open Hist

val io (a:Type u#a) : Type u#a

val io_return (#a:Type) (x:a) : io a

val io_bind
  (#a:Type u#a)
  (#b:Type u#b)
  (l : io a)
  (k : a -> io b) :
  io b

val read () : io (resexn bool)
val write (x:bool) : io (resexn unit)

val theta : #a:Type -> io a -> hist a

let return = io_return
let (let!@) = io_bind
