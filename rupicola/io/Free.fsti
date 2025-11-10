module Free

(** we only have bools in STLC right now **)

(** I would like quotation to happen at the interface level
    and not at the representation level. I think this way
    one could produce code as close as the one written usin the
    do notation. **)

val free (a:Type u#a) : Type u#a

val free_return (#a:Type) (x:a) : free a

val free_bind
  (#a:Type u#a)
  (#b:Type u#b)
  (l : free a)
  (k : a -> free b) :
  free b

val free_read () : free bool
val free_write (x:bool) : free unit
