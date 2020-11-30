module MIO.Effect

open IO.Effect

effect MIO
  (a:Type) =
  IOwp a (fun _ p -> forall res le. p res le)
