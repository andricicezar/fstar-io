module MIIO.Effect

open IIO.Effect

effect MIIO
  (a:Type) =
  IIOwp a (fun _ p -> forall res le. p res le)
