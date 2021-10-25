module DM.MIIO

open Common
open Free
open Free.IO
open DM.IIO
open DM.IIO.Primitives
open TC.Trivialize.IIOwp

effect MIIO
  (a:Type) =
  IIOwp a (fun _ p -> forall res le. p res le)

let _IIOwp_as_MIIO
  (pre:'a -> trace -> bool)
  (post:'a -> trace -> (m:'b) -> trace -> Type0)
  (f:(x:'a ->
    IIOwp 'b (fun h p -> pre x h /\ (forall r lt. post x h r lt ==> p r lt))))
  (x:'a) :
  MIIO (maybe 'b) =
  (trivialize 
    #_ 
    #(trivializeable_IIOwp _ _ (fun x h -> pre x h) post) f) x

let _IIOwp_as_MIIO_2
  (pre:'a -> 'b -> trace -> bool)
  (post:'a -> 'b -> trace -> (m:'c) -> trace -> Type0)
  (f:(x:'a -> y:'b ->
    IIOwp 'c (fun h p -> pre x y h /\ (forall r lt. post x y h r lt ==> p r lt))))
  (x:'a) (y:'b):
  MIIO (maybe 'c) =
  (trivialize 
    #_ 
    #(trivializeable_IIOwp_2 _ _ _ (fun x y h -> pre x y h) post) f) x y
