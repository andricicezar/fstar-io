module MIIO.Effect

open IO.Free
open IIO.Effect

effect MIIO
  (a:Type) =
  IIOwp a (fun _ p -> forall res le. p res le)

let _IIOwp_as_MIIO
  (pre:'a -> trace -> bool)
  (post:'a -> trace -> (m:maybe 'b) -> trace -> Type0)
  (f:(x:'a ->
    IIOwp 'b (fun h p -> pre x h /\ (forall r lt. post x h r lt ==> p r lt))))
  (x:'a) :
  MIIO 'b =
  _IIOwp_as_IIO pre post f x

(** this is just a backup. not useful anymore. **)
// let _IIO_as_MIIO
//   (#t1:Type)
//   (#t2:Type)
//   (pi:monitorable_prop)
//   (pre:t1 -> trace -> Type0) {| d3:checkable2 pre |}
//   (post: t1 -> trace -> maybe t2 -> trace -> Type0)
//   (f:(x:t1 -> IIO t2 pi (pre x) (post x)))
//   (x:t1) :
//   MIIO t2 =
//   // IIOwp t2 (fun h p -> forall r lt.
//     // ((Inr? r /\ Inr?.v r == Contract_failure /\ lt == []) \/
//     // post x h r lt) ==> p r lt) = admit();
//   let h = get_trace () in
//   (** TODO: Can any global property help us remove 'enforced_globally'?
//       The context is instrumented, therefore this should check **)
//   if check2 #t1 #trace #pre x h && enforced_globally pi h then
//     f x
//   else IIO.Effect.throw Contract_failure
