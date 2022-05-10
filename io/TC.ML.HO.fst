module TC.ML.HO

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open TC.ML

(** ** The effect for ML arrows **)
effect MIO (a:Type) = DM.IO.IOwp a (Hist.trivial_hist ())
effect MIIO (a:Type) = DM.IIO.IIOwp a (Hist.trivial_hist ())

(** ** Arrows **)
instance ml_arrow_mio 
  (t1:Type) (t2:Type)
  {| ml t1 |}
  {| ml t2 |} : 
  Tot (ml_arrow (t1 -> MIO t2)) = 
  { mldummy = () }

instance ml_arrow_miio 
  (t1:Type) (t2:Type)
  {| ml t1 |}
  {| ml t2 |} : 
  Tot (ml_arrow (t1 -> MIIO t2)) = 
  { mldummy = () }

(** ** Instrumented arrows **)
open TC.Monitorable.Hist

effect IIOpi (a:Type) (pi : monitorable_prop) = 
  DM.IIO.IIOwp a (fun p h -> (forall r lt. (enforced_locally pi h lt) ==> p lt r))

(** the `ml t1` restrictions may be too weak. 
Something is instrumented only if all functions it calls are instrumented.
What if t1 is a ML_ARROW? it can be an attacker...
in the same time, it can call other compromised functions **)
instance ml_instrumented_iio 
  (t1:Type) (t2:Type) 
  {| ml t1 |}
  {| ml t2 |}
  (pi:monitorable_prop) : 
  Tot (ml_instrumented (t1 -> IIOpi t2 pi)) = 
    { mlinstdummy = () }

(** ** Some tests **)

private
let test_fo t1 {| d:mlfo t1 |} : ml t1 =
  ML_FO d 

private
let test_arrity1 t1 t2 {| d1:mlfo t1 |} {| d2:mlfo t2 |} : ml (t1 -> MIO t2) =
  ML_ARROW (ml_arrow_mio t1 t2 #(ML_FO d1) #(ML_FO d2)) 

private
let test_arrity1_ho t1 t2 {| d1:ml_arrow t1 |} {| d2:ml_arrow t2 |} : ml (t1 -> MIO t2) =
  ML_ARROW (ml_arrow_mio t1 t2 #(ML_ARROW d1) #(ML_ARROW d2)) 

private
let test_arrity1_ho_2 t1 t2 t3 t4 {| d1:mlfo t1 |} {| d2:mlfo t2 |} {| d3:mlfo t3 |} {| d4:mlfo t4 |} : ml ((t1 -> MIO t2) -> MIIO (t3 -> MIIO t4)) =
  ML_ARROW (ml_arrow_miio (t1 -> MIO t2) (t3 -> MIIO t4) 
    #(ML_ARROW 
      (ml_arrow_mio t1 t2 #(ML_FO d1) #(ML_FO d2)))
    #(ML_ARROW 
      (ml_arrow_miio t3 t4 #(ML_FO d3) #(ML_FO d4)))) 

private
let test_instrumented t1 t2 {| d1:ml_instrumented t1 |} {| d2:mlfo t2 |} : ml (t1 -> MIO t2) =
  ML_ARROW (ml_arrow_mio t1 t2 #(ML_INST d1) #(ML_FO d2)) 

