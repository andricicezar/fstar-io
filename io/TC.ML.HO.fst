module TC.ML.HO

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open TC.ML

open TC.Export
open TC.Monitorable.Hist
  
 
(** ** ML Target language **)

(** ** Arrows **)
class ml_arrow (t:Type) = { mldummy : unit }

class ml_instrumented (t:Type) (pi:monitorable_prop) = { mlinstdummy : unit }

(** why is this not a type class? **)
noeq
type ml (t:Type) =
| ML_FO : mlfo t -> ml t
| ML_ARROW : ml_arrow t -> ml t
| ML_INST : #pi:monitorable_prop -> ml_instrumented t pi -> ml t

(** some instances **)
instance mlfo_maybe t1 {| ml t1 |} : mlfo (maybe t1) = { mlfodummy = () }

instance exportable_maybe
  t1 {| d1:exportable t1 |} :
  Tot (exportable (maybe t1)) =
  mk_exportable 
    (maybe d1.etype)
    #(mlfo_maybe d1.etype #(ML_FO d1.cetype))
    (fun (x:maybe t1) -> match x with | Inl x' -> Inl (export x') | Inr err -> Inr err)

(** **** The effect for ML arrows **)
effect MIO (a:Type) = DM.IO.IOwp a (Hist.trivial_hist ())
effect MIIO (a:Type) = DM.IIO.IIOwp a (Hist.trivial_hist ())

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
  Tot (ml_instrumented (t1 -> IIOpi t2 pi) pi) = 
    { mlinstdummy = () }
(** ** Instrumentation **)
class instrumentable (t:Type) (pi:monitorable_prop) = { 
  inst_type : Type;
  cinst_type : ml_instrumented inst_type pi;
  (** be careful to not use reify while writing strengthen **)
  strengthen : inst_type -> t
} 

(** ** Compilation (?) **)
class mlifyable (t : Type) =
  { matype : Type; 
    cmatype : ml_arrow matype;
    mlify : t -> matype }

let mk_mlifyable
  (#t1:Type)
  (t2:Type) {| ml_arrow t2 |} 
  (exp : t1 -> t2) : 
  mlifyable t1 =
  { matype = t2; 
    mlify = exp;
    cmatype = solve }


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
let test_instrumented t1 t2 pi {| d1:ml_instrumented t1 pi |} {| d2:mlfo t2 |} : ml (t1 -> MIO t2) =
  ML_ARROW (ml_arrow_mio t1 t2 #(ML_INST d1) #(ML_FO d2)) 

