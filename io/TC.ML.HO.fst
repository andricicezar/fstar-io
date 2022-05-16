module TC.ML.HO

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open TC.ML

open TC.Export
open TC.Monitorable.Hist
  
 
(** ** ML Target language **)

(** ** Arrows **)
class ml_arrow (t:Type) (pi:monitorable_prop) = { mldummy : unit }

(** why is this not a type class? **)
noeq
type ml (t:Type) =
| ML_FO : mlfo t -> ml t
| ML_ARROW : #pi:monitorable_prop -> ml_arrow t pi -> ml t

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
  
effect IOpi (a:Type) (pi : monitorable_prop) = 
  DM.IIO.IIOwp a (fun p h -> (forall r lt. (enforced_locally pi h lt) ==> p lt r))

effect IIOpi (a:Type) (pi : monitorable_prop) = 
  DM.IIO.IIOwp a (fun p h -> (forall r lt. (enforced_locally pi h lt) ==> p lt r))

let trivial_pi () : monitorable_prop = fun _ _ _ -> true

let trivial_pi_is_trivial (h lt:IO.Sig.trace) :
  Lemma (enforced_locally (trivial_pi ()) h lt == true) [SMTPat (enforced_locally (trivial_pi ()) h lt)] = admit ()

effect MIO (a:Type) = IOpi a (trivial_pi ())
effect MIIO (a:Type) = IIOpi a (trivial_pi ())

instance ml_instrumented_io
  (t1:Type) {| ml t1 |}
  (t2:Type) {| ml t2 |} 
  (pi:monitorable_prop) : 
  Tot (ml_arrow (t1 -> IIOpi t2 pi) pi) = 
  { mldummy = () }

instance ml_instrumented_iio
  (t1:Type) {| ml t1 |}
  (t2:Type) {| ml t2 |} 
  (pi:monitorable_prop) : 
  Tot (ml_arrow (t1 -> IIOpi t2 pi) pi) = 
  { mldummy = () }

instance ml_arrow_mio
  (t1:Type) {| ml t1 |}
  (t2:Type) {| ml t2 |} : 
  Tot (ml_arrow (t1 -> MIO t2) (trivial_pi ())) = 
  { mldummy = () }

instance ml_arrow_miio
  (t1:Type) {| ml t1 |}
  (t2:Type) {| ml t2 |} : 
  Tot (ml_arrow (t1 -> MIIO t2) (trivial_pi ())) = 
  { mldummy = () }

(** ** Instrumentation **)
class instrumentable (t:Type) (pi:monitorable_prop) = { 
  inst_type : Type;
  cinst_type : ml_arrow inst_type pi;
  (** be careful to not use reify while writing strengthen **)
  strengthen : inst_type -> t
} 

(** ** Compilation (?) **)
class mlifyable (t : Type) (pi:monitorable_prop) =
  { matype : Type; 
    cmatype : ml_arrow matype pi;
    mlify : t -> matype }

let mk_mlifyable
  (#t1:Type)
  (#pi:monitorable_prop)
  (t2:Type) {| ml_arrow t2 pi |} 
  (exp : t1 -> t2) : 
  mlifyable t1 pi =
  { matype = t2; 
    mlify = exp;
    cmatype = solve }

(** ** Some tests **)

private
let test_fo t1 {| d:mlfo t1 |} : ml t1 =
  ML_FO d 

private
let test_arrity1 t1 t2 {| d1:mlfo t1 |} {| d2:mlfo t2 |} : ml (t1 -> MIO t2) =
  ML_ARROW (ml_arrow_mio t1 #(ML_FO d1) t2 #(ML_FO d2)) 

private
let test_arrity1_ho t1 t2 {| d1:ml_arrow t1 (trivial_pi ()) |} {| d2:ml_arrow t2 (trivial_pi ()) |} : ml (t1 -> IIOpi t2 (trivial_pi ())) =
  ML_ARROW (ml_arrow_mio t1 #(ML_ARROW d1) t2 #(ML_ARROW d2)) 

private
let test_arrity1_ho_2 t1 t2 t3 t4 {| d1:mlfo t1 |} {| d2:mlfo t2 |} {| d3:mlfo t3 |} {| d4:mlfo t4 |} : ml ((t1 -> MIO t2) -> MIIO (t3 -> MIIO t4)) =
  ML_ARROW
    (ml_arrow_miio (t1 -> MIO t2) 
    #(ML_ARROW (ml_arrow_mio t1 #(ML_FO d1) t2 #(ML_FO d2)))
    (t3 -> MIIO t4)
    #(ML_ARROW (ml_arrow_miio t3 #(ML_FO d3) t4 #(ML_FO d4))))

private
let test_instrumented t1 t2 pi {| d1:ml_arrow t1 pi |} {| d2:mlfo t2 |} : ml (t1 -> MIO t2) =
  ML_ARROW (ml_arrow_mio t1 #(ML_ARROW d1) t2 #(ML_FO d2)) 

