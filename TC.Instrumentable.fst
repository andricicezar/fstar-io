module TC.Instrumentable

open FStar.Tactics
open FStar.Tactics.Typeclasses

open TC.Export
open TC.MLify

class instrumentable (t:Type) = { 
  a: Type; b: Type;
  a_c: ml a;
  b_c: ml b;
  start_type : Type;
  start_type_c : ml_arrow start_type;
  (** be careful to not use reify while writing this instrument **)
  instrument : start_type -> t
} 
