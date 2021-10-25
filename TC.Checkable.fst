module TC.Checkable

class checkable (#t:Type) (p : t -> Type0) =
  { check : (x:t -> b:bool{b ==> p x}) }
instance general_is_checkeable t (p : t -> bool) : checkable (fun x -> p x) =
  { check = fun x -> p x }

class checkable2 (#t1 #t2:Type) (p : t1 -> t2 -> Type0) =
  { check2 : (x1:t1 -> x2:t2 -> b:bool{b ==> p x1 x2}) }
instance general_is_checkable2
  t1 t2 (p : t1 -> t2 -> bool) :
  Tot (checkable2 (fun x y -> p x y)) =
  { check2 = fun x y -> p x y}

class checkable3
  (#b1 #b2 #b3:Type)
  (p : b1 -> b2 -> b3 -> Type0) =
  { check3 : (x1:b1 -> x2:b2 -> x3:b3 -> b:bool{b ==> p x1 x2 x3}) }
instance general_is_checkable3
  b1 b2 b3
  (p : b1 -> b2 -> b3 -> bool) :
  Tot (checkable3 (fun x1 x2 x3 -> p x1 x2 x3)) =
  { check3 = fun x1 x2 x3 -> p x1 x2 x3}

class checkable4
  (#b1 #b2 #b3 #b4:Type)
  (p : b1 -> b2 -> b3 -> b4 -> Type0) =
  { check4 : (x1:b1 -> x2:b2 -> x3:b3 -> x4:b4 -> b:bool{b ==> p x1 x2 x3 x4}) }
instance general_is_checkable4
  b1 b2 b3 b4
  (p : b1 -> b2 -> b3 -> b4 -> bool) :
  Tot (checkable4 (fun x1 x2 x3 x4 -> p x1 x2 x3 x4)) =
  { check4 = fun x1 x2 x3 x4 -> p x1 x2 x3 x4}
