module Stream

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Classical
open FStar.IndefiniteDescription
open FStar.Calc
open FStar.FunctionalExtensionality
open Util

(** Streams

    We use the encoding of streams of a as functions from nat to a.
    To recover extensionality of streams, we use restricted pure functions
    as evidenced by the ^-> operator instead of ->.

*)

let stream a =
  nat ^-> a

(** Stream truncation *)
let rec stream_trunc #a (s : stream a) (n : nat) : list a =
  if n = 0
  then []
  else stream_trunc s (n - 1) @ [ s (n-1) ]

let stream_prepend #a (l : list a) (s : stream a) : stream a =
  on nat (fun n ->
    if n < length l
    then index l n
    else s (n - length l)
  )

let stream_drop #a (n : nat) (s : stream a) : stream a =
  on nat (fun m -> s (n + m))

let shead #a (s : stream a) : a =
  s 0

let stail #a (s : stream a) : stream a =
  stream_drop 1 s

let rec suffix_of_stream_trunc #a (s : stream a) (n : nat) (l : list a) :
  Lemma (
    l `suffix_of` stream_trunc s n ==>
    (exists m. m <= n /\ l == stream_trunc s m)
  )
= if n = 0
  then ()
  else begin
    suffix_of_append_one l (stream_trunc s (n - 1)) (s (n-1)) ;
    suffix_of_stream_trunc s (n-1) l
  end

let rec stream_trunc_length #a (s : stream a) (n : nat) :
  Lemma (length (stream_trunc s n) == n)
= if n = 0
  then ()
  else begin
    append_length (stream_trunc s (n - 1)) [s (n-1)] ;
    stream_trunc_length s (n-1)
  end

let rec index_stream_trunc #a (s : stream a) (n m : nat) :
  Lemma (m < length (stream_trunc s n) ==> index (stream_trunc s n) m == s m)
= if n = 0
  then ()
  else begin
    append_length (stream_trunc s (n - 1)) [s (n-1)] ;
    if m < length (stream_trunc s n) - 1
    then begin
      index_append_left (stream_trunc s (n - 1)) [s (n-1)] m ;
      index_stream_trunc s (n-1) m
    end
    else if m = length (stream_trunc s n) - 1
    then begin
      index_append_right (stream_trunc s (n - 1)) [s (n-1)] m ;
      stream_trunc_length s (n-1)
    end
    else ()
  end

let stream_trunc_drop #a (n : nat) (s : stream a) :
  Lemma (s `feq` stream_prepend (stream_trunc s n) (stream_drop n s))
= stream_trunc_length s n ;
  forall_intro (index_stream_trunc s n)

// Could also only require ext on positions below n
let rec stream_trunc_ext #a (p q : stream a) (n  : nat) :
  Lemma (p `feq` q ==> stream_trunc p n == stream_trunc q n)
= if n = 0
  then ()
  else stream_trunc_ext p q (n - 1)

let stream_prepend_nil #a (s : stream a) :
  Lemma (stream_prepend [] s `feq` s)
= ()

let stream_prepend_trunc_left #a (l : list a) (s : stream a) (n : nat) :
  Lemma (n <= length l ==> stream_trunc (stream_prepend l s) n == firstn n l)
= if n <= length l
  then begin
    move_requires (index_extensionality (stream_trunc (stream_prepend l s) n)) (firstn n l) ;
    stream_trunc_length (stream_prepend l s) n ;
    lemma_firstn_length n l ;
    forall_intro (index_stream_trunc (stream_prepend l s) n) ;
    stream_trunc_length s n ;
    assert (forall i. i < n ==> index (stream_trunc (stream_prepend l s) n) i == stream_prepend l s i) ;
    index_firstn n l ;
    assert (forall i. i < n ==> index (firstn n l) i == index l i) ;
    assert (forall i. i < n ==> index (stream_trunc (stream_prepend l s) n) i == index (firstn n l) i)
  end
  else ()

let stream_prepend_trunc_right #a (l : list a) (s : stream a) (n : nat) :
  Lemma (n >= length l ==> stream_trunc (stream_prepend l s) n == l @ stream_trunc s (n - length l))
= if n >= length l
  then begin
    move_requires (index_extensionality (stream_trunc (stream_prepend l s) n)) (l @ stream_trunc s (n - length l)) ;
    stream_trunc_length (stream_prepend l s) n ;
    append_length l (stream_trunc s (n - length l)) ;
    stream_trunc_length s (n - length l) ;

    forall_intro (index_stream_trunc (stream_prepend l s) n) ;
    forall_intro (index_append l (stream_trunc s (n - length l))) ;
    assert (forall i. i < n ==> index (l @ stream_trunc s (n - length l)) i == (if i < length l then index l i else index (stream_trunc s (n - length l)) (i - length l))) ;
    forall_intro (index_stream_trunc s (n - length l)) ;
    assert (forall i. i < n ==> index (l @ stream_trunc s (n - length l)) i == (if i < length l then index l i else s (i - length l))) ;
    assert (forall i. i < n ==> index (stream_trunc (stream_prepend l s) n) i == index (l @ stream_trunc s (n - length l)) i)
  end
  else ()

let stream_prepend_trunc #a (l : list a) (s : stream a) (n : nat) :
  Lemma (stream_trunc (stream_prepend l s) n == (if n <= length l then firstn n l else l @ stream_trunc s (n - length l)))
= stream_prepend_trunc_left l s n ; stream_prepend_trunc_right l s n

let stream_ext #a (p q : stream a) :
  Lemma (p `feq` q ==> p == q)
= extensionality nat (fun _ -> a) p q

let feq_head_tail #a (s : stream a) :
  Lemma (stream_prepend [shead s] (stail s) `feq` s)
= ()

let rec stream_trunc_succ #a (s : stream a) (n : nat) :
  Lemma (stream_trunc s (n+1) == shead s :: stream_trunc (stail s) n)
= if n = 0
  then ()
  else stream_trunc_succ s (n-1)

let skipn_stream_trunc #a (n m : nat) (s : stream a) :
  Lemma
    (requires n <= m)
    (ensures skipn n (stream_trunc s m) == stream_trunc (stream_drop n s) (m - n))
= calc (==) {
    skipn n (stream_trunc s m) ;
    == { stream_trunc_drop n s ; stream_trunc_ext (stream_prepend (stream_trunc s n) (stream_drop n s)) s m }
    skipn n (stream_trunc (stream_prepend (stream_trunc s n) (stream_drop n s)) m) ;
    == { stream_trunc_length s n ; stream_prepend_trunc_right (stream_trunc s n) (stream_drop n s) m }
    skipn n ((stream_trunc s n) @ stream_trunc (stream_drop n s) (m - n)) ;
    == { stream_trunc_length s n ; skipn_append_right n (stream_trunc s n) (stream_trunc (stream_drop n s) (m - n)) }
    skipn 0 (stream_trunc (stream_drop n s) (m - n)) ;
    == {}
    stream_trunc (stream_drop n s) (m - n) ;
  }

// TODO Worth keeping?
let stream_trunc_split_drop #a (n : nat) (s : stream a) l1 l2 :
  Lemma
    (requires l1 @ l2 == stream_trunc s n /\ n >= length l1)
    (ensures l2 == stream_trunc (stream_drop (length l1) s) (n - length l1))
= calc (==) {
    l2 ;
    == { skipn_append_right (length l1) l1 l2 }
    skipn (length l1) (l1 @ l2) ;
    == {}
    skipn (length l1) (stream_trunc s n) ;
    == { skipn_stream_trunc (length l1) n s }
    stream_trunc (stream_drop (length l1) s) (n - length l1) ;
  }

let stream_drop_drop #a (n m : nat) (s : stream a) :
  Lemma (stream_drop n (stream_drop m s) `feq` stream_drop (n + m) s)
= ()

// TODO cofix
