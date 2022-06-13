module LTL

open FStar.Tactics
open FStar.List.Tot
open ExtraTactics

open Common
open IO.Sig
open IO

(** *** Figure 1 **)
type time = (h:trace & (n:int{(-1 <= n /\ n < List.length h)}))

let test_start_time : time = (| [], -1 |)

val start_time : time -> Type0
let start_time (| _, i |) = i == 0

val empty_time : time -> Type0
let empty_time (| h, _ |) = h == []

val has_history : time -> Type0
let has_history (| _, i |) = i > 0

val end_time : time -> Type0
let end_time (| h, i |) = (i+1) == List.length h

val time_leq : time -> time -> Type0
let time_leq (| h1, i1 |) (| h2, i2 |) = i1 <= i2 /\ h1 == h2 // should it be = instead of prefix?

val time_lt : time -> time -> Type0
let time_lt (| h1, i1 |) (| h2, i2 |) = i1 < i2 /\ h1 == h2

// associative, cancellative, has right unit 0
unfold val time_sum : t:time -> n:int{-1 <= n+Mkdtuple2?._2 t /\ n+Mkdtuple2?._2 t < (List.length (Mkdtuple2?._1 t))} -> time 
let time_sum (| h, i1 |) n = (| h, i1 + n |)

val time_diff : t1:time -> t2:time{t2 `time_leq` t1} -> nat
let time_diff (| _, i1 |) (| _, i2 |) = i1 - i2

(** *** Figure 2 **)
type ltl_prop = time -> Type0
type prefix_prop = trace -> Type0

(** *** Effect **)
unfold val as_time : trace -> trace -> time
let as_time h lt = 
  List.Tot.Properties.rev_length h;
  (| List.rev h @ lt, List.length h - 1 |)

effect IOltl (a:Type) (pre:prefix_prop) (post:ltl_prop) =
  IO a 
    (fun h -> pre h) 
    (fun h r lt -> post (as_time h lt))

(** *** Figure 4 **)
val closed_interval : ltl_prop -> time -> time -> Type0
let closed_interval p s u = forall t. s `time_leq` t ==> t `time_leq` u ==> p t // shouldn't it be /\ instead of the first ==>?

val closed_open_interval : ltl_prop -> time -> time -> Type0
let closed_open_interval p s u = forall t.  s `time_leq` t ==> t `time_lt` u ==> p t

(** *** Figure 5 **)
val yesterday : ltl_prop -> ltl_prop
let yestarday p t =
  has_history t /\ p (t `time_sum` (-1))

val next : ltl_prop -> ltl_prop 
let next p t = 
  ~(end_time t) /\ p (t `time_sum` 1)

val eventually : ltl_prop -> ltl_prop
let eventually p t = exists u. t `time_leq` u /\ p u

val globally : ltl_prop -> ltl_prop
let globally p t = forall u. t `time_leq` u /\ p t

val until : ltl_prop -> ltl_prop -> ltl_prop
let until p q t = exists u. t `time_leq` u /\ (closed_open_interval p t u) /\ q u

val non_strict_until : ltl_prop -> ltl_prop -> ltl_prop
let non_strict_until p q t = exists u. t `time_leq` u /\ (closed_interval p t u) /\ q u

(** *** Relations between primitives **)
let next_implies_eventually (p:ltl_prop) (t:time) :
  Lemma (next p t ==> eventually p t)
        [SMTPat (next p t)] =
  introduce next p t ==> eventually p t with _. begin
    assert (next p t);
    assert (next p t ==> ~(end_time t)) by (norm [delta_only [`%next]]);
    assert (next p t ==> p (t `time_sum` 1)) by (norm [delta_only [`%next]]);
    let u = t `time_sum` 1 in
    introduce exists (u:time). t `time_leq` u /\ p u with u and begin
        assert (p u);
        assert (t `time_leq` u)
    end;
    assert (eventually p t) by (norm [delta_only [`%eventually]])
  end


(** *** Test Effect **)
val is_closed : file_descr -> ltl_prop
let is_closed fd (| h, i |) =
  0 <= i /\ i < List.length h /\
  (let e = List.Tot.index h i in
  (EClose? e /\ EClose?.a e == fd))

val is_open_ltl : file_descr -> ltl_prop
let is_open_ltl (fd:file_descr) t : Tot Type0 =
  let rec f' : (t:time) -> Tot Type0 (decreases (Mkdtuple2?._1 t)) = fun t -> begin
    match t with
    | (| [], _ |) -> false
    | (| h :: tail, i |) -> begin
      if i > 0 then f' (| tail, (i-1) |)
      else is_open fd (h::tail)
    end
  end in
  f' t

let lemma_index_of_append_skip (n:nat) (h lt:trace) :
  Lemma 
    (requires (n < length lt /\ List.length lt > 0))
    (ensures (
      index (h @ lt) (length h + n) ==
          index lt n))
    [SMTPat (index (h @ lt) (length h + n))] = 
  rev_length h;
  admit ()

let lemma_index_of_append_skip_rev (n:nat) (h lt:trace) :
  Lemma 
    (requires (n < length lt /\ List.length lt > 0))
    (ensures (
      rev_length h;
      index (rev h @ lt) (length h + n) ==
          index lt n))
    [SMTPat (index (rev h @ lt) (length h + n))] =
  rev_length h;
  lemma_index_of_append_skip 0 h lt

let lemma_index_of_append_skip_0 (h lt:trace) :
  Lemma 
    (requires (List.length lt > 0))
    (ensures (
      rev_length h;
      index (rev h @ lt) (length h) ==
          index lt 0))
    [SMTPat (index (rev h @ lt) (length h))] =
  lemma_index_of_append_skip_rev 0 h lt

unfold val prefix_as_ltl : prefix_prop -> ltl_prop
let prefix_as_ltl (p:prefix_prop) (| h, i |) =
  i == -1 /\
  p h

let close (fd:file_descr) : IOltl (io_resm Close) (io_pre Close fd) (next (is_closed fd)) 
  by (
  explode ();
  bump_nth 14;
  l_to_r [`append_nil_l;`append_l_nil];
  let _, _ = destruct_and (nth_binder (3)) in
  ExtraTactics.rewrite_lemma_2 (-1) 8 9;
  rewrite (nth_binder 10);
  let lem1 : term = `(rev_length (`#(nth_binder 1))) in
  let _ = pose_lemma lem1 in
  let lem2 : term = `(lemma_index_of_append_skip_0 (`#(nth_binder 1)) [convert_call_to_event Close (`#(nth_binder 0)) (`#(nth_binder 9))]) in
  let _ = pose_lemma lem2 in
  explode ()
  )
  =
  static_cmd Close fd

let eventually_closed (fd:file_descr) : IOltl unit (io_pre Close fd) (eventually (is_closed fd)) =
  let _ = close fd in
  ()
