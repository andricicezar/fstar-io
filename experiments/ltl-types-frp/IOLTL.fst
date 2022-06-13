module IOLTL

open FStar.Tactics
open FStar.List.Tot
open ExtraTactics

open Common
open IO.Sig
open IO

(** This is based on the paper LTL Types FRP Linear-time Temporal Logic Propositions as Types by Alan Jeffrey 
    Source: https://dl.acm.org/doi/10.1145/2103776.2103783 **)

(** *** Figure 1 -- time model **)
(** LTL Proposition are temporal proposition, therefore we need a time model. 
    I chose as a model for time the trace with a position.
    What is before the position is past,
    the position is present,
    and what is after the position is future.

    Since trace in this case is finite, there can be no future
**)
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

(** I think here it should be prefix **)
val time_leq : time -> time -> Type0
let time_leq (| h1, i1 |) (| h2, i2 |) = h1 == h2 /\ i1 <= i2

val time_lt : time -> time -> Type0
let time_lt (| h1, i1 |) (| h2, i2 |) = h1 == h2 /\ i1 < i2

// time_sum should be associative, cancellative, has right unit 0
unfold val time_sum : t:time -> n:int{-1 <= n+Mkdtuple2?._2 t /\ n+Mkdtuple2?._2 t < (List.length (Mkdtuple2?._1 t))} -> time 
let time_sum (| h, i1 |) n = (| h, i1 + n |)

val time_diff : t1:time -> t2:time{t2 `time_leq` t1} -> nat
let time_diff (| _, i1 |) (| _, i2 |) = i1 - i2

(** *** Figure 2 - type of props **)
type ltl_prop = time -> Type0

(** because we worked with prefixes until now, I add also
    the type of prefix_prop that looks at reversed histories. **)
type prefix_prop = trace -> Type0

unfold val prefix_as_ltl : prefix_prop -> ltl_prop
let prefix_as_ltl (p:prefix_prop) (| h, i |) =
  i == List.length h - 1 /\
  p (List.rev h)

unfold val prefix_as_ltl' : (trace -> Tot bool) -> ltl_prop
let prefix_as_ltl' p = prefix_as_ltl (fun h -> p h) 

(** *** Effect **)
unfold val as_time : trace -> trace -> time
let as_time h lt = 
  rev_length h;
  (| rev h @ lt, length h - 1 |)

(** it feels weird to have pre and post since ltl is temporal. 
probably this is not the best encoding, but probably the fact that 
we try to encode it in IOwp is a problem too**) 
effect IOltl (a:Type) (pre:ltl_prop) (post:ltl_prop) =
  IO a 
    (fun h -> rev_length h; pre (| (rev h), length h - 1 |)) 
    (fun h r lt -> post (as_time h lt))

(** *** Figure 4 - temporal props over intervals **)
val closed_interval : ltl_prop -> time -> time -> Type0
let closed_interval p s u = forall t. s `time_leq` t ==> t `time_leq` u ==> p t

val closed_open_interval : ltl_prop -> time -> time -> Type0
let closed_open_interval p s u = forall t.  s `time_leq` t ==> t `time_lt` u ==> p t

val exists_point_in_interval : ltl_prop -> time -> time -> Type0
let exists_point_in_interval p s u = exists t. s `time_leq` t /\ t `time_leq` u /\ p t

(** *** Figure 5 - temporal modalities **)
(** future modalities **)
val next : ltl_prop -> ltl_prop 
let next p t = 
  ~(end_time t) /\ p (t `time_sum` 1)

val eventually : ltl_prop -> ltl_prop
let eventually p t = exists u. t `time_leq` u /\ p u

val globally : ltl_prop -> ltl_prop
let globally p t = forall u. t `time_leq` u ==> p u

val until : ltl_prop -> ltl_prop -> ltl_prop
let until p q t = exists u. t `time_leq` u /\ closed_open_interval p t u /\ q u

val non_strict_until : ltl_prop -> ltl_prop -> ltl_prop
let non_strict_until p q t = exists u. t `time_leq` u /\ closed_interval p t u /\ q u

val constrains : ltl_prop -> ltl_prop -> ltl_prop
let constrains p q t = forall u. t `time_leq` u ==> closed_open_interval p t u ==> q u

val non_strict_constrains : ltl_prop -> ltl_prop -> ltl_prop
let non_strict_constrains p q t = forall u. t `time_leq` u ==> closed_interval p t u ==> q u

val choice : ltl_prop -> ltl_prop -> ltl_prop
let choice p q t = forall u. t `time_leq` u ==> closed_interval p t u ==> exists_point_in_interval q t u

(** past modalities **)
val yesterday : ltl_prop -> ltl_prop
let yestarday p t =
  has_history t /\ p (t `time_sum` (-1))

val once : ltl_prop -> ltl_prop
let once p t = exists s. s `time_leq` t /\ p s

val non_strict_since : ltl_prop -> ltl_prop -> ltl_prop
let non_strict_since p q t = exists s. s `time_leq` t /\ closed_interval p s t /\ q s

val historically : ltl_prop -> ltl_prop
let historically p t = forall s. s `time_leq` t ==> p s

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
val is_event : cmd:io_cmds -> io_sig.args cmd -> ltl_prop
let is_event cmd arg (| h, i |) =
  0 <= i /\ i < List.length h /\
  (let e = List.Tot.index h i in
  (exists r. e == convert_call_to_event cmd arg r))

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

let lemma_index_of_append_skip (n:nat) (h lt:list 'a) :
  Lemma 
    (requires (n < length lt /\ List.length lt > 0))
    (ensures (
      index (h @ lt) (length h + n) ==
          index lt n))
    [SMTPat (index (h @ lt) (length h + n))] = 
  rev_length h;
  admit ()

let lemma_index_of_append_skip_rev (n:nat) (h lt:list 'a) :
  Lemma 
    (requires (n < length lt /\ List.length lt > 0))
    (ensures (
      rev_length h;
      index (rev h @ lt) (length h + n) ==
          index lt n))
    [SMTPat (index (rev h @ lt) (length h + n))] =
  rev_length h;
  lemma_index_of_append_skip 0 h lt

let lemma_index_of_append_skip_0 (h lt:list 'a) :
  Lemma 
    (requires (List.length lt > 0))
    (ensures (
      rev_length h;
      index (rev h @ lt) (length h) ==
          index lt 0))
    [SMTPat (index (rev h @ lt) (length h))] =
  lemma_index_of_append_skip_rev 0 h lt

let lemma_rev_rev (l:list 'a) :
  Lemma (rev (rev l) == l) [SMTPat (rev (rev l))]= 
  rev_involutive l

let static_ltl_cmd (cmd:io_cmds) (arg:io_sig.args cmd) : IOltl (io_sig.res cmd arg) (prefix_as_ltl (io_pre cmd arg)) (next (is_event cmd arg)) 
  by (
  explode ();
  bump_nth 3;
  let _, r = destruct_and (nth_binder 4) in
  ExtraTactics.rewrite_lemma_2 (-1) 5 6;
  rewrite (nth_binder 7);
  let lem1 : term = `(rev_length (`#(nth_binder 2))) in
  let _ = pose_lemma lem1 in
  let lem2 : term = `(lemma_index_of_append_skip_0 (`#(nth_binder 2)) [convert_call_to_event (`#(nth_binder 0)) (`#(nth_binder 1)) (`#(nth_binder 6))]) in
  let _ = pose_lemma lem2 in
  explode ()
  )
  =
  static_cmd cmd arg

let eventually_closed (fd:file_descr) : IOltl unit (prefix_as_ltl' (is_open fd)) (eventually (is_event Close fd)) =
  let _ = static_ltl_cmd Close fd in
  ()

let eventually_read_closed (fd:file_descr) : IOltl unit (prefix_as_ltl' (is_open fd)) (eventually (is_event Close fd)) by (
  explode ();
  bump_nth 36;
  tadmit ();
  bump_nth 36;
  dump "h"
) =
  let _ = static_ltl_cmd Read fd in
  let _ = static_ltl_cmd Close fd in
  ()
