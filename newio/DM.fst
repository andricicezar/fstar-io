module DM

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open Hist

(** the behavior of f can differ based on the history in iio **)
let rec trace_of (lt:trace) (m:io 'a) (x:'a) =
  match lt, m with
  | [], Return x' -> x == x'
  | e::es, Call cmd arg k -> 
     (let (| cmd', arg', res' |) = destruct_event e in 
          (cmd' == cmd /\ arg == arg' /\ (trace_of es (k res') x)))
  | _, _ -> False

(** this is too complicated for io, but may be needed for iio: 
let rec trace_of (lt:trace) (m:io 'a) (x:'a) =
  match lt, m with
  | [], Return x' -> x == x'
  | [], Call cmd arg k -> (forall h. io_wps cmd arg (fun lt r -> lt == []) h) /\ (forall r. trace_of lt (k r) x)
  | e::es, Call cmd arg k -> 
          // either this is a silent call so we skip
          ((forall h. io_wps cmd arg (fun lt r -> lt == []) h) /\ (forall r. trace_of lt (k r) x)) \/
          // either this call has an event on the local trace
          (let (| cmd', arg', res' |) = destruct_event e in 
            (cmd' == cmd /\ arg == arg' /\ (trace_of es (k res') x)))
  | _, _ -> False **)

(** maybe worth thinking about a way to avoid using a different function: 
let exact_2 x y = fun x' y' -> x == x' /\ y == y'

let rec lemma_more_general_law m p h : 
  Lemma 
    (requires theta m p h) 
    (ensures (forall lt x. theta m (exact_2 lt x) h ==> p lt x)) = () **)

let exists_trace_of (x:'a) (m:io 'a) =
  exists lt. trace_of lt m x

let rec lemma_return_of_implies_exists_trace_of (x:'a) (m:io 'a) : 
  Lemma
    (requires (x `return_of` m))
    (ensures (exists_trace_of x m)) =
  match m with
  | Return _ -> assert (trace_of [] m x)
  | Call cmd arg k -> begin
    eliminate exists r. (x `return_of` (k r)) returns (exists_trace_of x m) with _. begin
      lemma_return_of_implies_exists_trace_of x (k r);
      assert (exists klt. trace_of klt (k r) x) by (assumption ());
      eliminate exists klt. trace_of klt (k r) x returns (exists_trace_of x m) with _. begin
        let e = convert_call_to_event cmd arg r in
        introduce exists lt. (trace_of lt m x) with (e::klt) and begin
          assert (trace_of (e::klt) m x)
        end
      end
    end
  end

unfold let io_wps (cmd:io_cmds) (arg:io_args cmd) : hist #event (io_resm cmd) = fun p h ->
  match cmd with
 // | GetTrace -> p [] h
  | _ -> io_pre cmd arg h /\ (forall r. p [convert_call_to_event cmd arg r] r)

let tret_of (m:free 'op 's 'a) : Type = (x:'a{x `return_of` m})

(** Inspierd from Kenji's thesis (2.4.5) **)
let rec theta (#a:Type) (m : io a) : hist #event (x:a{x `return_of` m}) =
  match m with
  | Return x -> hist_return x
  | Call cmd arg k ->
    hist_bind (io_resm cmd) (x:a{x `return_of` m}) (io_wps cmd arg) (fun r -> theta (k r))

let rec lemma_theta_result_implies_post m p h : 
  Lemma 
    (requires theta m p h) 
    (ensures (forall x lt. trace_of lt m x ==> p lt x)) =
  introduce forall x lt. trace_of lt m x ==> p lt x with begin
    introduce trace_of lt m x ==> p lt x with _. begin
      match m with
      | Return _ -> ()
      | Call cmd arg k -> begin
        let e::klt = lt in
        let (| cmd', arg', res' |) = destruct_event e in
        lemma_theta_result_implies_post (k res') (hist_post_shift p [convert_call_to_event cmd arg res']) (convert_call_to_event cmd arg res' :: h);
        assert (trace_of klt (k res') x) by (smt ());
        assert (hist_post_shift p [convert_call_to_event cmd arg res'] klt x) by (smt ())
      end
    end
  end

let rec lemma_return_of_free_bind (m:io 'a) (mx:'a{mx `return_of` m}) (f:(x:'a{x `return_of` m}) -> io 'b) :
  Lemma (forall fx. fx `return_of` (f mx) ==> fx `return_of` (io_bind m f)) =
  introduce forall fx. fx `return_of` (f mx) ==> fx `return_of` (io_bind m f) with begin
    introduce fx `return_of` (f mx) ==> fx `return_of` (io_bind m f) with _. begin
      match m with
      | Return _ -> ()
      | Call cmd arg k -> begin
        eliminate exists r. return_of mx (k r) returns fx `return_of` (io_bind m f) with _. begin
	  lemma_return_of_free_bind (k r) mx f
	end
      end
    end
  end

unfold 
let cast_hist_bind_return_of
  (m:io 'a)
  (mx:'a{mx `return_of` m})
  (f:(x:'a{x `return_of` m}) -> io 'b)
  (wp:hist (x:'b{x `return_of` f mx})) :
  Tot (hist (x:'b{x `return_of` (io_bind m f)})) =
  lemma_return_of_free_bind m mx f;
  wp

let theta_of_f_x 
  (m:io 'a)
  (f:(x:'a{x `return_of` m}) -> io 'b)
  (mx:'a{mx `return_of` m}) :
  Tot (hist (x:'b{x `return_of` (io_bind m f)})) =
  cast_hist_bind_return_of m mx f (theta (f mx))

(**
let hist_bind' (m:io 'a) (f:'a -> io 'b) (wp1:hist (x:'a{x `return_of` m})) (wp2:((x:'a) -> hist (x':'b{x' `return_of` (f x)}))) : hist (x:'b{x `return_of` io_bind m f})=
  hist_bind wp1 wp2**)
  
let lemma_theta_is_monad_morphism_ret v :
  Lemma (theta (io_return v) == hist_return v) by (compute ()) = ()

(** TODO: remove the admits **)
let rec lemma_theta_is_monad_morphism_bind (m:io 'a) (f:(x:'a{x `return_of` m}) -> io 'b) :
  Lemma
    (theta (io_bind m f) == hist_bind _ _ (theta m) (theta_of_f_x m f)) = 
  match m with
  | Return x ->
    calc (==) {
      theta (io_bind m f);
      == {}
      theta (io_bind (Return x) f);
      == {} // unfold io_bind
      theta (f x); 
      == { _ by (tadmit ()) } // unfold hist_bind
      hist_bind _ _ (hist_return x) (theta_of_f_x m f);
      == { _ by (compute ()) } // unfold theta
      hist_bind _ _ (theta (Return x)) (theta_of_f_x m f);
    };
    (** this should be inside calc, but for some reason it fails there **)
    assert (hist_bind _ _ (theta (Return x))  (theta_of_f_x m f)
      == hist_bind _ _ (theta m) (theta_of_f_x m f)) by (rewrite_eqs_from_context ())
  | Call cmd arg k ->

    admit ()
     (**
    (** this should be useful later to do a rewrite **)
    introduce forall (r:io_resm cmd). theta (io_bind (k r) f) == hist_bind (theta (k r)) (theta_of_f_x m f) with begin
      lemma_theta_is_monad_morphism_bind (k r) f
    end;

    calc (==) {
      theta (io_bind m f);
      == {}
      theta (io_bind (Call cmd arg k) f);
      == { _ by (compute ()) } // unfold io_bind
      theta (Call cmd arg (fun r -> io_bind (k r) f)) <: hist (x:'b{x `return_of` Call cmd arg (fun r -> io_bind (k r) f)});
      == { _ by (tadmit (); (); dump "h") } // unfold theta
      hist_bind (io_wps cmd arg) (fun r -> theta (io_bind (k r) f));
      == { _ by (tadmit ()) } // rewrite here by applying this lemma again for (k r) and f
      hist_bind (io_wps cmd arg) (fun r -> hist_bind (theta (k r)) (theta_of_f_x m f));
      == { lemma_hist_bind_associativity (io_wps cmd arg) (fun r -> theta (k r)) (theta_of_f_x m f) }
      hist_bind #_ #(x:'a{x `return_of` m}) #(x:'b{x `return_of` io_bind m f}) (hist_bind (io_wps cmd arg) (fun r -> theta (k r))) (theta_of_f_x m f);
      == { _ by (compute ()) } // unfold theta
      hist_bind #_ #(x:'a{x `return_of` m}) #(x:'b{x `return_of` io_bind m f}) (theta (Call cmd arg k)) (theta_of_f_x m f);
    };
    (** this should be inside calc, but for some reason it fails there **)
    assert (hist_bind (theta (Call cmd arg k)) (theta_of_f_x m f)
      == hist_bind (theta m) (theta_of_f_x m f)) by (rewrite_eqs_from_context ()) **)

// The Dijkstra Monad
let dm (a:Type) (wp:hist a) =
  (m:(io a){wp `hist_ord` theta m})

let dm_return (a : Type) (x : a) : dm a (hist_return x) =
  io_return x

let awesome_lemma 
  (a b:Type)
  (v:io a)
  (f:(x:a{x `return_of` v}) -> io b) : 
  Lemma (
  (hist_bind (x:a{x `return_of` v}) b (theta v) (fun x -> theta (f x))) == 
    ((hist_bind (x:a{x `return_of` v}) (x:b{x `return_of` io_bind v f}) (theta v) (theta_of_f_x v f)) <: hist b)) by 
    (explode ();
     tadmit (); tadmit ();
    ExtraTactics.rewrite_lemma 5 6;
    norm [delta_only [`%theta_of_f_x; `%cast_hist_bind_return_of]];
    tadmit ();
    dump "H")= () 
    
let dm_bind
  (a b : Type)
  (wp_v : hist a)
  (wp_f: a -> hist b)
  (v : dm a wp_v)
  (f : (x:a{x `return_of` v} -> dm b (wp_f x))) :
  Tot (dm b (hist_bind _ _ wp_v wp_f)) =
  (** we lost the fact that theta is a monad morphism because we added
      the refinement `return_of` on the free_bind. We can prove this bind, 
      if we specialize the proof (Theo was able to that for his DM), but that
      implies that we do not get a DM for free. **)
  
  (** hist is monotonic. **)
  
  lemma_theta_is_monad_morphism_bind v f;
  (**
  calc (==) {
    theta (io_bind v f);
    == { lemma_theta_is_monad_morphism_bind v f }
    hist_bind (x:a{x `return_of` v}) _ (theta v) (theta_of_f_x v f);
    == { _ by (norm [delta_only [`%theta_of_f_x; `%cast_hist_bind_return_of]]; dump "H") }
    hist_bind (x:a{x `return_of` v}) b (theta v) (fun x -> theta (f x));
  }; **)
  assert (theta (io_bind v f) == hist_bind (x:a{return_of x v}) (x:b{return_of x (io_bind v f)}) (theta v) (theta_of_f_x v f)); 
  assert (wp_v `hist_ord` theta v);
  assert (forall (x:a{x `return_of` v}). wp_f x `hist_ord #_ #b` theta (f x));

  assert (hist_bind a b wp_v wp_f `hist_ord #_ #b`
  	   hist_bind (x:a{x `return_of` v}) _ (theta v) (fun x -> theta (f x)));
	   
  awesome_lemma a b v f;
  (** goal: **)
  assert (hist_bind _ b wp_v wp_f `hist_ord #_ #b` theta (io_bind v f));

  io_bind v f

let dm_subcomp (a:Type) (wp1 wp2: hist a) (f : dm a wp1) :
  Pure (dm a wp2)
    (requires hist_ord wp2 wp1)
    (ensures fun _ -> True) =
  f

let dm_if_then_else (a : Type) (wp1 wp2: hist a) (f : dm a wp1) (g : dm a wp2) (b : bool) : Type =
  dm a (hist_if_then_else wp1 wp2 b)

let lemma_hist_bind_implies_wp2_if_x
  (wp1:hist 'a) (wp2:'a -> hist 'b)
  (m:dm 'a wp1) p h x :
  Lemma 
    (requires (hist_bind _ _ wp1 wp2 p h /\ x `return_of` m))
    (ensures (exists lt. wp2 x (hist_post_shift p lt) (List.rev lt @ h))) =
  lemma_theta_result_implies_post m (fun lt r -> wp2 r (hist_post_shift p lt) (rev lt @ h)) h;
  lemma_return_of_implies_exists_trace_of x m
