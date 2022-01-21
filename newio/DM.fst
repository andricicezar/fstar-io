module DM

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open Hist


unfold
let ret (m : free 'op 'sig 'a) =
  x : 'a { x `return_of` m }

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

(** Inspierd from Kenji's thesis (2.4.5) **)
let rec theta (#a:Type) (m : io a) : hist #event (x:a{x `return_of` m}) =
  match m with
  | Return x -> hist_return x
  | Call cmd arg k ->
    hist_bind (io_resm cmd) (x:a{x `return_of` m}) (io_wps cmd arg) (fun r -> theta (k r))

(** this proof is not robust, sometimes it passes, sometimes it is not **)
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

let lemma_theta_is_monad_morphism_ret v :
  Lemma (theta (io_return v) == hist_return v) by (compute ()) = ()

let theta_of_f_x 
  (m:io 'a)
  (f:(x:'a{x `return_of` m}) -> io 'b)
  (mx:'a{mx `return_of` m}) :
  Tot (hist (ret (io_bind m f))) =
  lemma_return_of_free_bind m mx f;
  hist_subcomp (theta (f mx))

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
  
let getref #a #p (x : a { p x }) : Lemma (p x) = ()


let another_lemma (wp1:hist 'a) (wp2:'a -> hist 'b) (wp3:'a -> hist 'b) p h : 
  Lemma 
    (requires ((forall x. (wp2 x) `hist_ord` (wp3 x)) /\ hist_bind _ _ wp1 wp2 p h))
    (ensures (hist_bind _ _ wp1 wp3 p h)) = ()
    
#set-options "--print_implicits --print_bound_var_types"

let awesome_lemma 
  (a b:Type)
  (v:io a)
  (f:(ret v) -> io b) : 
  Lemma (
  (hist_bind (ret v) b (theta v) (fun x -> hist_subcomp (theta (f x)))) `hist_ord` 
    hist_subcomp #_ #_ #(fun x -> x `return_of` (io_bind v f)) (hist_bind (ret v) (ret (io_bind v f)) (theta v) (theta_of_f_x v f))) = 

  let wp1 : hist b =                   hist_bind (ret v) b                   (theta v) (fun x -> hist_subcomp (theta (f x))) in
  let wp2 : hist (ret (io_bind v f)) = hist_bind (ret v) (ret (io_bind v f)) (theta v) (theta_of_f_x v f) in

  assert (theta v `hist_ord` theta v);
  assert (forall (x:ret v). (hist_subcomp (theta (f x))) `hist_ord #_ #b` (theta_of_f_x v f x));
  introduce forall (p:hist_post b) h. wp1 p h ==> wp2 p h with begin
      introduce wp1 p h ==> wp2 p h with _. begin
        another_lemma #event #(ret v) #b (theta v) (fun x -> hist_subcomp (theta (f x))) (theta_of_f_x v f) p h;
        let p1 = (fun lt (r:ret v) -> theta_of_f_x #a #b v f r (fun lt' (r':b) -> p (lt@lt') r') (List.rev lt @ h)) in
        let p2 = (fun lt (r:ret v) -> theta_of_f_x #a #b v f r (fun lt' (r':ret (io_bind v f)) -> p (lt@lt') r') (List.rev lt @ h)) in
        assert (p1 `hist_post_ord` p2);
        assert (theta v p1 h); 
        assert (theta v p2 h);
        assert (wp2 p h)
    end
  end

let dm_bind
  (a b : Type)
  (wp_v : hist a)
  (wp_f: a -> hist b)
  (v : dm a wp_v)
  (f : (x:a{x `return_of` v} -> dm b (wp_f x))) :
  Tot (dm b (hist_bind _ _ wp_v wp_f)) =
  calc (hist_ord) {
    hist_bind a b wp_v wp_f;
    `hist_ord` { 
         assert (wp_v `hist_ord` theta v); 
         assert (forall (x:(ret v)). wp_f x `hist_ord #_ #b` theta (f x))
         (** hist is monotonic **) 
    } 
    hist_bind (ret v) b (theta v) (fun x -> hist_subcomp #_ #b #(fun x' -> x' `return_of` (f x)) (theta (f x)));
    `hist_ord` { awesome_lemma a b v f }
    hist_subcomp #_ #b #(fun x' -> x' `return_of` (io_bind v f)) (hist_bind (ret v) (ret (io_bind v f)) (theta v) (theta_of_f_x v f));
    == { lemma_theta_is_monad_morphism_bind v f }
    hist_subcomp #_ #b #(fun x' -> x' `return_of` (io_bind v f)) (theta (io_bind v f));
  };
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
