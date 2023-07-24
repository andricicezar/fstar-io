module TauIODiv.Test

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics // Also defines forall_intro so place before Classical

open Util
open Stream
open IIOSig
open IIOSigSpec
open TauIODiv
open DivFree
open DivFreeTauSpec
open DivFreeTauDM



let body (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun hist r -> terminates r /\ 
  (exists s. ret_trace r == [ERead fd s])) =
  let msg = read fd in
  ()

let _repeat_with_inv 
  (#pre:trace -> Type0)
  (#inv:(trace -> Type0){forall h lt. pre h /\ inv lt ==> pre (rev_acc lt h)})
  (body : iodiv_dm unit (iprepost (fun hist -> pre hist) (fun hist r -> terminates r /\ inv (ret_trace r)))) :
  iodiv_dm
    unit
    (iprepost
      (fun hist -> pre hist)
      (fun hist r -> diverges r /\ repeat_inv_post inv r)
    )
= _repeat_with_inv_aux pre inv (dm_bind body (fun _ -> dm_ret (Inl ())))

#set-options "--print_implicits"

let repeat_with_inv 
  (#pre:trace -> Type0)
  (#inv:trace -> Type0)
  (#c1:squash (forall h lt. pre h /\ inv lt ==> pre (rev_acc lt h)))
  ($body : unit -> IODiv unit pre (ensures fun hist r -> terminates r /\ inv (ret_trace r))) :
  // ^ The dollar sign here tells F* to check for type equality in this argument,
  // instead of just subtyping, so a call `repeat_with_inv body` can actually
  // help the unifier find pre/inv/c1.
  IODiv
    unit
    (requires fun hist -> pre hist)
    (ensures fun hist r -> diverges r /\ repeat_inv_post inv r)
= IODIV?.reflect (_repeat_with_inv #pre #inv (reify (body ())))

[@"opaque_to_smt"]
let myinv (fd:file_descr) : trace -> Type0 = fun tr -> exists s. tr == [ERead fd s]

[@"opaque_to_smt"]
let mypre (fd:file_descr) : trace -> Type0 = fun h -> is_open fd h

val yes : (fd:file_descr) -> squash (forall h lt. mypre fd h /\ myinv fd lt ==> mypre fd (rev_acc lt h))
let yes fd = 
  reveal_opaque (`%mypre) mypre;
  reveal_opaque (`%myinv) myinv

[@"opaque_to_smt"]
let body' (fd :file_descr) () : IODiv unit (mypre fd) (ensures fun hist r -> terminates r /\ myinv fd (ret_trace r)) =
  reveal_opaque (`%mypre) mypre;
  reveal_opaque (`%myinv) myinv;
  body fd

let repeat_with_inv' (fd:file_descr) = repeat_with_inv #(mypre fd) #(myinv fd) #(yes fd)

let repeat_loop_body (fd : file_descr) : IODiv unit (mypre fd) (ensures fun hist r -> diverges r /\ repeat_inv_post (myinv fd) r) =
  repeat_with_inv' fd (body' fd)


// let open_file (s : string) : IODiv file_descr (requires fun hist -> True) (ensures fun hist r -> terminates r /\ ret_trace r == [ EOpenfile s (result r) ]) =
//   act_call Openfile s

// let read (fd : file_descr) : IODiv string (requires fun hist -> is_open fd hist) (ensures fun hist r -> terminates r /\ ret_trace r == [ ERead fd (result r) ]) =
//   act_call Read fd

// let close (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun hist r -> terminates r /\ ret_trace r == [ EClose fd ]) =
//   act_call Close fd

let open_file' = act_call Openfile
let read' = act_call Read
let close' = act_call Close

(** for some reason, there is a big difference in how big the VC is for these synonyms. **)
let ho_test () :
  IODiv unit
    (requires (fun _ -> True))
    (ensures (fun _ _ -> True)) =
  (** this checks instantly -- 5 goals **)
  //let _ = open_file "test.txt" in
  (** this takes a little bit longer -- 56 goals **)
  // let _ = open_file' "test.txt" in
  (** this takes a long time -- 205 goals // It's now only 23! **)
  let _ = act_call Openfile "test.txt" in
  ()

let ho_test'
  (f : (unit -> IODiv unit (fun h -> True) (fun h r -> True))) :
  IODiv unit
    (requires (fun _ -> True))
    (ensures (fun _ _ -> True)) =
  let _ = f () in
  (** this checks instantly -- 10 goals **)
  //let _ = open_file "test.txt" in
  (** this takes a little bit longer -- 103 goals **)
  //let _ = open_file' "test.txt" in
  (** this takes a long time - 396 goals // Now 25 **)
  let _ = act_call Openfile "test.txt" in
  ()

let test_1 (s : string) : IODiv string (requires fun h -> True) (ensures fun _ _ -> True) =
  let fd = open_file s in
  read fd

let test_1' (s : string) : IODiv string (requires fun _ -> True) (ensures fun _ _ -> True)
= let fd = open_file s in
  let fd' = open_file s in
  read fd

let test_2 (s : string) : IODiv file_descr (requires fun _ -> True) (ensures fun _ _ -> True) =
  let msg = test_1 s in
  open_file s

let test (s : string) : IODiv unit (requires fun _ -> True) (ensures fun _ _ -> True) =
  let fd = open_file s in
  let _ = read fd in
  close fd

let print01 () : IODiv unit (requires fun _ -> True) (ensures fun hist r -> terminates r /\ (ret_trace r == [ EPrint "1"; EPrint "2"; EPrint "3"; EPrint "4"; EPrint "5"; EPrint "6"; EPrint "7"; EPrint "8"])) = //; EPrint "9"])) =
  (** Stress test : limit 8 events **)
  print "1";
  print "2";
  print "3";
  print "4";
  print "5";
  print "6";
  print "7";
  print "8"
//  ;  print "9"

let test_ (s : string) : IODiv unit (requires fun _ -> True) (ensures fun hist r -> terminates r /\ (exists fd msg. ret_trace r == [ EOpenfile s fd ; ERead fd msg ; EClose fd ])) =
  let fd = open_file s in
  let msg = read fd in
  close fd

let test'' (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun hist r -> terminates r /\ is_open fd (rev_acc (ret_trace r) hist)) =
  let msg = read fd in
  ()

let test_more (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun _ _ -> True) =
  test'' fd ; test'' fd

let test_more' (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun _ _ -> True) =
  test'' fd ;
  test'' fd ;
  test'' fd

let test3 (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun _ _ -> True) =
  let msg = read fd in
  () ; () ; ()

let test' (s : string) : IODiv unit (requires fun _ -> True) (ensures fun _ _ -> True)
= let fd = open_file s in
  let msg = read fd in
  ()

let test'_ (s : string) : IODiv string (requires fun _ -> True) (ensures fun _ _ -> True) =
  let fd = open_file s in
  read fd

let open_close_test (s : string) : IODiv unit (requires fun _ -> True) (ensures fun hist r -> terminates r /\ (exists fd. ret_trace r == [ EOpenfile s fd ; EClose fd ])) =
  let fd = open_file s in
  close fd

let many_open_test (s : string) : IODiv unit (requires fun _ -> True) (ensures fun hist r -> terminates r)
= let x = open_file s in
  let y = open_file s in
  ()

let many_open_test' (s : string) : IODiv file_descr (requires fun _ -> True) (ensures fun hist r -> terminates r) =
  let x = open_file s in
  open_file s

// Hoisting body out of repeat_open_close_test
let body2 (s:string) : unit -> IODiv unit (fun _ -> True) (fun hist r -> terminates r) =
  fun _ -> open_close_test s

let repeat_open_close_test (s : string)
  : IODiv unit (requires fun _ -> True) (ensures fun _ _ -> True)
=
  repeat_with_inv #(fun _ -> True) #(fun _ -> True) (body2 s)

let repeat_pure (t : unit -> unit) : IODiv unit (requires fun hist -> True) (ensures fun hist r -> diverges r
  // /\ False (** does not work **)
) =
  repeat_with_inv #(fun hist -> True) #(fun tr -> True) (fun () -> t () <: IODiv _ _ _);
  (** I think the explanation of this is that this is to
      be expected since iwp_bind just throws the continuition
      because the current spec diverges.**)
  assert (False)

// Hoisting body out of repeat_more
let body3 (fd:file_descr)
  : unit -> IODiv unit (fun hist -> is_open fd hist) (fun hist r -> terminates r)
  = fun _ -> let s = read fd in ()

let inv3_pf (fd:file_descr) : squash (forall h lt. is_open fd h ==> is_open fd (rev_acc lt h)) = magic()
// This is not true, so the program below is wrong I think? But then
// the program still fails even when assuming this.

// Afterwards find an example with a real invariant
let repeat_more (fd:file_descr)
  : IODiv unit
        (requires fun hist -> is_open fd hist)
        (ensures fun hist r -> diverges #unit r /\ repeat_inv_post (fun _ -> True) r)
= repeat_with_inv #_ #(fun _ -> True) #(inv3_pf fd) (body3 fd)

let repeat_test (s : string) : IODiv unit (requires fun hist -> True) (ensures fun hist r -> (*exists fd.*) diverges r (*/\ repeat_inv_post (fun tr -> exists s. tr == [ERead fd s]) r*))
= let fd = open_file s in
  repeat (fun b hist -> is_open fd hist) (fun tr -> exists s. tr == [ERead fd s]) (fun b ->
    let x = read fd in
    if b && x = "" then true else false
  ) false




let repeat_test_aux1 (fd : file_descr) : IODiv unit (requires fun hist -> is_open fd hist) (ensures fun hist r -> diverges r /\ repeat_inv_post (fun tr -> exists s. tr == [ERead fd s]) r)
// by (explode () ; bump_nth 12 ; dump "hh")
= admit () ;
  repeat (fun b hist -> is_open fd hist) (fun tr -> exists s. tr == [ERead fd s]) (fun b ->
    let x = read fd in
    if b && x = "" then true else false
  ) false

let test_using_assume (fd : file_descr) : IODiv string (requires fun _ -> True) (ensures fun hist r -> terminates r) =
  assume (forall hist. is_open fd hist) ;
  read fd

// A second test to make sure exfalso isn't used
let test_assume #a #pre (f : unit -> IODiv a (requires fun hist -> pre) (ensures fun hist r -> True)) : IODiv a (fun hist -> True) (fun hist r -> True) =
  assume pre ;
  f ()

let test_assert p : IODiv unit (requires fun hist -> p) (ensures fun hist r -> True) =
  assert p

let partial_match (l : list nat) : IODiv unit (requires fun hist -> l <> []) (ensures fun hist r -> True) =
  match l with
  | x :: r -> ()

let partial_match_io (l : list string) : IODiv file_descr (requires fun hist -> l <> []) (ensures fun hist r -> True) =
  match l with
  | s :: _ -> open_file s

let partial_match_pre (l : list nat) : IODiv nat (requires fun hist -> l <> []) (ensures fun hist r -> terminates r /\ result r == hd l) =
  match l with
  | x :: r -> x

// Cezar's tests

assume val p : prop
assume val p' : prop
assume val pure_lemma (_ : unit) : Lemma p
assume val some_f (_ : squash p) : IODiv unit (requires fun _ -> True) (ensures fun _ _ -> True)
assume val some_f' : unit -> IODiv unit (requires fun _ -> p) (ensures fun _ _ -> p')

let pure_lemma_test () : IODiv unit (requires fun _ -> True) (ensures fun _ _ -> True) =
  pure_lemma () ;
  some_f ()

let pure_lemma_test2 () : IODiv unit (requires fun _ -> True) (ensures fun _ _ -> True) =
  pure_lemma () ;
  some_f () ;
  some_f' () ;
  assert p'
