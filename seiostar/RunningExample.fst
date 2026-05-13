module RunningExample

open FStar.Tactics.V1
open Trace
open IOStar
open RQ.Metaprogram
open ExamplesIO
open RrHP
open QTypes.OpenValComp
open QTypes.HelperTactics
open RQ.TypingRelation
open LambdaIO

(* We consider the task is string that need to replace the old contents *)

val notb : bool -> bool
let notb b = if b then false else true

val andb : bool -> bool -> bool
let andb b1 b2 = if b1 then b2 else false

val validate : string -> string -> string -> bool
let validate olds task news = eq_string task news
  // andb (notb (eq_string olds news)) (eq_string task news)

let read_file (f : string) : io (resexn string) =
  let!@! fd = io_call OOpen f in
  let!@! r = io_call ORead fd in
  let!@! () = io_call OClose fd in
  io_return (Inl r)


val wrapper : string -> string -> (string -> string -> io unit) -> io (resexn unit)
let wrapper f task agent =
  let!@! contents = read_file f in
  let!@ () = agent f task in
  let!@! new_contents = read_file f in
  if validate contents task new_contents
  then io_return (Inl ())
  else io_return (Inr ())


(* Specification *)

unfold
let hist_prepost #a (pre : hist_pre) (post : (h:_ -> hist_post h a)) : hist a =
  fun h p -> pre h /\ (forall r lt. post h lt r ==> p lt r)

let rec fst_read_from_fd (fd:file_descr) (lt:trace) =
  match lt with
  | [] -> None
  | EvRead fd' (Inl msg) ::lt' -> if fd = fd' then Some msg else fst_read_from_fd fd lt'
  | _::lt' -> fst_read_from_fd fd lt'

let rec fst_read_from (f:string) (lt:trace) =
  match lt with
  | [] -> None
  | EvOpen f' (Inl fd) ::lt' -> if f = f' then fst_read_from_fd fd lt' else fst_read_from f lt'
  | _::lt' -> fst_read_from f lt'

let rec last_read_from_open (f:string) (lt:trace) =
  match lt with
  | [] -> None
  | EvOpen f' (Inl fd) ::lt' -> if f = f' then Some fd else last_read_from_open f lt'
  | _::lt' -> last_read_from_open f lt'

let rec last_read_from_read (fnm:string) (fd:file_descr) (lt:trace) =
  match lt with
  | [] -> None
  | EvRead fd' (Inl msg) ::lt' -> if fd = fd' then Some msg else last_read_from_read fnm fd lt'
  | EvOpen f' (Inl fd') ::lt' -> if fnm = f' && fd = fd' then None else last_read_from_read fnm fd lt'
  | _::lt' -> last_read_from_read fnm fd lt'

let last_read_from (f:string) (lt:trace) =
  match last_read_from_open f (List.rev lt) with
  | None -> None
  | Some fd -> last_read_from_read f fd (List.rev lt)


(* We assume the agent as a trivial spec.
  In principle we should require in the wrapper that the agent satisfies it,
  because we would need parametricity to claim it.
  For now we assume it in the proof.
*)
unfold
let agent_spec =
  hist_prepost
    (fun h -> True)
    (fun h lt r -> True)

unfold
let openfile_spec (f : string) =
  hist_prepost
    (fun h -> True)
    (fun h lt (r:resexn file_descr) ->
      Inl? r ==>
      lt == [ EvOpen f (Inl (Inl?.v r)) ]
    )

let openfile_sat_spec f :
  Lemma (theta (io_call OOpen f) ⊑ openfile_spec f)
= ()

unfold
let read_spec (fd : file_descr) =
  hist_prepost
    (fun h -> True)
    (fun h lt (r:resexn string) ->
      Inl? r ==>
      lt == [ EvRead fd (Inl (Inl?.v r)) ]
    )

let read_sat_spec fd :
  Lemma (theta (io_call ORead fd) ⊑ read_spec fd)
= ()

unfold
let close_spec (fd : file_descr) =
  hist_prepost
    (fun h -> True)
    (fun h lt (r:resexn unit) ->
      Inl? r ==>
      lt == [ EvClose fd (Inl ()) ]
    )

let close_sat_spec fd :
  Lemma (theta (io_call OClose fd) ⊑ close_spec fd)
= ()

unfold
let read_file_spec (f : string) =
  hist_prepost
    (fun h -> True)
    (fun h lt (r:resexn string) ->
      Inl? r ==>
      exists fd. lt == [ EvOpen f (Inl fd) ; EvRead fd (Inl (Inl?.v r)) ; EvClose fd (Inl ()) ]
    )

let hist_bind_commut_resexn #a #b (m : hist (resexn a)) (k : a -> io (resexn b)) :
  Lemma (
    hist_bind m (fun (r : resexn a) -> theta (match r with | Inl x -> k x | Inr x -> io_return (Inr x))) `hist_equiv`
    hist_bind m (fun r -> match r with | Inl x -> theta (k x) | Inr x -> hist_return (Inr x)))
= introduce forall r. (fun (r : resexn a) -> theta (match r with | Inl x -> k x | Inr x -> io_return (Inr x))) r `hist_equiv` (fun r -> match r with | Inl x -> theta (k x) | Inr x -> hist_return (Inr x)) r
  with begin
    match r with
    | Inl x -> ()
    | Inr x -> theta_monad_morphism_ret #(resexn a) (Inr x)
  end ;
  lem_hist_bind_equiv m m (fun (r : resexn a) -> theta (match r with | Inl x -> k x | Inr x -> io_return (Inr x))) (fun r -> match r with | Inl x -> theta (k x) | Inr x -> hist_return (Inr x))

unfold
let hist_inl #a #b (k : a -> hist (resexn b)) (r : resexn a) : hist (resexn b) =
  fun h p ->
    (Inl? r ==> k (Inl?.v r) h p) /\
    (hist_return (Inr ()) h p)

let hist_bind_resexn_weaken #a #b (m : hist (resexn a)) (k : a -> io (resexn b)) :
  Lemma (
    hist_bind m (fun (r : resexn a) -> theta (match r with | Inl x -> k x | Inr x -> io_return (Inr x))) ⊑
    hist_bind m (hist_inl (fun x -> theta (k x)))
  )
= introduce forall r. (fun (r : resexn a) -> theta (match r with | Inl x -> k x | Inr x -> io_return (Inr x))) r ⊑ (hist_inl (fun x -> theta (k x))) r
  with begin
    match r with
    | Inl x -> ()
    | Inr x -> theta_monad_morphism_ret #(resexn b) (Inr x)
  end ;
  lem_hist_bind_subset m m (fun (r : resexn a) -> theta (match r with | Inl x -> k x | Inr x -> io_return (Inr x))) (hist_inl (fun x -> theta (k x)))

let lem_hist_bind_hist_inl_subset #a #b (w:hist (resexn a)) (k1 k2 : a -> hist (resexn b))
  (lem : (x:a -> Lemma (k1 x ⊑ k2 x))) :
  Lemma (hist_bind w (hist_inl k1) ⊑ hist_bind w (hist_inl k2))
= Classical.forall_intro (Classical.move_requires lem)

let lem_hist_bind_match_resexn_subset (#a #b:Type) (m:hist (resexn a))
  (k1 k2 : a -> hist (resexn b))
  (lem : (x:a -> Lemma (k1 x ⊑ k2 x))) :
  Lemma (
    hist_bind m (fun res -> match res with | Inl x -> k1 x | Inr e -> hist_return (Inr e))
    ⊑
    hist_bind m (fun res -> match res with | Inl x -> k2 x | Inr e -> hist_return (Inr e))
  )
= Classical.forall_intro (Classical.move_requires lem)

#push-options "--z3rlimit 50"
let close_return_pointwise (fd:file_descr) (r:string) (res:resexn unit) :
  Lemma (
    theta (match res with | Inl () -> io_return (Inl r) | Inr x -> io_return (Inr x))
    ⊑
    (hist_inl (fun () -> hist_return (Inl r))) res
  )
= theta_monad_morphism_ret (Inl #string #unit r);
  theta_monad_morphism_ret (Inr #string #unit ());
  match res with | Inl () -> () | Inr _ -> ()
#pop-options

#push-options "--z3rlimit 50"
let close_return_sat_spec (fd:file_descr) (r:string) :
  Lemma (
    theta (let!@! () = io_call OClose fd in io_return (Inl r))
    ⊑
    hist_bind (close_spec fd) (hist_inl (fun () -> hist_return (Inl r)))
  )
= calc (⊑) {
    theta (let!@! () = io_call OClose fd in io_return (Inl r)) ;
    `hist_equiv` {
      theta_monad_morphism_bind (io_call OClose fd) (fun res ->
        match res with | Inl () -> io_return (Inl r) | Inr x -> io_return (Inr x))
    }
    hist_bind (theta (io_call OClose fd)) (fun res ->
      theta (match res with | Inl () -> io_return (Inl r) | Inr x -> io_return (Inr x))
    ) ;
    ⊑ { close_sat_spec fd }
    hist_bind (close_spec fd) (fun res ->
      theta (match res with | Inl () -> io_return (Inl r) | Inr x -> io_return (Inr x))
    ) ;
    ⊑ { hist_bind_resexn_weaken (close_spec fd) (fun () -> io_return (Inl r)) }
    hist_bind (close_spec fd) (hist_inl (fun () -> theta (io_return (Inl r)))) ;
    ⊑ {
      theta_monad_morphism_ret (Inl #string #unit r);
      introduce forall (res:resexn unit).
        (hist_inl (fun () -> theta (io_return (Inl r)))) res ⊑
        (hist_inl (fun () -> hist_return (Inl r))) res
      with ()
    }
    hist_bind (close_spec fd) (hist_inl (fun () -> hist_return (Inl r))) ;
  }
#pop-options

#push-options "--z3rlimit 100"
let read_close_return_sat_spec (fd:file_descr) :
  Lemma (
    theta (
      let!@! r = io_call ORead fd in
      let!@! () = io_call OClose fd in
      io_return (Inl r)
    )
    ⊑
    hist_bind (read_spec fd) (hist_inl (fun r ->
      hist_bind (close_spec fd) (hist_inl (fun () -> hist_return (Inl r)))))
  )
=
  assert (
    theta (
      let!@! r = io_call ORead fd in
      let!@! () = io_call OClose fd in
      io_return (Inl r)
    )
    ==
    theta (
      io_bind (io_call ORead fd) (fun res ->
        match res with
        | Inl r ->
          let!@! () = io_call OClose fd in
          io_return (Inl r)
        | Inr x -> io_return (Inr x)
      )
    )
  ) by (compute());
  theta_monad_morphism_bind (io_call ORead fd) (fun res ->
    match res with
    | Inl r ->
      let!@! () = io_call OClose fd in
      io_return (Inl r)
    | Inr x -> io_return (Inr x)
  );
  read_sat_spec fd;
  hist_bind_resexn_weaken (read_spec fd) (fun r ->
    let!@! () = io_call OClose fd in
    io_return (Inl r)
  );
  lem_hist_bind_hist_inl_subset (read_spec fd)
    (fun r -> theta (let!@! () = io_call OClose fd in io_return (Inl r)))
    (fun r -> hist_bind (close_spec fd) (hist_inl (fun () -> hist_return (Inl r))))
    (fun r -> close_return_sat_spec fd r)
#pop-options

#push-options "--z3rlimit 200 --fuel 8 --ifuel 4"
let read_file_bind_chain_sat_spec (f:string) :
  Lemma (
    hist_bind (openfile_spec f) (hist_inl (fun fd ->
      hist_bind (read_spec fd) (hist_inl (fun r ->
        hist_bind (close_spec fd) (hist_inl (fun () ->
          hist_return (Inl r)))))))
    ⊑
    read_file_spec f
  )
= ()
#pop-options

let read_file_sat_spec f :
  Lemma (theta (read_file f) ⊑ read_file_spec f)
= calc (⊑) {
    theta (read_file f) ;
    == {}
    theta (
      let!@! fd = io_call OOpen f in
      let!@! r = io_call ORead fd in
      let!@! () = io_call OClose fd in
      io_return (Inl r)
    ) ;
    == { _ by (compute ()) }
    theta (
      io_bind (io_call OOpen f) (fun res ->
        match res with
        | Inl fd ->
          let!@! r = io_call ORead fd in
          let!@! () = io_call OClose fd in
          io_return (Inl r)
        | Inr x -> io_return (Inr x)
      )
    ) ;
    `hist_equiv` {
      theta_monad_morphism_bind (io_call OOpen f) (fun res ->
        match res with
        | Inl fd ->
          let!@! r = io_call ORead fd in
          let!@! () = io_call OClose fd in
          io_return (Inl r)
        | Inr x -> io_return (Inr x)
      )
    }
    hist_bind (theta (io_call OOpen f)) (fun res ->
      theta (
        match res with
        | Inl fd ->
          let!@! r = io_call ORead fd in
          let!@! () = io_call OClose fd in
          io_return (Inl r)
        | Inr x -> io_return (Inr x)
      )
    ) ;
    ⊑ { openfile_sat_spec f }
    hist_bind (openfile_spec f) (fun res ->
      theta (
        match res with
        | Inl fd ->
          let!@! r = io_call ORead fd in
          let!@! () = io_call OClose fd in
          io_return (Inl r)
        | Inr x -> io_return (Inr x)
      )
    ) ;
    ⊑ {
      hist_bind_resexn_weaken (openfile_spec f) (fun fd ->
        let!@! r = io_call ORead fd in
        let!@! () = io_call OClose fd in
        io_return (Inl r)
      )
    }
    hist_bind (openfile_spec f) (hist_inl (fun fd ->
      theta (
        let!@! r = io_call ORead fd in
        let!@! () = io_call OClose fd in
        io_return (Inl r)
      )
    )) ;
    ⊑ {
      lem_hist_bind_hist_inl_subset (openfile_spec f)
        (fun fd ->
          theta (let!@! r = io_call ORead fd in let!@! () = io_call OClose fd in io_return (Inl r)))
        (fun fd ->
          hist_bind (read_spec fd) (hist_inl (fun r ->
            hist_bind (close_spec fd) (hist_inl (fun () -> hist_return (Inl r))))))
        (fun fd -> read_close_return_sat_spec fd)
    }
    hist_bind (openfile_spec f) (hist_inl (fun fd ->
      hist_bind (read_spec fd) (hist_inl (fun r ->
        hist_bind (close_spec fd) (hist_inl (fun () ->
          hist_return (Inl r)
        ))
      ))
    )) ;
    ⊑ { read_file_bind_chain_sat_spec f }
    read_file_spec f ;
  }

unfold
let wrapper_spec (f task : string) =
  hist_prepost
    (fun h -> True)
    (fun h lt (r:resexn unit) -> Inl? r ==>
      Some? (fst_read_from f lt) /\ Some? (last_read_from f lt) /\
      (validate (Some?.v (fst_read_from f lt)) task (Some?.v (last_read_from f lt))))

#push-options "--z3rlimit 100"
let read_validate_sat_spec (f task contents : string) :
  Lemma (
    theta (
      let!@! new_contents = read_file f in
      if validate contents task new_contents
      then io_return (Inl ())
      else io_return (Inr ())
    )
    ⊑
    hist_bind (read_file_spec f) (fun res' ->
      match res' with
      | Inl new_contents ->
        hist_if_then_else
          (hist_return (Inl ()))
          (hist_return (Inr ()))
          (validate contents task new_contents)
      | Inr x -> hist_return (Inr x)
    )
  )
= assert (
    theta (
      let!@! new_contents = read_file f in
      if validate contents task new_contents
      then io_return (Inl ())
      else io_return (Inr ())
    )
    ==
    theta (
      io_bind (read_file f) (fun res ->
        match res with
        | Inl new_contents ->
          if validate contents task new_contents
          then io_return (Inl ())
          else io_return (Inr ())
        | Inr x -> io_return (Inr x)
      )
    )
  ) by (compute(); trefl());
  theta_monad_morphism_bind (read_file f) (fun res ->
    match res with
    | Inl new_contents ->
      if validate contents task new_contents
      then io_return (Inl ())
      else io_return (Inr ())
    | Inr x -> io_return (Inr x)
  );
  read_file_sat_spec f;
  hist_bind_commut_resexn (read_file_spec f) (fun new_contents ->
    if validate contents task new_contents
    then io_return (Inl ())
    else io_return (Inr ())
  );
  theta_monad_morphism_ret (Inl #unit #unit ());
  theta_monad_morphism_ret (Inr #unit #unit ())
#pop-options

let inner_computation_sat_spec (f task contents : string) (agent : string -> string -> io unit) :
  Lemma (requires theta (agent f task) ⊑ agent_spec) (ensures
    theta (
      let!@ () = agent f task in
      let!@! new_contents = read_file f in
      if validate contents task new_contents
      then io_return (Inl ())
      else io_return (Inr ())
    )
    ⊑
    hist_bind agent_spec (fun () ->
      hist_bind (read_file_spec f) (fun res' ->
        match res' with
        | Inl new_contents ->
          hist_if_then_else
            (hist_return (Inl ()))
            (hist_return (Inr ()))
            (validate contents task new_contents)
        | Inr x -> hist_return (Inr x)
      )
    )
  )
= let body : unit -> io (resexn unit) = fun () ->
    let!@! new_contents = read_file f in
    if validate contents task new_contents
    then io_return (Inl ())
    else io_return (Inr ())
  in
  let body_spec : unit -> hist (resexn unit) = fun () ->
    hist_bind (read_file_spec f) (fun res' ->
      match res' with
      | Inl new_contents ->
        hist_if_then_else
          (hist_return (Inl ()))
          (hist_return (Inr ()))
          (validate contents task new_contents)
      | Inr x -> hist_return (Inr x))
  in
  assert (
    theta (
      let!@ () = agent f task in
      let!@! new_contents = read_file f in
      if validate contents task new_contents
      then io_return (Inl ())
      else io_return (Inr ())
    )
    ==
    theta (io_bind (agent f task) body)
  ) by (compute(); trefl());
  theta_monad_morphism_bind (agent f task) body;
  read_validate_sat_spec f task contents;
  assert (forall (u:unit). theta (body u) ⊑ body_spec u);
  lem_hist_bind_subset (theta (agent f task)) agent_spec (fun u -> theta (body u)) body_spec

#push-options "--z3rlimit 100"
let wrapper_inner_step (f task : string) (agent : string -> string -> io unit) :
  Lemma (requires theta (agent f task) ⊑ agent_spec) (ensures
    hist_bind (read_file_spec f) (fun res ->
      match res with
      | Inl contents ->
        theta (
          let!@ () = agent f task in
          let!@! new_contents = read_file f in
          if validate contents task new_contents
          then io_return (Inl ())
          else io_return (Inr ())
        )
      | Inr x -> hist_return (Inr x))
    ⊑
    hist_bind (read_file_spec f) (fun res ->
      match res with
      | Inl contents ->
        hist_bind agent_spec (fun () ->
          hist_bind (read_file_spec f) (fun res' ->
            match res' with
            | Inl new_contents ->
              hist_if_then_else
                (hist_return (Inl ()))
                (hist_return (Inr ()))
                (validate contents task new_contents)
            | Inr x -> hist_return (Inr x)
          )
        )
      | Inr x -> hist_return (Inr x))
  )
= let k1 (contents:string) : hist (resexn unit) =
      theta (
        let!@ () = agent f task in
        let!@! new_contents = read_file f in
        if validate contents task new_contents
        then io_return (Inl ())
        else io_return (Inr ())
      )
  in
  let k2 (contents:string) : hist (resexn unit) =
      hist_bind agent_spec (fun () ->
        hist_bind (read_file_spec f) (fun res' ->
          match res' with
          | Inl new_contents ->
            hist_if_then_else
              (hist_return (Inl ()))
              (hist_return (Inr ()))
              (validate contents task new_contents)
          | Inr x -> hist_return (Inr x)
        )
      )
  in
  let pf (contents:string) : Lemma (k1 contents ⊑ k2 contents) =
    inner_computation_sat_spec f task contents agent
  in
  lem_hist_bind_match_resexn_subset (read_file_spec f) k1 k2 pf
#pop-options

#push-options "--fuel 4 --ifuel 2"
let lem_fst_read_from_prefix (f:string) (fd:file_descr) (contents:string) (rest:trace) :
  Lemma (ensures (
    fst_read_from f (List.Tot.append [EvOpen f (Inl fd); EvRead fd (Inl contents); EvClose fd (Inl ())] rest) = Some contents))
    [SMTPat (fst_read_from f (List.Tot.append [EvOpen f (Inl fd); EvRead fd (Inl contents); EvClose fd (Inl ())] rest))]
= ()
#pop-options

open FStar.List.Tot.Properties

#push-options "--fuel 5 --ifuel 2 --z3rlimit 50"
let lem_last_read_from_suffix (f:string) (fd:file_descr) (nc:string) (prefix:trace) :
  Lemma (ensures last_read_from f (List.Tot.append prefix [EvOpen f (Inl fd); EvRead fd (Inl nc); EvClose fd (Inl ())]) = Some nc)
    [SMTPat (last_read_from f (List.Tot.append prefix [EvOpen f (Inl fd); EvRead fd (Inl nc); EvClose fd (Inl ())]))]
= rev_append prefix [EvOpen f (Inl fd); EvRead fd (Inl nc); EvClose fd (Inl ())]
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 30"
let wrapper_sat_spec_aux f task agent :
  Lemma (
    hist_bind (read_file_spec f) (fun res ->
      match res with
      | Inl contents ->
        hist_bind agent_spec (fun () ->
          hist_bind (read_file_spec f) (fun res' ->
            match res' with
            | Inl new_contents ->
              hist_if_then_else
                (hist_return (Inl ()))
                (hist_return (Inr ()))
                (validate contents task new_contents)
            | Inr x -> hist_return (Inr x)
          )
        )
      | Inr x -> hist_return (Inr x)
    ) ⊑
    wrapper_spec f task
  )
= let rev_lem (a b : trace) : Lemma (ensures List.rev (List.Tot.append a b) == List.Tot.append (List.rev b) (List.rev a)) [SMTPat (List.rev (List.Tot.append a b))] =
    rev_append a b
  in
  let aa_lem (a b c : trace) : Lemma (ensures List.Tot.append a (List.Tot.append b c) == List.Tot.append (List.Tot.append a b) c) [SMTPat (List.Tot.append a (List.Tot.append b c))] =
    append_assoc a b c
  in
  ()
#pop-options

let wrapper_sat_spec f task agent :
  Lemma
    (requires theta (agent f task) ⊑ agent_spec)
    (ensures theta (wrapper f task agent) ⊑ wrapper_spec f task)
  = calc (⊑) {
      theta (wrapper f task agent) ;
      == {}
      theta (
        let!@! contents = read_file f in
        let!@ () = agent f task in
        let!@! new_contents = read_file f in
        if validate contents task new_contents
        then io_return (Inl ())
        else io_return (Inr ())
      ) ;
      == { _ by (compute ()) }
      theta (
        io_bind (read_file f) (fun res ->
          match res with
          | Inl contents ->
            let!@ () = agent f task in
            let!@! new_contents = read_file f in
            if validate contents task new_contents
            then io_return (Inl ())
            else io_return (Inr ())
          | Inr x -> io_return (Inr x)
        )
      ) ;
      `hist_equiv` {
        theta_monad_morphism_bind (read_file f) (fun res ->
          match res with
          | Inl contents ->
            let!@ () = agent f task in
            let!@! new_contents = read_file f in
            if validate contents task new_contents
            then io_return (Inl ())
            else io_return (Inr ())
          | Inr x -> io_return (Inr x)
        )
      }
      hist_bind (theta (read_file f)) (fun res ->
        theta (
          match res with
          | Inl contents ->
            let!@ () = agent f task in
            let!@! new_contents = read_file f in
            if validate contents task new_contents
            then io_return (Inl ())
            else io_return (Inr ())
          | Inr x -> io_return (Inr x)
        )
      ) ;
      ⊑ { read_file_sat_spec f }
      hist_bind (read_file_spec f) (fun res ->
        theta (
          match res with
          | Inl contents ->
            let!@ () = agent f task in
            let!@! new_contents = read_file f in
            if validate contents task new_contents
            then io_return (Inl ())
            else io_return (Inr ())
          | Inr x -> io_return (Inr x)
        )
      ) ;
      `hist_equiv` {
        hist_bind_commut_resexn (read_file_spec f) (fun contents ->
          let!@ () = agent f task in
          let!@! new_contents = read_file f in
          if validate contents task new_contents
          then io_return (Inl ())
          else io_return (Inr ())
        )
      }
      hist_bind (read_file_spec f) (fun res ->
        match res with
        | Inl contents ->
          theta (
            let!@ () = agent f task in
            let!@! new_contents = read_file f in
            if validate contents task new_contents
            then io_return (Inl ())
            else io_return (Inr ())
          )
        | Inr x -> hist_return (Inr x)
      ) ;
      ⊑ { wrapper_inner_step f task agent }
      hist_bind (read_file_spec f) (fun res ->
        match res with
        | Inl contents ->
          hist_bind agent_spec (fun () ->
            hist_bind (read_file_spec f) (fun res' ->
              match res' with
              | Inl new_contents ->
                hist_if_then_else
                  (hist_return (Inl ()))
                  (hist_return (Inr ()))
                  (validate contents task new_contents)
              | Inr x -> hist_return (Inr x)
            )
          )
        | Inr x -> hist_return (Inr x)
      ) ;
      ⊑ { wrapper_sat_spec_aux f task agent }
      wrapper_spec f task ;
    }

val main : (string -> string -> io unit) -> io bool
let main agent =
  let!@ r = wrapper "./temp" "overwrite\n" agent in
  match r with
  | Inl _ -> return true
  | Inr _ -> return false

// %splice_t[validate_derivation] (generate_derivation "validate_derivation" (`validate))
// %splice_t[read_file_derivation] (generate_derivation "read_file_derivation" (`read_file))

// %splice_t[main_derivation] (generate_derivation "main_derivation" (`main))

%splice_t[wrapper_derivation] (generate_derivation "wrapper_derivation" (`wrapper))

[@@ (preprocess_with simplify_qType)]
let main_derivation () : ((qString ^-> qString ^->!@ qUnit) ^->!@ qBool) ⊩ main
  by (RQ.TypingRelation.Tests.simplify_via_norm ())
  = pack_turnstile (QLambdaIO (
      QBind
        (QAppIO
          (QApp (QApp (dsnd (wrapper_derivation _)) (QStringLit "./temp"))
                (QStringLit "overwrite\n"))
          QAxiom)
        (QCaseIO QAxiom
          (QReturn QTrue)
          (QReturn QFalse))))

let re_int : intS = {
  ct = (qString ^-> qString ^->!@ qUnit)
}


let main' () : fs_val (re_int.ct ^->!@ qBool) by (compute ()) =
  main

val ps_main : progS re_int
let ps_main : progS re_int =
  (| main' (), (| main_derivation empty, (_ by (norm [delta; iota])) |) |)

let pt_main = RrHP.compile_prog ps_main

(* bad: this agent does nothing *)
let lazy_agent : exp = ELam (ELam EUnit)

(* good: this agent writes the expected string on the file *)
let write_agent : exp =
  ELam (* filename *)
    (ELam (* content *)
      (ECase (ECall OOpen (EVar 1))
        (* Inl fd *)
        (
          (* fd = EVar 0
             content = EVar 1
             filename = EVar 2 *)
          EApp
            (* after io_call OWrite: io_call OClose fd *)
            (ELam (ECall OClose (EVar 1)))
            (ECall OWrite (EPair (EVar 0) (EVar 1)))
        )
        (* Inr _ => unit *)
        EUnit
      )
    )

(* bad: this agent writes twice the string on the file *)
let write_twice_agent : exp =
  ELam (* filename *)
    (ELam (* content *)
      (ECase (ECall OOpen (EVar 1))

        (* Inl fd *)
        (
          EApp
            (* after first io_call OWrite *)
            (ELam
              (EApp
                (* after second io_call OWrite *)
                (ELam (ECall OClose (EVar 2)))
                (ECall OWrite (EPair (EVar 1) (EVar 2)))
              ))
            (ECall OWrite (EPair (EVar 0) (EVar 1)))
        )
        (* Inr _ *)
        EUnit
      )
    )

(* bad: this agent, confused writes the filename on a file named by string *)
let write_mixedup_agent : exp =
  ELam (* filename *)
    (ELam (* content *)
      (ECase (ECall OOpen (EVar 0))
        (* Inl fd *)
        (
          (* fd = EVar 0
             content = EVar 1
             filename = EVar 2 *)
          EApp
            (* after io_call OWrite: io_call OClose fd *)
            (ELam (ECall OClose (EVar 1)))
            (ECall OWrite (EPair (EVar 0) (EVar 2)))
        )
        (* Inr _ => unit *)
        EUnit
      )
    )

(* bad: this agent writes the content fact(5)=120 times on the file.
   fact(5) is computed dynamically by ENRec using a pair accumulator (c,a):
     ENRec 5 (0,1) (λ(c,a). (c+1, (c+1)*a))  →  (5, 120)
   then snd gives 120, and a second ENRec loops 120 writes. *)
let bad_factorial_agent : exp =
  ELam (* filename *)
    (ELam (* EVar 0 = content, EVar 1 = filename *)
      (* Bind n = fact(5) computed by ENRec *)
      (EApp
        (ELam (* EVar 0 = n, EVar 1 = content, EVar 2 = filename *)
          (* Open file *)
          (ECase (ECall OOpen (EVar 2))
            (* Inl fd: EVar 0 = fd, EVar 1 = n, EVar 2 = content, EVar 3 = filename *)
            (EApp
              (* After all writes: close fd *)
              (ELam (* EVar 0 = _, EVar 1 = fd, EVar 2 = n, EVar 3 = content *)
                (ECall OClose (EVar 1))
              )
              (* Loop n times, each step writes (fd, content) *)
              (ENRec (EVar 1) EUnit
                (ELam (* EVar 0 = _, EVar 1 = fd, EVar 2 = n, EVar 3 = content *)
                  (ECall OWrite (EPair (EVar 1) (EVar 3)))
                )
              )
            )
            (* Inr _ *)
            EUnit
          )
        )
        (* Compute fact(5) via pair accumulator (counter, product):
             ENRec 5 (0,1) (λ(c,a). (c+1, mult (c+1) a))
           where mult a b = ENRec a 0 (λacc. ENRec b acc succ) *)
        (ESnd (ENRec (nat_to_exp 5) (EPair EZero (ESucc EZero))
          (ELam (* EVar 0 = (c, a) *)
            (EPair
              (ESucc (EFst (EVar 0)))
              (* mult (c+1) a = ENRec (c+1) 0 (λacc_m. ENRec a acc_m succ) *)
              (ENRec
                (ESucc (EFst (EVar 0)))
                EZero
                (ELam (* EVar 0 = acc_m, EVar 1 = (c, a) *)
                  (ENRec (ESnd (EVar 1)) (EVar 0) (ELam (ESucc (EVar 0))))
                )
              )
            )
          )
        ))
      )
    )

(* good: this agent first writes the given filename into a file "TMP", then reads the filename back from "TMP", opens that file, and writes the provided content into it *)
let indirect_agent : exp =
  ELam (* filename *)
    (ELam (* content *)
      (* open "TMP" *)
      (ECase (ECall OOpen (EString "TMP"))
        (* Inl tmpfd *)
        (
          EApp
            (* after writing filename to TMP *)
            (ELam
              (* reopen TMP *)
              (ECase (ECall OOpen (EString "TMP"))
                (* Inl tmpfd2 *)
                (
                  ECase (ECall ORead (EVar 0))
                    (* Inl fname *)
                    (
                      EApp
                        (* after closing tmpfd2 *)
                        (ELam
                          (* open fname *)
                          (ECase (ECall OOpen (EVar 1))
                            (* Inl fd *)
                            (
                              EApp
                                (ELam (ECall OClose (EVar 1)))
                                (ECall OWrite (EPair (EVar 0) (EVar 6)))
                            )
                            (* Inr _ *)
                            EUnit
                          )
                        )
                        (ECall OClose (EVar 1))
                    )
                    (* Inr _ *)
                    EUnit
                )
                (* Inr _ *)
                EUnit
              )
            )
            (ECall OWrite (EPair (EVar 0) (EVar 2)))
        )
        (* Inr _ *)
        EUnit
      )
    )
