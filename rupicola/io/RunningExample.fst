module RunningExample

open FStar.Tactics.V1
open Trace
open IO
open Metaprogram
open ExamplesIO
open RrHP
open QTyp
open QExp
open STLC

(* We consider the task is string that need to replace the old contents *)

val notb : bool -> bool
let notb b = if b then false else true

val andb : bool -> bool -> bool
let andb b1 b2 = if b1 then b2 else false

val validate : string -> string -> string -> bool
let validate olds task news = eq_string task news
  // andb (notb (eq_string olds news)) (eq_string task news)

let read_file (f : string) : io (resexn string) =
  let!@! fd = openfile f in
  let!@! r = read fd in
  let!@! () = close fd in
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
      exists fd. lt == [ EvOpen f (Inl fd) ]
    )

let openfile_sat_spec f :
  Lemma (theta (openfile f) ⊑ openfile_spec f)
= ()

unfold
let read_spec (fd : file_descr) =
  hist_prepost
    (fun h -> True)
    (fun h lt (r:resexn string) ->
      Inl? r ==>
      exists fd. lt == [ EvRead fd (Inl (Inl?.v r)) ]
    )

let read_sat_spec fd :
  Lemma (theta (read fd) ⊑ read_spec fd)
= ()

unfold
let close_spec (fd : file_descr) =
  hist_prepost
    (fun h -> True)
    (fun h lt (r:resexn unit) ->
      Inl? r ==>
      exists fd. lt == [ EvClose fd (Inl ()) ]
    )

let close_sat_spec fd :
  Lemma (theta (close fd) ⊑ close_spec fd)
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

let read_file_sat_spec f :
  Lemma (theta (read_file f) ⊑ read_file_spec f)
= calc (⊑) {
    theta (read_file f) ;
    == {}
    theta (
      let!@! fd = openfile f in
      let!@! r = read fd in
      let!@! () = close fd in
      io_return (Inl r)
    ) ;
    == { _ by (compute ()) }
    theta (
      io_bind (openfile f) (fun res ->
        match res with
        | Inl fd ->
          let!@! r = read fd in
          let!@! () = close fd in
          io_return (Inl r)
        | Inr x -> io_return (Inr x)
      )
    ) ;
    `hist_equiv` {
      theta_monad_morphism_bind (openfile f) (fun res ->
        match res with
        | Inl fd ->
          let!@! r = read fd in
          let!@! () = close fd in
          io_return (Inl r)
        | Inr x -> io_return (Inr x)
      )
    }
    hist_bind (theta (openfile f)) (fun res ->
      theta (
        match res with
        | Inl fd ->
          let!@! r = read fd in
          let!@! () = close fd in
          io_return (Inl r)
        | Inr x -> io_return (Inr x)
      )
    ) ;
    ⊑ { openfile_sat_spec f }
    hist_bind (openfile_spec f) (fun res ->
      theta (
        match res with
        | Inl fd ->
          let!@! r = read fd in
          let!@! () = close fd in
          io_return (Inl r)
        | Inr x -> io_return (Inr x)
      )
    ) ;
    `hist_equiv` {
      hist_bind_commut_resexn (openfile_spec f) (fun fd ->
        let!@! r = read fd in
        let!@! () = close fd in
        io_return (Inl r)
      )
    }
    hist_bind (openfile_spec f) (fun res ->
      match res with
      | Inl fd ->
        theta (
          let!@! r = read fd in
          let!@! () = close fd in
          io_return (Inl r)
        )
      | Inr x -> hist_return (Inr x)
    ) ;
    // Skipping ahead for now, just manipulations as the ones above
    ⊑ { admit () }
    hist_bind (openfile_spec f) (fun res ->
      match res with
      | Inl fd ->
        hist_bind (read_spec fd) (fun res2 ->
          match res2 with
          | Inl r ->
            hist_bind (close_spec fd) (fun res3 ->
              match res3 with
              | Inl () ->
                hist_return (Inl r)
              | Inr x -> hist_return (Inr x)
            )
          | Inr x -> hist_return (Inr x)
        )
      | Inr x -> hist_return (Inr x)
    ) ;
    // ⊑ { _ by (compute ()) }
    ⊑ { admit () }
    read_file_spec f ;
  }

unfold
let wrapper_spec (f task : string) =
  hist_prepost
    (fun h -> True)
    (fun h lt (r:resexn unit) -> Inl? r ==>
      Some? (fst_read_from f lt) /\ Some? (last_read_from f lt) /\
      (validate (Some?.v (fst_read_from f lt)) task (Some?.v (last_read_from f lt))))

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
= introduce
    forall h p.
      wrapper_spec f task h p ==>
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
      ) h p
  with begin
    calc (==>) {
      wrapper_spec f task h p ;
      // ==> { _ by (compute () ; dump "h") }
      ==> { admit () }
    (* (forall r lt.
        (Inl? r ==>
          (exists (fd: (i: int{i >= 0 == true /\ i >= 0 == true})).
              lt ==
              [
                EvOpen f (Inl fd);
                EvRead fd
                  (Inl (match r as proj_ret returns$ string with | Inl v -> v));
                EvClose fd (Inl ())
              ])) ==>
        (match r with
          | Inl contents ->
            hist_bind agent_spec
              (fun _ ->
                  hist_bind (read_file_spec f)
                    (fun res' ->
                        (match res' with
                          | Inl new_contents ->
                            hist_if_then_else (hist_return (Inl ()))
                              (hist_return (Inr ()))
                              (validate contents task new_contents)
                          | Inr x -> hist_return (Inr x))
                        <:
                        hist (either unit unit)))
          | Inr () -> hist_return (Inr ())) (match
              match lt with
              | [] -> []
              | hd :: tl -> List.Tot.Base.rev_acc tl [hd]
            with
            | [] -> h
            | a :: tl -> a :: (tl @ h))
          (fun lt' r ->
              p (match lt with
                  | [] -> lt'
                  | a :: tl -> a :: (tl @ lt'))
                r)) ;
      == { _ by (compute ()) } *)
      // read_file_spec f h (fun lt (res : resexn string) ->
      //   begin match res with
      //   | Inl contents ->
      //     hist_bind agent_spec (fun () ->
      //       hist_bind (read_file_spec f) (fun res' ->
      //         match res' with
      //         | Inl new_contents ->
      //           hist_if_then_else
      //             (hist_return (Inl ()))
      //             (hist_return (Inr ()))
      //             (validate contents task new_contents)
      //         | Inr x -> hist_return (Inr x)
      //       )
      //     )
      //   | Inr () -> hist_return #(resexn unit) (Inr ())
      //   end (h ++ lt) (hist_post_shift h p lt)
      // ) ;
      // == {}
      read_file_spec f h (hist_post_bind' (fun res ->
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
        | Inr () -> hist_return (Inr ())
      ) p) ;
      == {}
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
        | Inr () -> hist_return (Inr ())
      ) h p ;
    }
  end

let wrapper_sat_spec f task agent :
  Lemma (theta (wrapper f task agent) ⊑ wrapper_spec f task)
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
      // Skipping ahead for now, just manipulations as the ones above
      ⊑ { admit () }
      hist_bind (read_file_spec f) (fun res ->
        match res with
        | Inl contents ->
          hist_bind (theta (agent f task)) (fun () ->
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
      // We assume the agent has the trivial spec
      ⊑ { admit () }
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
  let!@ r = wrapper "./temp" "overwrite" agent in
  match r with
  | Inl _ -> return true
  | Inr _ -> return false

// %splice_t[validate_derivation] (generate_derivation "validate_derivation" (`validate))
// %splice_t[read_file_derivation] (generate_derivation "read_file_derivation" (`read_file))

// %splice_t[main_derivation] (generate_derivation "main_derivation" (`main))

%splice_t[wrapper_derivation] (generate_derivation "wrapper_derivation" (`wrapper))
[@@ (preprocess_with simplify_qType)]
let main_derivation #g : oval_quotation g (helper_oval_g #_ #g main)
  by (trefl ())
  = QLambdaProd (
      QBindProd
        (QAppProd
          (QApp (QApp wrapper_derivation (QStringLit "./temp"))
                (QStringLit "overwrite"))
          QVar0)
        (QCaseProd QVar0
          (QReturn QTrue)
          (QReturn QFalse)))

let re_int : intS = {
  ct = (qString ^-> qString ^->!@ qUnit)
}


val ps_main : progS re_int
let ps_main : progS re_int=
  (| main, main_derivation #empty |)

let pt_main = RrHP.compile_prog ps_main

(* bad: this agent does nothing *)
let lazy_agent : exp = ELam (ELam EUnit)

(* good: this agent writes the expected string on the file *)
let write_agent : exp =
  ELam (* filename *)
    (ELam (* content *)
      (ECase (EOpen (EVar 1))
        (* Inl fd *)
        (
          (* fd = EVar 0
             content = EVar 1
             filename = EVar 2 *)
          EApp
            (* after write: close fd *)
            (ELam (EClose (EVar 1)))
            (EWrite (EVar 0) (EVar 1))
        )
        (* Inr _ => unit *)
        EUnit
      )
    )

(* bad: this agent writes twice the string on the file *)
let write_twice_agent : exp =
  ELam (* filename *)
    (ELam (* content *)
      (ECase (EOpen (EVar 1))

        (* Inl fd *)
        (
          EApp
            (* after first write *)
            (ELam
              (EApp
                (* after second write *)
                (ELam (EClose (EVar 2)))
                (EWrite (EVar 1) (EVar 2))
              ))
            (EWrite (EVar 0) (EVar 1))
        )
        (* Inr _ *)
        EUnit
      )
    )

(* bad: this agent, confused writes the filename on a file named by string *)
let write_mixedup_agent : exp =
  ELam (* filename *)
    (ELam (* content *)
      (ECase (EOpen (EVar 0))
        (* Inl fd *)
        (
          (* fd = EVar 0
             content = EVar 1
             filename = EVar 2 *)
          EApp
            (* after write: close fd *)
            (ELam (EClose (EVar 1)))
            (EWrite (EVar 0) (EVar 2))
        )
        (* Inr _ => unit *)
        EUnit
      )
    )

(* good: this agent first writes the given filename into a file "TMP", then reads the filename back from "TMP", opens that file, and writes the provided content into it *)
let indirect_agent : exp =
  ELam (* filename *)
    (ELam (* content *)
      (* open "TMP" *)
      (ECase (EOpen (EString "TMP"))
        (* Inl tmpfd *)
        (
          EApp
            (* after writing filename to TMP *)
            (ELam
              (* reopen TMP *)
              (ECase (EOpen (EString "TMP"))
                (* Inl tmpfd2 *)
                (
                  ECase (ERead (EVar 0))
                    (* Inl fname *)
                    (
                      EApp
                        (* after closing tmpfd2 *)
                        (ELam
                          (* open fname *)
                          (ECase (EOpen (EVar 1))
                            (* Inl fd *)
                            (
                              EApp
                                (ELam (EClose (EVar 1)))
                                (EWrite (EVar 0) (EVar 6))
                            )
                            (* Inr _ *)
                            EUnit
                          )
                        )
                        (EClose (EVar 1))
                    )
                    (* Inr _ *)
                    EUnit
                )
                (* Inr _ *)
                EUnit
              )
            )
            (EWrite (EVar 0) (EVar 2))
        )
        (* Inr _ *)
        EUnit
      )
    )
