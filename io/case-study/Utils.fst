module Utils

open FStar.Tactics
open FStar.List.Tot

open Compiler.Languages

val valid_http_response : Bytes.bytes -> bool
let valid_http_response res = Bytes.length res < 500

val valid_http_request : Bytes.bytes -> bool
let valid_http_request req = Bytes.length req < 500

(** The web server has to prove this predicate to call the
    handler, which happens immediately after it reads from a client.
    Also, the handler has to prove this predicate to call `send`,
    which should also hold since during the execution of the handler
    no reads by Prog can happen. **)
let rec did_not_respond_acc (h:trace) (fds:list file_descr) : bool =
  match h with
  (** got request **)
  | ERead Prog arg _ :: tl ->
    let (fd, _) = arg in 
    not (List.mem fd fds)
  | EWrite _ arg _ :: tl ->
    let (fd, _) = arg in did_not_respond_acc tl (fd::fds)
  | _::tl -> did_not_respond_acc tl fds
  | _ -> true

let did_not_respond (h:trace) : bool =
  did_not_respond_acc h []

let rec is_opened_by_untrusted (h:trace) (fd:file_descr) : bool =
  match h with
  | [] -> false
  | EOpenfile Ctx _ res :: tl ->
    if Inl? res && fd = Inl?.v res then true
    else is_opened_by_untrusted tl fd
  | EClose _ fd' res :: tl ->
    if Inl? res && fd = fd' then false
    else is_opened_by_untrusted tl fd
  | e :: tl -> is_opened_by_untrusted tl fd

val wrote : trace -> bool
let rec wrote h =
  match h with
  | [] -> false
  (** the event before calling the handler is the read of the request **)
  | ERead Prog _ _::tl -> false
  (** the handler can write only once to the client using Prog **)
  | EWrite Prog _ _::tl -> true
  | _ :: tl -> wrote tl

val every_request_gets_a_response_acc : trace -> list file_descr -> Type0
let rec every_request_gets_a_response_acc lt read_descrs =
  match lt with
  | [] -> read_descrs == []
  | ERead Prog arg (Inl _) :: tl ->
    let (fd, _) = arg in every_request_gets_a_response_acc tl (fd :: read_descrs)
  | EWrite Prog (fd,_) _ :: tl -> every_request_gets_a_response_acc tl (filter (fun fd' -> fd <> fd') read_descrs)
  | _ :: tl -> every_request_gets_a_response_acc tl read_descrs

val every_request_gets_a_response : trace -> Type0
let every_request_gets_a_response lt =
  every_request_gets_a_response_acc lt []

let no_write_true e =
  match e with
  | EWrite Prog _ _ -> false
  | _ -> true

let no_read_true e : GTot bool =
  match e with
  | ERead Prog _ (Inl _) -> false
  | _ -> true

noeq
type cst = {
  opened : list file_descr;
  written : bool;
  waiting : bool;
}

let models (c:cst) (h:trace) : Type0 =
  (forall fd. fd `List.mem` c.opened <==> is_opened_by_untrusted h fd)
  /\ (c.written == wrote h)
  /\ (c.waiting == did_not_respond h)

let mymst : mst = {
  cst = cst;
  models = models;
}

effect MyMIO
  (a:Type)
  (fl:FStar.Ghost.erased tflag)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  MIO a mymst fl pre post

let my_init_cst : mymst.cst =
  { opened = [] ; written = false ; waiting = false }

let is_neq (#a:eqtype) (x y : a) : bool = x <> y

let close_upd_cst (s : cst) arg : cst = {
  opened = List.Tot.Base.filter (is_neq arg) s.opened ;
  written = s.written ;
  waiting = s.waiting
}

// TODO MOVE
let rec mem_filter (#a:Type) (f: (a -> Tot bool)) (l: list a) (x: a) :
  Lemma (requires x `memP` filter f l) (ensures x `memP` l)
= match l with
  | y :: tl ->
    if f y
    then begin
      eliminate x == y \/ x `memP` filter f tl
      returns x `memP` l
      with _. ()
      and _. mem_filter f tl x
    end
    else mem_filter f tl x

// TODO MOVE
let rec filter_mem (#a:Type) (f: (a -> Tot bool)) (l: list a) (x: a) :
  Lemma (requires x `memP` l /\ f x) (ensures x `memP` filter f l)
= match l with
  | y :: tl ->
    if f y
    then begin
      eliminate x == y \/ x `memP` tl
      returns x `memP` filter f l
      with _. ()
      and _. filter_mem f tl x
    end
    else filter_mem f tl x

let my_update_cst_close s0 caller arg rr :
  Lemma (
    forall h.
      s0 `models` h ==>
      close_upd_cst s0 arg `models` (EClose caller arg (Inl rr) :: h)
  )
= let e = EClose caller arg (Inl rr) in
  let s1 = close_upd_cst s0 arg in
  introduce forall h. s0 `models` h ==> s1 `models` (e::h)
  with begin
    introduce s0 `models` h ==> s1 `models` (e::h)
    with _. begin
      introduce forall fd. fd `List.mem` s1.opened <==> is_opened_by_untrusted (e :: h) fd
      with begin
        introduce fd `List.mem` s1.opened ==> is_opened_by_untrusted (e :: h) fd
        with _. begin
          mem_filter (is_neq arg) s0.opened fd
        end ;
        introduce is_opened_by_untrusted (e :: h) fd ==> fd `List.mem` s1.opened
        with _. begin
          assert (arg <> fd) ;
          assert (is_opened_by_untrusted h fd) ;
          assert (fd `mem` s0.opened) ;
          filter_mem (is_neq arg) s0.opened fd
        end
      end ;
      assert (s1.written <==> wrote (e::h)) ;
      assert (s1.waiting <==> did_not_respond (e :: h))
    end
  end

let write_upd_cst (s : cst) fd : cst = {
  opened = s.opened ;
  written = true ;
  waiting = false
}

let my_update_cst_write s0 caller fd bb rr :
  Lemma (
    forall h.
      s0 `models` h ==>
      write_upd_cst s0 fd `models` (EWrite caller (fd, bb) (Inl rr) :: h)
  )
= let e = EWrite caller (fd, bb) (Inl rr) in
  let s1 = write_upd_cst s0 fd in
  introduce forall h. s0 `models` h ==> s1 `models` (e::h)
  with begin
    introduce s0 `models` h ==> s1 `models` (e::h)
    with _. begin
      assert (forall fd'. fd' `List.mem` s0.opened ==> is_opened_by_untrusted h fd') ;
      // assume (forall fd'. fd' `List.mem` s1.opened ==> is_opened_by_untrusted (e :: h) fd') ;
      assume (s1.written ==> wrote (e::h)) ;
      assume (not (did_not_respond (e :: h))) // No way to know it's true?
    end
  end

let my_update_cst (s0:cst) (e:event) : (s1:cst{forall h. s0 `models` h ==> s1 `models` (e::h)}) =
  let opened = s0.opened in
  let written = s0.written in
  let waiting = s0.waiting in
  let (| caller, cmd, arg, res |) = destruct_event e in
  match cmd, res with
  | Accept, Inl _ -> admit (); { opened = opened; written = written; waiting = true }
  | Openfile, Inl fd ->
    if caller = Ctx
    then { opened = fd :: opened ; written = written ; waiting = waiting }
    else s0
  | Close, Inl rr ->
    my_update_cst_close s0 caller arg rr ;
    close_upd_cst s0 arg
  | Write, Inl rr ->
    let arg : file_descr * Bytes.bytes = arg in
    let (fd, bb) = arg in
    my_update_cst_write s0 caller fd bb rr ;
    write_upd_cst s0 fd
  | _ -> admit (); s0

val pi : policy_spec
let pi h c cmd arg =
  match c, cmd with
  | Ctx, Openfile ->
    let (fnm, _, _) : string * (list open_flag) * zfile_perm= arg in
    if fnm = "/temp" then true else false
  | Ctx, Read ->
    let (fd, _) : file_descr * UInt8.t = arg in
    is_opened_by_untrusted h fd
  | Ctx, Close -> is_opened_by_untrusted h arg
  | Ctx, Access ->
    let (fnm, _) : string * list access_permission = arg in
    if fnm = "/temp" then true
    else false
  | Ctx, Stat ->
    if arg = "/temp" then true else false
  | Prog, Write -> true
  | _ -> false

val phi : policy mymst pi
let phi s0 cmd arg =
  match cmd with
  | Openfile ->
    let (fnm, _, _) : string * (list open_flag) * zfile_perm= arg in
    if fnm = "/temp" then true else false
  | Read ->
    let (fd, _) : file_descr * UInt8.t = arg in
    fd `List.mem` s0.opened
  | Close -> arg `List.mem` s0.opened
  | Access -> 
    let (fnm, _) : string * list access_permission = arg in
    if fnm = "/temp" then true 
    else false
  | Stat -> 
    if arg = "/temp" then true else false
  | _ -> false

let ergar = every_request_gets_a_response_acc

let rec ergar_ignore_no_write_read lt e lt' rl :
  Lemma
    (requires ergar (lt @ lt') rl /\ no_write_true e /\ no_read_true e)
    (ensures ergar (lt @ e :: lt') rl)
= match lt with
  | [] -> ()
  | ERead Prog arg (Inl _) :: tl -> 
    let (fd, _) = arg in ergar_ignore_no_write_read tl e lt' (fd :: rl)
  | EWrite Prog (fd,x) y :: tl ->
    assert_norm (ergar (EWrite Prog (fd,x) y :: tl @ lt') rl == ergar (tl @ lt') (filter (fun fd' -> fd <> fd') rl)) ;
    ergar_ignore_no_write_read tl e lt' (filter (fun fd' -> fd <> fd') rl) ;
    assert_norm (ergar (tl @ e :: lt') (filter (fun fd' -> fd <> fd') rl) == ergar (EWrite Prog (fd,x) y :: tl @ e :: lt') rl)
  | _ :: tl -> ergar_ignore_no_write_read tl e lt' rl

let is_write_true e : GTot bool =
  match e with
  | EWrite Prog _ y -> true
  | _ -> false

let write_true_fd e : Pure file_descr (requires is_write_true e) (ensures fun _ -> True) =
  match e with
  | EWrite Prog arg y -> fst arg

let cong (f : 'a -> 'b) (x y : 'a) :
  Lemma (requires x == y) (ensures f x == f y)
= ()

let ergar_write_true e l rl :
  Lemma
    (requires is_write_true e)
    (ensures
      ergar (e :: l) rl ==
      ergar l (filter (fun fd' -> write_true_fd e <> fd') rl)
    )
= match e with
  | EWrite Prog (fd,x) y ->
    calc (==) {
      write_true_fd e ;
      == {}
      write_true_fd (EWrite Prog (fd,x) y) ;
      == {}
      fd ;
    } ;
    // assert_norm ((fun fd' -> fd <> fd') == (fun fd' -> write_true_fd e <> fd')) ;
    cong (fun fd -> (fun fd' -> fd <> fd')) fd (write_true_fd e) ;
    calc (==) {
      ergar (e :: l) rl ;
      == {}
      ergar (EWrite Prog (fd,x) y :: l) rl ;
      == { _ by (FStar.Tactics.compute ()) }
      ergar l (filter (fun fd' -> fd <> fd') rl) ;
      == {}
      ergar l (filter (fun fd' -> write_true_fd e <> fd') rl) ;
    }

let rec filter_append (f : 'a -> bool) l r :
  Lemma (filter f (l @ r) == filter f l @ filter f r)
= match l with
  | [] -> ()
  | x :: l -> filter_append f l r

let rec ergar_merge lt rl0 rl1 rl2 :
  Lemma
    (requires ergar lt (rl0 @ rl1) /\ ergar lt (rl0 @ rl2))
    (ensures ergar lt (rl0 @ rl1 @ rl2))
= match lt with
  | [] -> ()
  | ERead Prog (fd,_) (Inl _) :: tl ->
    assert (ergar tl (fd :: rl0 @ rl1)) ;
    assert (ergar tl (fd :: rl0 @ rl2)) ;
    ergar_merge tl (fd :: rl0) rl1 rl2
  | EWrite Prog (fd,x) y :: tl ->
    cong (fun fd -> (fun fd' -> fd <> fd')) fd (write_true_fd (EWrite Prog (fd,x) y)) ;

    ergar_write_true (EWrite Prog (fd,x) y) tl (rl0 @ rl1) ;
    assert (ergar tl (filter (fun fd' -> fd <> fd') (rl0 @ rl1))) ;
    filter_append (fun fd' -> fd <> fd') rl0 rl1 ;

    ergar_write_true (EWrite Prog (fd,x) y) tl (rl0 @ rl2) ;
    assert (ergar tl (filter (fun fd' -> fd <> fd') (rl0 @ rl2))) ;
    filter_append (fun fd' -> fd <> fd') rl0 rl2 ;

    ergar_merge tl (filter (fun fd' -> fd <> fd') rl0) (filter (fun fd' -> fd <> fd') rl1) (filter (fun fd' -> fd <> fd') rl2) ;

    calc (==) {
      filter (fun fd' -> fd <> fd') rl0 @ filter (fun fd' -> fd <> fd') rl1 @ filter (fun fd' -> fd <> fd') rl2 ;
      == { filter_append (fun fd' -> fd <> fd') rl1 rl2 }
      filter (fun fd' -> fd <> fd') rl0 @ filter (fun fd' -> fd <> fd') (rl1 @ rl2) ;
      == { filter_append (fun fd' -> fd <> fd') rl0 (rl1 @ rl2) }
      filter (fun fd' -> fd <> fd') (rl0 @ rl1 @ rl2) ;
    } ;

    ergar_write_true (EWrite Prog (fd,x) y) tl (rl0 @ rl1 @ rl2) ;
    assert (ergar tl (filter (fun fd' -> fd <> fd') (rl0 @ rl1 @ rl2)))
  | _ :: tl -> ergar_merge tl rl0 rl1 rl2

let rec ergar_split lt rl1 rl2 :
  Lemma
    (requires ergar lt (rl1 @ rl2))
    (ensures ergar lt rl1 /\ ergar lt rl2)
= match lt with
  | [] -> ()
  | ERead Prog (fd,_) (Inl _) :: tl ->
    assert (ergar tl (fd :: rl1 @ rl2)) ;
    ergar_split tl (fd :: rl1) rl2 ;
    assert (ergar tl (fd :: rl1)) ;
    ergar_split tl [fd] rl1 ;
    ergar_merge tl [] [fd] rl2 ;
    assert (ergar tl (fd :: rl2))
  | EWrite Prog (fd,x) y :: tl ->
    cong (fun fd -> (fun fd' -> fd <> fd')) fd (write_true_fd (EWrite Prog (fd,x) y)) ;

    ergar_write_true (EWrite Prog (fd,x) y) tl (rl1 @ rl2) ;
    assert (ergar tl (filter (fun fd' -> fd <> fd') (rl1 @ rl2))) ;
    filter_append (fun fd' -> fd <> fd') rl1 rl2 ;

    ergar_split tl (filter (fun fd' -> fd <> fd') rl1) (filter (fun fd' -> fd <> fd') rl2) ;

    ergar_write_true (EWrite Prog (fd,x) y) tl rl1 ;
    ergar_write_true (EWrite Prog (fd,x) y) tl rl2
  | _ :: tl -> ergar_split tl rl1 rl2

let rec filter_swap f g l :
  Lemma (filter f (filter g l) == filter g (filter f l))
= match l with
  | [] -> ()
  | x :: l -> filter_swap f g l

let rec ergar_filter lt rl f :
  Lemma
    (requires ergar lt rl)
    (ensures ergar lt (filter f rl))
= match lt with
  | [] -> ()
  | ERead Prog (fd,_) (Inl _) :: tl ->
    assert (ergar tl (fd :: rl)) ;
    ergar_filter tl (fd :: rl) f ;
    assert (ergar tl (filter f (fd :: rl))) ;
    if f fd
    then ()
    else begin
      assert (ergar tl (fd :: rl)) ;
      assert (ergar tl (filter f rl)) ;
      ergar_split tl [fd] rl ;
      ergar_merge tl [] [fd] (filter f rl) ;
      assert (ergar tl (fd :: filter f rl))
    end
  | EWrite Prog (fd,x) y :: tl ->
    ergar_write_true (EWrite Prog (fd,x) y) tl rl ;
    cong (fun fd -> (fun fd' -> fd <> fd')) fd (write_true_fd (EWrite Prog (fd,x) y)) ;
    assert (ergar tl (filter (fun fd' -> fd <> fd') rl)) ;
    ergar_filter tl (filter (fun fd' -> fd <> fd') rl) f ;
    assert (ergar tl (filter f (filter (fun fd' -> fd <> fd') rl))) ;
    ergar_write_true (EWrite Prog (fd,x) y) tl (filter f rl) ;
    filter_swap (fun fd' -> fd <> fd') f rl ;
    assert (ergar tl (filter (fun fd' -> fd <> fd') (filter f rl)))
  | _ :: tl -> ergar_filter tl rl f

let rec ergar_write_irr lt e0 lt' rl :
  Lemma
    (requires ergar (lt @ lt') rl /\ is_write_true e0)
    (ensures ergar ((lt @ [ e0 ]) @ lt') rl)
= match lt with
  | [] ->
    assert (ergar lt' rl) ;
    ergar_filter lt' rl (fun fd' -> write_true_fd e0 <> fd') ;
    ergar_write_true e0 lt' rl ;
    assert (ergar lt' (filter (fun fd' -> write_true_fd e0 <> fd') rl))
  | ERead Prog (fd,_) (Inl _) :: tl ->
    assert (ergar (tl @ lt') (fd :: rl)) ;
    ergar_write_irr tl e0 lt' (fd :: rl) ;
    assert (ergar ((tl @ [ e0 ]) @ lt') (fd :: rl))
  | EWrite Prog (fd,x) y :: tl ->
    cong (fun fd -> (fun fd' -> fd <> fd')) fd (write_true_fd (EWrite Prog (fd,x) y)) ;

    ergar_write_true (EWrite Prog (fd,x) y) (tl @ lt') rl ;
    assert (ergar (tl @ lt') (filter (fun fd' -> fd <> fd') rl)) ;

    ergar_write_irr tl e0 lt' (filter (fun fd' -> fd <> fd') rl) ;

    ergar_write_true (EWrite Prog (fd,x) y) ((tl @ [e0]) @ lt') rl ;
    assert (ergar ((tl @ [ e0 ]) @ lt') (filter (fun fd' -> fd <> fd') rl))
  | _ :: tl -> ergar_write_irr tl e0 lt' rl

let rec ergar_pi_irr h lth lt lt' :
  Lemma
    (requires enforced_locally pi h lth /\ every_request_gets_a_response (lt @ lt'))
    (ensures every_request_gets_a_response (lt @ lth @ lt'))
    (decreases lth)
= match lth with
  | [] -> ()
  | e :: l ->
    append_assoc lt [ e ] (l @ lt') ;
    assert ((lt @ [ e ]) @ l @ lt' == lt @ e :: l @ lt') ;
    assert (enforced_locally pi (e :: h) l) ;
    append_assoc lt [ e ] lt' ;
    assert (every_request_gets_a_response (lt @ lt')) ;
    begin match e with
    | EWrite Prog (fd,x) y ->
      ergar_write_irr lt (EWrite Prog (fd,x) y) lt' [] ;
      assert (every_request_gets_a_response ((lt @ [ EWrite Prog (fd,x) y ]) @ lt')) ;
      ergar_pi_irr (e :: h) l (lt @ [ e ]) lt'
    | _ ->
      ergar_ignore_no_write_read lt e lt' [] ;
      ergar_pi_irr (e :: h) l (lt @ [ e ]) lt'
    end

let rec ergar_pi_write_aux h lth client :
  Lemma
    (requires enforced_locally pi h lth /\ wrote ((List.rev lth) @ h))
    (ensures ergar lth [client])
    (decreases lth)
= admit (); match lth with
  | [] -> ()
  | e :: l ->
    assert (enforced_locally pi (e :: h) l) ;
    begin match e with
    | EWrite Prog (fd,x) y ->
      if fd = client
      then ergar_pi_irr (e :: h) l [] []
      else ergar_pi_write_aux (e :: h) l client
    | _ -> ergar_pi_write_aux (e :: h) l client
  end

let rec ergar_trace_merge lt lt' rl rl' :
  Lemma
    (requires ergar lt rl /\ ergar lt' rl')
    (ensures ergar (lt @ lt') (rl @ rl'))
= match lt with
  | [] -> ()
  | ERead Prog (fd,limit) (Inl _) :: tl ->
    assert (ergar tl (fd :: rl)) ;
    ergar_trace_merge tl lt' (fd :: rl) rl'
  | EWrite Prog (fd,x) y :: tl ->
    cong (fun fd -> (fun fd' -> fd <> fd')) fd (write_true_fd (EWrite Prog (fd,x) y)) ;

    ergar_write_true (EWrite Prog (fd,x) y) tl rl ;
    assert (ergar tl (filter (fun fd' -> fd <> fd') rl)) ;

    assert (ergar lt' rl') ;
    ergar_filter lt' rl' (fun fd' -> fd <> fd') ;

    filter_append (fun fd' -> fd <> fd') rl rl' ;
    ergar_trace_merge tl lt' (filter (fun fd' -> fd <> fd') rl) (filter (fun fd' -> fd <> fd') rl') ;

    ergar_write_true (EWrite Prog (fd,x) y) (tl @ lt') (rl @ rl') ;
    assert (ergar (tl @ lt') (filter (fun fd' -> fd <> fd') (rl @ rl')))
  | _ :: tl -> ergar_trace_merge tl lt' rl rl'

let ergar_pi_write h lth client limit r lt :
  Lemma
    (requires enforced_locally pi h lth /\ wrote ((List.rev lth)@h) /\ every_request_gets_a_response lt)
    (ensures every_request_gets_a_response (lt @ [ ERead Prog (client,limit) (Inl r) ] @ lth))
= ergar_pi_write_aux h lth client ;
  assert (ergar lth [client]) ;
  assert (every_request_gets_a_response (ERead Prog (client,limit) (Inl r) :: lth)) ;
  append_assoc lt [ ERead Prog (client,limit) (Inl r) ] lth ;
  ergar_trace_merge lt ([ ERead Prog (client,limit) (Inl r) ] @ lth) [] []

let every_request_gets_a_response_append () : 
  Lemma (
    forall lt1 lt2.
      every_request_gets_a_response lt1 /\ every_request_gets_a_response lt2 ==>
      every_request_gets_a_response (lt1 @ lt2)
  ) 
= introduce forall lt1 lt2. ergar lt1 [] /\ ergar lt2 [] ==> ergar (lt1 @ lt2) []
  with begin
    introduce ergar lt1 [] /\ ergar lt2 [] ==> ergar (lt1 @ lt2) []
    with _. ergar_trace_merge lt1 lt2 [] []
  end
