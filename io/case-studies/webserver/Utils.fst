module Utils

open FStar.Tactics
open FStar.List.Tot

open Compiler.Languages

include MonitorParam

val valid_http_response : Bytes.bytes -> bool
let valid_http_response res = Bytes.length res < 500

val valid_http_request : Bytes.bytes -> bool
let valid_http_request req = Bytes.length req < 500

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

let rec is_waiting (h : trace) =
  match h with
  | [] -> true
  | EAccept _ arg res :: tl -> (match res with | Inl _ -> false | Inr _ -> is_waiting tl)
  | ERead Prog _ res :: tl -> (match res with | Inl _ -> false | Inr _ -> is_waiting tl)
  | EWrite Prog _ res :: tl -> (match res with | Inl _ -> true | Inr _ -> is_waiting tl)
  | _ :: tl -> is_waiting tl

effect MyMIO
  (a:Type)
  (fl:FStar.Ghost.erased tflag)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  MIO a fl mymst pre post

val sgm : policy_spec
let sgm h c cmd arg =
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

val pi : policy sgm mymst
let pi s0 cmd arg =
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
    (requires enforced_locally sgm h lth /\ every_request_gets_a_response (lt @ lt'))
    (ensures every_request_gets_a_response (lt @ lth @ lt'))
    (decreases lth)
= match lth with
  | [] -> ()
  | e :: l ->
    append_assoc lt [ e ] (l @ lt') ;
    assert ((lt @ [ e ]) @ l @ lt' == lt @ e :: l @ lt') ;
    assert (enforced_locally sgm (e :: h) l) ;
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

let rec wrote_to_split client l l' :
  Lemma
    (requires wrote_to client (l @ l'))
    (ensures wrote_to client l \/ wrote_to client l')
= match l with
  | [] -> ()
  | EAccept _ arg (Inl fd) :: tl ->
    if fd = client
    then ()
    else wrote_to_split client tl l'
  | EWrite Prog arg _ :: tl ->
    let (fd, _) = arg in
    if fd = client
    then ()
    else wrote_to_split client tl l'
  | _ :: tl -> wrote_to_split client tl l'

let rec ergar_pi_write_aux h lth client :
  Lemma
    (requires enforced_locally sgm h lth /\ wrote_to client (List.rev lth))
    (ensures ergar lth [client])
    (decreases lth)
= match lth with
  | [] -> ()
  | e :: l ->
    assert (enforced_locally sgm (e :: h) l) ;
    rev_append [e] l ;
    wrote_to_split client (rev l) [e] ;
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
    (requires enforced_locally sgm h lth /\ wrote_to client (List.rev lth) /\ every_request_gets_a_response lt)
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
