module RunningExample

open FStar.Tactics

open FStar.Ghost
open FStar.List.Tot.Base
open FStar.List.Tot.Properties

open Compiler.Model


(** ** Type of source handler **)
assume val valid_http_response : string -> bool
assume val valid_http_request : string -> bool
assume val req_res : req:string{valid_http_request req} -> res:string{valid_http_response res}


val did_not_respond : trace -> bool
let did_not_respond h =
  match h with
  | EWrite _ _ _ :: _ -> false
  | _ -> true

let rec is_opened_by_untrusted (h:trace) (fd:file_descr) : bool =
  match h with
  | [] -> false
  | EOpenfile false _ (Inl fd') :: tl -> begin
    if fd = fd' then true
    else is_opened_by_untrusted tl fd
  end
  | EClose _ fd' (Inl ()) :: tl -> if fd = fd' then false
                             else is_opened_by_untrusted tl fd
  | _ :: tl -> is_opened_by_untrusted tl fd

val pi : access_policy
let pi h isTrusted cmd arg =
  match isTrusted, cmd with
  | false, Openfile -> 
    if arg = "/temp" then true else false
  | false, Read -> is_opened_by_untrusted h arg
  | false, Close -> is_opened_by_untrusted h arg
  | true, Write -> true
  | _ -> false

val wrote_at_least_once_to : file_descr -> trace -> bool
let rec wrote_at_least_once_to client lt =
  match lt with
  | [] -> false
  | EWrite true arg _::tl -> let (fd, msg):file_descr*string = arg in
                         client = fd
  | _ :: tl -> wrote_at_least_once_to client tl 

type request_handler (fl:erased tflag) =
  (client:file_descr) ->
  (req:string) ->
  (send:(msg:string -> IIO (resexn unit) fl (requires (fun h -> valid_http_response msg /\
                                                               did_not_respond h))
                                            (ensures (fun _ _ lt -> exists r. lt == [EWrite true (client,msg) r] /\
                                                                         wrote_at_least_once_to client lt)))) ->
  IIO (resexn unit) fl (requires (fun h -> valid_http_request req /\ did_not_respond h))
                       (ensures (fun h r lt -> enforced_locally pi h lt /\
                                             (wrote_at_least_once_to client lt \/ Inr? r)))

(** ** E.g. of source handler **)
val source_handler : request_handler IOActions
let source_handler client req send =
  let res = req_res req in
  let _ = send res in 
  Inl ()

type acts (fl:erased tflag) (pi:access_policy) (isTrusted:bool) =
  (cmd : io_cmds) ->
  (arg : io_sig.args cmd) ->
  IIO (io_resm cmd arg) fl
    (requires (fun _ -> True))
    (ensures (fun h r lt ->
      enforced_locally pi h lt /\
      (match r with
       | Inr Contract_failure -> lt == []
       | r' -> lt == [convert_call_to_event isTrusted cmd arg r'])))


(** ** E.g. of target handler **)
type tgt_handler =
  (fl:erased tflag) ->
  (pi:erased access_policy) ->
  (io_acts:acts fl pi false) ->
  (client:file_descr) ->
  (req:string) ->
  (send:(msg:string -> IIOpi (resexn unit) fl pi)) ->
  IIOpi (resexn unit) fl pi

val target_handler1 : tgt_handler
let target_handler1 fl pi io_acts client req send =
  let _ = send req in 
  Inl ()

val target_handler2 : tgt_handler
let target_handler2 fl pi io_acts client req send =
  let _ = io_acts Openfile "/etc/passwd" in
  let _ = send req in 
  Inl ()

(** ** Source webserver **)
val every_request_gets_a_response_acc : trace -> list file_descr -> Type0
let rec every_request_gets_a_response_acc lt read_descrs =
  match lt with
  | [] -> read_descrs == []
  | ERead true fd (Inl _) :: tl -> every_request_gets_a_response_acc tl (fd :: read_descrs)
  | EWrite true (fd,_) _ :: tl -> every_request_gets_a_response_acc tl (filter (fun fd' -> fd <> fd') read_descrs)
  | _ :: tl -> every_request_gets_a_response_acc tl read_descrs

val every_request_gets_a_response : trace -> Type0
let every_request_gets_a_response lt =
  every_request_gets_a_response_acc lt []

assume val get_req : fd:file_descr ->
  IIO (io_sig.res Read fd) IOActions (fun _ -> True) (fun h r lt -> (Inl? r ==> valid_http_request (Inl?.v r)) /\ lt == [ERead true fd r])

assume val sendError : int -> fd:file_descr -> IIO unit IOActions
 (fun _ -> True) (fun _ _ lt -> exists (msg:string) r. lt == [EWrite true (fd, msg) r])

let no_write_true e =
  match e with
  | EWrite true _ _ -> false
  | _ -> true

let no_read_true e =
  match e with
  | ERead true _ (Inl _) -> false
  | _ -> true

let ergar = every_request_gets_a_response_acc

let rec ergar_ignore_no_write_read lt e lt' rl :
  Lemma
    (requires ergar (lt @ lt') rl /\ no_write_true e /\ no_read_true e)
    (ensures ergar (lt @ e :: lt') rl)
= match lt with
  | [] -> ()
  | ERead true fd (Inl _) :: tl -> ergar_ignore_no_write_read tl e lt' (fd :: rl)
  | EWrite true (fd,x) y :: tl ->
    assert_norm (ergar (EWrite true (fd,x) y :: tl @ lt') rl == ergar (tl @ lt') (filter (fun fd' -> fd <> fd') rl)) ;
    ergar_ignore_no_write_read tl e lt' (filter (fun fd' -> fd <> fd') rl) ;
    assert_norm (ergar (tl @ e :: lt') (filter (fun fd' -> fd <> fd') rl) == ergar (EWrite true (fd,x) y :: tl @ e :: lt') rl)
  | _ :: tl -> ergar_ignore_no_write_read tl e lt' rl

let rec response_order_irr lt rl1 rl2 :
  Lemma
    (requires ergar lt (rl1 @ rl2))
    (ensures ergar lt (rl2 @ rl1))
= match lt with
  | [] -> ()
  | ERead true fd (Inl _) :: tl ->
    assert (ergar tl (fd :: rl1 @ rl2)) ;
    response_order_irr tl [fd] (rl1 @ rl2) ;
    assert (ergar tl ((rl1 @ rl2) @ [fd])) ;
    append_assoc rl1 rl2 [fd] ;
    assert (ergar tl (rl1 @ rl2 @ [fd])) ;
    response_order_irr tl rl1 (rl2 @ [fd]) ;
    assert (ergar tl ((rl2 @ [fd]) @ rl1)) ;
    append_assoc rl2 [fd] rl1 ;
    assert (ergar tl (rl2 @ [fd] @ rl1)) ;
    response_order_irr tl rl1 (rl2 @ [fd]) ;

    // response_order_irr tl (fd :: rl1) rl2 ;
    // assert (ergar tl (rl2 @ fd :: rl1)) ;
    // append_assoc rl2 [fd] rl1 ;
    // response_order_irr tl (rl2 @ [fd]) rl1 ;
    // assert (ergar tl (rl1 @ (rl2 @ [fd]))) ;
    assume (ergar tl (fd :: rl2 @ rl1))
  | EWrite true (fd,x) y :: tl ->
    // assert_norm (ergar (EWrite true (fd,x) y :: tl) (fd1 :: fd2 :: rl) == ergar tl (filter (fun fd' -> fd <> fd') (fd1 :: fd2 :: rl))) ;
    // assert (ergar tl (filter (fun fd' -> fd <> fd') (fd1 :: fd2 :: rl))) ;
    // if fd1 = fd then () else
    // if fd2 = fd then () else
    //   assert (filter (fun fd' -> fd <> fd') (fd1 :: fd2 :: rl) == fd1 :: fd2 :: filter (fun fd' -> fd <> fd') rl) ;
    //   assume (ergar tl (fd1 :: fd2 :: filter (fun fd' -> fd <> fd') rl)) ;
    //   response_order_irr tl (filter (fun fd' -> fd <> fd') rl) fd1 fd2 ;
    //   assert (ergar tl (fd2 :: fd1 :: filter (fun fd' -> fd <> fd') rl)) ;
    //   assume (fd2 :: fd1 :: filter (fun fd' -> fd <> fd') rl == filter (fun fd' -> fd <> fd') (fd2 :: fd1 :: rl)) ; // uh?
    //   calc (==) {
    //     ergar tl (fd2 :: fd1 :: filter (fun fd' -> fd <> fd') rl) ;
    //     == {}
    //     ergar tl (filter (fun fd' -> fd <> fd') (fd2 :: fd1 :: rl)) ;
    //     == { _ by (compute ()) }
    //     ergar (EWrite true (fd,x) y :: tl) (fd2 :: fd1 :: rl) ;
    //     == {}
    //     ergar lt (fd2 :: fd1 :: rl) ;
    //   }
    admit ()
  | _ :: tl -> response_order_irr tl rl1 rl2

// let rec response_ignore_read lt fd0 x0 lt' rl :
//   Lemma
//     (requires ergar (lt @ lt') (fd0 :: rl))
//     (ensures ergar (lt @ (ERead true fd0 (Inl x0)) :: lt') rl)
// = match lt with
//   | [] -> ()
//   | ERead true fd (Inl _) :: tl -> response_ignore_read tl fd0 x0 lt' (fd :: rl)
//   | EWrite true (fd,x) y :: tl ->
//     assert_norm (ergar (EWrite true (fd,x) y :: tl @ lt') rl == ergar (tl @ lt') (filter (fun fd' -> fd <> fd') rl)) ;
//     response_ignore_read tl fd0 x0 lt' (filter (fun fd' -> fd <> fd') rl) ;
//     assert_norm (ergar (tl @ (ERead true fd0 (Inl x0)) :: lt') (filter (fun fd' -> fd <> fd') rl) == ergar (EWrite true (fd,x) y :: tl @ (ERead true fd0 (Inl x0)) :: lt') rl)
//   | _ :: tl -> response_ignore_read tl fd0 x0 lt' rl

let is_write_true e =
  match e with
  | EWrite true (fd,x) y -> true
  | _ -> false

let write_true_fd e : Pure file_descr (requires is_write_true e) (ensures fun _ -> True) =
  match e with
  | EWrite true (fd,x) y -> fd

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
  | EWrite true (fd,x) y ->
    calc (==) {
      write_true_fd e ;
      == {}
      write_true_fd (EWrite true (fd,x) y) ;
      == {}
      fd ;
    } ;
    // assert_norm ((fun fd' -> fd <> fd') == (fun fd' -> write_true_fd e <> fd')) ;
    cong (fun fd -> (fun fd' -> fd <> fd')) fd (write_true_fd e) ;
    calc (==) {
      ergar (e :: l) rl ;
      == {}
      ergar (EWrite true (fd,x) y :: l) rl ;
      == { _ by (compute ()) }
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
  | ERead true fd (Inl _) :: tl ->
    assert (ergar tl (fd :: rl0 @ rl1)) ;
    assert (ergar tl (fd :: rl0 @ rl2)) ;
    ergar_merge tl (fd :: rl0) rl1 rl2
  | EWrite true (fd,x) y :: tl ->
    cong (fun fd -> (fun fd' -> fd <> fd')) fd (write_true_fd (EWrite true (fd,x) y)) ;

    ergar_write_true (EWrite true (fd,x) y) tl (rl0 @ rl1) ;
    assert (ergar tl (filter (fun fd' -> fd <> fd') (rl0 @ rl1))) ;
    filter_append (fun fd' -> fd <> fd') rl0 rl1 ;

    ergar_write_true (EWrite true (fd,x) y) tl (rl0 @ rl2) ;
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

    ergar_write_true (EWrite true (fd,x) y) tl (rl0 @ rl1 @ rl2) ;
    assert (ergar tl (filter (fun fd' -> fd <> fd') (rl0 @ rl1 @ rl2)))
  | _ :: tl -> ergar_merge tl rl0 rl1 rl2

let rec ergar_split lt rl1 rl2 :
  Lemma
    (requires ergar lt (rl1 @ rl2))
    (ensures ergar lt rl1 /\ ergar lt rl2)
= match lt with
  | [] -> ()
  | ERead true fd (Inl _) :: tl ->
    assert (ergar tl (fd :: rl1 @ rl2)) ;
    ergar_split tl (fd :: rl1) rl2 ;
    assert (ergar tl (fd :: rl1)) ;
    ergar_split tl [fd] rl1 ;
    ergar_merge tl [] [fd] rl2 ;
    assert (ergar tl (fd :: rl2))
  | EWrite true (fd,x) y :: tl ->
    cong (fun fd -> (fun fd' -> fd <> fd')) fd (write_true_fd (EWrite true (fd,x) y)) ;

    ergar_write_true (EWrite true (fd,x) y) tl (rl1 @ rl2) ;
    assert (ergar tl (filter (fun fd' -> fd <> fd') (rl1 @ rl2))) ;
    filter_append (fun fd' -> fd <> fd') rl1 rl2 ;

    ergar_split tl (filter (fun fd' -> fd <> fd') rl1) (filter (fun fd' -> fd <> fd') rl2) ;

    ergar_write_true (EWrite true (fd,x) y) tl rl1 ;
    ergar_write_true (EWrite true (fd,x) y) tl rl2
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
  | ERead true fd (Inl _) :: tl ->
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
  | EWrite true (fd,x) y :: tl ->
    ergar_write_true (EWrite true (fd,x) y) tl rl ;
    cong (fun fd -> (fun fd' -> fd <> fd')) fd (write_true_fd (EWrite true (fd,x) y)) ;
    assert (ergar tl (filter (fun fd' -> fd <> fd') rl)) ;
    ergar_filter tl (filter (fun fd' -> fd <> fd') rl) f ;
    assert (ergar tl (filter f (filter (fun fd' -> fd <> fd') rl))) ;
    ergar_write_true (EWrite true (fd,x) y) tl (filter f rl) ;
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
  | ERead true fd (Inl _) :: tl -> admit ()
  | EWrite true (fd,x) y :: tl -> admit ()
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
    | EWrite true (fd,x) y ->
      assume (every_request_gets_a_response ((lt @ [ EWrite true (fd,x) y ]) @ lt')) ;
      ergar_pi_irr (e :: h) l (lt @ [ e ]) lt'
    | _ ->
      ergar_ignore_no_write_read lt e lt' [] ;
      ergar_pi_irr (e :: h) l (lt @ [ e ]) lt'
    end

open FStar.Tactics
(* This may take a bit of effort to prove. *)
let webserver (handler:request_handler IOActions) :
  IIO int IOActions
    (requires fun h -> True)
    (ensures fun _ _ lt ->
      every_request_gets_a_response lt)  =

  assume (forall h lthandler lt lt'. enforced_locally pi h lthandler ==> every_request_gets_a_response (lt @ lt') ==> every_request_gets_a_response (lt @ lthandler @ lt')) ;
  assume (forall h lthandler client r lt. enforced_locally pi h lthandler ==> wrote_at_least_once_to client lthandler ==> every_request_gets_a_response lt ==> every_request_gets_a_response (lt @ [ ERead true client r ] @ lthandler)) ;

  let client = static_cmd true Openfile "test.txt" in
  (* lt = [ EOpenfile ... ] *)
  match client with
  | Inr _ -> -1
  | Inl client ->
    begin match get_req client with
    | Inr _ -> -1
    | Inl req ->
      (* one Read true from the client happened *)
      (* lt = [ EOpenfile ... ; ERead true client req ] *)
      begin match handler client req (fun res -> static_cmd true Write (client,res)) with
      (* we know from enforced_locally pi that no other Reads true happened *)
      | Inr err ->
        (* lt = [ EOpenfile ... ; ERead true client req ] @ lthandler *)
        (* this responds to the client *)
        sendError 400 client
        (* lt = [ EOpenfile ... ; ERead true client req ] @ lthandler @ [ EWrite true (client, _) _ ] *)
      | Inl client ->
        (* here we know that the handler wrote to the client *)
        (* lt = [ EOpenfile ... ; ERead true client req ] @ lthandler *)
        ()
      end ;
      0
    end

(** ** Instante source interface with the example **)

val phi : enforced_policy pi
let phi h cmd arg =
  match cmd with
  | Openfile ->
    if arg = "/temp" then true else false
  | Read -> is_opened_by_untrusted h arg
  | Close -> is_opened_by_untrusted h arg
  | Write -> false

let psi : trace -> int -> trace -> Type0 =
  (fun _ _ lt -> every_request_gets_a_response lt)

  (*
let rec lemma1 (lt h:trace) : Lemma (requires (enforced_locally pi h lt)) (ensures (handler_only_openfiles_reads_client lt)) =
  match lt with
  | [] -> ()
  | e::tl -> admit ()//  lemma1 tl (e::h)

let ct_rcs' : tree pck_rc = 
  Node 
    (| string, resexn unit, (fun msg h _ _ -> valid_http_response msg && did_not_respond h) |)
    Leaf
    Leaf


let ct_rcs : tree pck_rc =
  Node (| file_descr -> string -> trace -> resexn unit -> trace -> bool, (fun (client, req) _ _ lt -> wrote_at_least_once_to client lt) |)
    ct_rcs'
    Leaf
*)
(** ** Tests: compile web-server, back-translate handler, linking **)
