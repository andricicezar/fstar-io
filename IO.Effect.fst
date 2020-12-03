module IO.Effect

open FStar.Tactics
open ExtraTactics

open Common
open IO.Free

let io_post a = maybe a -> trace -> Type0  // local_events (from old to new)
let io_wpty a = trace -> io_post a -> Type0  // past_events (from new to old; reversed compared with local_events)

unfold
let io_return_wp (a:Type) (x:a) : io_wpty a =
  fun _ p -> p (Inl x) []

unfold
let compute_post (a b:Type) (h:trace) (kw : a -> io_wpty b) (p:io_post b)
  : io_post a =
      (fun result local_events -> 
        match result with
        | Inl result -> (
            kw result
            ((List.rev local_events) @ h) 
            (fun result' local_events' -> 
                p result' (local_events @ local_events')))
        | Inr err -> p (Inr err) local_events)

unfold
let io_bind_wp (a:Type) (b:Type) (w : io_wpty a) (kw : a -> io_wpty b) : io_wpty b =
  fun h p -> 
    w h (compute_post a b h kw p)

let gen_post #a (post:io_post a) (e:event) = 
  fun x local_events -> post x (e :: local_events)

let rec io_interpretation #a
  (m : io a) 
  (p : io_post a) : Type0 = 
  match m with
  | Return x -> p (Inl x) []
  | Throw err -> p (Inr err) []
  | Cont (Call cmd args fnc) -> (
    forall res. (
      FStar.WellFounded.axiom1 fnc res;
      let e : event = convert_call_to_event cmd args res in
      io_interpretation (fnc res) (gen_post p e)))


// REFINED COMPUTATION MONAD (repr)
let io_irepr (a:Type) (wp:io_wpty a) =
  h:trace -> post:io_post a ->
    Pure (io a)
      (requires (wp h post))
      (ensures (fun (t:io a) -> io_interpretation t post))

let io_ireturn (a : Type) (x : a) : io_irepr a (io_return_wp a x) =
  fun _ _ -> io_return a x

unfold
val io_wpty_ord (#a : Type) : io_wpty a -> io_wpty a -> Type0
let io_wpty_ord wp1 wp2 = forall h p. wp1 h p ==> wp2 h p

let io_ibind (a b : Type) (wp_v : io_wpty a) (wp_f: a -> io_wpty b) (v : io_irepr a wp_v)
  (f : (x:a -> io_irepr b (wp_f x))) : io_irepr b (io_bind_wp _ _ wp_v wp_f) =
  fun h p -> 
    let t = (io_bind a b 
        (v h (compute_post a b h wp_f p))
        (fun x ->
          assume (wp_f x h p);
           f x h p)) in
    assume (io_interpretation t p);
    t

unfold
let isubcomp (a:Type) (wp1 wp2: io_wpty a) (f : io_irepr a wp1) :
  Pure (io_irepr a wp2) (requires io_wpty_ord wp2 wp1) (ensures fun _ -> True) = f

unfold
let wp_if_then_else (#a:Type) (wp1 wp2:io_wpty a) (b:bool) : io_wpty a =
  fun h p -> (b ==> wp1 h p) /\ ((~b) ==> wp2 h p)

unfold
let i_if_then_else (a : Type) (wp1 wp2: io_wpty a) (f : io_irepr a wp1) (g : io_irepr a wp2) (b : bool) : Type =
  io_irepr a (wp_if_then_else wp1 wp2 b)

total
reifiable
reflectable
layered_effect {
  IOwp : a:Type -> wp : io_wpty a -> Effect
  with
       repr       = io_irepr
     ; return     = io_ireturn
     ; bind       = io_ibind

     ; subcomp      = isubcomp
     ; if_then_else = i_if_then_else
}

let lift_pure_iowp (a:Type) (wp:pure_wp a) (f:(eqtype_as_type unit -> PURE a wp)) :
  Tot (io_irepr a (fun s0 p -> wp (fun r -> p (Inl r) [])))
  = fun s0 p -> let r = elim_pure f (fun r -> p (Inl r) []) in io_return _ r

sub_effect PURE ~> IOwp = lift_pure_iowp
  
effect IO
  (a:Type)
  (pre : trace -> Type0)
  (post : trace -> maybe a -> trace -> Type0) =
  IOwp a (fun (h:trace) (p:io_post a) ->
    pre h /\ (forall res le. post h res le ==>  p res le))

let rec is_open (fd:file_descr) (h: trace) :
  Tot bool =
  match h with
  | [] -> false
  | h :: tail -> match h with
               | EOpenfile _ (Inl fd') ->
                   if fd = fd' then true
                   else is_open fd tail
               | EClose fd' _ -> 
                    if fd = fd' then false
                    else is_open fd tail
               | _ -> is_open fd tail

val default_check : monitorable_prop
let default_check (h:trace) (action:action_type) =
  match action with
  | (| Openfile, fnm |) -> true
  | (| Read, fd |) -> is_open fd h
  | (| Close, fd |) -> is_open fd h

let static_cmd
  (cmd : io_cmds)
  (argz : io_args cmd) :
  IO (res cmd)
    (requires (fun h -> default_check h (| cmd, argz |)))
    (ensures (fun h r local_trace ->
      ~(Inr? r /\ Inr?.v r == Contract_failure) /\
      local_trace == [convert_call_to_event cmd argz r]
      /\ enforced_locally default_check h local_trace
  )) =
  IOwp?.reflect(fun _ _ -> io_call cmd argz)
