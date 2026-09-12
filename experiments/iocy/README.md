1. Define an interleaving function for asynchronous traces
2. Define LTL on a normal trace
    - LTL gives an option between Angel or Demonic (different from the choice in the theta)


val interleave #e
    (map: map_t (promise) (atrace e)) (** tr suffix of promise.lt **)
    (_ : forall pr. pr in map ==> closed map (map pr))
    (at : atrace e){closed map at}
    : set (trace e)
where 
  trace e = list e
  atrace e = list (event e)
  closed map tr = forall pr. pr in (free tr) ==> pr in map


let await pr :
  Cy unit
    (requires fun (h:atrace e) -> (EAsync pr) in* h) (** h could be a interleaved trace that contains Async and Awaits. **)
    (ensures  fun _ _ (lt:atrace e) -> lt == [EAwait pr]) =
  reflect (Await pr)

let _ =
  let pr = async (fun _ -> ...) in
  (fun () -> await pr) (** the type of the callback depends on pr **)

let w_pre = h:atrace e -> map:map_t (promise e) (atrace e){
                                closed map h /\ 
                                (forall pr. pr in map ==> map pr `suffix` pr.lt)} -> Type0
let w_post a =
    a -> lt:atrace e -> map':map_t (promise e) (atrace e){
       map < map' /\
       closed map' (h @ lt) /\ 
    } -> Type0

w a = h:atrace -> map:... -> w_post a map -> Typo0  

let f pr :
  Cy unit
    (requires fun (h:atrace e) map -> closed map h /\ pr in map) 
    (ensures  fun _ map _ (lt:atrace e) map' ->
        map' == (map_await map pr) /\ (** map' = map[pr := []] **) 
        closed map' (h@lt) /\
        lt == [EAwait pr; Ev 0] /\
        ltl (Eventually (Now 0)) (interleave map () lt)) =
  await pr;
  print 0

let g () =
  let pr' = async (fun _ -> 
    let pr = async (fun _ -> print -2) in
    f pr) in (** h of f = [EAsync pr]) **)
  let pr'' = async (fun _ -> print -1) in
  await pr';
  await pr''
{ Eventually (And (Now -2) (Eventually (Now 0))) }
