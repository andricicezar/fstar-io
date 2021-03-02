module Handle

let static_cmd
  (pi : monitorable_prop)
  (cmd : io_cmds)
  (argz : io_args cmd) :
  IO (res cmd) pi
    (requires (fun h -> pi h (| cmd, argz |)))
    (ensures (fun _ r lt ->
      ~(Inr? r /\ Inr?.v r == Contract_failure) /\
      (_obs_cmds cmd ==>  lt == [convert_call_to_event cmd argz r]) /\
      (_tau_cmds cmd ==>  lt == []))) =
  IOwp?.reflect(fun _ _ -> io_call cmd argz)

let _IIOwp_as_MIIO
  (pre:'a -> trace -> bool)
  (post:'a -> trace -> (m:maybe 'b) -> trace -> (r:Type0))
  (f:(x:'a ->
    IIOwp 'b (fun h p -> pre x h /\ (forall r lt. post x h r lt ==> p r lt))))
  (x:'a) :
  MIIO 'b =
  let h = get_trace () in
  if pre x h then f x
  else IIO.Effect.throw Contract_failure

let dynamic_cmd
  (pi : monitorable_prop)
  (cmd : io_cmds)
  (arg : args cmd) :
  IIO (res cmd) pi
    (requires (fun _ -> True))
    (ensures (fun _ r lt ->
      (match r with
      | Inr Contract_failure -> lt == []
      | _ -> (_obs_cmds cmd ==> lt == [convert_call_to_event cmd arg r]) /\
            (_tau_cmds cmd ==> lt == [])))) =
  let h = get_trace () in
  let action = (| cmd, arg |) in
  match pi h action with
  | true -> static_cmd pi cmd arg
  | false -> throw Contract_failure


let rec _import_pi_IIO
  (#b:Type)
  (tree : iio b)
  (pi:monitorable_prop) :
  IIO b pi (fun _ -> True) (fun _ _ _ -> True) =
  match tree with
  | Return (Inl r) -> r
  | Return (Inr err) -> IIO.Effect.throw err
  | Call GetTrace argz fnc ->
      let h = IIO.Effect.get_trace () in
      let z' : iio b = fnc (Inl h) in
      rev_append_rev_append ();
      _import_pi_IIO z' pi
  | Call cmd argz fnc ->
      let rez : res cmd = IIO.Effect.dynamic_cmd pi cmd argz in
      let rezm : resm cmd = Inl rez in
      let z' : iio b = fnc rezm in
      rev_append_rev_append ();
      _import_pi_IIO z' pi

let handle = _import_pi_IIO

let ctx_t_to_ctx_p
  (pi:monitorable_prop)
  (f:'a -> MIIO 'b)
  (x:'a) :
  IIO 'b pi (fun _ -> True) (fun _ _ _ -> True) =
    handle ((* MIIO.*)reify (f x) [] (fun _ _ -> True)) pi
