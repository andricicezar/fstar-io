open FStar_Pervasives

let ctx (x:Types.file_descr) : unit Common.maybe =
  try
    Inl (Plugin.plugin x)
  with err ->
    raise err;
    Inr err

let _ =
  match WebServer_Compiled.compiled_webserver'' ctx with
  | Inl _ -> ()
  | Inr err -> raise err
