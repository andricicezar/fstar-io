let plugin (client:Types.file_descr) : unit =
  let (msg, size) = IUnix.read client 250 in
    if size < 1 then () 
    else begin
      let _ = IUnix.write client msg in
      ()
    end
