let plugin (client:Unixc.file_descr) : unit = 
  let (msg, size) = Unixc.read client 250 in
    if size < 1 then ()
    else begin
      let _ = Unixc.write client msg in
      ()
    end
