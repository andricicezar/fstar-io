let plugin (client:Types.file_descr) : unit = 
  print_string "Reached the plugin ...";
  flush stdout;
  let (msg, size) = IUnix.read client 250 in
    if size < 1 then begin 
      print_string "Exiting\n";
      flush stdout;
      ()
    end else begin
      let _ = IUnix.write client msg in
      print_string "Exiting\n";
      flush stdout;
      ()
    end
