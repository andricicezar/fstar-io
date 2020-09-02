

let openfile10
  (argz : string) :
  IOStHist file_descr 
    (requires (fun s0 -> default_check s0 (| Openfile, argz |)))
    (ensures (fun s0 (result:maybe (events_trace * file_descr)) local_trace -> True)) =
  IOStHist?.reflect(lift_io_iost #file_descr (io_openfile argz))

val m4_openfile10 : string -> M4 file_descr 
let m4_openfile10 = export openfile10

let x = reify (openfile10 "asd") []
let y = reify (m4_openfile10 "asd")
let _ = assert (x == y) by (
  unfold_def(`y);
  dump "h")
  
