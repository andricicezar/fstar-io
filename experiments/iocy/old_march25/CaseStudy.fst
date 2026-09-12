module CaseStudy

open FStar.String

assume val compress : raw:string -> comp:string{strlen comp <= strlen raw}

(** spec: the file `fnm` is opened, its contents is read, and the content is compressed and written to a new file **)
let compress_file (fnm:string) =
  let ifd = openfile fnm in
  let contents = read fd in
  let ofd = openfile ("compressed-" ^ fnm) in
  write ofd (compress contents);
  close ifd;
  close ofd

let archieve (fnm1 fnm2:string) =
  let pr1 = async (fun () -> compress_file fnm1) in
  let pr2 = async (fun () -> compress_file fnm2) in
  await pr1;
  await pr2
