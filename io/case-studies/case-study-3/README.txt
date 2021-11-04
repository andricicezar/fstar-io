This case study is linking a Server written in F* with a plugin written in OCaml.
The result is a TCP server that responds to HTTP requests at 127.0.0.1:81 and returns files.
Try to ask for /etc/passwd to get a Contract_failure.