WebServer

10 top-level defiinitions + `static_op` + type `req_handler`.

- Refinement.
  Only one, in the return type of `get_req`
  ```fstar
  let get_req (fd:file_descr) :
      MIO (resexn (r:Bytes.bytes{valid_http_request r})) IOOps mymst (fun _ -> True) (fun _ _ lt -> exists r'. lt == [ERead Prog (fd, (UInt8.uint_to_t 255)) r']) =
  ```
- Fixpoints.
  Two: `server_loop` (fuel) and `process_connections` (list of clients)
- Proofs/Lemmas
  -  `process_connection` seems to be the most difficult for the SMT. The proof is inlined and `split_queries` is used.
  - `process_connections`, `server_loop_body`, `server_loop`, `webserver` have one lemma application
- Data Structures
  - Lists
  - Tuples
  - Sums
  - erased -- is this problematic?
  - file_descr
  - bytes
- Pattern Matching
- Size
  - biggest seems to be `get_new_connection`, 10 lines of code, match, if, match
  - `process_connection` or `process_connections` may be harder to do
  - `process_connections` seems to have the most functional applications. 5
- Anonymous lambdas
  In `process_connection`, but a synonym could be defined outside.

We want to compile the "compiled web-server".
The hope is that by normalizing, the import/export TC dissapear, and one is left only with the HOC.
  