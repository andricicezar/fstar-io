module DivFreeTauSpec.Test

open DivFreeTauSpec


let test1 : iwp unit =
  iprepost (fun _ -> True) (fun h r -> diverges r)

let testfalse : iwp unit =
  iprepost (fun _ -> False) (fun h r -> True)

// TODO: is this surprising?
let d = assert (test1 `ile` i_bind test1 (fun _ -> testfalse))
