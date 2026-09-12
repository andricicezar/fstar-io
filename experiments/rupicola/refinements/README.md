Saving here some pieces of code I did previously:

```fstar
type_quotation =
| RRefined : #t:typ ->
             #s:Type0 ->
             rtyp t s ->
             p:(s -> Type0) ->
             rtyp t (x:s{p x})

let rec (∋) .. = 
| RRefined #t' #s' r' p -> begin
  assert (p fs_v);
  (| t', s', r' |) ∋ (fs_v, e)
end
```