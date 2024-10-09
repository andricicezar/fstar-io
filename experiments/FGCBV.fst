module FGCBV

type typ =
| TUnit   : typ
| TArr    : typ -> typ -> typ 
| TPair   : typ -> typ -> typ

type var = nat

type exp =
| EProduce     : exp -> exp
| ETo          : exp -> exp -> exp
| EUnit        : exp
| EVar         : var -> exp
| EApp         : exp -> exp -> exp
| EAbs         : typ -> exp -> exp
| ELet         : exp -> exp -> exp
| EPm          : exp -> exp -> exp
| EPair        : fst:exp -> snd:exp -> exp

type context = var -> Tot (option typ)

val empty : context
let empty _ = None

(* we only need extend at 0 *)
val extend : typ -> context -> Tot context
let extend t g y = if y = 0 then Some t
                   else g (y-1)

noeq type typing_v : context -> exp -> typ -> Type0 =
| TyVar : #g:context ->
          x:var{Some? (g x)} ->
          typing_v g (EVar x) (Some?.v (g x))

| TyPair : #g:context ->
           #e1:exp -> 
           #e2:exp ->
           #t1:typ ->
           #t2:typ -> 
           typing_v g e1 t1 ->
           typing_v g e2 t2 ->
           typing_v g (EPair e1 e2) (TPair t1 t2)
| TyLetV : #g:context ->
           #e1:exp -> 
           #t1:typ ->
           #e2:exp ->
           #t2:typ ->
           typing_v g e1 t1 ->
           typing_v (extend t1 g) e2 t2 ->
           typing_v g (ELet e1 e2) t2
| TyPmV : #g:context ->
          #e1:exp ->
          #t1:typ ->
          #t2:typ ->
          #e2:exp ->
          typing_v g e1 (TPair t1 t2) ->
          typing_v (extend t2 (extend t1 g)) e2 t2 ->
          typing_v g (EPm e1 e2) t2
| TyAbs : #g:context ->
          t1:typ ->
          #e2:exp -> 
          #t2:typ ->
          typing_p (extend t1 g) e2 t2 ->
          typing_v g (EAbs t1 e2) (TArr t1 t2)
and typing_p : context -> exp -> typ -> Type0 =
| TyProduce : #g:context ->
              #e:exp ->
              #t:typ ->
              typing_v g e t ->
              typing_p g (EProduce e) t
| TyLetP : #g:context ->
           #e1:exp -> 
           #t1:typ ->
           #e2:exp ->
           #t2:typ ->
           typing_v g e1 t1 ->
           typing_p (extend t1 g) e2 t2 ->
           typing_p g (ELet e1 e2) t2
| TyPmP : #g:context ->
          #e1:exp ->
          #t1:typ ->
          #t2:typ ->
          #e2:exp ->
          typing_v g e1 (TPair t1 t2) ->
          typing_p (extend t2 (extend t1 g)) e2 t2 ->
          typing_p g (EPm e1 e2) t2
| TyTo  : #g:context ->
          #e1:exp ->
          #t1:typ ->
          #e2:exp ->
          #t2:typ ->
          typing_p g e1 t1 ->
          typing_p (extend t1 g) e2 t2 ->
          typing_p g (ETo e1 e2) t2
| TyApp : #g:context ->
          #e1:exp ->
          #t1:typ ->
          #e2:exp ->
          #t2:typ ->
          typing_v g e1 (TArr t1 t2) ->
          typing_v g e2 t2 ->
          typing_p g (EApp e1 e2) t2
