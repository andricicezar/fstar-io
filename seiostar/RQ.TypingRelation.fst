module RQ.TypingRelation

open FStar.Tactics

open IOStar
include QTypes.Sem

(** Fine-grained call by value **)
[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type typing : #a:qType -> g:typ_env -> fs_oval g a -> Type =
| Qtt         : #g : typ_env -> typing g (fs_oval_return g qUnit ())
| QFd         : #g : typ_env -> fd:file_descr -> typing g (fs_oval_return g qFileDescr fd)

| QVar0       : #g : typ_env ->
                #a : qType ->
                typing (extend a g) (fs_oval_var0 g a)

| QVarS       : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #x : fs_oval g a ->
                typing g x ->
                typing (extend b g) (fs_oval_varS b x)

| QAppGhost   : #g : typ_env ->
                #a : qType ->
                #f : fs_oval g (a ^-> qUnit) -> (** This has to be Tot. If it is GTot unit, F* can treat it as Pure unit **)
                #x : fs_oval g a ->
                typing #qUnit g (fs_oval_app #_ #_ #_ f x)

| QApp        : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #f : fs_oval g (a ^-> b) ->
                #x : fs_oval g a ->
                typing g f ->
                typing g x ->
                typing g (fs_oval_app #_ #_ #_ f x)

| QLambda     : #a : qType ->
                #b : qType ->
                #g : typ_env ->
                #body : fs_oval (extend a g) b ->
                typing (extend a g) body ->
                typing #(a ^-> b) g (fs_oval_lambda body)

| QTrue       : #g : typ_env -> typing g (fs_oval_return g qBool true)
| QFalse      : #g : typ_env -> typing g (fs_oval_return g qBool false)
| QStringLit  : #g : typ_env -> s:string -> typing g (fs_oval_return g qString s)
| QStringEq   : #g : typ_env ->
                #s1 : fs_oval g qString ->
                typing g s1 ->
                #s2 : fs_oval g qString ->
                typing g s2 ->
                typing g (fs_oval_eq_string s1 s2)
| QIf         : #g : typ_env ->
                #a : qType ->
                #c : fs_oval g qBool ->
                typing g c ->
                #t : fs_oval g a ->
                typing g t ->
                #e : fs_oval g a ->
                typing g e ->
                typing g (fs_oval_if c t e)

| QMkpair   : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #x : fs_oval g a ->
              #y : fs_oval g b ->
              typing g x ->
              typing g y ->
              typing g (fs_oval_pair x y)
| QFst      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g (a ^* b) ->
              typing g p ->
              typing g (fs_oval_fmap p fst)
| QSnd      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g (a ^* b) ->
              typing g p ->
              typing g (fs_oval_fmap p snd)
| QInl      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g a ->
              typing g p ->
              typing #(a ^+ b) g (fs_oval_fmap p Inl)
| QInr      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g b ->
              typing g p ->
              typing #(a ^+ b) g (fs_oval_fmap p Inr)
| QCase     : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #c : qType ->
              #cond : fs_oval g (a ^+ b) ->
              typing g cond ->
              #inlc : fs_oval (extend a g) c ->
              typing _ inlc ->
              #inrc : fs_oval (extend b g) c ->
              typing _ inrc ->
              typing g (fs_oval_case cond inlc inrc)
| QLambdaProd : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #body : fs_oprod (extend a g) b ->
                typing_io (extend a g) body ->
                typing g (fs_oval_lambda_oprod body)
and typing_io : #a:qType -> g:typ_env -> fs_oprod g a -> Type =
| QCall :
        #g:typ_env ->
        o:io_ops ->
        #args:fs_oval g (q_io_args o) ->
        typing g args ->
        typing_io #(q_io_res o) g (fs_oprod_call_oval o args)

| QReturn :
        #g:typ_env ->
        #a:qType ->
        #x:fs_oval g a ->
        typing g x ->
        typing_io #a g (fs_oprod_return x)

| QBindProd :
        #g:typ_env ->
        #a:qType ->
        #b:qType ->
        #m:fs_oprod g a ->
        #k:fs_oprod (extend a g) b ->
        typing_io g m ->
        typing_io (extend a g) k ->
        typing_io #b g (fs_oprod_bind m k)

| QAppProd    : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #f : fs_oval g (a ^->!@ b) ->
                #x : fs_oval g a ->
                typing g f ->
                typing g x ->
                typing_io g (fs_oprod_app_oval_oval f x)
| QIfProd     : #g : typ_env ->
                #a : qType ->
                #c : fs_oval g qBool ->
                typing #qBool g c ->
                #t : fs_oprod g a ->
                typing_io g t ->
                #e : fs_oprod g a ->
                typing_io g e ->
                typing_io g (fs_oprod_if_oval c t e)
| QCaseProd : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #c : qType ->
              #cond : fs_oval g (a ^+ b) ->
              typing g cond ->
              #inlc : fs_oprod (extend a g) c ->
              typing_io _ inlc ->
              #inrc : fs_oprod (extend b g) c ->
              typing_io _ inrc ->
              typing_io g (fs_oprod_case_oval cond inlc inrc)

let (⊢) (#a:qType) (g:typ_env) (x:fs_oval g a) =
  typing g x

unfold
let helper_oval (#a:qType) (x:fs_val a) : fs_oval empty a = fun _ -> x

unfold
let helper_oval_g (#a:qType) (#g:typ_env) (x:fs_val a) : fs_oval g a = fun _ -> x

unfold
let helper_oprod (#a:qType) (x:fs_prod a) : fs_oprod empty a = fun _ -> x

let (⊩) (a:qType) (x:fs_val a) =
  typing #a empty (helper_oval x)

type prod_quotation (a:qType) (x:fs_prod a) =
  typing_io #a empty (helper_oprod x)
