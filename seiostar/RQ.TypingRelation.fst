module RQ.TypingRelation

open FStar.Tactics

open IOStar
include QTypes.OpenValComp

(** Fine-grained call by value **)
[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type typing : #a:qType -> g:typ_env -> #wpG:spec_env g a -> fs_oval g a wpG -> Type =
| Qtt         : #g : typ_env -> typing g (fs_oval_return g #qUnit ())
| QFd         : #g : typ_env -> fd:file_descr -> typing g (fs_oval_return g #qFileDescr fd)

| QAxiom      : #g : typ_env ->
                #a : qType ->
                typing (extend a g) (fs_oval_axiom g a)

| QWeaken      : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #wpX : spec_env g a ->
                #x : fs_oval g a wpX ->
                typing g x ->
                typing (extend b g) (fs_oval_weaken b x)

| QAppGhost   : #g : typ_env ->
                #a : qType ->
                #wpF : spec_env g (a ^-> qUnit) ->
                #f : fs_oval g (a ^-> qUnit) wpF -> (** This has to be Tot. If it is GTot unit, F* can treat it as Pure unit **)
                #wpX : spec_env g a ->
                #x : fs_oval g a wpX ->
                typing g (fs_oval_app f x)

| QApp        : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #wpF : spec_env g (a ^-> b) ->
                #f : fs_oval g (a ^-> b) wpF ->
                #wpX : spec_env g a ->
                #x : fs_oval g a wpX ->
                typing g f ->
                typing g x ->
                typing g (fs_oval_app f x)

| QLambda     : #a : qType ->
                #b : qType ->
                #g : typ_env ->
                #wpBody : spec_env (extend a g) b ->
                #body : fs_oval (extend a g) b wpBody ->
                typing (extend a g) body ->
                typing #(a ^-> b) g (fs_oval_lambda body)

| QTrue       : #g : typ_env -> typing g (fs_oval_return g #qBool true)
| QFalse      : #g : typ_env -> typing g (fs_oval_return g #qBool false)
| QStringLit  : #g : typ_env -> s:string -> typing g (fs_oval_return g #qString s)
| QStringEq   : #g : typ_env ->
                #wpS1 : spec_env g qString ->
                #s1 : fs_oval g qString wpS1 ->
                typing g s1 ->
                #wpS2 : spec_env g qString ->
                #s2 : fs_oval g qString wpS2 ->
                typing g s2 ->
                typing g (fs_oval_eq_string s1 s2)
| QIf         : #g : typ_env ->
                #a : qType ->
                #wpC : spec_env g qBool ->
                #c : fs_oval g qBool wpC ->
                typing g c ->
                #wpT : spec_env g a ->
                #t : fs_oval g a wpT ->
                typing g t ->
                #wpE : spec_env g a ->
                #e : fs_oval g a wpE ->
                typing g e ->
                typing g (fs_oval_if c t e)

| QMkpair   : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #wpX : spec_env g a ->
              #x : fs_oval g a wpX ->
              #wpY : spec_env g b ->
              #y : fs_oval g b wpY ->
              typing g x ->
              typing g y ->
              typing g (fs_oval_pair x y)
| QFst      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #wpP : spec_env g (a ^* b) ->
              #p : fs_oval g (a ^* b) wpP ->
              typing g p ->
              typing g (fs_oval_fmap p fst)
| QSnd      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #wpP : spec_env g (a ^* b) ->
              #p : fs_oval g (a ^* b) wpP ->
              typing g p ->
              typing g (fs_oval_fmap p snd)
| QInl      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #wpP : spec_env g a ->
              #p : fs_oval g a wpP ->
              typing g p ->
              typing #(a ^+ b) g (fs_oval_fmap p Inl)
| QInr      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #wpP : spec_env g b ->
              #p : fs_oval g b wpP ->
              typing g p ->
              typing #(a ^+ b) g (fs_oval_fmap p Inr)
| QCase     : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #c : qType ->
              #wpCond : spec_env g (a ^+ b) ->
              #cond : fs_oval g (a ^+ b) wpCond->
              typing g cond ->
              #wpInlc : spec_env (extend a g) c ->
              #inlc : fs_oval (extend a g) c wpInlc ->
              typing _ inlc ->
              #wpInrc : spec_env (extend b g) c ->
              #inrc : fs_oval (extend b g) c wpInrc ->
              typing _ inrc ->
              typing g (fs_oval_case cond inlc inrc)
| QLambdaIO : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #wpBody : spec_env (extend a g) b ->
                #body : fs_ocomp (extend a g) b wpBody ->
                typing_io (extend a g) body ->
                typing g (fs_oval_lambda_ocomp body)
and typing_io : #a:qType -> g:typ_env -> #wpG:spec_env g a -> fs_ocomp g a wpG -> Type =
| QCall :
        #g:typ_env ->
        o:io_ops ->
        #wpArgs:spec_env g (q_io_args o) ->
        #args:fs_oval g (q_io_args o) wpArgs ->
        typing g args ->
        typing_io #(q_io_res o) g (fs_ocomp_call_oval o args)

| QReturn :
        #g:typ_env ->
        #a:qType ->
        #wpX:spec_env g a ->
        #x:fs_oval g a wpX ->
        typing g x ->
        typing_io #a g (fs_ocomp_return_oval x)

| QBind :
        #g:typ_env ->
        #a:qType ->
        #b:qType ->
        #wpM:spec_env g a ->
        #m:fs_ocomp g a wpM ->
        #wpK:(spec_env (extend a g) b) ->
        #k:fs_ocomp (extend a g) b wpK ->
        typing_io g m ->
        typing_io (extend a g) k ->
        typing_io #b g (fs_ocomp_bind m k)

| QAppIO    : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #wpF : spec_env g (a ^->!@ b) ->
                #f : fs_oval g (a ^->!@ b) wpF ->
                #wpX : spec_env g a ->
                #x : fs_oval g a wpX ->
                typing g f ->
                typing g x ->
                typing_io g (fs_ocomp_app_oval_oval f x)
| QIfIO     : #g : typ_env ->
              #a : qType ->
              #wpC : spec_env g qBool ->
              #c : fs_oval g qBool wpC ->
              typing g c ->
              #wpT : spec_env g a ->
              #t : fs_ocomp g a wpT ->
              typing_io g t ->
              #wpE : spec_env g a ->
              #e : fs_ocomp g a wpE ->
              typing_io g e ->
              typing_io g (fs_ocomp_if_oval c t e)
| QCaseIO : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #c : qType ->
              #wpCond : spec_env g (a ^+ b) ->
              #cond : fs_oval g (a ^+ b) wpCond ->
              typing g cond ->
              #wpInlc : spec_env (extend a g) c ->
              #inlc : fs_ocomp (extend a g) c wpInlc->
              typing_io _ inlc ->
              #wpInrc : spec_env (extend b g) c ->
              #inrc : fs_ocomp (extend b g) c wpInrc ->
              typing_io _ inrc ->
              typing_io g (fs_ocomp_case_oval cond inlc inrc)

let (⊢) (#a:qType) (g:typ_env) (#wp:spec_env g a) (x:fs_oval g a wp) =
  typing g x

let fs_oval_helper (#a:qType) (x:fs_val a) (#wp:spec_env empty a) (#_:squash (forall fsG. wp fsG `pure_stronger _` pure_return _ x))
  : fs_oval empty a wp
  = fun _ -> x

let (⊩) (a:qType) (x:fs_val a) =
  wp:spec_env empty a & (proof:squash (forall fsG. wp fsG `pure_stronger _` pure_return _ x) -> typing #a empty #wp (fs_oval_helper x))

let mk_dturniqet #a #x (#wp:spec_env empty a) (thk_dv:(proof:squash (forall fsG. wp fsG `pure_stronger _` pure_return _ x) -> typing #a empty #wp (fs_oval_helper x))) : a ⊩ x =
  (| _, thk_dv |)