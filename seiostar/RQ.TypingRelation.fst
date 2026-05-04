module RQ.TypingRelation

open IOStar
include QTypes.OpenValComp

(** Fine-grained call by value **)
[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type typing : #a:qType -> g:typ_env -> #preG:spec_env g -> fs_oval g a preG -> Type =
| Qtt         : #g : typ_env -> typing g (fs_oval_return g #qUnit ())
| QFd         : #g : typ_env -> fd:file_descr -> typing g (fs_oval_return g #qFileDescr fd)

| QAxiom      : #g : typ_env ->
                #a : qType ->
                typing (extend a g) (fs_oval_axiom g a)

| QWeaken      : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #preX : spec_env g ->
                #x : fs_oval g a preX ->
                typing g x ->
                typing (extend b g) (fs_oval_weaken b x)

| QRef    : #g : typ_env ->
                #a : qType ->
                #preV : spec_env g ->
                #v : fs_oval g a preV ->
                typing g v ->
                #ref : (ref_type a -> Type0) ->
                typing g (fs_oval_ref v ref)

| QApp        : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #preF : spec_env g ->
                #f : fs_oval g (a ^-> b) preF ->
                #preX : spec_env g ->
                #x : fs_oval g a preX ->
                typing g f ->
                typing g x ->
                typing g (fs_oval_app f x)

| QLambda     : #a : qType ->
                #b : qType ->
                #g : typ_env ->
                #preBody : spec_env (extend a g) ->
                #body : fs_oval (extend a g) b preBody ->
                typing (extend a g) body ->
                typing #(a ^-> b) g (fs_oval_lambda body)

| QZero       : #g : typ_env -> typing #qNat g (fs_oval_zero g)
| QSucc       : #g : typ_env ->
                #preN : spec_env g ->
                #n : fs_oval g qNat preN ->
                typing g n ->
                typing #qNat g (fs_oval_succ n)
| QNRec       : #g : typ_env ->
                #a : qType ->
                #preN : spec_env g ->
                #n : fs_oval g qNat preN ->
                #preBase : spec_env g ->
                #base : fs_oval g a preBase ->
                #preF : spec_env g ->
                #f : fs_oval g (a ^-> a) preF ->
                typing g n ->
                typing g base ->
                typing g f ->
                typing g (fs_oval_nrec n base f)

| QTrue       : #g : typ_env -> typing g (fs_oval_return g #qBool true)
| QFalse      : #g : typ_env -> typing g (fs_oval_return g #qBool false)
| QStringLit  : #g : typ_env -> s:string -> typing g (fs_oval_return g #qString s)
| QStringEq   : #g : typ_env ->
                #preS1 : spec_env g ->
                #s1 : fs_oval g qString preS1 ->
                typing g s1 ->
                #preS2 : spec_env g ->
                #s2 : fs_oval g qString preS2 ->
                typing g s2 ->
                typing g (fs_oval_eq_string s1 s2)
| QIf         : #g : typ_env ->
                #a : qType ->
                #preC : spec_env g ->
                #c : fs_oval g qBool preC ->
                typing g c ->
                #preT : spec_env g ->
                #t : fs_oval g a preT ->
                typing g t ->
                #preE : spec_env g ->
                #e : fs_oval g a preE ->
                typing g e ->
                typing g (fs_oval_if c t e)

| QMkpair   : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #preX : spec_env g ->
              #x : fs_oval g a preX ->
              #preY : spec_env g ->
              #y : fs_oval g b preY ->
              typing g x ->
              typing g y ->
              typing g (fs_oval_pair x y)
| QFst      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #preP : spec_env g ->
              #p : fs_oval g (a ^* b) preP ->
              typing g p ->
              typing g (fs_oval_fmap p fst)
| QSnd      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #preP : spec_env g ->
              #p : fs_oval g (a ^* b) preP ->
              typing g p ->
              typing g (fs_oval_fmap p snd)
| QInl      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #preP : spec_env g ->
              #p : fs_oval g a preP ->
              typing g p ->
              typing #(a ^+ b) g (fs_oval_fmap p Inl)
| QInr      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #preP : spec_env g ->
              #p : fs_oval g b preP ->
              typing g p ->
              typing #(a ^+ b) g (fs_oval_fmap p Inr)
| QCase     : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #c : qType ->
              #preCond : spec_env g ->
              #cond : fs_oval g (a ^+ b) preCond->
              typing g cond ->
              #preInlc : spec_env (extend a g) ->
              #inlc : fs_oval (extend a g) c preInlc ->
              typing _ inlc ->
              #preInrc : spec_env (extend b g) ->
              #inrc : fs_oval (extend b g) c preInrc ->
              typing _ inrc ->
              typing g (fs_oval_case cond inlc inrc)
| QLambdaIO : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #preBody : spec_env (extend a g) ->
                #body : fs_ocomp (extend a g) b preBody ->
                typing_io (extend a g) body ->
                typing g (fs_oval_lambda_ocomp body)
and typing_io : #a:qType -> g:typ_env -> #preG:spec_env g -> fs_ocomp g a preG -> Type =
| QCall :
        #g:typ_env ->
        o:io_ops ->
        #preArgs:spec_env g ->
        #args:fs_oval g (q_io_args o) preArgs ->
        typing g args ->
        typing_io #(q_io_res o) g (fs_ocomp_call_oval o args)

| QReturn :
        #g:typ_env ->
        #a:qType ->
        #preX:spec_env g ->
        #x:fs_oval g a preX ->
        typing g x ->
        typing_io #a g (fs_ocomp_return_oval x)

| QBind :
        #g:typ_env ->
        #a:qType ->
        #b:qType ->
        #preM:spec_env g ->
        #m:fs_ocomp g a preM ->
        #preK:(spec_env (extend a g)) ->
        #k:fs_ocomp (extend a g) b preK ->
        typing_io g m ->
        typing_io (extend a g) k ->
        typing_io #b g (fs_ocomp_bind m k)

| QAppIO    : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #preF : spec_env g ->
                #f : fs_oval g (a ^->!@ b) preF ->
                #preX : spec_env g ->
                #x : fs_oval g a preX ->
                typing g f ->
                typing g x ->
                typing_io g (fs_ocomp_app_oval_oval f x)
| QIfIO     : #g : typ_env ->
              #a : qType ->
              #preC : spec_env g ->
              #c : fs_oval g qBool preC ->
              typing g c ->
              #preT : spec_env g ->
              #t : fs_ocomp g a preT ->
              typing_io g t ->
              #preE : spec_env g ->
              #e : fs_ocomp g a preE ->
              typing_io g e ->
              typing_io g (fs_ocomp_if_oval c t e)
| QCaseIO : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #c : qType ->
              #preCond : spec_env g ->
              #cond : fs_oval g (a ^+ b) preCond ->
              typing g cond ->
              #preInlc : spec_env (extend a g) ->
              #inlc : fs_ocomp (extend a g) c preInlc->
              typing_io _ inlc ->
              #preInrc : spec_env (extend b g) ->
              #inrc : fs_ocomp (extend b g) c preInrc ->
              typing_io _ inrc ->
              typing_io g (fs_ocomp_case_oval cond inlc inrc)

let (⊢) (#a:qType) (g:typ_env) (#pre:spec_env g) (x:fs_oval g a pre) =
  typing g x

let fs_oval_helper_g (g:typ_env) (#a:qType) (x:fs_val a) (pre:spec_env g)
  : fs_oval g a pre
  = fun _ -> x

let fs_oval_helper #a x pre = fs_oval_helper_g empty #a x pre

(* guarded_turnstile *)
let packed_turnstile_g g (a:qType) (x:fs_val a) =
  pre:spec_env g & (g ⊢ (fs_oval_helper_g g x pre))

let pack_turnstile_g #g #a #x (#pre:spec_env g) (turnstile:(g ⊢ (fs_oval_helper_g g x pre))) : 
  packed_turnstile_g g a x
   =
  (| _, turnstile |)

let (⊩) (a:qType) (x: fs_val a) =
  packed_turnstile_g empty a x

let pack_turnstile #a #x (#pre:spec_env empty) (turnstile:(empty ⊢ (fs_oval_helper_g empty x pre))) 
  : a ⊩ x =
  pack_turnstile_g turnstile

let rec lemma_pre_is_always_provable #a #x (packed_turnstile:a ⊩ x) : Lemma ((dfst packed_turnstile) empty_eval) =
  admit ()

let (⊫) (a:qType) (x: fs_val a) =
  pre:spec_env empty &
  proof:squash (pre empty_eval) &
  typing #a empty #pre (fs_oval_helper x pre)

(** Package a thunked derivation together with its precondition and
    a witness discharging it into the [⊫] dependent triple. *)
let mk_turniqet #a #x
  (thk_deriv:a ⊩ x)
  (proof:squash ((dfst thk_deriv) empty_eval))
  : a ⊫ x
  = (| dfst thk_deriv, proof, (dsnd thk_deriv) |)
