module QTypes.OpenValComp

open LambdaIO
open IOStar

include QTypes.TypEnv
include QTypes.EvalEnv

(** F* works better with these functions because it helps dealing with qTypes,
    even if they are synonyms *)

type fs_val (t:qType) = get_Type t

type spec_env (g:typ_env) =
  eval_env g -> pure_pre

type fs_oval (g:typ_env) (t:qType) (pre:spec_env g) =
  fsG:(eval_env g){pre fsG} -> fs_val t

unfold
let spec_env_return (#g:typ_env) (#a:qType) (x:fs_val a) : spec_env g =
  fun _ -> True

unfold
let spec_env_bind (#g:typ_env) (#a:qType)
  (preM:spec_env g) (preK:spec_env (extend a g)) : spec_env g =
  fun fsG -> preM fsG /\ (forall (x:fs_val a). preK (stack fsG x))

unfold
let spec_env_bind' (#g:typ_env) (#a:qType)
  (preP:spec_env g) (preK:(fs_val a -> spec_env g)) : spec_env g =
  spec_env_bind preP (fun fsG -> preK (hd fsG) (tail fsG))

unfold
let spec_env_axiom (#g:typ_env) (#a:qType) : spec_env (extend a g) =
  fun _ -> True

unfold
let spec_env_weaken (#g:typ_env) (#b:qType) (x:spec_env g) : spec_env (extend b g) =
  fun fsG -> x (tail fsG)

unfold
let spec_env_index (#g:typ_env) (x:var{Some? (g x)}) : spec_env g =
  fun _ -> True

unfold
val spec_env_app : #g :typ_env ->
                preF : spec_env g ->
                preX : spec_env g ->
                spec_env g
let spec_env_app preF preX =
  (fun fsG -> preF fsG /\ preX fsG)

unfold
val spec_env_lambda_tot : #g :typ_env ->
                #a :qType ->
                preBody:spec_env (extend a g) ->
                spec_env g

let spec_env_lambda_tot #g #a preBody fsG : pure_pre =
  forall (x:fs_val a). preBody (stack fsG x)

type fs_comp (t:qType) = io (fs_val t)

type fs_ocomp (g:typ_env) (t:qType) (pre:spec_env g) =
  fsG:(eval_env g){pre fsG} -> fs_comp t

unfold
let spec_env_return_comp (#g:typ_env) (#a:qType) (comp:fs_comp a) : spec_env g =
  fun _ -> True

unfold
let spec_env_return_oval (#g:typ_env) (#a:qType) #preX (x:fs_oval g a preX) : spec_env g =
  preX

unfold
val spec_env_if : #g :typ_env ->
                #preC : spec_env g ->
                c : fs_oval g qBool preC ->
                preT : spec_env g ->
                preE : spec_env g ->
                spec_env g
let spec_env_if #_ #preC c preT preE =
  (fun fsG -> preC fsG /\ (c fsG ==> preT fsG) /\ ((~(c fsG)) ==> preE fsG))

unfold
val spec_env_seq_ghost : #g:typ_env ->
                ref:Type0 ->
                preV:spec_env g ->
                preK:spec_env g ->
                spec_env g
let spec_env_seq_ghost ref preV preK =
  fun fsG -> preV fsG /\ (ref ==> preK fsG)

unfold
val spec_env_ref : #g:typ_env ->
                #preV:spec_env g ->
                #a:qType ->
                v:fs_oval g a preV ->
                ref:(ref_type a -> Type0)  ->
                spec_env g
let spec_env_ref #_ #preV v ref =
  fun fsG -> preV fsG /\ // a `subQtype_of` b
             ref (v fsG)

(** Closed values **)
unfold
let fs_val_if (#a:qType) (c:fs_val qBool) (e:fs_val a) (t:fs_val a) : fs_val a =
  if c then e else t

unfold
val fs_val_case : #a  : qType ->
                  #b  : qType ->
                  #c  : qType ->
                  cond: fs_val (a ^+ b) ->
                  inlc: (fs_val a -> fs_val c) ->
                  inrc: (fs_val b -> fs_val c) ->
                  fs_val c
let fs_val_case cond inlc inrc =
  match cond with
  | Inl x -> inlc x
  | Inr x -> inrc x

unfold
let fs_val_pair (#a #b:qType) (x:fs_val a) (y:fs_val b) : fs_val (a ^* b) =
  (x, y)

(** Closed computations **)
unfold
val fs_comp_bind : #a:qType ->
                    #b:qType ->
                    m:fs_comp a ->
                    k:(fs_val a -> fs_comp b) ->
                    fs_comp b
let fs_comp_bind m k =
  io_bind m k

unfold
val fs_comp_if_val :
                #a  : qType ->
                c   : fs_val qBool ->
                t   : fs_comp a ->
                e   : fs_comp a ->
                fs_comp a
let fs_comp_if_val c t e =
  if c then t else e

unfold
val fs_comp_case_val : #a  : qType ->
                #b : qType ->
                #c : qType ->
                cond : fs_val (a ^+ b) ->
                inlc : (fs_val a -> fs_comp c) ->
                inrc : (fs_val b -> fs_comp c) ->
                fs_comp c
let fs_comp_case_val cond inlc inrc =
  match cond with
  | Inl x -> inlc x
  | Inr x -> inrc x

unfold
let q_io_call (o:io_ops) (arg:fs_val (q_io_args o)) : fs_comp (q_io_res o) =
  lem_q_io_args o;
  lem_q_io_res o;
  io_call o arg

unfold
val fs_comp_call_val :
        o:io_ops ->
        args:fs_val (q_io_args o) ->
        fs_comp (q_io_res o)
let fs_comp_call_val o args : fs_comp (q_io_res o) =
  q_io_call o args

(** Open values **)
unfold
let fs_oval_return (g:typ_env) (#t:qType) (x:fs_val t)
  : fs_oval g t (spec_env_return x)
  = fun _ -> x

unfold
let fs_oval_fmap
  (#g:typ_env)
  (#a:qType)
  (#b:qType)
  (#preP : spec_env g)
  (m : fs_oval g a preP)
  (f : fs_val a -> fs_val b)
  : fs_oval g b preP =
  fun fsG ->
    f (m fsG)

unfold
let fs_oval_axiom (g:typ_env) (t:qType)
  : fs_oval (extend t g) t (spec_env_axiom) =
  fun fsG -> hd fsG

unfold
let fs_oval_weaken (#g:typ_env) (#a:qType) (b:qType) (#preX:spec_env g) (x:fs_oval g a preX)
  : fs_oval (extend b g) a (spec_env_weaken preX)
  = fun fsG ->
    x (tail fsG)

unfold
let fs_oval_var (g:typ_env) (x:var{Some? (g x)})
  : fs_oval g (Some?.v (g x)) (spec_env_index x)
  = fun fsG -> index fsG x

unfold
val fs_oval_app: #g : typ_env ->
                 #a : qType ->
                 #b : qType ->
                 #preF :spec_env g ->
                 f :fs_oval g (a ^-> b) preF ->
                 #preX : spec_env g ->
                 x :fs_oval g a preX ->
                 fs_oval g b (spec_env_app preF preX)
let fs_oval_app #_ #_ #_ #preF f #preX x fsG =
  (f fsG) (x fsG)


unfold
let fs_oval_lambda
  (#g :typ_env)
  (#a :qType)
  (#b :qType)
  (#preBody : spec_env (extend a g))
  (body :fs_oval (extend a g) b preBody)
  : fs_oval g (a ^-> b) (spec_env_lambda_tot preBody)
  = fun fsG ->
      fun x -> body (stack fsG x)

unfold
val fs_oval_ref : #g:typ_env ->
                #a:qType ->
                #preV:spec_env g ->
                v:fs_oval g a preV ->
                ref:(ref_type a -> Type0) ->
                fs_oval g (change_refinement a ref) (spec_env_ref v ref)
let fs_oval_ref v _ =
  fun fsG -> v fsG

unfold
val fs_oval_seq_ghost : #g:typ_env ->
                #preV:spec_env g ->
                ref:Type0 ->
                v:fs_oval g (qUnitR (fun _ -> ref)) preV ->
                #a:qType ->
                #preK:spec_env g ->
                k:fs_oval g a preK ->
                fs_oval g a (spec_env_seq_ghost ref preV preK)
let fs_oval_seq_ghost ref v k =
  fun fsG -> v fsG ; k fsG

unfold
val fs_oval_eq_string :
  #g : typ_env ->
  #preS1 : spec_env g ->
  s1 : fs_oval g qString preS1 ->
  #preS2 : spec_env g ->
  s2 : fs_oval g qString preS2 ->
  fs_oval g qBool (spec_env_app preS1 preS2)
let fs_oval_eq_string #_ #preS1 s1 #preS2 s2 fsG =
  (s1 fsG) = (s2 fsG)

unfold
val fs_oval_if : #g :typ_env ->
                 #a  : qType ->
                 #preC : spec_env g ->
                 c   : fs_oval g qBool preC ->
                 #preT : spec_env g ->
                 t   : fs_oval g a preT ->
                 #preE : spec_env g ->
                 e   : fs_oval g a preE ->
                 fs_oval g a (spec_env_if c preT preE)
let fs_oval_if #_ #_ #preC c #preT t #preE e fsG =
  if c fsG then t fsG else e fsG

unfold
val fs_oval_pair : #g : typ_env ->
                   #a : qType ->
                   #b : qType ->
                   #preX : spec_env g ->
                   x : fs_oval g a preX ->
                   #preY : spec_env g ->
                   y : fs_oval g b preY ->
                   fs_oval g (a ^* b) (spec_env_app preX preY)
let fs_oval_pair #_ #_ #_ #preX x #preY y fsG =
  fs_val_pair (x fsG) (y fsG)

val spec_env_case : #g :typ_env ->
                #a :qType ->
                #b  : qType ->
                #preCond : spec_env g ->
                cond : fs_oval g (a ^+ b) preCond ->
                preInlc : spec_env (extend a g) ->
                preInrc : spec_env (extend b g) ->
                spec_env g
let spec_env_case #_ #_ #_ #preCond cond preInlc preInrc =
  (fun fsG -> preCond fsG /\
    (Inl? (cond fsG) ==> preInlc (stack fsG (Inl?.v (cond fsG)))) /\
    (Inr? (cond fsG) ==> preInrc (stack fsG (Inr?.v (cond fsG)))))

unfold
val fs_oval_case : #g :typ_env ->
                  #a  : qType ->
                  #b  : qType ->
                  #c  : qType ->
                  #preCond : spec_env g ->
                  cond: fs_oval g (a ^+ b) preCond ->
                  #preInlc : spec_env (extend a g) ->
                  inlc: fs_oval (extend a g) c preInlc ->
                  #preInrc : spec_env (extend b g) ->
                  inrc: fs_oval (extend b g) c preInrc ->
                  fs_oval g c (spec_env_case cond preInlc preInrc)
let fs_oval_case #_ #_ #_ #_ #preCond cond #preInlc inlc #preInrc inrc fsG =
  match cond fsG with
  | Inl x ->
    inlc (stack fsG x)
  | Inr x ->
    inrc (stack fsG x)

(** Open computations **)

unfold
val fs_ocomp_return :
        g:typ_env ->
        #a:qType ->
        x:fs_comp a ->
        fs_ocomp g a (spec_env_return_comp x)
let fs_ocomp_return g #a x _ = x

unfold
val fs_ocomp_return_oval :
        #g:typ_env ->
        #a:qType ->
        #preX:spec_env g ->
        x:fs_oval g a preX ->
        fs_ocomp g a preX
let fs_ocomp_return_oval #_ #a #preX x fsG =
  io_return (x fsG)

val fs_ocomp_return_val :
        g:typ_env ->
        a:qType ->
        x:fs_val a ->
        fs_ocomp g a (spec_env_return_comp (io_return x))
let fs_ocomp_return_val g a x =
  fs_ocomp_return_oval (fs_oval_return g x)

unfold
val fs_ocomp_bind : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    #preM : spec_env g ->
                    m:fs_ocomp g a preM ->
                    #preK : (spec_env (extend a g)) ->
                    k:fs_ocomp (extend a g) b preK ->
                    fs_ocomp g b (spec_env_bind preM preK)
let fs_ocomp_bind #g #_ #b #preM m #preK k fsG =
  fs_comp_bind (m fsG) (fun x ->
    k (stack fsG x))

(** a standard version of the bind **)
unfold
val fs_ocomp_bind' : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    #preM : spec_env g ->
                    m:fs_ocomp g a preM ->
                    #preK : (fs_val a -> spec_env g) ->
                    k:(x:fs_val a -> fs_ocomp g b (preK x)) ->
                    fs_ocomp g b (spec_env_bind' preM preK)
let fs_ocomp_bind' m k =
  fs_ocomp_bind m (fun fsG -> k (hd fsG) (tail fsG))

val fs_ocomp_fmap : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    #preP : spec_env g ->
                    p : fs_ocomp g a preP ->
                    f : (fs_val a -> fs_val b) ->
                    fs_ocomp g b (spec_env_bind' #g #a preP (fun x -> spec_env_return_comp #g #b (io_return (f x))))
let fs_ocomp_fmap p f =
  fs_ocomp_bind' p (fun p' ->
    fs_ocomp_return_val _ _ (f p'))


unfold
val fs_ocomp_call :
        #g:typ_env ->
        o:io_ops ->
        #preArgs : spec_env g ->
        args:fs_ocomp g (q_io_args o) preArgs ->
        fs_ocomp g (q_io_res o) (spec_env_bind' #g #(q_io_args o) preArgs (fun a -> spec_env_return_comp #g #(q_io_res o) (fs_comp_call_val o a)))
let fs_ocomp_call o args =
  fs_ocomp_bind' args (fun args' fsG -> q_io_call o args')

unfold
val fs_ocomp_call_oval :
        #g:typ_env ->
        o:io_ops ->
        #preArgs : spec_env g ->
        args:fs_oval g (q_io_args o) preArgs ->
        fs_ocomp g (q_io_res o) preArgs
let fs_ocomp_call_oval o args =
  fun fsG -> q_io_call o (args fsG)

unfold
val fs_oval_lambda_ocomp : #g :typ_env ->
                #a :qType ->
                #b :qType ->
                #preBody : spec_env (extend a g) ->
                body :fs_ocomp (extend a g) b preBody ->
                fs_oval g (a ^->!@ b) (spec_env_lambda_tot preBody)
let fs_oval_lambda_ocomp #_ #_ #_ #_ body fsG x = body (stack fsG x)

unfold
val fs_ocomp_app_oval_oval :
                #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #preF : spec_env g ->
                f :fs_oval g (a ^->!@ b) preF ->
                #preX : spec_env g ->
                x :fs_oval g a preX ->
                fs_ocomp g b (spec_env_app preF preX)
let fs_ocomp_app_oval_oval #_ #_ #_ #preF f #preX x fsG =
  (f fsG) (x fsG)

unfold
val fs_ocomp_if_val : #g :typ_env ->
                #a  : qType ->
                c   : fs_val qBool ->
                #preT : spec_env g ->
                t   : fs_ocomp g a preT ->
                #preE : spec_env g ->
                e   : fs_ocomp g a preE ->
                fs_ocomp g a (fun fsG -> if c then preT fsG else preE fsG)
let fs_ocomp_if_val c t e fsG =
  if c then t fsG else e fsG

unfold
val fs_ocomp_if_oval : #g :typ_env ->
                #a  : qType ->
                #preC : spec_env g ->
                c   : fs_oval g qBool preC ->
                #preT : spec_env g ->
                t   : fs_ocomp g a preT ->
                #preE : spec_env g ->
                e   : fs_ocomp g a preE ->
                fs_ocomp g a (spec_env_if c preT preE)
let fs_ocomp_if_oval #_ #_ #preC c t e fsG =
  if c fsG then t fsG else e fsG

val fs_ocomp_if : #g :typ_env ->
                  #a : qType ->
                  #preC : spec_env g ->
                  c  : fs_ocomp g qBool preC ->
                  #preT : spec_env g ->
                  t  : fs_ocomp g a preT ->
                  #preE : spec_env g ->
                  e  : fs_ocomp g a preE ->
                  fs_ocomp g a (spec_env_bind' #g #qBool preC (fun c' -> if c' then preT else preE))
let fs_ocomp_if c t e =
  fs_ocomp_bind' c (fun c' -> fs_ocomp_if_val c' t e)

unfold
val fs_ocomp_case_val : #g :typ_env ->
                #a  : qType ->
                #b : qType ->
                #c : qType ->
                cond : fs_val (a ^+ b) ->
                #preInlc : spec_env (extend a g) ->
                inlc : fs_ocomp (extend a g) c preInlc ->
                #preInrc : spec_env (extend b g) ->
                inrc : fs_ocomp (extend b g) c preInrc ->
                fs_ocomp g c (fun fsG -> match cond with | Inl x -> preInlc (stack fsG x) | Inr x -> preInrc (stack fsG x))
let fs_ocomp_case_val cond inlc inrc fsG =
  match cond with
  | Inl x -> inlc (stack fsG x)
  | Inr x -> inrc (stack fsG x)

unfold
val fs_ocomp_case_oval : #g :typ_env ->
                #a  : qType ->
                #b : qType ->
                #c : qType ->
                #preCond : spec_env g ->
                cond : fs_oval g (a ^+ b) preCond ->
                #preInlc : spec_env (extend a g) ->
                inlc : fs_ocomp (extend a g) c preInlc ->
                #preInrc : spec_env (extend b g) ->
                inrc : fs_ocomp (extend b g) c preInrc ->
                fs_ocomp g c (spec_env_case cond preInlc preInrc)
let fs_ocomp_case_oval #_ #_ #_ #_ #preCond cond inlc inrc fsG =
  match cond fsG with
  | Inl x -> inlc (stack fsG x)
  | Inr x -> inrc (stack fsG x)

val fs_ocomp_case : #g :typ_env ->
                #a  : qType ->
                #b : qType ->
                #c : qType ->
                #preCond : spec_env g ->
                cond : fs_ocomp g (a ^+ b) preCond ->
                #preInlc : spec_env (extend a g) ->
                inlc : fs_ocomp (extend a g) c preInlc ->
                #preInrc : spec_env (extend b g) ->
                inrc : fs_ocomp (extend b g) c preInrc ->
                fs_ocomp g c (spec_env_bind' #g #(a ^+ b) preCond (fun cond' -> fun fsG -> match cond' with | Inl x -> preInlc (stack fsG x) | Inr x -> preInrc (stack fsG x)))
let fs_ocomp_case cond inlc inrc =
  fs_ocomp_bind' cond (fun cond' ->
    fs_ocomp_case_val cond' inlc inrc)

let fs_ocomp_var (g:typ_env) (x:var{Some? (g x)}) : fs_ocomp g (Some?.v (g x)) (spec_env_bind' #g #(Some?.v (g x)) (spec_env_index x) (fun v -> spec_env_return_comp #g #(Some?.v (g x)) (io_return v))) =
  fs_ocomp_return_oval (fs_oval_var g x)

val fs_ocomp_lambda : #g :typ_env ->
                #a :qType ->
                #b :qType ->
                #preBody : spec_env (extend a g) ->
                body :fs_ocomp (extend a g) b preBody ->
                fs_ocomp g (a ^->!@ b) (spec_env_bind' #g #(a ^->!@ b) (spec_env_lambda_tot preBody) (fun x -> spec_env_return_comp #g #(a ^->!@ b) (io_return x)))
let fs_ocomp_lambda body =
  fs_ocomp_return_oval (fs_oval_lambda_ocomp body)

val fs_ocomp_app : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    #preF : spec_env g ->
                    f:fs_ocomp g (a ^->!@ b) preF ->
                    #preX : spec_env g ->
                    x:fs_ocomp g a preX ->
                    fs_ocomp g b (spec_env_bind' #g #(a ^->!@ b) preF (fun f' -> spec_env_bind' #g #a preX (fun x' -> spec_env_return_comp #g #b (f' x'))))
let fs_ocomp_app f x =
  fs_ocomp_bind' f (fun f' ->
    fs_ocomp_bind' x (fun x' ->
      fs_ocomp_return _ (f' x')))

val fs_ocomp_pair : #g : typ_env ->
                   #a : qType ->
                   #b : qType ->
                   #preX : spec_env g ->
                   x : fs_ocomp g a preX ->
                   #preY : spec_env g ->
                   y : fs_ocomp g b preY ->
                   fs_ocomp g (a ^* b) (spec_env_bind' #g #a preX (fun x' -> spec_env_bind' #g #b preY (fun y' -> spec_env_return_comp #g #(a ^* b) (io_return (fs_val_pair x' y')))))
let fs_ocomp_pair x y =
  fs_ocomp_bind' x (fun x' ->
    fs_ocomp_bind' y (fun y' ->
      fs_ocomp_return_val _ _ (fs_val_pair x' y')))

val fs_ocomp_string_eq : #g : typ_env ->
                         #preX : spec_env g ->
                         x : fs_ocomp g qString preX ->
                         #preY : spec_env g ->
                         y : fs_ocomp g qString preY ->
                         fs_ocomp g qBool (spec_env_bind' #g #qString preX (fun x' -> spec_env_bind' #g #qString preY (fun y' -> spec_env_return_comp #g #qBool (io_return (x' = y')))))
let fs_ocomp_string_eq x y =
  fs_ocomp_bind' x (fun x' ->
    fs_ocomp_bind' y (fun y' ->
      fs_ocomp_return_val _ _ (x' = y')))

let fs_nrec_val (#a:qType) (n:nat) (b:fs_val a) (f:fs_val a -> fs_val a) : fs_val a =
  io_nrec n b f

unfold
let fs_oval_zero (g:typ_env) : fs_oval g qNat _ = fs_oval_return g 0

unfold
let fs_oval_succ (#g:typ_env) (#preN:spec_env g) (n:fs_oval g qNat preN) : fs_oval g qNat preN =
  fun fsG -> n fsG + 1

unfold
let fs_oval_nrec
  (#g:typ_env)
  (#a:qType)
  (#preN:spec_env g)
  (n:fs_oval g qNat preN)
  (#preB:spec_env g)
  (b:fs_oval g a preB)
  (#preF:spec_env g)
  (f:fs_oval g (a ^-> a) preF)
  : fs_oval g a (spec_env_app preN (spec_env_app preB preF)) =
  fun fsG -> fs_nrec_val #a (n fsG) (b fsG) (f fsG)

let rec fs_io_nrec_val (#a:qType) (n:nat) (b:fs_val a) (f:fs_val a -> fs_comp a) : fs_comp a =
  if n = 0 then io_return b
  else io_bind (f b) (fun b' -> fs_io_nrec_val #a (n-1) b' f)

let rec fs_io_nrec_comp (#a:qType) (n:nat) (b:fs_comp a) (f:fs_comp (a ^->!@ a)) : fs_comp a =
  if n = 0 then b
  else fs_io_nrec_comp #a (n-1)
    (fs_comp_bind f (fun f' ->
      fs_comp_bind b (fun b' ->
        f' b')))
    f

let fs_ocomp_nrec
    (#g:typ_env)
    (#a:qType)
    (#preN:spec_env g)
    (fn:fs_ocomp g qNat preN)
    (#preB:spec_env g)
    (fb:fs_ocomp g a preB)
    (#preF:spec_env g)
    (ff:fs_ocomp g (a ^->!@ a) preF)
    : fs_ocomp g a (spec_env_bind' #g #qNat preN (fun _ -> spec_env_app preB preF)) =
  fs_ocomp_bind' fn (fun n' ->
    fun fsG -> fs_io_nrec_comp #a n' (fb fsG) (ff fsG))
