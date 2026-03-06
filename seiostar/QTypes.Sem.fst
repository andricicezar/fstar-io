module QTypes.Sem

open LambdaIO
open IOStar

include QTypes.TypEnv
include QTypes.EvalEnv

(** Closed values **)
type fs_val (t:qType) =
  get_Type t

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
let fs_val_pair #a #b (x:fs_val a) (y:fs_val b) : fs_val (a ^* b) =
  (x, y)

(** Open values **)
type fs_oval (g:typ_env) (t:qType) =
  eval_env g -> get_Type t

(** We compile F* values, not F* expressions.
    When compiling F* lambdas, there is no way to match and get
    the body of the lambda.

    To avoid this limitation, we do closure conversion of F* lambdas:
    - be a lambda f:'a -> 'b
    - we wrap f to a function that takes as argument an F* evaluation environment
      that was extended to contain a value of type 'a
    - we take the value from the environment to open f:
        fun fsG -> f (index fsG 0)

    What is cool about this is that the evaluation environment can be abstract.
 **)

unfold
let fs_oval_return (g:typ_env) (t:qType) (x:fs_val t) : fs_oval g t =
  fun _ -> x

unfold
let fs_oval_var0 (g:typ_env) (t:qType) : fs_oval (extend t g) t =
  fun fsG -> hd fsG

unfold
let fs_oval_varS (#g:typ_env) (#a:qType) (b:qType) (x:fs_oval g a) : fs_oval (extend b g) a =
  fun fsG -> x (tail fsG)

unfold
let fs_oval_var (g:typ_env) (x:var{Some? (g x)}) : fs_oval g (Some?.v (g x)) =
  fun fsG -> index fsG x

unfold
val fs_oval_app: #g : typ_env ->
                 #a : qType ->
                 #b : qType ->
                 f :fs_oval g (a ^-> b) ->
                 x :fs_oval g a ->
                 fs_oval g b
let fs_oval_app f x fsG = (f fsG) (x fsG)

unfold
val fs_oval_lambda : #g :typ_env ->
                     #a :qType ->
                     #b :qType ->
                     body :fs_oval (extend a g) b ->
                     fs_oval g (a ^-> b)
let fs_oval_lambda #_ #_ body fsG x = body (stack fsG x)

unfold
val fs_oval_eq_string :
  #g : typ_env ->
  s1 : fs_oval g qString ->
  s2 : fs_oval g qString ->
  fs_oval g qBool
let fs_oval_eq_string s1 s2 fsG =
  (s1 fsG) = (s2 fsG)

unfold
val fs_oval_if : #g :typ_env ->
                 #a  : qType ->
                 c   : fs_oval g qBool ->
                 t   : fs_oval g a ->
                 e   : fs_oval g a ->
                 fs_oval g a
let fs_oval_if c t e fsG =
  if c fsG then t fsG else e fsG

unfold
val fs_oval_pair : #g : typ_env ->
                   #a : qType ->
                   #b : qType ->
                   x : fs_oval g a ->
                   y : fs_oval g b ->
                   fs_oval g (a ^* b)
let fs_oval_pair x y fsG =
  fs_val_pair (x fsG) (y fsG)

unfold
val fs_oval_fmap : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    p : fs_oval g a ->
                    f : (fs_val a -> fs_val b) ->
                    fs_oval g b
let fs_oval_fmap p f fsG = f (p fsG)

unfold
val fs_oval_case : #g :typ_env ->
                  #a  : qType ->
                  #b  : qType ->
                  #c  : qType ->
                  cond: fs_oval g (a ^+ b) ->
                  inlc: fs_oval (extend a g) c ->
                  inrc: fs_oval (extend b g) c ->
                  fs_oval g c
let fs_oval_case cond inlc inrc fsG =
  match cond fsG with
  | Inl x -> inlc (stack fsG x)
  | Inr x -> inrc (stack fsG x)

(** Producers **)
type fs_prod (t:qType) =
   io (get_Type t)

unfold
val fs_prod_bind : #a:qType ->
                    #b:qType ->
                    m:fs_prod a ->
                    k:(fs_val a -> fs_prod b) ->
                    fs_prod b
let fs_prod_bind m k = io_bind m k

unfold
val fs_prod_if_val :
                #a  : qType ->
                c   : fs_val qBool ->
                t   : fs_prod a ->
                e   : fs_prod a ->
                fs_prod a
let fs_prod_if_val c t e =
  if c then t else e

unfold
val fs_prod_case_val : #a  : qType ->
                #b : qType ->
                #c : qType ->
                cond : fs_val (a ^+ b) ->
                inlc : (fs_val a -> fs_prod c) ->
                inrc : (fs_val b -> fs_prod c) ->
                fs_prod c
let fs_prod_case_val cond inlc inrc =
  match cond with
  | Inl x -> inlc x
  | Inr x -> inrc x

type fs_oprod (g:typ_env) (t:qType) =
  eval_env g -> io (get_Type t)

unfold
val fs_oprod_return :
        #g:typ_env ->
        #a:qType ->
        x:fs_oval g a ->
        fs_oprod g a
let fs_oprod_return x fsG = io_return (x fsG)

unfold
val fs_oprod_bind : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    m:fs_oprod g a ->
                    k:fs_oprod (extend a g) b ->
                    fs_oprod g b
let fs_oprod_bind m k fsG =
  fs_prod_bind (m fsG) (fun x -> k (stack fsG x))

(** a standard version of the bind **)
unfold
val fs_oprod_bind' : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    m:fs_oprod g a ->
                    k:(fs_val a -> fs_oprod g b) ->
                    fs_oprod g b
let fs_oprod_bind' m k =
  fs_oprod_bind m (fun fsG -> k (hd fsG) (tail fsG))

unfold
val fs_oval_lambda_oprod : #g :typ_env ->
                #a :qType ->
                #b :qType ->
                body :fs_oprod (extend a g) b ->
                fs_oval g (a ^->!@ b)
let fs_oval_lambda_oprod #_ #_ body fsG x = body (stack fsG x)

unfold
val fs_oprod_app_oval_oval :
                #g : typ_env ->
                #a : qType ->
                #b : qType ->
                f :fs_oval g (a ^->!@ b) ->
                x :fs_oval g a ->
                fs_oprod g b
let fs_oprod_app_oval_oval f x fsG =
  (f fsG) (x fsG)

unfold
val fs_oprod_if_val : #g :typ_env ->
                #a  : qType ->
                c   : fs_val qBool ->
                t   : fs_oprod g a ->
                e   : fs_oprod g a ->
                fs_oprod g a
let fs_oprod_if_val c t e fsG =
  fs_prod_if_val c (t fsG) (e fsG)

unfold
val fs_oprod_if_oval : #g :typ_env ->
                #a  : qType ->
                c   : fs_oval g qBool ->
                t   : fs_oprod g a ->
                e   : fs_oprod g a ->
                fs_oprod g a
let fs_oprod_if_oval c t e fsG =
  fs_oprod_if_val (c fsG) t e fsG

val fs_oprod_if : #g :typ_env ->
                  #a : qType ->
                  c  : fs_oprod g qBool ->
                  t  : fs_oprod g a ->
                  e  : fs_oprod g a ->
                  fs_oprod g a
let fs_oprod_if c t e =
  fs_oprod_bind' c (fun c' -> fs_oprod_if_val c' t e)

unfold
val fs_oprod_case_val : #g :typ_env ->
                #a  : qType ->
                #b : qType ->
                #c : qType ->
                cond : fs_val (a ^+ b) ->
                inlc : fs_oprod (extend a g) c ->
                inrc : fs_oprod (extend b g) c ->
                fs_oprod g c
let fs_oprod_case_val cond inlc inrc fsG =
  match cond with
  | Inl x -> inlc (stack fsG x)
  | Inr x -> inrc (stack fsG x)

unfold
val fs_oprod_case_oval : #g :typ_env ->
                #a  : qType ->
                #b : qType ->
                #c : qType ->
                cond : fs_oval g (a ^+ b) ->
                inlc : fs_oprod (extend a g) c ->
                inrc : fs_oprod (extend b g) c ->
                fs_oprod g c
let fs_oprod_case_oval cond inlc inrc fsG =
  fs_oprod_case_val (cond fsG) inlc inrc fsG

val fs_oprod_case : #g :typ_env ->
                #a  : qType ->
                #b : qType ->
                #c : qType ->
                cond : fs_oprod g (a ^+ b) ->
                inlc : fs_oprod (extend a g) c ->
                inrc : fs_oprod (extend b g) c ->
                fs_oprod g c
let fs_oprod_case cond inlc inrc =
  fs_oprod_bind' cond (fun cond' ->
    fs_oprod_case_val cond' inlc inrc)

(** Necessary for the backtranslation **)
val fs_oprod_return_prod :
        g:typ_env ->
        a:qType ->
        x:fs_prod a ->
        fs_oprod g a
let fs_oprod_return_prod g a x =
  (fun _ -> x)

val fs_oprod_return_val :
        g:typ_env ->
        a:qType ->
        x:fs_val a ->
        fs_oprod g a
let fs_oprod_return_val g a x =
  fs_oprod_return (fs_oval_return g a x)

let fs_oprod_var (g:typ_env) (x:var{Some? (g x)}) : fs_oprod g (Some?.v (g x)) =
  fs_oprod_return (fs_oval_var g x)

val fs_oprod_lambda : #g :typ_env ->
                #a :qType ->
                #b :qType ->
                body :fs_oprod (extend a g) b ->
                fs_oprod g (a ^->!@ b)
let fs_oprod_lambda body =
  fs_oprod_return (fs_oval_lambda_oprod body)

val fs_oprod_app : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    f:fs_oprod g (a ^->!@ b) ->
                    x:fs_oprod g a ->
                    fs_oprod g b
let fs_oprod_app f x =
  fs_oprod_bind' f (fun f' ->
    fs_oprod_bind' x (fun x' ->
      fs_oprod_return_prod _ _ (f' x')))

val fs_oprod_pair : #g : typ_env ->
                   #a : qType ->
                   #b : qType ->
                   x : fs_oprod g a ->
                   y : fs_oprod g b ->
                   fs_oprod g (a ^* b)
let fs_oprod_pair x y =
  fs_oprod_bind' x (fun x' ->
    fs_oprod_bind' y (fun y' ->
      fs_oprod_return_val _ _ (fs_val_pair x' y')))

val fs_oprod_string_eq : #g : typ_env ->
                         x : fs_oprod g qString ->
                         y : fs_oprod g qString ->
                         fs_oprod g qBool
let fs_oprod_string_eq x y =
  fs_oprod_bind' x (fun x' ->
    fs_oprod_bind' y (fun y' ->
      fs_oprod_return_val _ _ (x' = y')))

val fs_oprod_fmap : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    p : fs_oprod g a ->
                    f : (fs_val a -> fs_val b) ->
                    fs_oprod g b
let fs_oprod_fmap p f =
  fs_oprod_bind' p (fun p' ->
    fs_oprod_return_val _ _ (f p'))

unfold
let q_io_args (o:io_ops) : qType =
  match o with
  | OOpen  -> qString
  | ORead  -> qFileDescr
  | OWrite -> qFileDescr ^* qString
  | OClose -> qFileDescr

unfold
let q_io_res (o:io_ops) : qType =
  match o with
  | OOpen  -> qResexn qFileDescr
  | ORead  -> qResexn qString
  | OWrite -> qResexn qUnit
  | OClose -> qResexn qUnit

unfold
val fs_oprod_call :
        #g:typ_env ->
        o:io_ops ->
        args:fs_oprod g (q_io_args o) ->
        fs_oprod g (q_io_res o)
let fs_oprod_call o args =
  fs_oprod_bind' args (fun args' ->
    fs_oprod_return_prod _ _ (io_call o args'))

unfold
val fs_oprod_call_oval :
        #g:typ_env ->
        o:io_ops ->
        args:fs_oval g (q_io_args o) ->
        fs_oprod g (q_io_res o)
let fs_oprod_call_oval o args fsG = io_call o (args fsG)

val fs_prod_call_val :
        o:io_ops ->
        args:fs_val (q_io_args o) ->
        fs_prod (q_io_res o)
let fs_prod_call_val o args = io_call o args

unfold val fs_beh : #t:qType -> fs_prod t -> h:history -> hist_post h (fs_val t)
let fs_beh m = thetaP m

let lem_fs_beh_call (o:io_ops) (args:io_args o) (res:io_res o args) (h:history) :
  Lemma (requires io_post h o args res)
        (ensures fs_beh #(q_io_res o) (io_call o args) h [op_to_ev o args res] res) =
  lem_thetaP_call o args res h

let lem_fs_beh_return #a (x:fs_val a) (h:history) :
  Lemma (fs_beh (return x) h [] x) =
  lem_thetaP_return x h

let lem_fs_beh_bind #a #b (m:fs_prod a) (h:history) (lt1:local_trace h) (fs_r_m:fs_val a) (k:fs_val a -> fs_prod b) (lt2:local_trace (h++lt1)) (fs_r:fs_val b) :
  Lemma (requires fs_beh m h lt1 fs_r_m /\
                  fs_beh (k fs_r_m) (h++lt1) lt2 fs_r)
        (ensures fs_beh (fs_prod_bind m k) h (lt1@lt2) fs_r) =
  lem_thetaP_bind m h lt1 fs_r_m k lt2 fs_r

unfold val e_beh : closed_exp -> closed_exp -> h:history -> local_trace h -> Type0
let e_beh e e' h lt =
  steps e e' h lt /\ indexed_irred e' (h++lt)
