module QTypes.OpenValComp

open LambdaIO
open IOStar

include QTypes.TypEnv
include QTypes.EvalEnv

(** F* works better with these functions because it helps dealing with qTypes,
    even if they are synonyms *)

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
let fs_val_pair (#a #b:qType) (x:fs_val a) (y:fs_val b) : fs_val (a ^* b) =
  (x, y)

(** Closed computations **)
type fs_comp (t:qType) =
   io (get_Type t)

unfold
val fs_comp_bind : #a:qType ->
                    #b:qType ->
                    m:fs_comp a ->
                    k:(fs_val a -> fs_comp b) ->
                    fs_comp b
let fs_comp_bind m k = io_bind m k

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
  
val fs_comp_call_val :
        o:io_ops ->
        args:fs_val (q_io_args o) ->
        fs_comp (q_io_res o)
let fs_comp_call_val o args = io_call o args

(** Open values **)
type fs_oval (g:typ_env) (t:qType) =
  eval_env g -> get_Type t

unfold
let fs_oval_return (g:typ_env) (#t:qType) (x:fs_val t) : fs_oval g t =
  fun _ -> x

unfold
val fs_oval_fmap : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    p : fs_oval g a ->
                    f : (fs_val a -> fs_val b) ->
                    fs_oval g b
let fs_oval_fmap p f fsG = f (p fsG)

unfold
let fs_oval_axiom (g:typ_env) (t:qType) : fs_oval (extend t g) t =
  fun fsG -> hd fsG

unfold
let fs_oval_weaken (#g:typ_env) (#a:qType) (b:qType) (x:fs_oval g a) : fs_oval (extend b g) a =
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

(** Open computations **)

type fs_ocomp (g:typ_env) (t:qType) =
  eval_env g -> io (get_Type t)

unfold
val fs_ocomp_return :
        g:typ_env ->
        #a:qType ->
        x:fs_comp a ->
        fs_ocomp g a
let fs_ocomp_return _ x _ = x

unfold
val fs_ocomp_return_oval :
        #g:typ_env ->
        #a:qType ->
        x:fs_oval g a ->
        fs_ocomp g a
let fs_ocomp_return_oval x fsG = io_return (x fsG)

val fs_ocomp_return_val :
        g:typ_env ->
        a:qType ->
        x:fs_val a ->
        fs_ocomp g a
let fs_ocomp_return_val g a x =
  fs_ocomp_return_oval (fs_oval_return g x)

unfold
val fs_ocomp_bind : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    m:fs_ocomp g a ->
                    k:fs_ocomp (extend a g) b ->
                    fs_ocomp g b
let fs_ocomp_bind m k fsG =
  fs_comp_bind (m fsG) (fun x -> k (stack fsG x))

(** a standard version of the bind **)
unfold
val fs_ocomp_bind' : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    m:fs_ocomp g a ->
                    k:(fs_val a -> fs_ocomp g b) ->
                    fs_ocomp g b
let fs_ocomp_bind' m k =
  fs_ocomp_bind m (fun fsG -> k (hd fsG) (tail fsG))

val fs_ocomp_fmap : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    p : fs_ocomp g a ->
                    f : (fs_val a -> fs_val b) ->
                    fs_ocomp g b
let fs_ocomp_fmap p f =
  fs_ocomp_bind' p (fun p' ->
    fs_ocomp_return_val _ _ (f p'))


unfold
val fs_ocomp_call :
        #g:typ_env ->
        o:io_ops ->
        args:fs_ocomp g (q_io_args o) ->
        fs_ocomp g (q_io_res o)
let fs_ocomp_call o args =
  fs_ocomp_bind' args (fun args' ->
    fs_ocomp_return _ (io_call o args'))

unfold
val fs_ocomp_call_oval :
        #g:typ_env ->
        o:io_ops ->
        args:fs_oval g (q_io_args o) ->
        fs_ocomp g (q_io_res o)
let fs_ocomp_call_oval o args fsG = io_call o (args fsG)

unfold
val fs_oval_lambda_ocomp : #g :typ_env ->
                #a :qType ->
                #b :qType ->
                body :fs_ocomp (extend a g) b ->
                fs_oval g (a ^->!@ b)
let fs_oval_lambda_ocomp #_ #_ body fsG x = body (stack fsG x)

unfold
val fs_ocomp_app_oval_oval :
                #g : typ_env ->
                #a : qType ->
                #b : qType ->
                f :fs_oval g (a ^->!@ b) ->
                x :fs_oval g a ->
                fs_ocomp g b
let fs_ocomp_app_oval_oval f x fsG =
  (f fsG) (x fsG)

unfold
val fs_ocomp_if_val : #g :typ_env ->
                #a  : qType ->
                c   : fs_val qBool ->
                t   : fs_ocomp g a ->
                e   : fs_ocomp g a ->
                fs_ocomp g a
let fs_ocomp_if_val c t e fsG =
  fs_comp_if_val c (t fsG) (e fsG)

unfold
val fs_ocomp_if_oval : #g :typ_env ->
                #a  : qType ->
                c   : fs_oval g qBool ->
                t   : fs_ocomp g a ->
                e   : fs_ocomp g a ->
                fs_ocomp g a
let fs_ocomp_if_oval c t e fsG =
  fs_ocomp_if_val (c fsG) t e fsG

val fs_ocomp_if : #g :typ_env ->
                  #a : qType ->
                  c  : fs_ocomp g qBool ->
                  t  : fs_ocomp g a ->
                  e  : fs_ocomp g a ->
                  fs_ocomp g a
let fs_ocomp_if c t e =
  fs_ocomp_bind' c (fun c' -> fs_ocomp_if_val c' t e)

unfold
val fs_ocomp_case_val : #g :typ_env ->
                #a  : qType ->
                #b : qType ->
                #c : qType ->
                cond : fs_val (a ^+ b) ->
                inlc : fs_ocomp (extend a g) c ->
                inrc : fs_ocomp (extend b g) c ->
                fs_ocomp g c
let fs_ocomp_case_val cond inlc inrc fsG =
  match cond with
  | Inl x -> inlc (stack fsG x)
  | Inr x -> inrc (stack fsG x)

unfold
val fs_ocomp_case_oval : #g :typ_env ->
                #a  : qType ->
                #b : qType ->
                #c : qType ->
                cond : fs_oval g (a ^+ b) ->
                inlc : fs_ocomp (extend a g) c ->
                inrc : fs_ocomp (extend b g) c ->
                fs_ocomp g c
let fs_ocomp_case_oval cond inlc inrc fsG =
  fs_ocomp_case_val (cond fsG) inlc inrc fsG

val fs_ocomp_case : #g :typ_env ->
                #a  : qType ->
                #b : qType ->
                #c : qType ->
                cond : fs_ocomp g (a ^+ b) ->
                inlc : fs_ocomp (extend a g) c ->
                inrc : fs_ocomp (extend b g) c ->
                fs_ocomp g c
let fs_ocomp_case cond inlc inrc =
  fs_ocomp_bind' cond (fun cond' ->
    fs_ocomp_case_val cond' inlc inrc)

let fs_ocomp_var (g:typ_env) (x:var{Some? (g x)}) : fs_ocomp g (Some?.v (g x)) =
  fs_ocomp_return_oval (fs_oval_var g x)

val fs_ocomp_lambda : #g :typ_env ->
                #a :qType ->
                #b :qType ->
                body :fs_ocomp (extend a g) b ->
                fs_ocomp g (a ^->!@ b)
let fs_ocomp_lambda body =
  fs_ocomp_return_oval (fs_oval_lambda_ocomp body)

val fs_ocomp_app : #g:typ_env ->
                    #a:qType ->
                    #b:qType ->
                    f:fs_ocomp g (a ^->!@ b) ->
                    x:fs_ocomp g a ->
                    fs_ocomp g b
let fs_ocomp_app f x =
  fs_ocomp_bind' f (fun f' ->
    fs_ocomp_bind' x (fun x' ->
      fs_ocomp_return _ (f' x')))

val fs_ocomp_pair : #g : typ_env ->
                   #a : qType ->
                   #b : qType ->
                   x : fs_ocomp g a ->
                   y : fs_ocomp g b ->
                   fs_ocomp g (a ^* b)
let fs_ocomp_pair x y =
  fs_ocomp_bind' x (fun x' ->
    fs_ocomp_bind' y (fun y' ->
      fs_ocomp_return_val _ _ (fs_val_pair x' y')))

val fs_ocomp_string_eq : #g : typ_env ->
                         x : fs_ocomp g qString ->
                         y : fs_ocomp g qString ->
                         fs_ocomp g qBool
let fs_ocomp_string_eq x y =
  fs_ocomp_bind' x (fun x' ->
    fs_ocomp_bind' y (fun y' ->
      fs_ocomp_return_val _ _ (x' = y')))