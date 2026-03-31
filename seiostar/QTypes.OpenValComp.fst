module QTypes.OpenValComp

open LambdaIO
open IOStar

include QTypes.TypEnv
include QTypes.EvalEnv

module M = FStar.Monotonic.Pure
private unfold
let mk_pure_wp #a (wp:pure_wp' a{M.is_monotonic wp}) : pure_wp a =
  M.intro_pure_wp_monotonicity wp; wp

(** F* works better with these functions because it helps dealing with qTypes,
    even if they are synonyms *)

type fs_val (t:qType) = get_Type t
type fs_comp (t:qType) = io (fs_val t)

type spec_env (g:typ_env) (a:qType) =
  eval_env g -> pure_wp (fs_val a)

let spec_env_return (#g:typ_env) (#a:qType) (x:fs_val a) : spec_env g a =
  fun _ -> pure_return _ x

let spec_env_bind (#g:typ_env) (#a:qType) (#b:qType) (wpP:spec_env g a) (wpK:(fs_val a -> spec_env g b)) : spec_env g b =
  fun fsG -> pure_bind_wp _ _ (wpP fsG) (fun x -> wpK x fsG)

let spec_env_axiom (#g:typ_env) (#a:qType) : spec_env (extend a g) a =
  fun fsG -> pure_return _ (hd fsG)

let spec_env_weaken (#g:typ_env) (#a #b:qType) (x:spec_env g a) : spec_env (extend b g) a =
  fun fsG -> x (tail fsG)

let spec_env_index (#g:typ_env) (x:var{Some? (g x)}) : spec_env g (Some?.v (g x)) =
  fun fsG -> pure_return _ (index fsG x)

val spec_env_app : #g :typ_env ->
                #a :qType ->
                #b :qType ->
                wpF : spec_env g (a ^-> b) ->
                wpX : spec_env g a ->
                spec_env g b
let spec_env_app #_ #a #b wpF wpX =
  (fun fsG ->
    pure_bind_wp _ _ (wpF fsG) (fun f' ->
      pure_bind_wp _ _ (wpX fsG) (fun x' ->
        pure_return _ (f' x'))))

type fs_oval (g:typ_env) (t:qType) (wpG:spec_env g t) =
  fsG:eval_env g -> PURE (fs_val t) (wpG fsG)

let fs_ocomp_wp (g:typ_env) (t:qType) (wpG:spec_env g t) fsG : pure_wp (fs_comp t) =
  // mk_pure_wp (fun (p:pure_post (fs_comp t)) -> 
  //   forall comp. theta (comp) ⊑ wp_lift_pure_hist (wpG fsG) ==> p comp)
  // CA: I think the previous would be intuitively what we want,
  //     which could be simplified to the following since the operations
  //     have no pre-conditions for now.
  // Q:  The use of `as_requires` is weird, but we do not have a `p` to apply to `wpG`.
  mk_pure_wp (fun (p:pure_post (fs_comp t)) -> 
    as_requires (wpG fsG) /\ forall comp. p comp)

type fs_ocomp (g:typ_env) (t:qType) (wpG:spec_env g t) =
  fsG:eval_env g -> PURE (fs_comp t) (fs_ocomp_wp g t wpG fsG)

(** Closed values **)
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
unfold
let fs_oval_return (g:typ_env) (#t:qType) (x:fs_val t) 
  : fs_oval g t (spec_env_return x)
  = fun _ -> x

open FStar.Tactics

unfold
let fs_oval_fmap 
  (#g:typ_env)
  (#a:qType)
  (#b:qType)
  (#wpP : spec_env g a)
  (m : fs_oval g a wpP)
  (f : fs_val a -> fs_val b)
  : fs_oval g b (spec_env_bind wpP (fun x -> spec_env_return (f x))) =
  fun fsG ->
    M.elim_pure_wp_monotonicity (wpP fsG);
    f (m fsG)

unfold
let fs_oval_axiom (g:typ_env) (t:qType) 
  : fs_oval (extend t g) t (spec_env_axiom) =
  fun fsG -> hd fsG

unfold
let fs_oval_weaken (#g:typ_env) (#a:qType) (b:qType) (#wpX:spec_env g a) (x:fs_oval g a wpX) 
  : fs_oval (extend b g) a (spec_env_weaken wpX) 
  = fun fsG ->
    M.elim_pure_wp_monotonicity (wpX (tail fsG));
    x (tail fsG)

unfold
let fs_oval_var (g:typ_env) (x:var{Some? (g x)}) 
  : fs_oval g (Some?.v (g x)) (spec_env_index x)
  = fun fsG -> index fsG x

unfold
val fs_oval_app: #g : typ_env ->
                 #a : qType ->
                 #b : qType ->
                 #wpF :spec_env g (a ^-> b) ->
                 f :fs_oval g (a ^-> b) wpF ->
                 #wpX : spec_env g a ->
                 x :fs_oval g a wpX ->
                 fs_oval g b (spec_env_app wpF wpX)
let fs_oval_app #_ #_ #_ #wpF f #wpX x fsG = 
  M.elim_pure_wp_monotonicity (wpF fsG);
  M.elim_pure_wp_monotonicity (wpX fsG);
  (f fsG) (x fsG)


unfold
val spec_env_lambda_tot : #g :typ_env ->
                #a :qType ->
                #b :qType ->
                #wpBody:spec_env (extend a g) b ->
                body:fs_oval (extend a g) b wpBody ->
                spec_env g (a ^-> b)

let spec_env_lambda_tot #g #a #b #wpBody body fsG : pure_wp (fs_val (a ^-> b)) by (
  norm [delta_only [`%fs_val; `%op_Hat_Subtraction_Greater; `%get_Type]]
)= (** Cezar: this looks exactly like what F* generates **)
  mk_pure_wp (fun (p:pure_post (fs_val (a ^-> b))) ->
    (forall (x:a._1). auto_squash (wpBody (stack fsG x) (fun _ -> True))) /\
    (pure_bind_wp _ _ 
      (pure_return (fs_val (a ^-> b)) (fun x -> body (stack fsG x))))
      (pure_return (fs_val (a ^-> b))) p)
    // pure_return (fs_val (a ^-> b)) (fun (x:a._1) -> body (stack fsG x)) p)
    // p (fun (x:fs_val a) -> body (stack fsG x)))

unfold
let fs_oval_lambda 
  (#g :typ_env)
  (#a :qType)
  (#b :qType)
  (#wpBody : spec_env (extend a g) b)
  (body :fs_oval (extend a g) b wpBody)
  : fs_oval g (a ^-> b) (spec_env_lambda_tot body) by (
  norm [delta_only [`%fs_val; `%op_Hat_Subtraction_Greater; `%get_Type]]; (** not sure why I have to do this **)
  simpl ())
  = fun fsG ->
      fun x -> body (stack fsG x)

unfold
val fs_oval_eq_string :
  #g : typ_env ->
  #wpS1 : spec_env g qString ->
  s1 : fs_oval g qString wpS1 ->
  #wpS2 : spec_env g qString ->
  s2 : fs_oval g qString wpS2 ->
  fs_oval g qBool (spec_env_bind wpS1 (fun s1' -> spec_env_bind wpS2 (fun s2' -> spec_env_return (s1' = s2'))))
let fs_oval_eq_string #_ #wpS1 s1 #wpS2 s2 fsG =
  M.elim_pure_wp_monotonicity (wpS1 fsG);
  M.elim_pure_wp_monotonicity (wpS2 fsG);
  (s1 fsG) = (s2 fsG)

val spec_env_if : #g :typ_env ->
                #a :qType ->
                wpC : spec_env g qBool ->
                wpT : spec_env g a ->
                wpE : spec_env g a ->
                spec_env g a
let spec_env_if #_ #a wpC wpT wpE =
  (fun fsG ->
    pure_bind_wp _ _ (wpC fsG) (fun r ->
      pure_if_then_else _ r (wpT fsG) (wpE fsG)))

unfold
val fs_oval_if : #g :typ_env ->
                 #a  : qType ->
                 #wpC : spec_env g qBool ->
                 c   : fs_oval g qBool wpC ->
                 #wpT : spec_env g a ->
                 t   : fs_oval g a wpT ->
                 #wpE : spec_env g a ->
                 e   : fs_oval g a wpE ->
                 fs_oval g a (spec_env_if wpC wpT wpE)
let fs_oval_if #_ #_ #wpC c #wpT t #wpE e fsG =
  M.elim_pure_wp_monotonicity (wpC fsG);
  M.elim_pure_wp_monotonicity (wpT fsG);
  M.elim_pure_wp_monotonicity (wpE fsG);
  if c fsG then t fsG else e fsG

unfold
val fs_oval_pair : #g : typ_env ->
                   #a : qType ->
                   #b : qType ->
                   #wpX : spec_env g a ->
                   x : fs_oval g a wpX ->
                   #wpY : spec_env g b ->
                   y : fs_oval g b wpY ->
                   fs_oval g (a ^* b) (spec_env_bind wpX (fun x -> spec_env_bind wpY (fun y -> spec_env_return (x, y))))
let fs_oval_pair #_ #_ #_ #wpX x #wpY y fsG =
  M.elim_pure_wp_monotonicity (wpX fsG);
  M.elim_pure_wp_monotonicity (wpY fsG);
  fs_val_pair (x fsG) (y fsG)

val spec_env_case : #g :typ_env ->
                #a :qType ->
                #b  : qType ->
                #c  : qType ->
                wpCond : spec_env g (a ^+ b) ->
                wpInlc : spec_env (extend a g) c ->
                wpInrc : spec_env (extend b g) c ->
                spec_env g c
let spec_env_case wpCond wpInlc wpInrc =
  (fun fsG ->
    pure_bind_wp _ _ (wpCond fsG) (fun r ->
      match r with
      | Inl x -> wpInlc (stack fsG x)
      | Inr x -> wpInrc (stack fsG x)))

unfold
val fs_oval_case : #g :typ_env ->
                  #a  : qType ->
                  #b  : qType ->
                  #c  : qType ->
                  #wpCond : spec_env g (a ^+ b) ->
                  cond: fs_oval g (a ^+ b) wpCond ->
                  #wpInlc : spec_env (extend a g) c ->
                  inlc: fs_oval (extend a g) c wpInlc ->
                  #wpInrc : spec_env (extend b g) c ->
                  inrc: fs_oval (extend b g) c wpInrc ->
                  fs_oval g c (spec_env_case wpCond wpInlc wpInrc)
let fs_oval_case #_ #_ #_ #_ #wpCond cond #wpInlc inlc #wpInrc inrc fsG =
  M.elim_pure_wp_monotonicity (wpCond fsG);
  match cond fsG with
  | Inl x -> 
    M.elim_pure_wp_monotonicity (wpInlc (stack fsG x));
    inlc (stack fsG x)
  | Inr x -> 
    M.elim_pure_wp_monotonicity (wpInrc (stack fsG x));
    inrc (stack fsG x)

(** Open computations **)

unfold
val fs_ocomp_return :
        g:typ_env ->
        #a:qType ->
        x:fs_comp a ->
        fs_ocomp g a (spec_env_return x)
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