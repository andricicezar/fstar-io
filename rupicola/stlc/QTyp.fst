module QTyp

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC

(** We define quotation for Type **)

(** We need quotation for types to define the logical relation. **)
noeq
type type_quotation : Type0 -> Type u#1 =
| QUnit : type_quotation unit
| QBool : type_quotation bool
| QArr : #s1:Type ->
         #s2:Type ->
         type_quotation s1 ->
         type_quotation s2 ->
         type_quotation (s1 -> s2)
| QPair : #s1:Type ->
          #s2:Type ->
          type_quotation s1 ->
          type_quotation s2 ->
          type_quotation (s1 & s2)
| QSum  : #s1:Type ->
          #s2:Type ->
          type_quotation s1 ->
          type_quotation s2 ->
          type_quotation (either s1 s2)

let test_match s (r:type_quotation s) = (** why does this work so well? **)
  match r with
  | QUnit -> assert (s == unit)
  | QBool -> assert (s == bool)
  | QArr #s1 #s2 _ _ -> assert (s == (s1 -> s2))
  | QPair #s1 #s2 _ _ -> assert (s == (s1 & s2))
  | QSum #s1 #s2 _ _ -> assert (s == either s1 s2)

let rec type_quotation_to_typ #s (r:type_quotation s) : typ =
  match r with
  | QUnit -> TUnit
  | QBool -> TBool
  | QArr rs1 rs2 -> TArr (type_quotation_to_typ rs1) (type_quotation_to_typ rs2)
  | QPair rs1 rs2 -> TPair (type_quotation_to_typ rs1) (type_quotation_to_typ rs2)
  | QSum rs1 rs2 -> TSum (type_quotation_to_typ rs1) (type_quotation_to_typ rs2)

(** Type of Quotable Types **)
type qType =
  s:Type & type_quotation s

let pack (q:type_quotation 's) : qType = (| _, q |)

let get_Type (t:qType) = Mkdtuple2?._1 t
let get_rel (t:qType) = Mkdtuple2?._2 t
let qUnit : qType = (| _, QUnit |)
let qBool : qType = (| _, QBool |)
let (^->) (t1 t2:qType) : qType =
  (| _, QArr (get_rel t1) (get_rel t2) |)

let (^*) (t1 t2:qType) : qType =
  (| _, QPair (get_rel t1) (get_rel t2) |)
let (^+) (t1 t2:qType) : qType =
  (| _, QSum (get_rel t1) (get_rel t2) |)

(** typ_env is a typing environment: variables to Quotable F* Types **)
type typ_env = var -> option qType
let empty : typ_env = fun _ -> None

(* we only need extend at 0 *)
let extend (t:qType) (g:typ_env)
  : typ_env
  = fun y -> if y = 0 then Some t
          else g (y-1)

let fv_in_env (g:typ_env) (e:exp) : Type0 =
  forall (fv:var). fv `memP` free_vars e ==> Some? (g fv)

let lem_no_fv_is_closed (e:exp) : Lemma
  (requires fv_in_env empty e)
  (ensures is_closed e)
  [SMTPat (is_closed e)] =
  ()

let lem_closed_is_no_fv (e:exp) : Lemma
  (requires is_closed e)
  (ensures fv_in_env empty e)
  [SMTPat (is_closed e)] =
  ()

let lem_fv_in_env_lam (g:typ_env) (t:qType) (body:exp) :
  Lemma (fv_in_env (extend t g) body <==>  fv_in_env g (ELam body))
   = admit ()

let lem_fv_in_env_app (g:typ_env) (e1 e2:exp) :
  Lemma ((fv_in_env g e1 /\ fv_in_env g e2) <==> fv_in_env g (EApp e1 e2))
  = admit ()

let lem_fv_in_env_if (g:typ_env) (e1 e2 e3:exp) :
  Lemma ((fv_in_env g e1 /\ fv_in_env g e2 /\ fv_in_env g e3) <==> fv_in_env g (EIf e1 e2 e3))
  = admit ()

let lem_fv_in_env_pair (g:typ_env) (e1 e2:exp) :
  Lemma ((fv_in_env g e1 /\ fv_in_env g e2) <==> fv_in_env g (EPair e1 e2))
  = admit ()

let lem_fv_in_env_fst (g:typ_env) (e:exp) :
  Lemma (fv_in_env g (EFst e) <==> fv_in_env g e)
  = admit ()

let lem_fv_in_env_snd (g:typ_env) (e:exp) :
  Lemma (fv_in_env g (ESnd e) <==>  fv_in_env g e)
  = admit ()

let lem_fv_in_env_inl (g:typ_env) (e:exp) :
  Lemma (fv_in_env g (EInl e) <==>  fv_in_env g e)
  = admit ()

let lem_fv_in_env_inr (g:typ_env) (e:exp) :
  Lemma (fv_in_env g (EInr e) <==>  fv_in_env g e)
  = admit ()

let lem_fv_in_env_case (g:typ_env) (t1 t2:qType) (e1 e2 e3:exp) :
  Lemma ((fv_in_env g e1 /\ fv_in_env (extend t1 g) e2 /\ fv_in_env (extend t2 g) e3) <==> fv_in_env g (ECase e1 e2 e3))
  = admit ()

let lem_fv_in_env_succ (g:typ_env) (e:exp) :
  Lemma (fv_in_env g (ESucc e) <==> fv_in_env g e)
  [SMTPat (fv_in_env g (ESucc e))]
  = ()

let lem_fv_in_env_nrec (g:typ_env) (e1 e2 e3:exp) :
  Lemma ((fv_in_env g e1 /\ fv_in_env g e2 /\ fv_in_env g e3) <==> fv_in_env g (ENRec e1 e2 e3))
  [SMTPat (fv_in_env g (ENRec e1 e2 e3))]
  = admit ()

(** STLC Evaluation Environment : variable -> value **)
let gsub (g:typ_env) (b:bool{b ==> (forall x. None? (g x))}) = (** CA: this b is polluting **)
  s:(sub b){forall x. Some? (g x) ==> is_value (s x)}

let gsub_empty : gsub empty true =
  (fun v -> EVar v)

let gsub_extend (#g:typ_env) #b (s:gsub g b) (t:qType) (v:value) : gsub (extend t g) false =
  let f = fun (y:var) -> if y = 0 then v else s (y-1) in
  introduce exists (x:var). ~(EVar? (f x)) with 0 and ();
  f

let gsubst (#g:typ_env) #b (s:gsub g b) (e:exp{fv_in_env g e}) : closed_exp =
  introduce forall (x:var). x `memP` free_vars_indx e 0 ==> free_vars_indx (s x) 0 == [] with begin
    introduce x `memP` free_vars_indx e 0 ==> free_vars_indx (s x) 0 == [] with _. begin
      assert (is_closed (s x))
    end
  end;
  lem_subst_freevars_closes_exp s e 0;
  subst s e

let lem_substitution #g #b (s:gsub g b) (t:qType) (v:value) (e:exp)
  : Lemma (
    (subst (sub_beta v) (subst (sub_elam s) e)) == (subst (gsub_extend s t v) e))
  = admit () (** common lemma **)

let lem_gsubst_closed_identiy #g #b (s:gsub g b) (e:closed_exp) :
  Lemma (gsubst s e == e)
  [SMTPat (gsubst s e)] =
  admit ()

module FE = FStar.FunctionalExtensionality

(** eval_env is F* Evaluation Environment : variable -> F* values **)
type eval_env g =
  FE.restricted_t (x:var{Some? (g x)}) (fun x -> get_Type (Some?.v (g x)))
let empty_eval : eval_env empty =
  FE.on_dom
    (x:var{Some? (empty x)})
    #(fun x -> get_Type (Some?.v (empty x)))
    (fun _ -> assert False)
val hd : #t:qType -> #g:_ -> eval_env (extend t g) -> get_Type t
let hd #g fsG = fsG 0
val stack : #g:_ -> fsG:eval_env g -> #t:qType -> get_Type t -> eval_env (extend t g)
let stack #g fsG #t fs_v =
  FE.on_dom
    (x:var{Some? ((extend t g) x)})
    #(fun x -> get_Type (Some?.v ((extend t g) x)))
    (fun y ->
      if y = 0 then fs_v else fsG (y-1))
val tail : #t:qType -> #g:_ -> eval_env (extend t g) -> eval_env g
let tail #t #g fsG =
  FE.on_dom
    (x:var{Some? (g x)})
    #(fun x -> get_Type (Some?.v (g x)))
    (fun y -> fsG (y+1))
val index : #g:_ -> eval_env g -> x:STLC.var{Some? (g x)} -> get_Type (Some?.v (g x))
let index #g fsG x = fsG x

val lem_hd_stack #t #g (fsG:eval_env g) (v:get_Type t)
  : Lemma (
 // (fs_hd fsG == fs_hd (fs_tail (fs_stack fsG v))) /\
   hd (stack fsG v) == v)
  [SMTPat (hd (stack fsG v))]
let lem_hd_stack fsG v = ()

val lem_stack_index #g (fsG:eval_env g) #t (v:get_Type t) : Lemma (
  (forall (x:var). Some? (g x) ==>  index fsG x == index (stack fsG v) (x+1)) /\
  index (stack fsG v) 0 == v)
  [SMTPat (stack fsG v)]
let lem_stack_index fsG v = ()

val lem_index_tail #g #t (fsG:eval_env (extend t g)) : Lemma (
  (forall (x:var). Some? (g x) ==>  index fsG (x+1) == index (tail fsG) x))
  [SMTPat (tail fsG)]
let lem_index_tail fsG = ()

val tail_stack_inverse #g (fsG:eval_env g) #t (x:get_Type t)
  : Lemma (tail (stack fsG x) == fsG)
  [SMTPat (tail (stack fsG x))]
let tail_stack_inverse #g fsG #t v =
  let fsG' : eval_env g = tail (stack fsG v) in
  assert (forall x. fsG' x == fsG x);
  assert (FE.feq fsG' fsG);
  FE.extensionality (x:var{Some? (g x)}) (fun x -> get_Type (Some?.v (g x))) fsG' fsG;
  assert (fsG' == fsG)

val index_0_hd #g #t (fsG:eval_env (extend t g))
  : Lemma (index fsG 0 == hd fsG)
let index_0_hd fsG = ()

type fs_val (t:qType) =
  get_Type t

type fs_oval (g:typ_env) (t:qType) =
  eval_env g -> get_Type t
