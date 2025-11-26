module QTyp

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC
open IO

(** We define quotation for Type **)

(** We need quotation for types to define the logical relation. **)
noeq
type type_quotation : Type0 -> Type u#1 =
| QUnit : type_quotation unit
| QBool : type_quotation bool
| QPair : #t1:Type ->
          #t2:Type ->
          type_quotation t1 ->
          type_quotation t2 ->
          type_quotation (t1 & t2)
(** Design decision:
    * Only one type of arrow: a -> io b.
      Advantage: simple representation
      Disatvantage:
      * no currying. one has to work with pairs
      Limitation:
      * how to do quotation of bind? one needs to be able to quote an `io a`

    * Having pure and IO arrows.

    * Having pure arrows and IO computations:
      Advantage: simple representation
      Limitation:
      * now IO computations are values, which means one can have pairs of computations



      The second one, forces us to treat IO computatinos as values in the logical
      expression. Sounds like a rule one would want if one would do Algebraic Effects?
**)
| QArr : #t1:Type ->
         #t2:Type ->
         type_quotation t1 ->
         type_quotation t2 ->
         type_quotation (t1 -> t2)
| QArrIO : #t1:Type ->
         #t2:Type ->
         type_quotation t1 ->
         type_quotation t2 ->
         type_quotation (t1 -> io t2)

let test_match t (tq:type_quotation t) = (** why does this work so well? **)
  match tq with
  | QUnit -> assert (t == unit)
  | QBool -> assert (t == bool)
  | QArr #t1 #t2 _ _ -> assert (t == (t1 -> t2))
  | QArrIO #t1 #t2 _ _ -> assert (t == (t1 -> io t2))
  | QPair #t1 #t2 _ _ -> assert (t == (t1 & t2))

let rec type_quotation_to_typ #s (r:type_quotation s) : typ =
  match r with
  | QUnit -> TUnit
  | QBool -> TBool
  | QPair qt1 qt2 -> TPair (type_quotation_to_typ qt1) (type_quotation_to_typ qt2)
  | QArr qt1 qt2
  | QArrIO qt1 qt2 ->
    TArr (type_quotation_to_typ qt1) (type_quotation_to_typ qt2)

(** Type of Quotable Types **)
type qType =
  t:Type & type_quotation t

let pack (q:type_quotation 's) : qType = (| _, q |)

let get_Type (t:qType) = Mkdtuple2?._1 t
let get_rel (t:qType) = Mkdtuple2?._2 t
let qUnit : qType = (| _, QUnit |)
let qBool : qType = (| _, QBool |)
let (^*) (t1 t2:qType) : qType =
  (| _, QPair (get_rel t1) (get_rel t2) |)
let (^->) (t1 t2:qType) : qType =
  (| _, QArr (get_rel t1) (get_rel t2) |)
let (^->!@) (t1 t2:qType) : qType =
  (| _, QArrIO (get_rel t1) (get_rel t2) |)

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
  Lemma
    (requires fv_in_env (extend t g) body)
    (ensures  fv_in_env g (ELam body)) = admit ()

let lem_fv_in_env_app (g:typ_env) (e1 e2:exp) :
  Lemma
    (requires fv_in_env g e1 /\ fv_in_env g e2)
    (ensures  fv_in_env g (EApp e1 e2)) = admit ()

let lem_app_fv_in_env (g:typ_env) (e1 e2:exp) :
  Lemma
    (requires fv_in_env g (EApp e1 e2))
    (ensures fv_in_env g e1 /\ fv_in_env g e2) = admit ()

let lem_fv_in_env_if (g:typ_env) (e1 e2 e3:exp) :
  Lemma
    (requires fv_in_env g e1 /\ fv_in_env g e2 /\ fv_in_env g e3)
    (ensures  fv_in_env g (EIf e1 e2 e3)) = admit ()

let lem_if_fv_in_env (g:typ_env) (e1 e2 e3:exp) :
  Lemma
    (requires fv_in_env g (EIf e1 e2 e3))
    (ensures fv_in_env g e1 /\ fv_in_env g e2 /\ fv_in_env g e3) = admit ()

let lem_fv_in_env_pair (g:typ_env) (e1 e2:exp) :
  Lemma
    (requires fv_in_env g e1 /\ fv_in_env g e2)
    (ensures  fv_in_env g (EPair e1 e2)) = admit ()

let lem_pair_fv_in_env (g:typ_env) (e1 e2:exp) :
  Lemma
    (requires fv_in_env g (EPair e1 e2))
    (ensures fv_in_env g e1 /\ fv_in_env g e2) = admit ()

let lem_fst_fv_in_env (g:typ_env) (e:exp) : // this only makes sense because of how we defined free_vars_indx
  Lemma
    (requires fv_in_env g (EFst e))
    (ensures fv_in_env g e) = admit ()

let lem_snd_fv_in_env (g:typ_env) (e:exp) :
  Lemma
    (requires fv_in_env g (ESnd e))
    (ensures fv_in_env g e) = admit ()

let lem_lam_fv_in_env (g:typ_env) (body:exp) (t1:qType) :
  Lemma
    (requires fv_in_env g (ELam body))
    (ensures fv_in_env (extend t1 g) body) = admit ()

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

(** eval_env is F* Evaluation Environment : variable -> F* values **)
val eval_env (g:typ_env) : Type u#0
val empty_eval : eval_env empty
val hd : #t:qType -> #g:_ -> eval_env (extend t g) -> get_Type t
val stack : #g:_ -> fsG:eval_env g -> #t:qType -> get_Type t -> eval_env (extend t g)
val tail : #t:qType -> #g:_ -> eval_env (extend t g) -> eval_env g
val index : #g:_ -> eval_env g -> x:STLC.var{Some? (g x)} -> get_Type (Some?.v (g x))

val lem_stack_hd #g (fsG:eval_env g) #t (v:get_Type t)
  : Lemma (
 // (fs_hd fsG == fs_hd (fs_tail (fs_stack fsG v))) /\
   hd (stack fsG v) == v)
  [SMTPat (stack fsG v)]

val lem_stack_index #g (fsG:eval_env g) #t (v:get_Type t) : Lemma (
  (forall (x:var). Some? (g x) ==>  index fsG x == index (stack fsG v) (x+1)) /\
  index (stack fsG v) 0 == v)
  [SMTPat (stack fsG v)]

val lem_index_tail #g #t (fsG:eval_env (extend t g)) : Lemma (
  (forall (x:var). Some? (g x) ==>  index fsG (x+1) == index (tail fsG) x))
  [SMTPat (tail fsG)]

val tail_stack_inveqse #g (fsG:eval_env g) #t (x:get_Type t)
  : Lemma (tail (stack fsG x) == fsG)
  [SMTPat (tail (stack fsG x))]

type fs_oexp (g:typ_env) (t:qType) =
  eval_env g -> get_Type t (** this should have no IO **)

type io_oexp (g:typ_env) (t:qType) =
  eval_env g -> io (get_Type t)
