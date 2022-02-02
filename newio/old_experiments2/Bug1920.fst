module Bug1920

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics
open FStar.FunctionalExtensionality

(***** spec monad **)

let hist_post a = lt:list unit -> r:a -> Type0
let hist_pre = h:list unit -> Type0

private let hist0 a = hist_post a -> hist_pre

unfold
let hist_post_ord (p1 p2:hist_post 'a) = forall lt r. p1 lt r ==> p2 lt r

let hist_wp_monotonic (wp:hist0 'a) =
  forall p1 p2. (p1 `hist_post_ord` p2) ==> (forall h. wp p1 h ==> wp p2 h)

let hist a = wp:(hist0 a){hist_wp_monotonic wp}

unfold
let hist_post_shift (p:hist_post 'a) (lt:list unit) : hist_post 'a =
  fun lt' r -> p (lt @ lt') r

unfold
let hist_post_bind
  (h:list unit)
  (kw : 'a -> hist0 'b)
  (p:hist_post 'b) :
  Tot (hist_post 'a) =
  fun lt r ->
    kw r (hist_post_shift p lt) (List.rev lt @ h)
  
unfold
let hist0_bind (a b:Type) (w : hist0 a) (kw : a -> hist0 b) : hist0 b =
  fun (p:hist_post a) (h:list unit) -> w (hist_post_bind #a #b h kw p) 

unfold
let hist_bind (a b:Type) (w : hist a) (kw : a -> hist b) : hist b =
  fun (p:hist_post a) (h:list unit) -> w (hist_post_bind #a #b h kw p) 


(***** comp monad **)

type op = | Read | Write

let args (cmd:op) = match cmd with | _ -> unit
let res (cmd:op) = match cmd with | _ -> unit

noeq
type io (a:Type) : Type =
  | Call : (l:op) -> args l -> cont:(res l -> io a) -> io a
  | Return : a -> io a

let rec return_of (x:'a) (f:io 'a) =
  match f with
  | Return x' -> x == x'
  | Call cmd arg k ->
     exists r'. return_of x (k r')

unfold
let ret_pred (m : io 'a) (x:'a) = x `return_of` m

unfold
let ret (m : io 'a) =
  x : 'a { ret_pred m x }

let rec io_bind (m:io 'a) (f:(ret m) -> io 'b) : io 'b =
  match m with
  | Return x -> f x
  | Call cmd arg k -> 
      Call cmd arg (fun r -> io_bind (k r) f)

let glue_lemma_1 cmd arg (k:res cmd -> io 'a) (r:res cmd) :
  Lemma (forall (x:'a). x `return_of` (k r) ==> x `return_of` (Call cmd arg k)) = ()

let theta_of_f_x 
  (m:io 'a)
  (f:(x:'a{x `return_of` m}) -> io 'b)
  (mx:'a{mx `return_of` m}) :
  Tot (hist #unit (ret (io_bind m f))) = admit ()

let theta (#a:Type) (m : io a) : hist #unit (x:a{x `return_of` m}) = admit ()

let fast_cast #event cmd arg (k:res cmd -> io 'a) (r:res cmd) (f:ret (Call cmd arg k) -> io 'b) (wp:hist #event (ret (io_bind (k r) f))) :
  hist #event (ret ((Call cmd arg (fun r -> glue_lemma_1 cmd arg k r; io_bind (k r) f)))) =
  admit ()
  
let reverse_cast_2
  event cmd arg 
  (k:res cmd -> io 'a)
  (f:ret (Call cmd arg k) -> io 'b)
  (wp:hist #event (ret ((Call cmd arg (fun r -> glue_lemma_1 cmd arg k r; io_bind (k r) f))))) :
  hist #event (ret (io_bind (Call cmd arg k) f)) = 
  admit ()


let lemma_intermediate_1 cmd arg (k:res cmd -> io 'a) (f:(ret (Call cmd arg k)) -> io 'b) : Tot unit =
    let m  : io 'a = Call cmd arg k in
    let ret' : Type = ret (io_bind m f) in
    let ret'' : Type = ret ((Call cmd arg (fun r -> glue_lemma_1 cmd arg k r; io_bind (k r) f))) in
    let hist' : Type = hist #unit ret' in
    let hist'' : Type = hist #unit ret'' in

    let term4_rhs : res cmd -> hist'' = (fun r -> 
      fast_cast cmd arg k r f (hist_bind (ret (k r)) (ret (io_bind (k r) f)) (theta (k r)) (theta_of_f_x (k r) f))) in

    let term4_rhs' : res cmd -> hist' = (fun (r:res cmd) -> 
      let rhs : hist'' = term4_rhs r in
      let rhs' : hist #unit ret'' = rhs in (**fails here **)
      admit ();
      let rhs'' : hist #unit (ret ((Call cmd arg (fun r -> glue_lemma_1 cmd arg k r; io_bind (k r) f)))) = rhs' in
      let wp : hist #unit (ret (io_bind (Call cmd arg k) f)) = reverse_cast_2 unit cmd arg k f rhs' in
      let wp' : hist' = wp in
      wp') in
    ()
