module IO

(** we only have bools in STLC right now **)
open Trace
open STLC

open FStar.Tactics.V1
open FStar.Calc

noeq
type io (a:Type u#a) : Type u#a =
| Call : o:io_ops -> args:io_args o -> (io_res o args -> io a) -> io a
| Return : a -> io a

let io_return (#a:Type) (x:a) : io a =
  Return x

let rec io_bind
  (#a:Type u#a)
  (#b:Type u#b)
  (l : io a)
  (k : a -> io b) :
  io b =
  match l with
  | Return x -> k x
  | Call o args fnc ->
      Call o args (fun i ->
        io_bind #a #b (fnc i) k)

let openfile (fnm:bool) : io (resexn file_descr) =
  Call OOpen fnm Return

let read (fd:file_descr) : io (resexn bool) =
  Call ORead fd Return

let write (x:file_descr * bool) : io (resexn unit) =
  Call OWrite x Return

let close (fd:file_descr) : io (resexn unit) =
  Call OClose fd Return

let op_wp (o:io_ops) (args:io_args o) : hist (io_res o args) =
  to_hist
    (fun h -> io_pre h o args)
    (fun h res lt -> io_post h o args res /\ lt == [op_to_ev o args res])

let rec theta #a (m:io a) : hist a =
  match m with
  | Return x -> hist_return x
  | Call o args k -> hist_bind (op_wp o args) (fun r -> theta (k r))

let theta_monad_morphism_ret x =
  assert (theta (return x) == hist_return x) by (FStar.Tactics.compute ())

let rec theta_monad_morphism_bind m k =
  match m with
  | Return _ -> ()
  | Call o arg m' -> 
    calc (hist_equiv) {
      theta (io_bind (Call o arg m') k);
      `hist_equiv` { _ by (compute ()) }
      theta (Call o arg (fun x -> io_bind (m' x) k));
      `hist_equiv` { _ by (norm [delta_once [`%theta]; iota]) }
      hist_bind (op_wp o arg) (fun r -> theta (io_bind (m' r) k));
      `hist_equiv` { 
        introduce forall r. theta (io_bind (m' r) k) `hist_equiv` hist_bind (theta (m' r)) (fun x -> theta (k x)) with begin
          theta_monad_morphism_bind (m' r) k
        end;
        lem_hist_bind_equiv (op_wp o arg) (op_wp o arg) (fun r -> theta (io_bind (m' r) k)) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k x)))
       }
      hist_bind (op_wp o arg) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k x)));
      `hist_equiv` { lemma_hist_bind_associativity (op_wp o arg) (fun r -> theta (m' r)) (fun x -> theta (k x)) }
      hist_bind (hist_bind (op_wp o arg) (fun r -> theta (m' r))) (fun x -> theta (k x));
      `hist_equiv` {
        assert (hist_equiv
          (hist_bind (theta (Call o arg m')) (fun x -> theta (k x))) 
          (hist_bind (hist_bind (op_wp o arg) (fun r -> theta (m' r))) (fun x -> theta (k x)))
        ) by (norm [delta_once [`%theta]; zeta; iota]; 
          apply_lemma (`lem_hist_equiv_reflexive)) }
      hist_bind (theta (Call o arg m')) (fun x -> theta (k x));
    }

let io_bind_equivalence (#a #b:Type) (k k':a -> io b) (m:io a) :
  Lemma (requires forall x. k x == k' x)
        (ensures theta (io_bind m k) `hist_equiv` theta (io_bind m k')) =
  match m with
  | Return _ -> ()
  | Call o arg m' ->
    calc (hist_equiv) {
      theta (io_bind (Call o arg m') k);
      `hist_equiv` { theta_monad_morphism_bind (Call o arg m') k }
      hist_bind (theta (Call o arg m')) (fun x -> theta (k x));
      `hist_equiv` { _ by (norm [delta_once [`%theta]; zeta;iota]) }
      hist_bind (hist_bind (op_wp o arg) (fun r -> theta (m' r))) (fun x -> theta (k x));
      `hist_equiv` { lemma_hist_bind_associativity (op_wp o arg) (fun r -> theta (m' r)) (fun x -> theta (k x)) }
      hist_bind (op_wp o arg) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k x)));
      `hist_equiv` {
        lem_hist_bind_equiv (op_wp o arg) (op_wp o arg) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k x))) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k' x)))
      }
      hist_bind (op_wp o arg) (fun r -> hist_bind (theta (m' r)) (fun x -> theta (k' x)));
      `hist_equiv` { lemma_hist_bind_associativity (op_wp o arg) (fun r -> theta (m' r)) (fun x -> theta (k' x)) }
      hist_bind (hist_bind (op_wp o arg) (fun r -> theta (m' r))) (fun x -> theta (k' x));
      `hist_equiv` {
        assert (hist_equiv
          (hist_bind (theta (Call o arg m')) (fun x -> theta (k' x))) 
          (hist_bind (hist_bind (op_wp o arg) (fun r -> theta (m' r))) (fun x -> theta (k' x)))
        ) by (norm [delta_once [`%theta]; zeta; iota]; 
          apply_lemma (`lem_hist_equiv_reflexive)) 
       }
      hist_bind (theta (Call o arg m')) (fun x -> theta (k' x));
      `hist_equiv` { theta_monad_morphism_bind m k' }
      theta (io_bind (Call o arg m') k');
    }

let wp2p_theta_bind m k =
  theta_monad_morphism_bind m k

let lem_theta_open arg res h =
  introduce forall (p:hist_post h (io_res OOpen arg)). (theta (openfile arg)) h p ==> p [EvOpen arg res] res with begin
    introduce _ ==> _ with _. begin
    match openfile arg with
    | Return x -> false_elim ()
    | Call OOpen arg k -> begin
      assert ((hist_bind (op_wp OOpen arg) (fun (r:io_res OOpen arg) -> theta (k r))) h p ==> (hist_bind (to_hist (fun h_ -> io_pre h_ OOpen arg) (fun h_ res_ lt_ -> io_post h_ OOpen arg res_ /\ lt_ == [op_to_ev OOpen arg res_])) (fun (r:io_res OOpen arg) -> theta (k r))) h p) by (compute ());
      eliminate forall (lt':local_trace h) (r':io_res OOpen arg). lt' == [EvOpen arg r'] ==> (theta (k r')) (h++lt') (fun (lt'':local_trace (h++lt')) (r'':io_res OOpen arg) -> p (lt' @ lt'') r'') with [EvOpen arg res] res
      end
    end
  end

let lem_theta_read arg res h =
  assert (thetaP (read arg) h [EvRead arg res] res) by (compute ())

let lem_theta_write arg res h =
  assert (thetaP (write arg) h [EvWrite arg res] res) by (compute ())

let lem_theta_close arg res h =
  assert (thetaP (close arg) h [EvClose arg res] res) by (compute ())
