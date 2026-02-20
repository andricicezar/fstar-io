module HistoryIndependence

(*let rec construct_step (#e #e':closed_exp) (#h:history) (#oev:option (event_h h)) (st:step e e' h oev) (h':history) (oev':option (event_h h')) : Pure (step e e' h' oev')
  (requires step e e' h oev /\
            (None? oev ==> None? oev') /\
            ((Some? oev /\ (EvRead? (Some?.v oev) \/ EvWrite? (Some?.v oev))) ==> (oev == oev')) /\
            ((Some? oev /\ ~(EvRead? (Some?.v oev) \/ EvWrite? (Some?.v oev))) ==> (test_event h' (Some?.v oev) ==> (oev == oev'))) /\
            ((Some? oev /\ ~(EvRead? (Some?.v oev) \/ EvWrite? (Some?.v oev))) ==> (~(test_event h' (Some?.v oev)) ==> (None? oev'))))
            // TODO: this is not correct - look at corresponding_event for correct spec
  (ensures fun _ -> step e e' h' oev')
  (decreases st) =
  match st with
  | AppRight e1 hst -> begin
    let hst' = construct_step hst h' oev' in
    AppRight e1 hst'
    end
  | AppLeft e2 hst -> begin
    let hst' = construct_step hst h' oev' in
    AppLeft e2 hst'
    end
  | Beta e11 e2 h -> Beta e11 e2 h'
  | IfCond e2 e3 hst -> begin
    let hst' = construct_step hst h' oev' in
    IfCond e2 e3 hst'
    end
  | IfTrue e2 e3 h -> IfTrue e2 e3 h'
  | IfFalse e2 e3 h -> IfFalse e2 e3 h'
  | PairLeft e2 hst -> begin
    let hst' = construct_step hst h' oev' in
    PairLeft e2 hst'
    end
  | PairRight e1 hst -> begin
    let hst' = construct_step hst h' oev' in
    PairRight e1 hst'
    end
  | FstPair hst -> begin
    let hst' = construct_step hst h' oev' in
    FstPair hst'
    end
  | FstPairReturn #e1 #e2 h -> FstPairReturn #e1 #e2 h'
  | SndPair hst -> begin
    let hst' = construct_step hst h' oev' in
    SndPair hst'
    end
  | SndPairReturn #e1 #e2 h -> SndPairReturn #e1 #e2 h'
  | SCase e2 e3 hst -> begin
    let hst' = construct_step hst h' oev' in
    SCase e2 e3 hst'
    end
  | SInl hst -> begin
    let hst' = construct_step hst h' oev' in
    SInl hst'
    end
  | SInlReturn e1 e2 e3 h -> SInlReturn e1 e2 e3 h'
  | SInr hst -> begin
    let hst' = construct_step hst h' oev' in
    SInr hst'
    end
  | SInrReturn e1 e2 e3 h -> SInrReturn e1 e2 e3 h'
  | SRead b h -> SRead b h'
  | SWrite hst -> begin
    let hst' = construct_step hst h' oev' in
    SWrite hst'
    end
  | SWriteReturn arg r h -> SWriteReturn arg r h'
  | SOpen hst -> begin
    let hst' = construct_step hst h' oev' in
    SOpen hst'
    end
  | SOpenReturnSuccess str h -> SOpenReturnSuccess str h'
  | SOpenReturnFail str h -> SOpenReturnFail str h'
  | SClose hst -> begin
    let hst' = construct_step hst h' oev' in
    SClose hst'
    end
  | SCloseReturn file_descr r h -> SCloseReturn file_descr r h'

let rec construct_option_ev (#e #e':closed_exp) (#h:history) (#oev:option (event_h h)) (st:step e e' h oev) (h':history) : Pure (option (event_h h'))
  (requires step e e' h oev)
  (ensures fun (oev') ->
    (step e e' h' oev') /\
    (None? oev ==> None? oev') /\
    ((Some? oev /\ (EvRead? (Some?.v oev) \/ EvWrite? (Some?.v oev))) ==> (oev == oev')) /\
    ((Some? oev /\ ~(EvRead? (Some?.v oev) \/ EvWrite? (Some?.v oev))) ==> (test_event h' (Some?.v oev) ==> (oev == oev'))) /\
    ((Some? oev /\ ~(EvRead? (Some?.v oev) \/ EvWrite? (Some?.v oev))) ==> (~(test_event h' (Some?.v oev)) ==> (None? oev'))))
  (decreases st) =
  match st with
  | AppRight e1 #e2 #e2' #h #oev2 hst2 -> begin
    let oev2' = construct_option_ev hst2 h' in
    let hst' : step e2 e2' h' oev2' = construct_step hst2 h' oev2' in
    let _ : step e e' h' oev2' = AppRight e1 hst' in
    oev2'
    end
  | AppLeft #e1 e2 #e1' #h #oev1 hst1 -> begin
    let oev1' = construct_option_ev hst1 h' in
    let hst' : step e1 e1' h' oev1' = construct_step hst1 h' oev1' in
    let _ : step e e' h' oev1' = AppLeft e2 hst' in
    oev1'
    end
  | Beta e11 e2 h -> begin
    let _ : step e e' h' None = Beta e11 e2 h' in
    None
    end
  | IfCond #e1 e2 e3 #e1' #h #oev1 hst1 -> begin
    let oev1' = construct_option_ev hst1 h' in
    let hst' : step e1 e1' h' oev1' = construct_step hst1 h' oev1' in
    let _ : step e e' h' oev1' = IfCond e2 e3 hst' in
    oev1'
    end
  | IfTrue e2 e3 h -> begin
    let _ : step e e' h' None = IfTrue e2 e3 h' in
    None
    end
  | IfFalse e2 e3 h -> begin
    let _ : step e e' h' None = IfFalse e2 e3 h' in
    None
    end
  | PairLeft #e1 e2 #e1' #h #oev1 hst1 -> begin
    let oev1' = construct_option_ev hst1 h' in
    let hst' : step e1 e1' h' oev1' = construct_step hst1 h' oev1' in
    let _ : step e e' h' oev1' = PairLeft e2 hst' in
    oev1'
    end
  | PairRight e1 #e2 #e2' #h #oev2 hst2 -> begin
    let oev2' = construct_option_ev hst2 h' in
    let hst' : step e2 e2' h' oev2' = construct_step hst2 h' oev2' in
    let _ : step e e' h' oev2' = PairRight e1 hst' in
    oev2'
    end
  | FstPair #e1 #e1' #h #oev hst -> begin
    let oev' = construct_option_ev hst h' in
    let hst' : step e1 e1' h' oev' = construct_step hst h' oev' in
    let _ : step e e' h' oev' = FstPair hst' in
    oev'
    end
  | FstPairReturn #e1 #e2 h -> begin
    let _ : step e e' h' None = FstPairReturn #e1 #e2 h' in
    None
    end
  | SndPair #e2 #e2' #h #oev hst -> begin
    let oev' = construct_option_ev hst h' in
    let hst' : step e2 e2' h' oev' = construct_step hst h' oev' in
    let _ : step e e' h' oev' = SndPair hst' in
    oev'
    end
  | SndPairReturn #e1 #e2 h -> begin
    let _ : step e e' h' None = SndPairReturn #e1 #e2 h' in
    None
    end
  | SCase #e1 e2 e3 #e1' #h #oev1 hst1 -> begin
    let oev1' = construct_option_ev hst1 h' in
    let hst' : step e1 e1' h' oev1' = construct_step hst1 h' oev1' in
    let _ : step e e' h' oev1' = SCase e2 e3 hst' in
    oev1'
    end
  | SInl #e12 #e12' #h #oev hst -> begin
    let oev' = construct_option_ev hst h' in
    let hst' : step e12 e12' h' oev' = construct_step hst h' oev' in
    let _ : step e e' h' oev' = SInl hst' in
    oev'
    end
  | SInlReturn e1 e2 e3 h -> begin
    let _ : step e e' h' None = SInlReturn e1 e2 e3 h' in
    None
    end
  | SInr #e12 #e12' #h #oev hst -> begin
    let oev' = construct_option_ev hst h' in
    let hst' : step e12 e12' h' oev' = construct_step hst h' oev' in
    let _ : step e e' h' oev' = SInr hst' in
    oev'
    end
  | SInrReturn e1 e2 e3 h -> begin
    let _ : step e e' h' None = SInrReturn e1 e2 e3 h' in
    None
    end
  | SRead b h -> begin
    let _ : step e e' h' (Some (EvRead () b)) = SRead b h' in
    Some (EvRead () b)
    end
  | SWrite #arg #arg' #h #oev hst -> begin
    let oev' = construct_option_ev hst h' in
    let hst' : step arg arg' h' oev' = construct_step hst h' oev' in
    let _ : step e e' h' oev' = SWrite hst' in
    oev'
    end
  | SWriteReturn arg r h -> begin
    let _ : step e e' h' (Some (EvWrite (get_bool arg) r)) = SWriteReturn arg r h' in
    Some (EvWrite (get_bool arg) r)
    end
  | SOpen #str #str' #h #oev hst -> begin
    let oev' = construct_option_ev hst h' in
    let hst' : step str str' h' oev' = construct_step hst h' oev' in
    let _ : step e e' h' oev' = SOpen hst' in
    oev'
    end
  | SOpenReturnSuccess str h -> begin
    let _ : step e e' h' (Some (EvOpen (get_bool str) (Inl (fresh_fd h)))) = SOpenReturnSuccess str h' in
    (Some (EvOpen (get_bool str) (Inl (fresh_fd h))))
    end
  | SOpenReturnFail str h -> begin
    let _ : step e e' h' (Some (EvOpen (get_bool str) (Inr ()))) = SOpenReturnFail str h' in
    (Some (EvOpen (get_bool str) (Inr ())))
    end
  | SClose #fd #fd' #h #oev hst -> begin
    let oev' = construct_option_ev hst h' in
    let hst' : step fd fd' h' oev' = construct_step hst h' oev' in
    let _ : step e e' h' oev' = SClose hst' in
    oev'
    end
  | SCloseReturn file_descr r h -> begin
    let _ : step e e' h' (Some (EvClose file_descr r)) = SCloseReturn file_descr r h' in
    Some (EvClose file_descr r)
    end

let step_history_independence (#e #e':closed_exp) (#h:history) (#oev:option (event_h h)) (st:step e e' h oev) :
  Lemma (ensures forall h'. exists oev'. step e e' h' oev' /\ (None? oev <==> None? oev')) =
  introduce forall h'. exists oev'. step e e' h' oev' /\ (None? oev <==> None? oev') with begin
    assert (step e e' h' (construct_option_ev st h'))
  end

let rec construct_local_trace (#e #e':closed_exp) (#h:history) (#lt:local_trace h) (st:steps e e' h lt) (h':history) : Pure (local_trace h')
  (requires steps e e' h lt)
  (ensures fun lt' ->
    steps e e' h' lt' /\
    (lt == [] <==> lt' == []))
  (decreases st) =
  match st with
  | SRefl _ _ -> []
  | STrans #e #e_i #e' #h #oev #_ e_step steps_to_e' -> begin
    step_history_independence e_step;
    let oev' = construct_option_ev e_step h' in
    assert (oev == oev');
    lem_step_implies_steps e e_i h' oev';
    let lt_ = as_lt oev' in
    let rest_of_trace = construct_local_trace steps_to_e' (h'++lt_) in
    lem_steps_transitive e e_i e' h' lt_ rest_of_trace;
    match oev' with
    | Some ev' -> [ev'] @ rest_of_trace
    | None -> rest_of_trace
    end

let steps_history_independence (#e #e':closed_exp) (#h:history) (#lt:local_trace h) (sts:steps e e' h lt) :
  Lemma (ensures forall h'. exists lt'. steps e e' h' lt' /\ (lt == [] <==> lt' == [])) =
  introduce forall h'. exists lt'. steps e e' h' lt' /\ (lt == [] <==> lt' == []) with begin
    assert (steps e e' h' (construct_local_trace sts h'))
 end

let indexed_can_step_history_independence (e:closed_exp) (h:history) :
  Lemma (requires indexed_can_step e h)
        (ensures forall h'. indexed_can_step e h') =
  introduce forall h'. exists (e':closed_exp) (oev:option (event_h h')). step e e' h' oev with begin
    eliminate exists e' oev. step e e' h oev
    returns exists e' oev. step e e' h' oev with _. begin
      bind_squash #(step e e' h oev) () (fun st ->
        assert (step e e' h' (construct_option_ev st h'))
      )
    end
  end

let lem_step_preserve_safe (e e':closed_exp) (h:history) (oev:option (event_h h)) :
  Lemma (requires safe e /\ step e e' h oev)
        (ensures safe e') =
  introduce forall e'' h' lt'. steps e' e'' h' lt' ==> (is_value e'' \/ indexed_can_step e'' (h'++lt')) with begin
    introduce steps e' e'' h' lt' ==> (is_value e'' \/ indexed_can_step e'' (h'++lt')) with _. begin
      bind_squash #(steps e' e'' h' lt') () (fun sts ->
      steps_history_independence sts;
      assert (forall h_. exists lt_. steps e' e'' h_ lt_);
      let lt_ev = as_lt oev in
      eliminate forall h_. exists lt_. steps e' e'' h_ lt_ with (h++lt_ev);
      assert (exists lt_. steps e' e'' (h++lt_ev) lt_);
      eliminate exists lt_. steps e' e'' (h++lt_ev) lt_
      returns is_value e'' \/ indexed_can_step e'' (h'++lt') with _. begin
        lem_step_implies_steps e e' h oev;
        assert (steps e e' h lt_ev);
        lem_steps_transitive e e' e'' h lt_ev lt_;
        eliminate forall e' h lt. steps e e' h lt ==> (is_value e' \/ indexed_can_step e' (h++lt)) with e'' h (lt_ev @ lt_);
        introduce indexed_can_step e'' (h++(lt_ev @ lt_)) ==> indexed_can_step e'' (h'++lt') with _. begin
          indexed_can_step_history_independence e'' (h++(lt_ev @ lt_))
        end
      end)
    end
  end

let indexed_irred_history_independence (e:closed_exp) (h:history) :
  Lemma (requires indexed_irred e h)
        (ensures forall h'. indexed_irred e h') =
  introduce forall (h':history) (e':closed_exp) (oev':option (event_h h')). step e e' h' oev' ==> False with begin
    introduce step e e' h' oev' ==> False with _. begin
      bind_squash #(step e e' h' oev') () (fun st ->
      step_history_independence st;
      eliminate forall h_. exists oev_. step e e' h_ oev_ with h;
      eliminate exists oev_. step e e' h oev_
      returns False with _. begin
        eliminate forall e_ oev_. step e e_ h oev_ ==> False with e' oev_
      end)
    end
  end

let sem_expr_shape_history_independence (e:closed_exp) (h:history) (t:typ) :
  Lemma (requires indexed_sem_expr_shape t e h)
        (ensures forall h'. indexed_sem_expr_shape t e h') =
  introduce forall (h':history) (e':closed_exp) (lt':local_trace h'). steps e e' h' lt' /\ indexed_irred e' (h'++lt') ==> sem_value_shape t e' with begin
    introduce steps e e' h' lt' /\ indexed_irred e' (h'++lt') ==> sem_value_shape t e' with _. begin
      bind_squash #(steps e e' h' lt') () (fun sts ->
      steps_history_independence sts;
      eliminate forall h_. exists lt_. steps e e' h_ lt_ with h;
      eliminate exists lt_. steps e e' h lt_
      returns sem_value_shape t e' with _. begin
        eliminate forall e_ (lt_:local_trace h). steps e e_ h lt_ /\ indexed_irred e_ (h++lt_) ==> sem_value_shape t e_ with e' lt_;
        assert (steps e e' h lt_ /\ indexed_irred e' (h++lt_) ==> sem_value_shape t e');
        indexed_irred_history_independence e' (h'++lt')
      end)
    end
  end

let lem_step_preserve_sem_expr_shape (e e':closed_exp) (h:history) (oev:option (event_h h)) (t:typ) :
  Lemma
    (requires indexed_sem_expr_shape t e h /\ step e e' h oev)
    (ensures indexed_sem_expr_shape t e' (h++(as_lt oev))) =
  introduce forall e'' lt'. steps e' e'' (h++(as_lt oev)) lt' /\ indexed_irred e'' ((h++(as_lt oev))++lt') ==> sem_value_shape t e'' with begin
    introduce _  ==> sem_value_shape t e'' with _. begin
      bind_squash #(steps e' e'' (h++(as_lt oev)) lt') () (fun sts ->
      steps_history_independence sts;
      let lt_ev = as_lt oev in
      eliminate forall h_. exists lt_. steps e' e'' h_ lt_ with (h++lt_ev);
      eliminate exists lt_. steps e' e'' (h++lt_ev) lt_
      returns sem_value_shape t e'' with _. begin
        lem_step_implies_steps e e' h oev;
        lem_steps_transitive e e' e'' h lt_ev lt_;
        eliminate forall e' lt. steps e e' h lt /\ indexed_irred e' (h++lt) ==> sem_value_shape t e' with e'' (lt_ev @ lt_);
        indexed_irred_history_independence e'' ((h++(as_lt oev))++lt')
      end)
    end
  end

let indexed_irred_history_independence (e:closed_exp) (h:history) :
  Lemma (requires indexed_irred e h)
        (ensures forall h'. indexed_irred e h') =
  introduce forall (h':history) (e':closed_exp) (oev':option (event_h h')). step e e' h' oev' ==> False with begin
    introduce step e e' h' oev' ==> False with _. begin
      bind_squash #(step e e' h' oev') () (fun st ->
      step_history_independence st;
      eliminate forall h_. exists oev_. step e e' h_ oev_ with h;
      eliminate exists oev_. step e e' h oev_
      returns False with _. begin
        eliminate forall e_ oev_. step e e_ h oev_ ==> False with e' oev_
      end)
    end
  end

let sem_expr_shape_history_independence (e:closed_exp) (h:history) (t:typ) :
  Lemma (requires indexed_sem_expr_shape t e h)
        (ensures forall h'. indexed_sem_expr_shape t e h') =
  introduce forall (h':history) (e':closed_exp) (lt':local_trace h'). steps e e' h' lt' /\ indexed_irred e' (h'++lt') ==> sem_value_shape t e' with begin
    introduce steps e e' h' lt' /\ indexed_irred e' (h'++lt') ==> sem_value_shape t e' with _. begin
      bind_squash #(steps e e' h' lt') () (fun sts ->
      steps_history_independence sts;
      eliminate forall h_. exists lt_. steps e e' h_ lt_ with h;
      eliminate exists lt_. steps e e' h lt_
      returns sem_value_shape t e' with _. begin
        eliminate forall e_ (lt_:local_trace h). steps e e_ h lt_ /\ indexed_irred e_ (h++lt_) ==> sem_value_shape t e_ with e' lt_;
        assert (steps e e' h lt_ /\ indexed_irred e' (h++lt_) ==> sem_value_shape t e');
        indexed_irred_history_independence e' (h'++lt')
      end)
    end
  end*)
