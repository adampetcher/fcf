
Set Implicit Arguments.

Require Import FCF.
Require Import RepeatCore.
Require Import CompFold.
Require Import Permutation.
Require Import RndListElem.
Require Import Array.
Require Import PRF.

Require Import TSet.
Require Import ESPADA_TSet_Once_Games.
Require Import ESPADA_TSet_Once.

(* Use the "one-trial TSet" correctness proof along with the arguments in RepeatCore to get security of the full ESPADA TSet scheme.  It would probably be better to prove this generically for any TSet scheme with a setup routine that may fail. *)

Section ESPADA_TSet_secure.

  Variable lambda : posnat.
  Variable A_State : Set.
  Hypothesis A_State_EqDec : EqDec A_State.
  Variable tSize bigB bigS : posnat.

  Variable F : Bvector lambda -> nat -> nat * Bvector lambda * Bvector (S lambda).
  Variable F_bar : Bvector lambda -> Blist -> Bvector lambda.

  Hypothesis F_b_correct : 
    forall k b i v1 v2,
      (b, v1, v2) = F k i ->
      b < bigB.

  Variable A1 : Comp ((T lambda * list Blist) * A_State).
  Variable A2 : A_State  -> TSet lambda * list (Bvector lambda) -> Comp bool.

  Hypothesis A1_t_correct : 
    forall s_A t qs, 
      In ((t, qs), s_A) (getSupport A1) ->
      bigN t = tSize.

  Hypothesis A1_wf : well_formed_comp A1.
  Hypothesis A2_wf : forall s_A p, well_formed_comp (A2 s_A p).

  Definition Repeat_A2 (s_A : A_State)(p : (option (TSet lambda)) * list (Bvector lambda)) :=
    [tSet_opt, ts] <-2 p;
    tSet <- 
         match tSet_opt with
           | None => nil
           | Some t => t
         end;
    A2 s_A (tSet, ts).

  (* numTrials is the number of attempts to obtain a valid TSet in an intermediate argument.  It shows up as part of an adversary against the PRF that must be efficient, so it must be polynomial in the security parameter.  It would be better if we could combine this with the success probability somehow. *)
  Variable numTrials : posnat.
  
  Variable setupFailRate : Rat.
  (* In order for this proof to be meaningful, the failure rate must be significantly less than one.  But in order to complete the proof we require that it be not equal to 1. *)
  Hypothesis setupFailRate_lt_1 : 
    ~ (1 <= setupFailRate).

  Definition setupSuccess(p : option (TSet lambda * FreeList) * Bvector lambda) :=
    if (fst p) then true else false.
  Hypothesis setupFailRate_correct : 
    forall t qs s_A, 
      In (t, qs, s_A) (getSupport A1) ->
    Pr[p <-$ ESPADA_TSetSetup_trial bigB bigS F F_bar t; ret (negb (setupSuccess p))] <= setupFailRate.

  Definition simSetupSuccess(p : option (TSet lambda * FreeList) * list (Bvector lambda)) :=
    if (fst p) then true else false.

  Hypothesis simFailRate_correct : 
    forall t qs s_A, 
      In (t, qs, s_A) (getSupport A1) ->
    Pr[p <-$ ESPADA_TSet_Sim_trial lambda bigB bigS F (@L_T lambda t qs) (map (arrayLookupList _ t) qs); ret (negb (simSetupSuccess p))] <= setupFailRate.

  Theorem ESPADA_TSetSetup_Some_in_support : 
      forall t qs s_A, 
        (In (t, qs, s_A) (getSupport A1)) ->
      exists k p, 
        In (Some p, k) (getSupport (ESPADA_TSetSetup_trial bigB bigS F F_bar t)).

    intuition.

    assert (~(Pr[p <-$ ESPADA_TSetSetup_trial bigB bigS F F_bar t;
                           ret (setupSuccess p) ] == 0)).
    intuition.

    assert (
        Pr 
      [p <-$ ESPADA_TSetSetup_trial bigB bigS F F_bar t; ret negb (setupSuccess p) ] + 
Pr 
      [p <-$ ESPADA_TSetSetup_trial bigB bigS F F_bar t; ret setupSuccess p ]  == 1 -> False).
    rewrite H0.
    rewrite <- ratAdd_0_r.
    intuition.
    assert (1 <= setupFailRate).
    rewrite <- H1.
    eauto.
    intuition.

    eapply H1.

    Lemma pred_both_sum_1 : 
      forall (A : Set)(c : Comp A)(P : A -> bool),
        well_formed_comp c ->
        Pr[a <-$ c; ret (P a)] + Pr[a <-$ c; ret negb (P a)] == 1.

      intuition.
      simpl.
      rewrite (sumList_filter_partition P).
      rewrite ratAdd_comm.
      rewrite (sumList_filter_partition P).

      assert (sumList (filter P (getSupport c))
     (fun b : A =>
      evalDist c b *
      (if EqDec_dec bool_EqDec (negb (P b)) true then 1 else 0)) == 0).
      eapply sumList_0.
      intuition.
      apply filter_In in H0.
      intuition.
      destruct (EqDec_dec bool_EqDec (negb (P a)) true).
      destruct (P a); simpl in *; discriminate.
      eapply ratMult_0_r.
      rewrite H0.
      clear H0.
      rewrite <- ratAdd_0_l.
      
      assert (sumList (filter (fun a : A => negb (P a)) (getSupport c))
      (fun b : A =>
       evalDist c b * (if EqDec_dec bool_EqDec (P b) true then 1 else 0)) == 0).
      eapply sumList_0.
      intuition.
      apply filter_In in H0.
      intuition.
      destruct (EqDec_dec bool_EqDec (P a) true ).
      destruct (P a); simpl in *; discriminate.
      eapply ratMult_0_r.
      rewrite H0.
      clear H0.
      rewrite <- ratAdd_0_r.
      
      eapply eqRat_trans.
      eapply ratAdd_eqRat_compat.
      eapply sumList_body_eq.
      intuition.
      apply filter_In in H0.
      intuition.
      destruct (EqDec_dec bool_EqDec (negb (P a)) true).
      eapply ratMult_1_r.
      congruence.
      
      eapply sumList_body_eq; intuition.
      apply filter_In in H0.
      intuition.
      destruct (EqDec_dec bool_EqDec (P a) true).
      eapply ratMult_1_r.
      congruence.
      rewrite ratAdd_comm.
      rewrite <- sumList_filter_partition.
      eapply evalDist_lossless.
      intuition.
    Qed.

    rewrite ratAdd_comm.
    eapply pred_both_sum_1.

     Theorem ESPADA_TSetSetup_trial_wf : 
      forall t,
      well_formed_comp (ESPADA_TSetSetup_trial bigB bigS F F_bar t).

      intuition.
      unfold ESPADA_TSetSetup_trial.
      unfold ESPADA_TSet.ESPADA_TSetSetup_trial.
      wftac.
      eapply compFold_wf; intuition.
      unfold ESPADA_TSetSetup_wLoop, ESPADA_TSet.ESPADA_TSetSetup_wLoop, foldBody_option.
      destruct a; wftac.
      destruct p.
      eapply compFold_wf; intuition.
      destruct a; wftac.
      unfold ESPADA_TSet.ESPADA_TSetSetup_tLoop.
      destruct p.
      destruct (F (F_bar b b0) a0).
      destruct p.
      comp_simp.
      unfold maybeBindComp.
      wftac.
      eapply rndListElem_wf.
      intuition.
      destruct b4; wftac.

    Qed.

    eapply ESPADA_TSetSetup_trial_wf.
    
    Lemma bind_ret_nz_exists : 
      forall (A : Set)(c : Comp A)(f : A -> bool), 
        (~(Pr[a <-$ c; ret (f a)] == 0)) ->
        exists a, In a (getSupport c) /\ f a = true.

      intuition.
      simpl in H.
      apply sumList_nz in H.
      destruct H.
      intuition.
      econstructor.
      intuition.
      eauto.
      destruct (EqDec_dec bool_EqDec (f x) true); intuition.
      exfalso.
      eapply H1.
      eapply ratMult_0_r.
    Qed.

    apply bind_ret_nz_exists in H0.
    destruct H0.
    intuition.
    destruct x.
    unfold setupSuccess in *.
    destruct o.
    simpl in H2.
    econstructor.
    econstructor.
    eauto.

    simpl in H2.
    discriminate.
  Qed.

  Theorem ESPADA_SimSetup_Some_in_support : 
      forall t qs s_A, 
        (In (t, qs, s_A) (getSupport A1)) ->
      exists r p, 
        In (Some p, r) (getSupport (ESPADA_TSet_Sim_trial lambda bigB bigS F (@L_T lambda t qs) (map (arrayLookupList _ t) qs))).

    intuition.

    assert (~(Pr[p <-$ ESPADA_TSet_Sim_trial lambda bigB bigS F (@L_T lambda t qs) (map (arrayLookupList _ t) qs);
                           ret (simSetupSuccess p) ] == 0)).
    intuition.

    assert (Pr 
      [p <-$  ESPADA_TSet_Sim_trial lambda bigB bigS F (@L_T lambda t qs) (map (arrayLookupList _ t) qs);
       ret negb (simSetupSuccess p) ]  + 
        Pr 
      [p <-$  ESPADA_TSet_Sim_trial lambda bigB bigS F (@L_T lambda t qs) (map (arrayLookupList _ t) qs);
       ret simSetupSuccess p ] == 1 -> False).

    rewrite H0.
    rewrite <- ratAdd_0_r.
    intuition.
    assert (1 <= setupFailRate).
    rewrite <- H1.
    eauto.
    intuition.

    eapply H1.

    rewrite ratAdd_comm.
    eapply pred_both_sum_1.

     Lemma ESPADA_TSet_Sim_trial_wf : 
      forall a0 l0 qs,
      well_formed_comp (ESPADA_TSet_Sim_trial lambda bigB bigS F (@L_T lambda a0 qs) l0).

      intuition.
      unfold ESPADA_TSet_Sim_trial; wftac.
      eapply compMap_wf; wftac.

      eapply compFold_wf; intuition.
      unfold ESPADA_TSetSetup_Sim_wLoop, foldBody_option.
      destruct a; wftac.
      destruct p.
      eapply compFold_wf; intuition.
      destruct a; wftac.
      unfold ESPADA_TSetSetup_tLoop.
      unfold ESPADA_TSet.ESPADA_TSetSetup_tLoop.
      destruct p.
      destruct (F a1 a2).
      destruct p.
      comp_simp.
      unfold maybeBindComp.
      wftac.
      eapply rndListElem_wf.
      intuition.
      destruct b4; wftac.
      eapply compFold_wf; intuition.
      unfold foldBody_option.
      destruct a; wftac.
      unfold randomTSetEntry.
      wftac.
      intuition.
      unfold maybeBindComp.
      wftac.
      eapply rndListElem_wf.
      intuition.
      destruct b6; wftac.

    Qed.

    eapply ESPADA_TSet_Sim_trial_wf.

    apply bind_ret_nz_exists in H0.
    destruct H0.
    intuition.
    destruct x.
    unfold simSetupSuccess in *.
    destruct o.
    simpl in H2.
    econstructor.
    econstructor.
    eauto.

    simpl in H2.
    discriminate.

  Qed.

  Theorem TSet_RepeatCore_Real_eq : 
    Pr [TSetReal (Bvector_EqDec lambda) (ESPADA_TSetSetup bigB bigS F F_bar)
      (ESPADA_TSetGetTag lambda F_bar) A1 A2 ] == 
    Pr[RepeatCore_G
      (fun p : option (TSet lambda) * list (Bvector lambda) =>
       if fst p then true else false) A1 Repeat_A2
      (Repeat_Real bigB bigS F F_bar) ].

    unfold TSetReal, RepeatCore_G, Repeat_A2, Repeat_Real, ESPADA_TSetSetup_once, ESPADA_TSetSetup.
    
    comp_skip; comp_simp.
    unfold TSet.A, fst.
    intuition.

    assert (Pr 
   [b1 <-$
    Repeat
      (z <-$
       (z <-$ ESPADA_TSetSetup_trial bigB bigS F F_bar t;
        [res, k_T]<-2 z; ret (getTSet_opt res, k_T));
       [tSet, k_T]<-2 z;
       tags <-$
       compMap (Bvector_EqDec lambda) (ESPADA_TSetGetTag lambda F_bar k_T)
         l ; ret (tSet, tags))
      (fun p : option (TSet lambda) * list (Bvector lambda) =>
       if fst p then true else false);


    [tSet_opt, ts]<-2 b1;
    A2 a (match tSet_opt with
          | Some t => t
          | None => nil
          end, ts) ]== 
            Pr 
   [b1 <-$
      Repeat
      (z <-$ ESPADA_TSetSetup_trial bigB bigS F F_bar t;
       tags <-$
       compMap (Bvector_EqDec lambda) (ESPADA_TSetGetTag lambda F_bar (snd z))
         l; ret (getTSet_opt (fst z), tags))
      (fun p  =>
       if fst p then true else false);


    [tSet_opt, ts]<-2 b1;
    A2 a (match tSet_opt with
          | Some t => t
          | None => nil
          end, ts) ]).

    comp_skip.
    
    case_eq a0; intuition.
    destruct (in_dec (EqDec_dec _ ) (Some t0, b) (getSupport (z <-$ ESPADA_TSetSetup_trial bigB bigS F F_bar t;
         tags <-$
         compMap (Bvector_EqDec lambda)
           (ESPADA_TSetGetTag lambda F_bar (snd z))
           l;
         ret (getTSet_opt (fst z), tags)))).

    eapply evalDist_Repeat_eq; intuition.
    comp_inline_l.
    comp_skip; comp_simp.
    comp_skip.
    simpl.
    eapply eqRat_refl.
    simpl.
    intuition.

    subst.
    repeat simp_in_support.
    destruct x.
    eapply filter_In; intuition.
    eapply getSupport_In_Seq.
    eapply getSupport_In_Seq.
    eauto.
    simpl.
    intuition.
   
    remember ((getTSet_opt o, b)) as v.
    destruct v.
    pairInv.
    eapply getSupport_In_Seq.
    eapply H2.
    simpl.
    left.
    f_equal.
    intuition.

    repeat simp_in_support.
    eapply eqRat_trans.
    eapply (@sumList_permutation _ _ _ (filter
        (fun
           p : option (ESPADA_TSet_Once_Games.TSet lambda) * list (Bvector lambda) =>
         if fst p then true else false)
        (getSupport
           (z <-$ ESPADA_TSetSetup_trial bigB bigS F F_bar t;
            tags <-$
            compMap (Bvector_EqDec lambda)
              (ESPADA_TSetGetTag lambda F_bar (snd z))
              l;
            ret (getTSet_opt (fst z), tags))))).

    eapply NoDup_Permutation; intuition.
    eapply filter_NoDup.
    eapply getSupport_NoDup.
    eapply filter_NoDup.
    eapply getSupport_NoDup.
    apply filter_In in H0; intuition.
    repeat simp_in_support.
    destruct x1.
    repeat simp_in_support.
    destruct x2.
    repeat simp_in_support.
    destruct x.
    simpl in H4.
    simpl in H5.
    eapply filter_In; intuition.
    eapply getSupport_In_Seq.
    eauto.
    eapply getSupport_In_Seq.
    eauto.
    simpl.
    intuition.

    apply filter_In in H0; intuition.
    repeat simp_in_support.
    destruct x1.
    eapply filter_In; intuition.
    eapply getSupport_In_Seq.
    eapply getSupport_In_Seq.
    eauto.
    comp_simp.
    simpl.
    intuition.
    comp_simp.
  
    eapply getSupport_In_Seq.
    eauto.
    simpl.
    intuition.

    eapply sumList_body_eq; intuition.
    comp_inline_l.
    comp_skip; comp_simp.
    comp_skip.
    simpl.
    intuition.
    simpl.
    intuition.

    repeat rewrite evalDistRepeat_sup_0; intuition;
    eapply getSupport_not_In_evalDist; intuition;
    repeat simp_in_support.
    destruct x.
    repeat simp_in_support.
    destruct x0.
    repeat simp_in_support.
    eapply n.
    eapply  getSupport_In_Seq.
    eauto.
    eapply getSupport_In_Seq.
    eauto.
    simpl.
    rewrite H1.
    intuition.

    repeat rewrite evalDistRepeat_pred_0.
    intuition.
    simpl. intuition.
    simpl. intuition.
    
    rewrite H0.
    clear H0.
 
    assert (
        Pr 
   [b1 <-$
    Repeat
      (z <-$ ESPADA_TSetSetup_trial bigB bigS F F_bar t;
       tags <-$
       compMap (Bvector_EqDec lambda)
         (ESPADA_TSetGetTag lambda F_bar (snd z)) l;
       ret (getTSet_opt (fst z), tags))
      (fun p : option (ESPADA_TSet_Once_Games.TSet lambda) * list (Bvector lambda) =>
       if fst p then true else false);
    [tSet_opt, ts]<-2 b1;
    A2 a (match tSet_opt with
          | Some t => t
          | None => nil
          end, ts) ] == 
        Pr 
   [b1 <-$
      (z <-$ Repeat
      (ESPADA_TSetSetup_trial bigB bigS F F_bar t)
      (fun p => if fst p then true else false);
       tags <-$ compMap (Bvector_EqDec lambda)
         (ESPADA_TSetGetTag lambda F_bar (snd z)) l;
       ret (getTSet_opt (fst z), tags));

    [tSet_opt, ts]<-2 b1;
    A2 a (match tSet_opt with
          | Some t => t
          | None => nil
          end, ts) ]).

    comp_skip.
    symmetry.
    eapply (@repeat_fission' _ _ _ _) ; intuition.

    apply ESPADA_TSetSetup_trial_wf.
    edestruct ESPADA_TSetSetup_Some_in_support .
    eauto.
    destruct H0.
    econstructor.
    eapply filter_In; intuition.
    eapply H0.
    simpl.
    trivial.

    wftac.
    eapply compMap_wf; intuition.
    unfold ESPADA_TSetGetTag.
    wftac.

    repeat simp_in_support.
    unfold getTSet_opt.
    simpl.
    destruct a2; trivial.

    rewrite  H0.
    clear H0.
    inline_first.
    comp_skip.
    eapply eqRat_refl.
  
    comp_simp.
    inline_first.
    comp_skip.
    simpl.
    eapply eqRat_refl.
    comp_simp.
    simpl.
    destruct o; simpl; intuition.
    reflexivity.
    reflexivity.
  Qed.

  Theorem TSet_RepeatCore_Ideal_eq : 
    Pr  [TSetIdeal (L_T (lambda:=lambda)) A1 A2
                   (ESPADA_TSet_Sim lambda bigB bigS F) ] == 
    Pr 
   [RepeatCore_G
      (fun p : option (TSet lambda) * list (Bvector lambda) =>
       if fst p then true else false) A1 Repeat_A2
      (Repeat_Ideal lambda bigB bigS F) ].

    unfold TSetIdeal, RepeatCore_G, Repeat_Ideal,  ESPADA_TSet_Sim, ESPADA_TSet_Sim_once, Repeat_A2, L_T.
    
    comp_skip.
    destruct x.
    destruct p.

    assert ( Pr 
   [b1 <-$
    Repeat
      (z <-$
       ESPADA_TSet_Sim_trial lambda bigB bigS F 
       (bigN t,
         map
           (fun x : Blist =>
            CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec))
              (removeDups (list_EqDec bool_EqDec) l) x 0) l)
         (map (arrayLookupList (list_EqDec bool_EqDec) t) l);
       [trialRes, tags]<-2 z; ret (getTSet_opt trialRes, tags))
      (fun p : option (TSet lambda) * list (Bvector lambda) =>
       if fst p then true else false);
    [tSet_opt, ts]<-2 b1;
    A2 a (match tSet_opt with
          | Some t => t
          | None => nil
          end, ts) ] ==
              Pr 
   [b1 <-$
    (p <-$ Repeat
      (ESPADA_TSet_Sim_trial lambda bigB bigS F 
        (bigN t,
         map
           (fun x : Blist =>
            CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec))
              (removeDups (list_EqDec bool_EqDec) l) x 0) l)
         (map (arrayLookupList (list_EqDec bool_EqDec) t) l))
      (fun p  => if fst p then true else false);
     ret (getTSet_opt (fst p), (snd p)));
    [tSet_opt, ts]<-2 b1;
    A2 a (match tSet_opt with
          | Some t => t
          | None => nil
          end, ts) ]
).

    comp_skip.
    symmetry.

    assert (evalDist
     (p <-$
      Repeat (ESPADA_TSet_Sim_trial lambda bigB bigS F 
        (bigN t,
         map
           (fun x : Blist =>
            CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec))
              (removeDups (list_EqDec bool_EqDec) l) x 0) l)
         (map (arrayLookupList (list_EqDec bool_EqDec) t) l))
        (fun
           p : option (ESPADA_TSet_Once_Games.TSet lambda * FreeList) *
               list (Bvector lambda) => if fst p then true else false);
      ret (getTSet_opt (fst p), snd p)) (a0, b) == 
            evalDist
     (Repeat (z <-$ ESPADA_TSet_Sim_trial lambda bigB bigS F 
       (bigN t,
         map
           (fun x : Blist =>
            CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec))
              (removeDups (list_EqDec bool_EqDec) l) x 0) l)
         (map (arrayLookupList (list_EqDec bool_EqDec) t) l);
             ret (getTSet_opt (fst z), snd z))
        (fun p => if fst p then true else false)) (a0, b)).
    eapply (@repeat_fission' _ _ _ _) ; intuition.

    eapply ESPADA_TSet_Sim_trial_wf.
    edestruct (ESPADA_SimSetup_Some_in_support).
    eauto.
    destruct H0.
    econstructor.
    eapply filter_In; intuition.
    eapply H0.
    trivial.
    wftac.

    repeat simp_in_support.
    simpl.
    unfold getTSet_opt.
    destruct a2; trivial.

    rewrite H0.
    clear H0.
    
    case_eq a0; intuition.
    destruct (in_dec (EqDec_dec _) (Some t0, b) (getSupport (z <-$ ESPADA_TSet_Sim_trial lambda bigB bigS F (bigN t,
           map
             (fun x : Blist =>
              CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec))
                (removeDups (list_EqDec bool_EqDec) l) x 0) l)
         (map (arrayLookupList (list_EqDec bool_EqDec) t) l);
         ret (getTSet_opt (fst z), snd z)))).
    
    eapply evalDist_Repeat_eq.
    comp_skip; comp_simp.
    simpl.
    intuition.
    trivial.

    repeat simp_in_support.
    eapply filter_In; intuition.
    eapply getSupport_In_Seq; eauto.
    simpl.
    left.
    f_equal.
    intuition.

    eapply eqRat_trans.
    eapply (@sumList_permutation _ _ _
            (filter
        (fun p : option (TSet lambda) * list (Bvector lambda) =>
         if fst p then true else false)
        (getSupport
           (z <-$ ESPADA_TSet_Sim_trial lambda bigB bigS F 
             (bigN t,
           map
             (fun x : Blist =>
              CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec))
                (removeDups (list_EqDec bool_EqDec) l) x 0) l)
         (map (arrayLookupList (list_EqDec bool_EqDec) t) l);
            [trialRes, tags]<-2 z; ret (getTSet_opt trialRes, tags))))).
    eapply NoDup_Permutation; intuition.
    eapply filter_NoDup.
    eapply getSupport_NoDup.
    eapply filter_NoDup.
    eapply getSupport_NoDup.
    apply filter_In in H1.
    intuition.
    repeat simp_in_support.
    eapply filter_In; intuition.
    eapply getSupport_In_Seq.
    eapply H2.
    destruct x0.
    destruct x.
    simpl.
    intuition.
    apply filter_In in H1.
    repeat simp_in_support.
    destruct x0.
    simp_in_support.
    eapply filter_In; intuition.
    eapply getSupport_In_Seq.
    eapply H2.
    destruct x.
    simpl.
    intuition.

    eapply sumList_body_eq; intuition.
    comp_skip.
    comp_simp.
    simpl.
    intuition.

    repeat rewrite evalDistRepeat_sup_0; intuition;
    eapply getSupport_not_In_evalDist; intuition;
    repeat simp_in_support.
    destruct x.
    eapply n.
    eapply getSupport_In_Seq; eauto.

    repeat rewrite evalDistRepeat_pred_0; intuition.
    rewrite H0.
    clear H0.
    inline_first.
    comp_skip.

    eapply eqRat_refl.
    
    comp_simp.
    simpl.
    destruct o; simpl; eapply eqRat_refl.
 
  Qed.

  Theorem ESPADA_TSet_eq_RepeatCore : 
    (| Pr[TSetReal _ (@ESPADA_TSetSetup lambda bigB bigS F F_bar) (@ESPADA_TSetGetTag lambda F_bar) A1 A2] -
      Pr[TSetIdeal (@L_T lambda) A1 A2 (@ESPADA_TSet_Sim lambda bigB bigS F)] |) ==
    RepeatCore_Adv (fun (p : option (TSet lambda) * list (Bvector lambda)) => if (fst p) then true else false) (Repeat_Real bigB bigS F F_bar) (Repeat_Ideal lambda bigB bigS F) A1 Repeat_A2.

    intuition.

    unfold RepeatCore_Adv.
    
    rewrite TSet_RepeatCore_Real_eq.
    rewrite TSet_RepeatCore_Ideal_eq.
    intuition.
  Qed.


  Theorem Repeat_Real_fail_eq : 
    forall t q, 
      Pr [b0 <-$ Repeat_Real bigB bigS F F_bar (t, q); ret negb (if fst b0 then true else false) ]
      == 
      Pr[p <-$ ESPADA_TSetSetup_trial bigB bigS F F_bar t; ret (negb (setupSuccess p))].

    intuition.
    unfold Repeat_Real, ESPADA_TSetSetup_once.
    comp_inline_l.
    comp_inline_l.
    comp_skip.
    comp_simp.
    unfold setupSuccess.
    inline_first.
    comp_irr_l.
    eapply compMap_wf; intuition.
    unfold ESPADA_TSetGetTag.
    wftac.

    destruct o;
    simpl; intuition.
  Qed.

  Theorem Repeat_Ideal_fail_eq : 
    forall t q, 
      Pr[b0 <-$ Repeat_Ideal lambda bigB bigS F (t, q); ret negb (if fst b0 then true else false) ]
    == 
    Pr[p <-$ ESPADA_TSet_Sim_trial lambda bigB bigS F (L_T t q) (map (arrayLookupList _ t) q); ret (negb (simSetupSuccess p))].

    intuition.
    unfold Repeat_Ideal.
    unfold ESPADA_TSet_Sim_once, L_T.
    comp_inline_l.
    comp_skip.
    comp_simp.
    
    unfold simSetupSuccess.
    unfold fst.
    simpl.
    destruct o;
    simpl;
    intuition.

  Qed.

  Definition Repeat_PRF_A1 :=
    (ESPADA_TSet_PRF_A1 _ 
        (B1 _ _  A1)).

  Definition ESPADA_TSet_PRF_A2 :=
    ESPADA_TSet_PRF_A2 bigB bigS F.
  
  Definition Repeat_PRF_A2 :=
    (ESPADA_TSet_PRF_A2
       (B2 _ 
           (Repeat_Real bigB bigS F F_bar) (Repeat_Ideal lambda bigB bigS F)
           (DM_RC_B2
              (fun p : option (TSet lambda) * list (Bvector lambda) =>
               if fst p then true else false) Repeat_A2) numTrials) 
        ).

  Definition ESPADA_TSet_IPRF_A1 :=
    ESPADA_TSet_IPRF_A1 bigB bigS F.
  
  Definition Repeat_IPRF_A1 :=
    (ESPADA_TSet_IPRF_A1 _
        (B1 _ _  A1)).


  Definition Repeat_IPRF_A2 :=
    (ESPADA_TSet_IPRF_A2
        (B2 _ 
           (Repeat_Real bigB bigS F F_bar) (Repeat_Ideal lambda bigB bigS F)
           (DM_RC_B2
              (fun p : option (TSet lambda) * list (Bvector lambda) =>
               if fst p then true else false) Repeat_A2) numTrials)).

  Lemma Repeat_Ideal_wf : 
    forall a : T lambda * list Blist,
      well_formed_comp (Repeat_Ideal lambda bigB bigS F a).
    
    intuition.
    unfold Repeat_Ideal.
    unfold ESPADA_TSet_Sim_once.
    eapply well_formed_Bind.
    eapply ESPADA_TSet_Sim_trial_wf.
    intuition.
    wftac.
    
  Qed.

  Lemma Repeat_Real_wf : 
    forall a : T lambda * list Blist,
      well_formed_comp (Repeat_Real bigB bigS F F_bar a).
    
    intuition.
    unfold Repeat_Real.
    unfold ESPADA_TSetSetup_once.
    wftac.
    eapply ESPADA_TSetSetup_trial_wf.
    eapply compMap_wf; intuition.
    unfold ESPADA_TSetGetTag.
    wftac.
  Qed.
  
  Lemma Repeat_Ideal_Repeat_wf : 
    forall t qs s_A,
      In (t, qs, s_A) (getSupport A1) ->
    exists b : option (TSet lambda) * list (Bvector lambda),
      In b
         (filter
            (fun p : option (TSet lambda) * list (Bvector lambda) =>
               if fst p then true else false)
            (getSupport (Repeat_Ideal lambda bigB bigS F (t, qs)))).
    
    intuition.
    edestruct ESPADA_SimSetup_Some_in_support.
    eauto.
    destruct H0.
    
    econstructor.
    unfold Repeat_Ideal.
    unfold ESPADA_TSet_Sim_once, L_T.
    eapply filter_In; intuition.
    eapply getSupport_In_Seq.
    eapply H0.
    comp_simp.
    simpl.
    intuition.
    trivial.
    
  Qed.

  Lemma Repeat_Real_Repeat_wf : 
    forall t qs s_A,
      In (t, qs, s_A) (getSupport A1) ->
    exists b : option (TSet lambda) * list (Bvector lambda),
      In b
         (filter
            (fun p : option (TSet lambda) * list (Bvector lambda) =>
               if fst p then true else false)
            (getSupport (Repeat_Real bigB bigS F F_bar (t, qs)))).
    
    intuition.
    edestruct ESPADA_TSetSetup_Some_in_support.
    eauto.
    destruct H0.
    
    edestruct (@well_formed_val_exists _ (compMap (Bvector_EqDec lambda) (ESPADA_TSetGetTag lambda F_bar x)
                                                  qs)).
    eapply compMap_wf; intuition.
    unfold ESPADA_TSetGetTag.
    wftac.
    
    econstructor.
    unfold Repeat_Real.
    unfold ESPADA_TSetSetup_once.
    eapply filter_In; intuition.
    eapply getSupport_In_Seq.
    eapply getSupport_In_Seq.
    eauto.

    comp_simp.
    simpl.
    intuition.
    comp_simp.
    
    eapply getSupport_In_Seq.
    eapply H1.
    simpl.
    intuition.
    simpl.
    trivial.
  Qed.
  
  Variable maxKeywords : nat.
  Hypothesis maxKeywords_correct : 
    (forall db q s_A,
      In (db, q, s_A) (getSupport A1) ->
      length (combineKeywords (removeDups _ q) (toW db)) <= maxKeywords)%nat.

  Variable PRF_NA_Adv : Rat.
  Hypothesis PRF_NA_Adv_correct_1 :
    (PRF_NA_Advantage (Rnd lambda) ({ 0 , 1 }^lambda) F_bar _ _ Repeat_PRF_A1 Repeat_PRF_A2) <= PRF_NA_Adv.

  Hypothesis PRF_NA_Adv_correct_2: 
    forall i, 
      PRF_NA_Advantage (Rnd lambda) (@RndF_range lambda bigB) F _ _                       (Hybrid.B1 nil _ _ Repeat_IPRF_A1 i) 
                       (Hybrid.B2 
                          (fun lsD => k <-$ {0, 1}^lambda; ret (map (F k) lsD))
            (fun lsD => [lsR, _] <-$2 oracleMap _ _ (RndR_func (@RndF_range lambda bigB) _) nil lsD; ret lsR)
            _ Repeat_IPRF_A2)
      <= PRF_NA_Adv.

  Theorem ESPADA_TSet_secure : 
  | Pr[TSetReal _ (@ESPADA_TSetSetup lambda bigB bigS F F_bar) (@ESPADA_TSetGetTag lambda F_bar) A1 A2] -
    Pr[TSetIdeal (@L_T lambda) A1 A2 (@ESPADA_TSet_Sim lambda bigB bigS F)] | 
  <=  numTrials / 1 * 
      (PRF_NA_Adv  + 
       (maxKeywords / 1) * 
       PRF_NA_Adv) + 
      expRat setupFailRate numTrials + expRat setupFailRate numTrials. 
    
    rewrite ESPADA_TSet_eq_RepeatCore.
    rewrite DistMult_impl_RepeatCore.
    rewrite DistSingle_impl_Mult.
    rewrite ESPADA_TSet_DistSingle_secure.
        
    eapply ratAdd_leRat_compat; [idtac | eapply leRat_refl].
    eapply ratAdd_leRat_compat; [idtac | eapply leRat_refl].
    eapply ratMult_leRat_compat; intuition.
    unfold Repeat_PRF_A1, Repeat_PRF_A2, Repeat_IPRF_A1, Repeat_IPRF_A2.
    eapply leRat_refl.

    apply (fun n => (pos 1, pos 1)).

    intuition.
    
    intuition.
    unfold B1 in *.
    repeat simp_in_support.
    destruct x.
    repeat simp_in_support.
    eauto.

    eauto.
    eauto.

    intuition.    
    apply Repeat_Ideal_wf.
    intuition.
    intuition.

    intuition.
    unfold Repeat_A2.
    destruct a; wftac.

    intuition.
    apply Repeat_Real_wf.   

    intuition.
    eapply Repeat_Real_Repeat_wf.
    eauto.

    intuition.
    apply Repeat_Ideal_wf.

    intuition.
    eapply Repeat_Ideal_Repeat_wf.
    eauto.

    intuition.
    rewrite Repeat_Real_fail_eq.
    eauto.

    intuition.
    rewrite Repeat_Ideal_fail_eq.
    eauto.
   Qed.

   Print Assumptions ESPADA_TSet_secure.

End ESPADA_TSet_secure.