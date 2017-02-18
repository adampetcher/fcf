(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import FCF.
Require Import ESPADA_TSet_Correct_Once_Games.
Require Import ESPADA_TSet_Correct_Once.
Require Import TSet.
Require Import ESPADA_TSet_Once_Games.
Require Import CompFold.


Section ESPADA_TSet_Correct.
  
  Variable lambda : posnat.
  Variable bigB bigS maxMatches : posnat.

  Variable F : Bvector lambda -> nat -> nat * Bvector lambda * Bvector (S lambda).
  Variable F_bar : Bvector lambda -> Blist -> Bvector lambda.

  Variable A : Comp (T lambda * list Blist).

  Definition ESPADA_TSetSetup_trial :=  ESPADA_TSetSetup_trial bigB bigS F F_bar.
  Definition ESPADA_TSetRetrieve := ESPADA_TSetRetrieve lambda F maxMatches.

  Variable failProb : Rat.
  Hypothesis failProb_correct :
    forall t l,
      In (t, l) (getSupport A) ->
      Pr[x <-$ ESPADA_TSetSetup_trial t; ret (if (fst x) then false else true)] <= failProb.
  Hypothesis failProb_lt_1 : 
    ~ (1 <= failProb).

  Hypothesis bigB_correct : 
    forall (k : Bvector lambda) (b i : nat) (v1 : Bvector lambda)
     (v2 : Bvector (S lambda)), (b, v1, v2) = F k i -> b < bigB.

  Require Import ESPADA_TSet_Secure.


  Definition TSetCorr_G0_RepeatBody z := 
    ([res, k_T] <-$2 ESPADA_TSetSetup_trial (fst z);  
      tags <-$ (foreach  (x in (snd z))ESPADA_TSetGetTag lambda F_bar k_T x);    
      tSet <- getTSet res;
      t_w <- (foreach  (x in tags)ESPADA_TSetRetrieve tSet x);

      t_w_correct <-
                  (foreach  (x in (snd z))Array.arrayLookupList (list_EqDec bool_EqDec) (fst z) x);
      b <- negb (eqb t_w t_w_correct);
      ret (res, (if res then true else false) && b)).

  Definition TSetCorr_G1 :=
    z <-$ A;
    z0 <-$
     Repeat 
     (TSetCorr_G0_RepeatBody z)
       (fun p => isSome (fst p)); 
    ret ( snd z0).

  Theorem ESPADA_TSet_Correct_G1_equiv : 
    AdvCor _ 
           (ESPADA_TSetSetup bigB bigS F F_bar)
           (ESPADA_TSetGetTag lambda F_bar)
           (ESPADA_TSetRetrieve)
           A ==
    Pr[TSetCorr_G1].

    unfold AdvCor, AdvCor_G, TSetCorr_G1.
    comp_skip.
    comp_simp.
    unfold ESPADA_TSetSetup.
    inline_first.

    Theorem Repeat_factor_indep : 
      forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(c1 : Comp A)(c2 : A -> Comp B) P x,
        well_formed_comp c1 ->
        (exists a, In a (filter P (getSupport c1))) ->
        (forall a, In a (getSupport c1) -> well_formed_comp (c2 a)) ->
        evalDist (Repeat (a <-$ c1; b <-$ (c2 a); ret (a, b)) (fun p => P (fst p))) x ==
        evalDist (a <-$ Repeat c1 P; b <-$ (c2 a); ret (a, b)) x.

      intuition.
      symmetry.
      eapply repeat_fission'; intuition.
      wftac.
      repeat simp_in_support.
      trivial.

    Qed.

    unfold TSetCorr_G0_RepeatBody.

    assert (
        Pr 
   [z0 <-$
    Repeat
      (z0 <-$ ESPADA_TSetSetup_trial (fst (t, l));
       [res, k_T]<-2 z0;
       tags <-$
       compMap (Bvector_EqDec lambda)
         (fun x : Blist => ESPADA_TSetGetTag lambda F_bar k_T x) 
         (snd (t, l));
       tSet <- getTSet res;
       t_w <-
       map (fun x : Bvector lambda => ESPADA_TSetRetrieve tSet x) tags;
       t_w_correct <-
       map
         (fun x : list bool =>
          Array.arrayLookupList (list_EqDec bool_EqDec) (fst (t, l)) x)
         (snd (t, l));
       b <- negb (eqb t_w t_w_correct);
       ret (res, (if res then true else false) && b))
      (fun p : option (TSet lambda * FreeList) * bool => isSome (fst p));
    ret snd z0 ]
   ==
   Pr 
   [z0 <-$
    Repeat
      (z0 <-$ ESPADA_TSetSetup_trial t;
       z1 <-$ (
            tags <-$
                 compMap (Bvector_EqDec lambda)
                 (fun x : Blist => ESPADA_TSetGetTag lambda F_bar (snd z0) x) 
                 l;
            tSet <- getTSet (fst z0);
            t_w <-
                map (fun x : Bvector lambda => ESPADA_TSetRetrieve tSet x) tags;
            t_w_correct <-
                        map
                        (fun x : list bool =>
                           Array.arrayLookupList (list_EqDec bool_EqDec) t x)
                        l;
            b <- negb (eqb t_w t_w_correct);
            ret ((if (fst z0) then true else false) && b)
       );
       ret (z0, z1))
      (fun p => isSome (fst (fst p)));
    ret snd z0 ]
   ).

    eapply comp_spec_eq_impl_eq.
    comp_skip.

    Theorem comp_spec_Repeat : 
      forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(c1 : Comp A)(c2 : Comp B) P P1 P2,
        comp_spec P c1 c2 ->
        (forall a b, P a b -> (P1 a = P2 b)) ->
        comp_spec P (Repeat c1 P1) (Repeat c2 P2).

      intuition.
      destruct H.
      intuition.

      exists (Repeat x (fun p => (P1 (fst p)) && (P2 (snd p)))).
      intuition.

      simpl.
      rewrite H1.
      unfold marginal_l.
      simpl.

      rewrite <- sumList_factor_constant_l.

      rewrite (sumList_filter_partition (fun p : A0 * B => P1 (fst p) && P2 (snd p))).
      
      assert (sumList
     (filter (fun a : A0 * B => negb (P1 (fst a) && P2 (snd a)))
        (getSupport x))
     (fun a : A0 * B =>
      indicator P1 r1 *
      ratInverse (sumList (filter P1 (getSupport c1)) (evalDist c1)) *
      (evalDist x a *
       (if EqDec_dec bool_EqDec (eqb (fst a) r1) true then 1 else 0)))
     == 0).
      eapply sumList_0.
      intuition.
      eapply filter_In in H2.
      intuition.
      unfold indicator .
      case_eq (P1 r1); intuition.
      rewrite ratMult_1_l.

      destruct (EqDec_dec bool_EqDec (eqb (fst a) r1) true).
      rewrite eqb_leibniz in e.
      subst.
      rewrite ratMult_1_r.
      
      eapply negb_true_iff in H5.
      eapply andb_false_iff in H5.
      intuition.
      congruence.
      specialize (H3 a).
      intuition.
      specialize (H0 _ _ H5).
      congruence.

      repeat rewrite ratMult_0_r.
      reflexivity.

      repeat rewrite ratMult_0_l.
      reflexivity.

      rewrite H2.
      clear H2.
      rewrite <- ratAdd_0_r.
      
      eapply sumList_body_eq.
      intuition.
      eapply filter_In in H2.
      intuition.
      unfold indicator.
      destruct (EqDec_dec bool_EqDec (eqb (fst a) r1) true).
      rewrite eqb_leibniz in e.
      subst.
      eapply andb_true_iff in H5.
      intuition.
      rewrite H2.
      simpl.
      rewrite H6.
      repeat rewrite ratMult_1_l.
      repeat rewrite ratMult_1_r.
      eapply ratMult_eqRat_compat; intuition.
      eapply ratInverse_eqRat_compat.
      eapply sumList_nz.
      destruct a.
      exists a.
      intuition.
      eapply filter_In.
      intuition.
      eapply getSupport_In_evalDist.
      rewrite H1.
      unfold marginal_l.
      simpl.
      eapply sumList_nz.
      exists (a, b).
      intuition.
      simpl in H5.
      rewrite eqb_refl in H5.
      destruct ( EqDec_dec bool_EqDec true true).
      rewrite ratMult_1_r in H5.
      eapply getSupport_In_evalDist;
      eauto.
      intuition.
      rewrite H1 in H5.
      unfold marginal_l in H5.
      simpl in H5.
      eapply sumList_nz; eauto.
      exists (a, b).
      intuition.
      simpl in H7.
      rewrite eqb_refl in H7.
      destruct (EqDec_dec bool_EqDec true true).
      rewrite ratMult_1_r in H7.
      eapply getSupport_In_evalDist; eauto.
      intuition.
      

      eapply eqRat_trans.
      eapply sumList_body_eq.
      intros.
      eapply H1.
      unfold marginal_l.
      simpl.
      rewrite sumList_summation.
      
      rewrite (sumList_filter_partition (fun p : A0 * B => P1 (fst p) && P2 (snd p))).

      assert (sumList
     (filter (fun a0 : A0 * B => negb (P1 (fst a0) && P2 (snd a0)))
        (getSupport x))
     (fun b : A0 * B =>
      sumList (filter P1 (getSupport c1))
        (fun a0 : A0 =>
         evalDist x b *
         (if EqDec_dec bool_EqDec (eqb (fst b) a0) true then 1 else 0)))
     == 0).
      eapply sumList_0.
      intuition.
      eapply filter_In in H5.
      intuition.
      eapply sumList_0.
      intuition.
      eapply filter_In in H5.
      intuition.
      destruct (EqDec_dec bool_EqDec (eqb (fst a0) a1) true).
      rewrite eqb_leibniz in e.
      subst.
      eapply negb_true_iff in H8.
      eapply andb_false_iff in H8.
      intuition.
      congruence.
      specialize (H3 _ H7).
      specialize (H0 _ _ H3).
      congruence.
      eapply ratMult_0_r.
      
      rewrite H5.
      clear H5.
      rewrite <- ratAdd_0_r.
      eapply sumList_body_eq.
      intuition.
      
      eapply filter_In in H5.
      intuition.
      eapply andb_true_iff in H8.
      intuition.
      rewrite sumList_factor_constant_l.
      symmetry.
      rewrite <- ratMult_1_r at 1.
      eapply ratMult_eqRat_compat.
      reflexivity.
      symmetry.
      rewrite (@sumList_exactly_one _ (fst a0) ); intuition.
      rewrite eqb_refl.
      destruct (EqDec_dec bool_EqDec true true); intuition.
      eapply filter_NoDup.
      eapply getSupport_NoDup.
      eapply filter_In.
      intuition.
      eapply getSupport_In_evalDist.
      intuition.
      rewrite H1 in H8.
      unfold marginal_l in H8.
      simpl in H8.
      eapply sumList_nz; eauto.
      econstructor.
      intuition.
      eauto.
      eapply ratMult_0 in H10.
      intuition.
      eapply getSupport_In_evalDist.
      eapply H7.
      eauto.
      rewrite eqb_refl in H11.
      destruct ( EqDec_dec bool_EqDec true true); intuition.
      case_eq ((eqb (fst a0) b)); intuition.
      rewrite eqb_leibniz in H11.
      intuition.
      destruct (EqDec_dec bool_EqDec false true ).
      discriminate.
      intuition.
      
      repeat rewrite ratMult_0_r.
      reflexivity.

      (* second marginal *)

      simpl.
      rewrite H.
      unfold marginal_r.
      simpl.

      rewrite <- sumList_factor_constant_l.

      rewrite (sumList_filter_partition (fun p : A0 * B => P1 (fst p) && P2 (snd p))).
      
      assert (sumList
     (filter (fun a : A0 * B => negb (P1 (fst a) && P2 (snd a)))
        (getSupport x))
     (fun a : A0 * B =>
      indicator P2 r2 *
      ratInverse (sumList (filter P2 (getSupport c2)) (evalDist c2)) *
      (evalDist x a *
       (if EqDec_dec bool_EqDec (eqb (snd a) r2) true then 1 else 0)))
     == 0).
      eapply sumList_0.
      intuition.
      eapply filter_In in H2.
      intuition.
      unfold indicator .
      case_eq (P2 r2); intuition.
      rewrite ratMult_1_l.

      destruct (EqDec_dec bool_EqDec (eqb (snd a) r2) true).
      rewrite eqb_leibniz in e.
      subst.
      rewrite ratMult_1_r.
      
      eapply negb_true_iff in H5.
      eapply andb_false_iff in H5.
      intuition.
      specialize (H3 a).
      intuition.
      specialize (H0 _ _ H5).
      congruence.
      congruence.

      repeat rewrite ratMult_0_r.
      reflexivity.

      repeat rewrite ratMult_0_l.
      reflexivity.

      rewrite H2.
      clear H2.
      rewrite <- ratAdd_0_r.
      
      eapply sumList_body_eq.
      intuition.
      eapply filter_In in H2.
      intuition.
      unfold indicator.
      destruct (EqDec_dec bool_EqDec (eqb (snd a) r2) true).
      rewrite eqb_leibniz in e.
      subst.
      eapply andb_true_iff in H5.
      intuition.
      rewrite H2.
      simpl.
      rewrite H6.
      repeat rewrite ratMult_1_l.
      repeat rewrite ratMult_1_r.
      eapply ratMult_eqRat_compat; intuition.
      eapply ratInverse_eqRat_compat.
      eapply sumList_nz.
      destruct a.
      exists b.
      intuition.
      eapply filter_In.
      intuition.
      eapply getSupport_In_evalDist.
      rewrite H.
      unfold marginal_r.
      simpl.
      eapply sumList_nz.
      exists (a, b).
      intuition.
      simpl in H5.
      rewrite eqb_refl in H5.
      destruct ( EqDec_dec bool_EqDec true true).
      rewrite ratMult_1_r in H5.
      eapply getSupport_In_evalDist;
      eauto.
      intuition.
      rewrite H in H5.
      unfold marginal_r in H5.
      simpl in H5.
      eapply sumList_nz; eauto.
      exists (a, b).
      intuition.
      simpl in H7.
      rewrite eqb_refl in H7.
      destruct (EqDec_dec bool_EqDec true true).
      rewrite ratMult_1_r in H7.
      eapply getSupport_In_evalDist; eauto.
      intuition.      

      eapply eqRat_trans.
      eapply sumList_body_eq.
      intros.
      eapply H.
      unfold marginal_r.
      simpl.
      rewrite sumList_summation.
      
      rewrite (sumList_filter_partition (fun p : A0 * B => P1 (fst p) && P2 (snd p))).

      assert (
          sumList
     (filter (fun a0 : A0 * B => negb (P1 (fst a0) && P2 (snd a0)))
        (getSupport x))
     (fun b : A0 * B =>
      sumList (filter P2 (getSupport c2))
        (fun a0 : B =>
         evalDist x b *
         (if EqDec_dec bool_EqDec (eqb (snd b) a0) true then 1 else 0)))
     == 0).
      eapply sumList_0.
      intuition.
      eapply filter_In in H5.
      intuition.
      eapply sumList_0.
      intuition.
      eapply filter_In in H5.
      intuition.
      destruct (EqDec_dec bool_EqDec (eqb (snd a0) a1) true).
      rewrite eqb_leibniz in e.
      subst.
      eapply negb_true_iff in H8.
      eapply andb_false_iff in H8.
      intuition.
      specialize (H3 _ H7).
      specialize (H0 _ _ H3).
      congruence.
      congruence.
      eapply ratMult_0_r.
      
      rewrite H5.
      clear H5.
      rewrite <- ratAdd_0_r.
      eapply sumList_body_eq.
      intuition.
      
      eapply filter_In in H5.
      intuition.
      eapply andb_true_iff in H8.
      intuition.
      rewrite sumList_factor_constant_l.
      symmetry.
      rewrite <- ratMult_1_r at 1.
      eapply ratMult_eqRat_compat.
      reflexivity.
      symmetry.
      rewrite (@sumList_exactly_one _ (snd a0) ); intuition.
      rewrite eqb_refl.
      destruct (EqDec_dec bool_EqDec true true); intuition.
      eapply filter_NoDup.
      eapply getSupport_NoDup.
      eapply filter_In.
      intuition.
      eapply getSupport_In_evalDist.
      intuition.
      rewrite H in H8.
      unfold marginal_r in H8.
      simpl in H8.
      eapply sumList_nz; eauto.
      econstructor.
      intuition.
      eauto.
      eapply ratMult_0 in H10.
      intuition.
      eapply getSupport_In_evalDist.
      eapply H7.
      eauto.
      rewrite eqb_refl in H11.
      destruct ( EqDec_dec bool_EqDec true true); intuition.
      case_eq ((eqb (snd a0) b)); intuition.
      rewrite eqb_leibniz in H11.
      intuition.
      destruct (EqDec_dec bool_EqDec false true ).
      discriminate.
      intuition.
      
      repeat rewrite ratMult_0_r.
      reflexivity.

      (* predicate holds on all values in support of joint distribution *)

      unfold getSupport in H2.
      fold getSupport in *.
      eapply filter_In in H2.
      intuition.
    Qed.

    assert (option (TSet lambda * FreeList)).
    apply None.
    assert (Bvector lambda).
    apply (oneVector lambda).
    eapply comp_spec_Repeat.
    comp_skip.
    inline_first.
    comp_skip.
    comp_simp.

    assert(
        comp_spec (fun x y => fst (fst y) = fst x /\ snd x = snd y)
     (ret (a0,
          (if a0 then true else false) &&
          negb
            (eqb
               (map
                  (fun x : Bvector lambda =>
                   ESPADA_TSetRetrieve (getTSet a0) x) b0)
               (map
                  (fun x : list bool =>
                   Array.arrayLookupList (list_EqDec bool_EqDec) 
                     (fst (t, l)) x) (snd (t, l))))))
     (ret (a0, b,
          (if fst (a0, b) then true else false) &&
          negb
            (eqb
               (map
                  (fun x : Bvector lambda =>
                   ESPADA_TSetRetrieve (getTSet (fst (a0, b))) x) b0)
               (map
                  (fun x : list bool =>
                   Array.arrayLookupList (list_EqDec bool_EqDec) t x) l))))

     ).

    eapply comp_spec_ret.
    simpl; intuition.
    eauto.

    intuition.
    simpl in *; subst.
    trivial.

    simpl in H2.
    intuition.
    subst.
    simpl.
    eapply comp_spec_eq_refl.

    rewrite H0.
    clear H0.
    
    assert
      (
        Pr 
   [z0 <-$
    Repeat
      (z0 <-$ ESPADA_TSetSetup_trial t;
       z1 <-$
       (tags <-$
        compMap (Bvector_EqDec lambda)
          (fun x : Blist => ESPADA_TSetGetTag lambda F_bar (snd z0) x) l;
        tSet <- getTSet (fst z0);
        t_w <-
        map (fun x : Bvector lambda => ESPADA_TSetRetrieve tSet x) tags;
        t_w_correct <-
        map
          (fun x : list bool =>
           Array.arrayLookupList (list_EqDec bool_EqDec) t x) l;
        b <- negb (eqb t_w t_w_correct);
        ret (if fst z0 then true else false) && b); 
       ret (z0, z1))
      (fun p : option (TSet lambda * FreeList) * Bvector lambda * bool =>
       isSome (fst (fst p))); ret snd z0 ]
        ==Pr 
   [z0 <-$ (
         z0 <-$
            Repeat
            (ESPADA_TSetSetup_trial t)
            (fun p  =>
               isSome (fst p));
       z1 <-$
       (tags <-$
        compMap (Bvector_EqDec lambda)
          (fun x : Blist => ESPADA_TSetGetTag lambda F_bar (snd z0) x) l;
        tSet <- getTSet (fst z0);
        t_w <-
        map (fun x : Bvector lambda => ESPADA_TSetRetrieve tSet x) tags;
        t_w_correct <-
        map
          (fun x : list bool =>
           Array.arrayLookupList (list_EqDec bool_EqDec) t x) l;
        b <- negb (eqb t_w t_w_correct);
        ret (if fst z0 then true else false) && b); 
       ret (z0, z1));
      ret snd z0 ]
   ).

    comp_skip.
    eapply (Repeat_factor_indep _ _ _ (fun x => isSome (fst x))).

    (*
    Theorem ESPADA_TSetSetup_trial_wf : 
      forall t,
       well_formed_comp (ESPADA_TSetSetup_trial t).

      intuition.
      unfold ESPADA_TSetSetup_trial , ESPADA_TSet_Once_Games.ESPADA_TSetSetup_trial.
      wftac.
      eapply compFold_wf.
      intuition.
      unfold foldBody_option.
      destruct a; wftac.
      unfold ESPADA_TSetSetup_wLoop .
      comp_simp.
      eapply compFold_wf.
      intuition.
      unfold foldBody_option.
      destruct a; wftac.
      unfold ESPADA_TSetSetup_tLoop.
      comp_simp.

      unfold maybeBindComp.
      wftac.
      eapply RndListElem.rndListElem_wf.
      intuition.
      destruct b4; wftac.

    Qed.

*)

    eapply ESPADA_TSetSetup_trial_wf .

    assert (In (t, l, tt) (getSupport (x <-$ A; ret (x, tt)))).
    eapply getSupport_In_Seq.
    eauto.
    simpl.
    intuition.
    
    specialize (@ESPADA_TSetSetup_Some_in_support lambda unit bigB bigS F F_bar
               (x <-$ A; ret (x, tt)) failProb); intuition.
    edestruct H2.
    intuition.
    
    repeat simp_in_support.
    unfold setupSuccess.
    eapply leRat_trans.
    Focus 2.
    eapply failProb_correct.
    eauto.
    unfold ESPADA_TSetSetup_trial.
    comp_skip.

    eapply eqRat_impl_leRat.
    eapply evalDist_ret_eq.
    unfold TSet.
    unfold ESPADA_TSet_Once.TSet.
    unfold TSet.
    destruct ( @fst
            (option
               (prod (list (list (option (TSet_Record lambda)))) FreeList))
            (Bvector (posnatToNat lambda)) ); simpl; trivial.
    eauto.

    destruct H1.
    econstructor.
    eapply filter_In.
    eauto.
  
    intuition.
    wftac.
    eapply compMap_wf.
    intuition.
    unfold ESPADA_TSetGetTag.
    wftac.

    rewrite H0.
    clear H0.

    inline_first.
    comp_skip.
    reflexivity.
    inline_first.
    comp_simp.
    comp_skip.
    simpl.
    reflexivity.
    unfold getSupport in H0.
    fold getSupport in H0.
    eapply filter_In in H0.
    intuition.
    comp_simp.
    eapply evalDist_ret_eq.
    simpl.
    simpl in H3.
    destruct o; simpl.
    reflexivity.

    simpl in H3.
    discriminate.
  Qed.
    
  Require Import RepeatCore.


  Theorem ESPADA_TSet_Correct_Single_G1_equiv : 
    Pr[TrueSingle_G
      (fun a : T lambda * list Blist =>
         TSetCorr_G0_RepeatBody a) A (fun x => snd x)] ==
     Pr[ESPADA_TSetCorr_G1 bigB bigS maxMatches F F_bar A ].

    unfold TrueSingle_G, TSetCorr_G0_RepeatBody, ESPADA_TSetCorr_G1.
    comp_skip.
    comp_simp.
    comp_inline_l.
    unfold fst.
    comp_skip.
    reflexivity.
    comp_simp.

    unfold snd.

    unfold ESPADA_TSetGetTag.

    inline_first.

    assert (
         Pr 
   [a <-$ (foreach  (x in l)ret F_bar b x);
    b0 <-$
    ret (o,
        (if o then true else false) &&
        negb
          (eqb
             (map
                (fun x : Bvector lambda =>
                 ESPADA_TSetRetrieve (getTSet o) x) a)
             (map
                (fun x : list bool =>
                 Array.arrayLookupList (list_EqDec bool_EqDec) t x) l)));
    ret (let (_, y) := b0 in y) ]
   ==
    Pr 
   [a <-$ ret (map (F_bar b) l);
    b0 <-$
    ret (o,
        (if o then true else false) &&
        negb
          (eqb
             (map
                (fun x : Bvector lambda =>
                 ESPADA_TSetRetrieve (getTSet o) x) a)
             (map
                (fun x : list bool =>
                 Array.arrayLookupList (list_EqDec bool_EqDec) t x) l)));
    ret (let (_, y) := b0 in y) ]
   ).

    inline_first.
    comp_skip.
    eapply comp_spec_eq_impl_eq.
    eapply compMap_map.

    rewrite H1.
    clear H1.
    
    comp_simp.
    reflexivity.
  Qed.


  Variable maxKeywords : nat.
  Hypothesis maxKeywords_correct : 
    forall (t : T lambda) (l : list Blist),
      In (t, l) (getSupport A) ->
      (length (combineKeywords (removeDups (list_EqDec bool_EqDec) l) (toW t)) <=
       maxKeywords)%nat.

  Hypothesis maxMatches_correct :
    forall (t : T lambda) (q : list Blist),
      In (t, q) (getSupport A) -> maxMatch t maxMatches.

  Require Import PRF.
  Require Import ESPADA_TSet_Once.
  Local Open Scope rat_scope.

  Hypothesis A_wf : well_formed_comp A.

  Variable PRF_NA_Adv : Rat.
  Hypothesis PRF_NA_Adv_correct_1 :
    PRF_NA_Advantage ({ 0 , 1 }^lambda) ({ 0 , 1 }^lambda) F_bar
     (list_EqDec bool_EqDec) (Bvector_EqDec lambda)
     (ESPADA_TSet_PRF_A1
        (pair_EqDec
           (list_EqDec
              (pair_EqDec (list_EqDec bool_EqDec)
                 (list_EqDec (Bvector_EqDec lambda))))
           (list_EqDec (list_EqDec bool_EqDec)))
        (z <-$ A; [t, l]<-2 z; ret (t, l, (t, l))))
     (ESPADA_TSet_PRF_A2 bigB bigS F
        (fun (s : T lambda * list Blist)
           (p : option (TSet lambda) * list (Bvector lambda)) =>
         [t, q0]<-2 s;
         [tSet_opt, tags]<-2 p;
         tSet <- match tSet_opt with
                 | Some x => x
                 | None => nil
                 end;
         ret (if tSet_opt then true else false) &&
             negb
               (eqb (foreach  (x in tags)ESPADA_TSetRetrieve tSet x)
                  (foreach  (x in q0)
                   arrayLookupList (list_EqDec bool_EqDec) t x))))
                         <= PRF_NA_Adv.

  Hypothesis PRF_NA_Adv_correct_2: 
    forall i, 
      PRF_NA_Advantage ({ 0 , 1 }^lambda) (RndF_R lambda bigB) F _ _  
                        (Hybrid.B1 nil _ _ (PRFI_A1 maxMatches A) i)
                        (Hybrid.B2 
                           (fun lsD => k <-$ {0, 1}^lambda; ret (map (F k) lsD))
            (fun lsD => [lsR, _] <-$2 oracleMap _ _ (RndR_func (@RndF_range lambda bigB) _) nil lsD; ret lsR) _
            (PRFI_A2 lambda))
                         <= PRF_NA_Adv.

  Theorem ESPADA_TSet_Correct : 
    AdvCor _ 
           (ESPADA_TSetSetup bigB bigS F F_bar)
           (ESPADA_TSetGetTag lambda F_bar)
           (ESPADA_TSetRetrieve)
           A <= 
    (lambda / 1) * ((maxKeywords * (S maxMatches))^2 / 2 ^ lambda + 
     (maxKeywords / 1) * PRF_NA_Adv                                                      
     +
    PRF_NA_Adv)  + (expRat failProb lambda).


    rewrite ESPADA_TSet_Correct_G1_equiv.
    unfold TSetCorr_G1.
    rewrite (@TrueMult_impl_Repeat _ _ _ A A_wf TSetCorr_G0_RepeatBody (fun p => snd p) (fun p => isSome (fst p))); intuition.

    rewrite TrueSingle_impl_Mult.
    eapply ratAdd_leRat_compat.
    eapply ratMult_leRat_compat.
    reflexivity.
    
    rewrite ESPADA_TSet_Correct_Single_G1_equiv.

    rewrite ESPADA_TSetCorr_once.
    eapply ratAdd_leRat_compat.
    reflexivity.
    unfold ESPADA_TSetRetrieve.
    reflexivity.
    intuition.
    trivial.
    intuition.
    intuition.

    eauto.
    eauto.
    reflexivity.

    unfold TSetCorr_G0_RepeatBody.
    wftac.
    eapply ESPADA_TSetSetup_trial_wf.
    eapply compMap_wf.
    intuition.
    unfold ESPADA_TSetGetTag.
    wftac.


    destruct x.
    assert (In (t, l, tt) (getSupport (z <-$ A; ret (z, tt)))).
    eapply getSupport_In_Seq.
    eauto.
    simpl.
    intuition.
    specialize (@ESPADA_TSetSetup_Some_in_support lambda unit bigB bigS F F_bar
               (z <-$ A; ret (z, tt)) failProb); intuition.

    edestruct H2.
    intuition.
    eapply leRat_trans.
    Focus 2.
    eapply failProb_correct.
    repeat simp_in_support.
    eauto.
    comp_skip.
    reflexivity.
    unfold setupSuccess.
    destruct x.
    destruct o;
    simpl; reflexivity.
    eauto.

    destruct H1.

    econstructor.
    eapply filter_In.
    intuition.
    unfold TSetCorr_G0_RepeatBody.
    eapply getSupport_In_Seq.
    eapply H1.
    comp_simp.
    eapply getSupport_In_Seq.

    unfold ESPADA_TSetGetTag.
    simpl.

    eapply getSupport_In_evalDist.
    intuition.
    
    assert (forall z, 
              evalDist
         (compMap (Bvector_EqDec lambda) (fun x1 : Blist => ret F_bar x x1) l) z 
              ==
              evalDist (ret (map (F_bar x) l)) z).

    intuition.
    eapply comp_spec_eq_impl_eq.
    eapply compMap_map.
    rewrite H4 in H3.
    eapply getSupport_In_evalDist; [idtac | eauto].
    simpl.
    left.
    reflexivity.
    simpl.
    left.
    reflexivity.
    trivial.

    destruct a.
    eapply leRat_trans.
    Focus 2.
    eapply failProb_correct.
    eauto.
    
    unfold TSetCorr_G0_RepeatBody.
    comp_inline_l.
    comp_skip.
    reflexivity.
    comp_simp.
    inline_first.
    comp_irr_l.
    eapply compMap_wf.
    intuition.
    unfold ESPADA_TSetGetTag.
    wftac.
    dist_compute.
  Qed.

  Print Assumptions ESPADA_TSet_Correct.

End ESPADA_TSet_Correct.