(* Some arguments about lists and random values. *)

Require Import FCF.
Require Import FCF.CompFold.
Require Import FCF.RndInList.

Set Implicit Arguments.
Local Open Scope list_scope.

Section RndListIn.

  Variable A : Set.
  Hypothesis eqda : EqDec A.
  Variable c : Comp A. 
  Variable a : A.
  
  Definition RndListIn_G (B : Type)(ls : list B) :=
    x <-$ compMap _ (fun _ => c) ls;
    ret (if (in_dec (EqDec_dec _) a x) then true else false).

  Theorem RndListIn_Prob : forall (B : Type)(ls : list B), 
    Pr[RndListIn_G ls] <= (length ls)/1 * (evalDist c a).

    Local Opaque evalDist.

    unfold RndListIn_G in *.
    induction ls; intuition idtac; simpl in *.
    comp_simp.
    match goal with
    | [|- context[if ?a then _ else _] ] => 
      destruct a
    end.
    simpl in *.
    intuition idtac.
    rewrite evalDist_ret_0.
    rattac.
    intuition idtac; discriminate.
    
    simpl.
    inline_first.
    eapply leRat_trans.
    eapply (evalDist_bind_event_le _ _ (fun z => eqb a z)).
    reflexivity.
    intuition idtac.
    
    assert (Pr 
   [x <-$
    (lsb' <-$ compMap _ (fun _ => c) ls;
     ret (a1 :: lsb')%list);
    ret (if in_dec (EqDec_dec _) a x then true else false)
   ] ==
            Pr 
   [x <-$ compMap _ (fun _ => c) ls;
    ret (if in_dec (EqDec_dec _) a x then true else false)
   ]).

    inline_first.
    comp_skip.

    match goal with
    | [|- context[if ?a then _ else _] ] => 
      destruct a
    end.
    simpl in *.
    intuition idtac; subst.
    rewrite eqb_refl in *.
    discriminate.
    match goal with
    | [|- context[if ?a then _ else _] ] => 
      destruct a
    end.
    reflexivity.
    intuition idtac.
    simpl in *.
    intuition idtac.
    match goal with
    | [|- context[if ?a then _ else _] ] => 
      destruct a
    end.
    intuition idtac.
    reflexivity.

    rewrite H1.
    rewrite IHls.
    reflexivity.

    rewrite <- evalDist_event_equiv.
    
    eapply leRat_trans.
    2:{
      eapply eqRat_impl_leRat.
      symmetry.
      replace (S (length ls)) with (1 + (length ls))%nat.
      rewrite ratAdd_num.
      rewrite ratMult_distrib_r.
      reflexivity.
      trivial.
    }
    eapply eqRat_impl_leRat.
    rewrite ratMult_1_l.
    reflexivity.

    Local Transparent evalDist.

  Qed.

End RndListIn.

Section RndListPred.

  Variable A : Set.
  Hypothesis eqda : EqDec A.
  Variable c : Comp A. 
  Variable f : A -> bool.

  Definition RndListPred_G (B : Type)(ls : list B) :=
    x <-$ compMap _ (fun _ => c) ls;
    ret (any_dec f x).

  Theorem RndListPred_Prob : forall (B : Type)(ls : list B), 
    Pr[RndListPred_G ls] <= (length ls)/1 * Pr[x <-$c; ret (f x)].

    Local Opaque evalDist.

    unfold RndListPred_G in *.
    induction ls; intuition idtac; simpl in *.
    comp_simp.
    unfold any_dec.
    simpl.
    rewrite evalDist_ret_0.
    eapply rat0_le_all.
    intuition idtac.
    discriminate.
    
    inline_first.
    eapply leRat_trans.
    eapply (evalDist_bind_event_le _ _ f).
    reflexivity.
    intuition idtac.
    
    assert (Pr 
   [x <-$
    (lsb' <-$ compMap _ (fun _ => c) ls;
     ret (a0 :: lsb')%list);
      ret any_dec f x 
   ] ==
            Pr 
   [x <-$ compMap _ (fun _ => c) ls;
    ret any_dec f x 
   ]).

    inline_first.
    comp_skip.

    rewrite any_dec_cons.
    eapply evalDist_ret_eq.
    rewrite H0.
    trivial.
    rewrite H1.
    eauto.
    
    eapply leRat_trans.
    2:{
      eapply eqRat_impl_leRat.
      symmetry.
      replace (S (length ls)) with (1 + (length ls))%nat.
      rewrite ratAdd_num.
      rewrite ratMult_distrib_r.
      reflexivity.
      trivial.
    }
    eapply eqRat_impl_leRat.
    rewrite ratMult_1_l.
    reflexivity.

    Local Transparent evalDist.

  Qed.

End RndListPred.

Section RndInList.

  Variable A : Set.
  Hypothesis eqda : EqDec A.
  Variable c : Comp A. 
  Hypothesis c_wf : well_formed_comp c.
  Variable r : Rat.
  Hypothesis collProb : forall x,
    evalDist c x <= r.
  
  Definition RndInList_G (a : list A) :=
    x <-$ c; 
    ret (if (in_dec (EqDec_dec _) x a) then true else false).

  Theorem RndInList_Prob : forall (a : list A),
    Pr[RndInList_G a] <= (length a)/1 * r.

    Local Opaque evalDist.

    unfold RndInList_G in *.
    induction a; intuition idtac; simpl in *.
    fcf_irr_l.
    rewrite evalDist_ret_0.
    eapply rat0_le_all.
    intuition idtac.
    discriminate.

    eapply leRat_trans.
    eapply (evalDist_bind_event_le _ _ (fun x => eqb a x || if (in_dec (EqDec_dec _) x a0) then true else false)).
    rewrite evalDist_orb_le.
    rewrite <- evalDist_event_equiv.
    rewrite IHa.
    rewrite collProb.
    reflexivity.
    intros.
  
    apply orb_false_elim in H0.
    intuition idtac.
    destruct (EqDec_dec eqda a a1).
    subst.
    rewrite eqb_refl in *.
    discriminate.
    destruct (in_dec (EqDec_dec eqda) a1 a0).
    discriminate.
    rewrite evalDist_ret_0.
    eapply rat0_le_all.
    intuition idtac.
    discriminate.
    rewrite <- ratAdd_0_r.
    rewrite ratMult_comm.
    rewrite ratMult_ratAdd_cd.
    simpl.
    rewrite ratMult_comm.
    reflexivity.
  Qed.

End RndInList.

Section DupList.

  Variable A : Set.
  Hypothesis eqda : EqDec A.
  Variable c : Comp A. 
  Hypothesis c_wf : well_formed_comp c.
  Variable r : Rat.

  Hypothesis collProb : 
    forall a, evalDist c a <= r.
  
  Definition DupList_G (B : Type)(ls : list B) :=
    x <-$ compMap _ (fun _ => c) ls;
    ret (hasDup _ x).

  Theorem DupList_Prob : forall (B : Type)(ls : list B), 
    Pr[DupList_G ls] <= ((length ls) * (length ls))/1 * r.

    Local Opaque evalDist.

    unfold DupList_G in *.
    induction ls; intuition idtac; simpl in *.
    comp_simp.
    simpl.
    rewrite evalDist_ret_0.
    eapply rat0_le_all.
    intuition idtac.
    discriminate.
    
    assert (Pr [x <-$
    (b <-$ c;
     lsb' <-$ compMap eqda (fun _ : B => c) ls;
     ret b :: lsb'); ret hasDup eqda x ]
      ==
    Pr [lsb' <-$ compMap eqda (fun _ : B => c) ls;
    a0 <-$ c;
    ret hasDup eqda (a0 :: lsb')]
    ).
    fcf_swap rightc.
    fcf_inline_first.
    fcf_skip.
    fcf_inline_first.
    fcf_skip.

    rewrite H.
    clear H.

    eapply leRat_trans.
    eapply (evalDist_bind_event_le _ _ (fun z => hasDup _ z )).
    eauto.
    intros.
    eapply (evalDist_bind_event_le _ _ (fun z => if (in_dec (EqDec_dec _) z a0) then true else false )).
    specialize (@RndInList_Prob _ _ c c_wf r collProb a0); intros.
    unfold RndInList_G in *.
    rewrite H1.
    apply compMap_length in H.
    rewrite H.
    reflexivity.
    intros.
    simpl.
    destruct (in_dec (EqDec_dec eqda) a1 a0).
    discriminate.
    rewrite H0.
    rewrite evalDist_ret_0.
    reflexivity.
    intuition idtac.
    discriminate.

    rewrite <- ratAdd_0_r.
    eapply leRat_trans.
    2:{
    eapply ratMult_leRat_compat.
    eapply leRat_terms.
    eapply Nat.le_succ_diag_r.
    reflexivity.
    reflexivity.
    }
    eapply leRat_trans.
    2:{
    eapply eqRat_impl_leRat.
    symmetry.
    rewrite ratAdd_den_same.
    rewrite ratMult_distrib_r.
    reflexivity.
    }
    rewrite ratAdd_comm.
    eapply ratAdd_leRat_compat.
    reflexivity.
    eapply ratMult_leRat_compat.
    eapply leRat_terms.
    eapply mult_le_compat.
    trivial.  
    lia.
    trivial.
    reflexivity.

    Local Transparent evalDist.
  Qed.

End DupList.
