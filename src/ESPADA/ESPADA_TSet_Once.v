Set Implicit Arguments.

Require Import FCF.
Require Import Array.
Require Import CompFold.
Require Import RndNat.
Require Import RndListElem. 
Require Import PRF.

Require Import TSet.
Require Import ESPADA_TSet_Once_Games.

Local Open Scope array_scope.
Local Open Scope list_scope.

Section ESPADA_TSet_once.

  Variable lambda : posnat.
  Variable tSize bigB bigS : posnat.
  Variable bucketSize : nat -> (posnat * posnat).
  Variable F : Bvector lambda -> nat -> nat * Bvector lambda * Bvector (S lambda).
  Variable F_bar : Bvector lambda -> Blist -> Bvector lambda.

  Definition TSet := (@TSet lambda).
  Definition initFree := (@initFree bigB bigS).

  Hypothesis F_b_correct : 
    forall k b i v1 v2,
      (b, v1, v2) = F k i ->
      b < bigB.


  Variable A_State : Set.
  Hypothesis A_State_EqDec : EqDec A_State.
  Variable A1 : Comp (T lambda * list Blist * A_State).
  Variable A2 : A_State  -> (option TSet) * list (Bvector lambda) -> Comp bool.

  
   Notation "'ESPADA_TSetSetup_Sim_wLoop'" := (ESPADA_TSet_Once_Games.ESPADA_TSetSetup_Sim_wLoop F) (at level 90).


   Notation "'gInst' g" := (@g lambda bigB bigS F F_bar A_State A1 A2) (at level 90).


   (* Step 1 : Inline and simplify. *)
  Theorem ESPADA_TSet_1_equiv:
    Pr[TSetReal _ (@ESPADA_TSetSetup_once lambda bigB bigS F F_bar) (@ESPADA_TSetGetTag lambda F_bar) A1 A2] == Pr[ gInst ESPADA_TSet_1 ].

    unfold ESPADA_TSet_1, TSetReal, ESPADA_TSetSetup, ESPADA_TSetSetup_trial.
    comp_skip.
    comp_simp.
    inline_first.
    comp_skip.
    inline_first.
    comp_skip.
    reflexivity.
    eapply trans.
    eapply evalDist_seq;
    intuition.
    eapply comp_spec_eq_impl_eq.
    eapply compMap_map.
    eapply eqRat_refl.
    comp_simp.
    eapply eqRat_refl.
  Qed.

  (* Step 2: pull out the stag computation and answer lookup.  We switch to the simulator setup loop because it happens to work here.  *)
  Theorem ESPADA_TSet_2_equiv : 
     Pr[gInst ESPADA_TSet_1] == Pr[gInst ESPADA_TSet_2].

     unfold  ESPADA_TSet_1,  ESPADA_TSet_2.
     
     do 3 (comp_skip; comp_simp).
     eapply comp_spec_eq_impl_eq.
     eapply (@compFold_eq).
     eapply list_pred_zip_r.
     eapply list_pred_map_r.
     eapply list_pred_map_l_eq.
     eapply list_pred_map_l_eq.
     eapply list_pred_map_l_eq.

     intuition.
     intuition.
     destruct H4.
     intuition.

     destruct a2; simpl in *; subst. 
     unfold ESPADA_TSetSetup_wLoop, ESPADA_TSet_Once_Games.ESPADA_TSetSetup_Sim_wLoop.
     comp_simp.
     unfold foldBody_option.
     eapply comp_spec_eq_refl.

   Qed.


  (* Step 3: initialize the TSet using all keywords -- including those that are in the the queries but not in the structure. *)
 
   Fixpoint lookupIndex (A : Set)(eqd : eq_dec A)(ls : list A)(a : A) def :=
     match ls with
         | nil => def
         | a' :: ls' =>
           if (eqd a a') then O else S (lookupIndex eqd ls' a def)
     end.

   (* Step 3_1 : Start by initializing the absent keywords at then end -- this will be a no-op *)
   Definition ESPADA_TSet_3_1 :=
     [t, q, s_A] <-$3 A1;
     k_T <-$ {0, 1} ^ lambda;
     stags <- map (F_bar k_T) (toW t);
     ts <- map (arrayLookupList _ t) (toW t);
     loopRes <-$ compFold _ (foldBody_option _ (ESPADA_TSetSetup_Sim_wLoop)) (Some (nil, initFree)) (zip stags ts);
     absent_qs <- (removePresent (EqDec_dec _) (toW t) (removeDups _ q));
     q_tags <- map (F_bar k_T) absent_qs ;
     q_ts <- map (arrayLookupList _ t) absent_qs;
     loopRes <-$ compFold _ (foldBody_option _ (ESPADA_TSetSetup_Sim_wLoop)) loopRes (zip q_tags q_ts);
     tSet <- getTSet_opt loopRes;
     tags <- map (F_bar k_T) q;
     A2 s_A (tSet, tags).


   (* Step 3_2 : Combine the two loops into one *)
   Definition ESPADA_TSet_3_2 :=
     [t, q, s_A] <-$3 A1;
     absent_qs <- (removePresent (EqDec_dec _) (toW t) (removeDups _ q));
     k_T <-$ {0, 1} ^ lambda;
     stags <- map (F_bar k_T) (toW t);
     q_tags <- map (F_bar k_T) absent_qs ;
     ts <- map (arrayLookupList _ t) (toW t);
     q_ts <- map (arrayLookupList _ t) absent_qs;
     loopRes <-$ compFold _ (foldBody_option _ (ESPADA_TSetSetup_Sim_wLoop)) (Some (nil, initFree)) ((zip stags ts) ++ (zip q_tags q_ts));
     tSet <- getTSet_opt loopRes;
     tags <- map (F_bar k_T) q;
     A2 s_A (tSet, tags).

   Ltac hypInv :=
      try (match goal with
          | [H: Some _ = Some _ |-_ ] => inversion H; clear H; subst
      end); try pairInv.

   Theorem ESPADA_TSet_3_1_equiv : 
     Pr[gInst ESPADA_TSet_2] == Pr[ESPADA_TSet_3_1].

     unfold ESPADA_TSet_2, ESPADA_TSet_3_1.

     comp_skip; comp_simp.
     comp_skip.
     comp_skip.
     reflexivity.

     comp_irr_r.

     eapply compFold_wf; intuition.
     unfold foldBody_option.
     destruct a0; wftac.
     unfold ESPADA_TSet_Once_Games.ESPADA_TSetSetup_Sim_wLoop;wftac.
     destruct p.
     unfold setLet.
     eapply compFold_wf; intuition.
     unfold foldBody_option.
     destruct a0; wftac.
     unfold ESPADA_TSetSetup_tLoop; wftac.

     destruct p.
     unfold ESPADA_TSet.ESPADA_TSetSetup_tLoop .
     unfold maybeBindComp.
     wftac.
     eapply rndListElem_wf.

     intuition.
     destruct b4; wftac.

     apply compFold_nop in H2; intuition.

     subst.
     intuition.     

     apply In_zip in H3.
     intuition.
     apply in_map_iff in H5.
     apply in_map_iff in H6.
     destruct H5.
     destruct H6.
     intuition.
     subst.

     unfold foldBody_option in *.
     destruct x0.

     unfold ESPADA_TSet_Once_Games.ESPADA_TSetSetup_Sim_wLoop in *.
     destruct p.
     unfold setLet in *.
   
     assert ((@arrayLookupList Blist (Bvector (posnatToNat lambda))
                     (@list_EqDec bool bool_EqDec) t x3) = nil).
     unfold arrayLookupList.

     case_eq (t # x3); intuition.
     exfalso.
     eapply removePresent_not_in.
     eauto.
     unfold toW.
     eapply in_removeDups.

     eapply arrayLookup_Some_In_unzip; eauto.

     rewrite H3 in H4.
     simpl in H4.
     intuition.
     simp_in_support.
     trivial.
   Qed.   

   Theorem ESPADA_TSet_3_2_equiv : 
     Pr[ESPADA_TSet_3_1] == Pr[ESPADA_TSet_3_2].

     unfold ESPADA_TSet_3_1, ESPADA_TSet_3_2.

     do 2 (comp_skip; comp_simp);
     rewrite <- evalDist_assoc.

     symmetry.
     comp_skip.
     eapply compFold_app; intuition.
 
     intuition.
   Qed.

   Theorem ESPADA_TSet_3_equiv : 
     Pr[ESPADA_TSet_3_2] == Pr[gInst ESPADA_TSet_3].
     
     unfold ESPADA_TSet_3_2, ESPADA_TSet_3.
     
     comp_skip; comp_simp.
     inline_first.
     comp_skip.
     comp_simp.
     comp_skip.
     eapply comp_spec_eq_impl_eq.
     eapply (compFold_eq).
  
     rewrite zip_app.
     repeat rewrite <- map_app.
     unfold combineKeywords.
     eapply list_pred_eq.

     repeat rewrite map_length.
     trivial.
     repeat rewrite map_length.
     trivial.
     
     intuition.
     subst.
     eapply comp_spec_eq_refl.

     rewrite map_map.
     symmetry.

     erewrite (map_ext_in  _ _ (F_bar x));
       intuition.

      erewrite nth_map_In.
      rewrite nth_lookupIndex .
      trivial.

      Lemma combineKeywords_in : 
        forall ls1 ls2 a,
          (In a ls1 \/ In a ls2) ->
          In a (combineKeywords ls1 ls2).

        intros.
        destruct (in_dec (EqDec_dec _) a ls1).
        clear H.
        unfold combineKeywords.
        eapply in_or_app.
        intuition.

        intuition.
        unfold combineKeywords.
        eapply in_or_app.
        right.
        eapply removePresent_In; intuition.

      Qed.

      eapply combineKeywords_in; intuition.
      right.
      eapply in_removeDups.
      trivial.
  
      eapply lookupIndex_lt_length.
      eapply combineKeywords_in ; intuition.
      right.
      eapply in_removeDups.
      trivial.

      Grab Existential Variables.
      apply nil.

    Qed.
  

   Require Import OTP.
   Notation "'gInst1' g" := (g lambda bigB bigS F A_State A1 A2) (at level 90).

   Theorem ESPADA_TSet_15_equiv : 
     Pr[gInst1 ESPADA_TSet_14] == Pr[gInst1 ESPADA_TSet_15].

     unfold ESPADA_TSet_14, ESPADA_TSet_15.

     do 4 (comp_skip; comp_simp).
     eapply comp_spec_eq_impl_eq.
     eapply comp_fold_ext; intuition.

     unfold foldBody_option.
     destruct a0.
     
     unfold ESPADA_TSetSetup_tLoop_14, ESPADA_TSetSetup_tLoop_15.
     comp_simp.
     comp_skip.
     comp_skip.
     eapply comp_spec_eq_symm.
     eapply comp_spec_seq.
     apply None.
     eapply None.
     eapply xor_OTP; intuition.
     intuition.
     subst.
     comp_skip.
     eapply comp_spec_eq_refl.
     eapply comp_spec_eq_refl.
   Qed.

   
   Theorem ESPADA_TSet_16_equiv : 
     Pr[gInst1 ESPADA_TSet_15] == Pr[gInst1 ESPADA_TSet_16].

     unfold ESPADA_TSet_15, ESPADA_TSet_16.

     do 4 (comp_skip; comp_simp).
     eapply comp_spec_eq_impl_eq.
     eapply compFold_eq.
     eapply list_pred_I.

     eapply length_flatten_eq.

     eapply list_pred_impl.
     eapply list_pred_map_r.

     eapply list_pred_map_l.
     eapply list_pred_map_l_eq.

     intuition.
     destruct H2.
     intuition.
     destruct H3.
     intuition.
     subst.

     rewrite numberedMap_length.
     trivial.

     intuition.

     unfold foldBody_option.
     destruct acc.
     unfold ESPADA_TSetSetup_tLoop_15, randomTSetEntry.
     comp_simp.
     comp_swap_l.
     comp_skip.
     comp_swap_l.
     comp_skip.
     comp_skip.
     comp_skip.
     destruct b5.
     comp_simp.
     eapply comp_spec_eq_refl.
     eapply comp_spec_eq_refl.
     eapply comp_spec_eq_refl.
   Qed.

   Theorem toW_NoDup : 
     forall (t : T lambda), 
       NoDup (toW t).
     
     intuition.
     apply removeDups_NoDup.
   Qed.
  
   Theorem ESPADA_TSet_17_equiv :
     Pr[gInst1 ESPADA_TSet_16] == Pr[gInst1 ESPADA_TSet_17].

     unfold ESPADA_TSet_16, ESPADA_TSet_17.
     do 4 (comp_skip; comp_simp).
     eapply comp_spec_eq_impl_eq.
     eapply compFold_eq.
     eapply list_pred_I.
     rewrite allNatsLt_length.

     unfold combineKeywords.

     rewrite skipn_app.

     repeat rewrite length_flatten.
     repeat rewrite fold_left_map_eq.
     Require Import Permutation.
   
     rewrite fold_left_add_removePresent.
     f_equal.

     symmetry.     

     rewrite (fold_add_nat_filter_partition (fun a => if (in_dec (EqDec_dec _) a (toW t)) then true else false)).

     rewrite plus_comm.
     rewrite fold_add_nat_0.
     rewrite plus_0_l.
     intuition.

     intuition.
     apply filter_In in H2.
     intuition.
     destruct (@in_dec Blist (@EqDec_dec Blist (@list_EqDec bool bool_EqDec))
                a0 (toW t)).
     simpl in *.
     discriminate.

     unfold toW in *.
     unfold arrayLookupList.

     rewrite notInArrayLookupNone.
     simpl.
     trivial.
     intuition.
     eapply n.

     eapply in_removeDups.
     trivial.

     eapply toW_NoDup.
     eapply removeDups_NoDup.

     intuition.
     eapply comp_spec_eq_refl.

     Theorem eqRat_eq : 
       forall x y,
         x = y ->
         x == y.

       intuition; subst; intuition.

     Qed.

     eapply eqRat_eq.
     f_equal.
     f_equal.
     f_equal.
     f_equal.
     eapply map_ext_in.
     intuition.
     unfold combineKeywords.
     
     Theorem lookupIndex_app : 
       forall (A : Set)(eqd : eq_dec A)(l1 l2 : list A)(a : A) n,
         In a l1 ->
         CompFold.lookupIndex eqd (l1 ++ l2) a n = 
         CompFold.lookupIndex eqd l1 a n.

       induction l1; intuition; simpl in *.
       intuition.

       intuition; subst.
       destruct (eqd a0 a0); intuition.


       destruct (eqd a0 a); intuition.
       

     Qed.

     eapply lookupIndex_app .
     eapply in_removeDups.
     trivial.

   Qed.

   Theorem ESPADA_TSet_18_equiv :
     Pr[gInst1 ESPADA_TSet_17] == Pr[gInst1 ESPADA_TSet_18].

     unfold ESPADA_TSet_17, ESPADA_TSet_18.
     do 3 (comp_skip; comp_simp).

     symmetry.
     
     eapply (@compFold_flatten _ _ _ _ eq).

     unfold flatten_prep.
     unfold numberedMap.
     eapply list_pred_eq.
 
     intuition.
     unfold foldBody_option.
     destruct init.
     unfold ESPADA_TSet_Once_Games.ESPADA_TSetSetup_Sim_wLoop.
     comp_simp.
     unfold foldBody_option.
     eapply comp_spec_impl_eq.
     eapply comp_spec_consequence.
     eapply (@compFold_eq _ _ (fun (p1 : nat * Bvector lambda) p2 => let (i1, s_i1) := p1 in let '(i2, len, tag, s_i2) := p2 in
                                                                                             i1 = i2 /\ s_i1 = s_i2 /\ tag = d /\ len = (length lsa))).
     
     eapply list_pred_map_l_inv in H2.
     
     eapply list_pred_impl.
     eapply H2.
     
     intuition.
     subst.
     intuition.
     intuition.
 
     destruct acc.

     Theorem ESPADA_TSetSetup_tLoop_4_equiv : 
       forall tag len acc i s_i x, 
         evalDist (ESPADA_TSetSetup_tLoop F tag len acc (i, s_i)) x ==
         evalDist (ESPADA_TSetSetup_tLoop_4 F acc (i, len, tag, s_i)) x.
       
       intuition.
       unfold ESPADA_TSetSetup_tLoop, ESPADA_TSetSetup_tLoop_4.

       
       unfold ESPADA_TSet.ESPADA_TSetSetup_tLoop.
       remember (F tag i) as v.
       destruct v.
       comp_simp.
       comp_skip.
       destruct x0.
       comp_simp.
       destruct (eq_nat_dec (S i) len).
       rewrite e.
       rewrite eqb_refl.
       unfold negb.
       eapply eqRat_refl.
       case_eq (eqb (S i) len); intuition.
       rewrite eqb_leibniz in H1.
       intuition.
       unfold negb.
       eapply eqRat_refl.

       intuition.
     Qed.

     destruct a2.
     destruct p0.
     destruct p0.
     intuition; subst.
     eapply eq_impl_comp_spec_eq.
     eapply (ESPADA_TSetSetup_tLoop_4_equiv).
     eapply comp_spec_eq_refl.

     intuition; subst; intuition.
     
     specialize (compFold_foldBodyOption_None ); intuition.
     unfold foldBody_option in *.
     rewrite H3.
     intuition.
   Qed.

   
   Theorem removeDups_pred : 
       forall (A B : Set) (f : A -> B)(f' : B -> A) (eqda : EqDec A)(eqdb : EqDec B)(lsa : list A)(lsb : list B),
         list_pred (fun a b => b = f a) lsa lsb ->
         (forall a, In a lsa -> f' (f a) = a) ->
         list_pred (fun a b => b = f a) (removeDups _ lsa) (removeDups _ lsb).

       induction 1; intuition; simpl in *.
       econstructor.

       destruct (in_dec (EqDec_dec eqda) a1 ls1).
       destruct (in_dec (EqDec_dec eqdb) a2 ls2).
       eauto.
       
       subst.
       exfalso.
       eapply n.

       Theorem list_pred_In_exists : 
         forall (A B : Set) P (lsa : list A)(lsb : list B),
           list_pred P lsa lsb ->
           forall a, In a lsa ->
             exists b, In b lsb /\ P a b.

         induction 1; intuition; simpl in *.
         intuition.
         intuition; subst.
         econstructor.
         intuition.

         edestruct IHlist_pred.
         eauto.
         intuition.
         exists x.
         intuition.

       Qed.

       edestruct  list_pred_In_exists.
       eapply IHlist_pred.
       intuition.
       eapply in_removeDups.
       eauto.
       intuition.
       subst.
       eapply removeDups_in.
       intuition.

       subst.
       destruct (in_dec (EqDec_dec eqdb) (f a1) ls2).
       exfalso.
       eapply n.
       rewrite <- (@H1 a1).
       eapply list_pred_symm in IHlist_pred.
       edestruct  list_pred_In_exists.
       eauto.
       eapply in_removeDups.
       eauto.
       intuition.
       rewrite H3.
       rewrite H1.
       eapply removeDups_in.
       trivial.

       right.
       eapply removeDups_in.
       trivial.
       
       intuition.
       intuition.
       
       econstructor; eauto.

     Qed.
     

   Theorem removeDups_NoDup_eq : 
     forall (A : Set)(eqd : EqDec A)(ls : list A),
       NoDup ls ->
       removeDups eqd ls = ls.

     induction 1; intuition; simpl in *.
     destruct (in_dec (EqDec_dec eqd) x l); intuition.
     f_equal.
     intuition.
   Qed.

   Definition ESPADA_TSet_19_1 := 
     [t, q, s_A]<-$3 A1;
     eqPattern <- map (fun x => lookupIndex (EqDec_dec _) (removeDups _ q) x O) q;
     qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ eqPattern);
     q_ts <-$ ret map (arrayLookupList _ t) (removeDups _ q);
     loopRes <-$ compFold _ (foldBody_option _ (ESPADA_TSetSetup_Sim_wLoop)) (Some (nil, initFree)) (zip qTags q_ts);
     loopRes <-$ compFold _ (foldBody_option _ (fun acc e => randomTSetEntry bigB acc)) loopRes (allNatsLt (minus (bigN t) (length (flatten q_ts))));
     tSet <- getTSet_opt loopRes;
     inds <- map (fun x => lookupIndex (EqDec_dec _) (removeDups _ q) x O) q;
     tags <- map (fun i => nth i qTags (Vector.const false lambda)) inds;
     A2 s_A (tSet, tags).

   Theorem ESPADA_TSet_19_1_equiv :
     Pr[gInst1 ESPADA_TSet_18] == Pr[ESPADA_TSet_19_1].

     unfold ESPADA_TSet_18, ESPADA_TSet_19_1.

     comp_skip.
     comp_simp.

     comp_skip.
     eapply compMap_eq.

     eapply (@removeDups_pred _ _ (fun a => CompFold.lookupIndex _ (removeDups _ l) a O) (fun b => nth b (removeDups _ l) nil)).
     eapply list_pred_map_r'.
     eapply list_pred_impl.
     eapply list_pred_eq.
     intuition; subst.
     reflexivity.
     intuition.
     eapply nth_lookupIndex.
     eapply in_removeDups.
     trivial.

     intuition.
     comp_simp.
     reflexivity.
   Qed.

   Definition ESPADA_TSet_19_2 := 
     [t, q, s_A]<-$3 A1;
     eqPattern <- map (fun x => lookupIndex (EqDec_dec _) (removeDups _ q) x O) q;
     qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ eqPattern);

     uniqueTs <-$ ret map (fun n => nth (firstIndexOf (EqDec_dec _ ) eqPattern n O) (map (arrayLookupList _ t) q) nil) (removeDups _ eqPattern);

     loopRes <-$ compFold _ (foldBody_option _ (ESPADA_TSetSetup_Sim_wLoop)) (Some (nil, initFree)) (zip qTags uniqueTs);
     loopRes <-$ compFold _ (foldBody_option _ (fun acc e => randomTSetEntry bigB acc)) loopRes (allNatsLt (minus (bigN t) (length (flatten uniqueTs))));
     tSet <- getTSet_opt loopRes;
     inds <- map (fun x => lookupIndex (EqDec_dec _) (removeDups _ q) x O) q;
     tags <- map (fun i => nth i qTags (Vector.const false lambda)) inds;
     A2 s_A (tSet, tags).

   Theorem ESPADA_TSet_19_2_equiv :
     Pr[ESPADA_TSet_19_1] == Pr[ESPADA_TSet_19_2].

     unfold ESPADA_TSet_19_1, ESPADA_TSet_19_2.
     comp_skip.
     comp_simp.
     eapply evalDist_seq_eq.
     intuition.
     intros.
     comp_skip.
     eapply evalDist_ret_eq.
     
     eapply map_eq.

     Theorem list_pred_In : 
       forall (A B : Set) (P : A -> B -> Prop) (lsa : list A)(lsb : list B),
         list_pred (fun a b => In a lsa -> In b lsb -> P a b) lsa lsb ->
         list_pred P lsa lsb.

       induction lsa; inversion 1; intuition; simpl in *.
       econstructor.
       subst.
       econstructor.
       eapply H2; intuition.
       eapply IHlsa.
       eapply list_pred_impl.
       eapply H4.
       intuition.
       
     Qed.
     
     eapply list_pred_In.
     eapply list_pred_impl.

  
     eapply (@removeDups_pred _ _ (fun a => CompFold.lookupIndex _ (removeDups _ l) a O) (fun b => nth b (removeDups _ l) nil)).
     eapply list_pred_map_r'.
     eapply list_pred_impl.
     eapply list_pred_eq.
     intuition; subst.
     reflexivity.
     intuition.
     eapply nth_lookupIndex.
     eapply in_removeDups.
     trivial.

     intuition.
     subst.
     
     Theorem firstIndexOf_map_1_1 : 
       forall (B A : Set) (f : B -> A) (eqda : eq_dec A)(eqdb : eq_dec B)(ls : list B)  (a : B),
         (forall a2, In a2 ls -> f a = f a2 -> a = a2) ->
         firstIndexOf eqda (map f ls) (f a) O = 
         firstIndexOf eqdb ls a O.

       induction ls; intuition; simpl in *.
       destruct (eqdb a0 a); subst.
       
       destruct (eqda (f a) (f a)); intuition.

       destruct ( eqda (f a0) (f a)).
       exfalso.
       eapply n.
       eapply H; intuition.

       f_equal.
       eauto.
     Qed.

     rewrite (@firstIndexOf_map_1_1 _ _ (fun a0 => CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec))
              (removeDups (list_EqDec bool_EqDec) l) a0 0) (EqDec_dec _) (EqDec_dec _)).
    
     erewrite map_nth_in. 
     rewrite nth_lookupIndex.
     trivial.

     eapply removeDups_in.
     trivial.

     eapply firstIndexOf_in_lt.
     eapply removeDups_in.
     trivial.

     intuition.     

     Theorem lookupIndex_1_1 : 
       forall (A : Set)(eqd : eq_dec A)(ls : list A)(a1 a2 : A) n,
         In a1 ls ->
         In a2 ls ->
         lookupIndex eqd ls a1 n = lookupIndex eqd ls a2 n ->
         a1 = a2.

       induction ls; intuition; simpl in *.
       intuition.

       intuition; subst; intuition.

       destruct (eqd a2 a1 ); intuition.
       destruct (eqd a1 a1); intuition.
       discriminate.
       
       destruct ( eqd a1 a2); intuition.
       destruct (eqd a2 a2); intuition.
       discriminate.
       
       destruct (eqd a1 a); 
       destruct ( eqd a2 a); subst; intuition; try discriminate.

       eapply IHls; intuition.

       inversion H1; clear H1; subst.
       eauto.

     Qed.

     eapply lookupIndex_1_1; eauto.
     eapply in_removeDups.
     trivial.

     Grab Existential Variables.
     eapply nil.
   Qed.
     
   Theorem ESPADA_TSet_19_equiv' :
     Pr[ESPADA_TSet_19_2] == Pr[gInst1 ESPADA_TSet_19].

     unfold ESPADA_TSet_19_2, ESPADA_TSet_19.
     comp_skip; comp_simp.
     comp_skip; comp_simp.
     reflexivity.
     reflexivity.

   Qed.

   Theorem ESPADA_TSet_19_equiv :
     Pr[gInst1 ESPADA_TSet_18] == Pr[gInst1 ESPADA_TSet_19].

     rewrite ESPADA_TSet_19_1_equiv.
     rewrite ESPADA_TSet_19_2_equiv.
     eapply ESPADA_TSet_19_equiv'.

   Qed.

   Theorem Ideal_equiv : 
     Pr[gInst1 ESPADA_TSet_19] == Pr[TSetIdeal (@L_T lambda) A1 A2 (ESPADA_TSet_Sim_once lambda bigB bigS F)].

     unfold ESPADA_TSet_19, ESPADA_TSet_Sim, ESPADA_TSet_Sim_trial, TSetIdeal, L_T.
     
     comp_skip; comp_simp.
     unfold ESPADA_TSet_Sim_once, ESPADA_TSet_Sim_trial.
     inline_first. comp_skip.
     inline_first. comp_skip.
     eapply comp_spec_eq_impl_eq.
     eapply compFold_eq.
     eapply list_pred_eq.
     intuition; subst.
     eapply comp_spec_eq_refl.
     
     inline_first. comp_skip.
     eapply comp_spec_eq_impl_eq.
     eapply compFold_eq.
     eapply list_pred_eq.
     intuition; subst.
     eapply comp_spec_eq_refl.

     comp_simp.
     reflexivity.
   Qed.
   
   

   Theorem ESPADA_TSet_4_equiv : 
     Pr[gInst ESPADA_TSet_3] == Pr[gInst ESPADA_TSet_4].

      unfold ESPADA_TSet_3, ESPADA_TSet_4.

      do 2 (comp_skip; comp_simp).
      comp_skip.
      eapply compFold_flatten.
      unfold flatten_prep.
      unfold numberedMap.
      eapply list_pred_eq.

      intuition.
      unfold ESPADA_TSet_Once_Games.ESPADA_TSetSetup_Sim_wLoop.
      
      unfold foldBody_option.
      destruct init.
      comp_simp.
      eapply comp_spec_eq_impl_eq.
      eapply (@compFold_eq _ _ (fun (p1 : nat * Bvector lambda) p2 => let (i1, s_i1) := p1 in let '(i2, len, tag, s_i2) := p2 in
                                                                                              i1 = i2 /\ s_i1 = s_i2 /\ tag = d /\ len = (length lsa))).

      eapply list_pred_map_l_inv in H1.
      eapply list_pred_impl.
      eapply H1.
      
      intuition.
      subst.
      intuition.
      intuition.
      
      destruct a2.
      destruct p.
      destruct p.
      intuition; subst.
      
      destruct acc.
      eapply eq_impl_comp_spec_eq.
      eapply ESPADA_TSetSetup_tLoop_4_equiv.
      eapply comp_spec_eq_refl.
       
      specialize (compFold_foldBodyOption_None ); intuition.
      unfold foldBody_option in *.
      rewrite H2.
      intuition.

    Qed.

    Theorem ESPADA_TSet_6_equiv : 
      Pr[gInst ESPADA_TSet_4] == Pr[gInst ESPADA_TSet_6].

      unfold ESPADA_TSet_4, ESPADA_TSet_6.
      
      do 3 (comp_skip; comp_simp).
      eapply comp_spec_eq_impl_eq.
      eapply (@compFold_eq _ _ (fun (p1 : nat * nat * Bvector lambda * Bvector lambda) (p2 : nat * nat * Bvector lambda * nat * Bvector lambda * Bvector (S lambda)) => 
                             let '(i1, len1, tag1, s_i1) := p1 in
                             let '(i2, len2, s_i2, b2, bigL2, bigK2) := p2 in
                             i1 = i2 /\ len1 = len2 /\ s_i1 = s_i2 /\ (b2, bigL2, bigK2) = F tag1 i1)).

      eapply list_pred_flatten_both.

      eapply list_pred_impl.
      eapply list_pred_map_both.
      eapply list_pred_eq.
      intuition.
      destruct H1.
      destruct H1.
      intuition.
      subst.
      comp_simp.
      unfold numberedMap.
      eapply list_pred_impl.
      eapply list_pred_map_both.
      eapply list_pred_eq.
      intuition.
      destruct H1.
      destruct H1.
      intuition.
      subst.
      destruct x2.
      pairInv.
      
      remember (F b n) as v1.
      destruct v1.
      destruct p.
      intuition.
      
      intuition.
      destruct a2.
      destruct p.
      destruct p.
      destruct p.
      destruct p.
      intuition; subst.

      unfold ESPADA_TSetSetup_tLoop_4, ESPADA_TSetSetup_tLoop_6.
      unfold foldBody_option.
      destruct acc.
      comp_simp.
      pairInv.
      eapply comp_spec_eq_refl.
      eapply comp_spec_eq_refl.
    Qed.

  Require Import Permutation.
 
 
    
  Definition correctFreeList (free : FreeList) :=
    (length free = bigB) /\ (forall ls, In ls free -> NoDup ls /\ (forall j, In j ls -> j < bigS)).

  Theorem ESPADA_TSet_7_equiv : 
    Pr[gInst ESPADA_TSet_6] == Pr[gInst ESPADA_TSet_7].

    unfold ESPADA_TSet_6, ESPADA_TSet_7.

    comp_skip; comp_simp.
    inline_first.
    comp_skip.
    comp_simp.

    comp_skip.
    eapply (compFold_perm
              (fun acc =>
                 match acc with
                     | None => True
                     | Some (tSet, free) =>
                       correctFreeList free
                 end)); intuition.

    eapply Permutation_flatten.
    eapply Permutation_map.

    repeat rewrite zip_map_eq.
    eapply Permutation_map.

    Theorem combineKeywords_Permutation : 
      forall ls1 ls2,
        NoDup ls1 ->
        NoDup ls2 ->
        Permutation (combineKeywords ls1 ls2) (combineKeywords ls2 ls1).

      intuition.
      eapply NoDup_Permutation; intuition.

      
      Theorem combineKeywords_NoDup : 
        forall (ls1 ls2 : list Blist),
          NoDup ls1 ->
          NoDup ls2 ->
          NoDup (combineKeywords ls1 ls2).

        unfold combineKeywords; intuition.
        eapply app_NoDup; intuition.
        eapply removePresent_NoDup; intuition.
        eapply removePresent_correct.
        eapply H1.
        eauto.

        eapply removePresent_correct.
        eapply H2.
        eauto.
      Qed.


      apply combineKeywords_NoDup; intuition.
      apply combineKeywords_NoDup; intuition.
  

      Theorem combineKeywords_in_iff : 
        forall a ls1 ls2,
          In a (combineKeywords ls1 ls2) <-> (In a ls1 \/ In a ls2).

        unfold combineKeywords in *; intuition.
        apply in_app_or in H; intuition.
        right.
        eapply removePresent_in_only_if; eauto.

        eapply in_or_app.
        destruct (in_dec Blist_eq_dec a ls1); intuition.
        right.

        eapply removePresent_correct2; intuition.

      Qed.

      eapply combineKeywords_in_iff in H1.
      eapply combineKeywords_in_iff; intuition.

      eapply combineKeywords_in_iff in H1.
      eapply combineKeywords_in_iff; intuition.

    Qed.

    eapply combineKeywords_Permutation.
   
   
    eapply toW_NoDup.
    eapply removeDups_NoDup.

    apply in_flatten in H1.
    apply in_flatten in H2.
    destruct H1.
    destruct H2.
    intuition.
    apply in_map_iff in H4.
    apply in_map_iff in H1.
    destruct H4.
    destruct H1.
    intuition.
    destruct x4.
    destruct x5.
    subst.

    unfold numberedMap in *.
    apply in_map_iff in H5.
    apply in_map_iff in H6.
    destruct H5.
    destruct H6.
    intuition.
    destruct x2.
    destruct x3.
    remember (F b12 n0) as v2.
    remember (F b11 n) as v3.
    destruct v2.
    destruct p.
    destruct v3.
    destruct p.
    repeat pairInv.

    unfold foldBody_option.
    destruct b.
    destruct p.

    Definition ESPADA_TSetSetup_tLoop_6' tSet (e : nat * nat * Bvector lambda * nat * Bvector lambda * Bvector (S lambda)) j :=
    let '(i, len, s_i, b, bigL, bigK) := e in
      bet <- if (eq_nat_dec (S i) len) then false else true;
                                                    newRecord <- (bigL, BVxor _ (Vector.cons _ bet _ s_i) bigK);
                                                    tSetUpdate tSet b j newRecord.

    Lemma tLoop_6_pair_equiv :
      forall tSet free len1 len2 i1 i2 s_i1 s_i2 b1 b2 bigL1 bigL2 bigK1 bigK2 x,
        evalDist
     (b' <-$ ESPADA_TSetSetup_tLoop_6 (tSet, free) (i1, len1, s_i1, b1, bigL1, bigK1);
      match b' with
      | Some b1 => ESPADA_TSetSetup_tLoop_6 b1 (i2, len2, s_i2, b2, bigL2, bigK2)
      | None => ret None
      end) x == 
        evalDist
          (opt_j1_j2 <-$
                     (free_b1 <- nth b1 free nil;
                      opt_j1 <-$ rndListElem _ (free_b1);
                      match opt_j1 with
                        | None => ret None
                        | Some j1 =>
                          free <- listReplace free b1 (removeFirst (EqDec_dec _) free_b1 j1) nil;
                        free_b2 <- nth b2 free nil;
                        opt_j2 <-$  rndListElem _ (free_b2);
                        match opt_j2 with
                          | None => ret None
                          | Some j2 =>
                            ret (Some (j1, j2))
                        end
                      end);
           match opt_j1_j2 with
             | None => ret None
             | Some (j1, j2) =>
               tSet <- ESPADA_TSetSetup_tLoop_6' tSet (i1, len1, s_i1, b1, bigL1, bigK1) j1;
               tSet <- ESPADA_TSetSetup_tLoop_6' tSet (i2, len2, s_i2, b2, bigL2, bigK2) j2;
               free <- listReplace free b1 (removeFirst (EqDec_dec _) (nth b1 free nil) j1) nil;
               free <- listReplace free b2 (removeFirst (EqDec_dec _) (nth b2 free nil) j2) nil;
               ret (Some (tSet, free))
           end)                                                 
          x.

      intuition.
      unfold ESPADA_TSetSetup_tLoop_6'.
      unfold ESPADA_TSetSetup_tLoop_6.

      comp_simp.
      inline_first.
      comp_skip.
      destruct x0.
      inline_first.
      comp_skip.
      destruct x0.
      comp_simp.

      eapply evalDist_ret_eq.
      f_equal.
      comp_simp.
      intuition.
      comp_simp.
      intuition.
    Qed.

    repeat rewrite tLoop_6_pair_equiv.
    comp_simp.
    (* case split on whether the buckets are the same *)
    destruct (eq_nat_dec b2 b8).
    subst.
   
    eapply (evalDist_iso (fun x => optSwap x) (fun x => optSwap x)); intuition.
    apply optSwap_involutive.
    apply optSwap_involutive.

    repeat simp_in_support.
    destruct x3.
    repeat simp_in_support.
    destruct x3.
    repeat simp_in_support.
    unfold optSwap.
    rewrite <- rndListElem_support in *.
    rewrite nth_listReplace_eq in *.

    destruct (eq_nat_dec n0 n); subst.
    eapply getSupport_In_Seq.
    rewrite <- rndListElem_support.
    eauto.

    cbv beta iota.
    eapply getSupport_In_Seq.
    rewrite <- rndListElem_support.
    rewrite nth_listReplace_eq in *.
    eauto.
    simpl.
    intuition.

    eapply getSupport_In_Seq.
    rewrite <- rndListElem_support.
    eapply removeFirst_in_iff.
    eauto.
    cbv beta iota.
    eapply getSupport_In_Seq.
    rewrite <- rndListElem_support.
    rewrite nth_listReplace_eq in *.
    eapply removeFirst_in.
    eauto.
    intuition.
    simpl.
    intuition.

    repeat simp_in_support.
    eapply getSupport_In_Seq.
    eapply H2.
    cbv beta iota.
    eapply getSupport_In_Seq.
    eauto.
    simpl.
    intuition.

    repeat simp_in_support.
    eapply getSupport_In_Seq.
    eauto.
    simpl.
    intuition.

    repeat simp_in_support.
    destruct x3.
    repeat simp_in_support.
    destruct x3.
    repeat simp_in_support.
    rewrite <-  rndListElem_support in *.
    rewrite nth_listReplace_eq in *.

    eapply comp_spec_impl_eq.
    eapply comp_spec_seq; try eapply None.
    eapply eq_impl_comp_spec;
    try apply rndListElem_wf.
    eapply rndListElem_uniform.
    eapply H3.
    eapply nth_In.
    assert (length f = bigB).
    eapply H3.
    rewrite H1.  
    eapply F_b_correct; eauto.

    rewrite <- rndListElem_support.
    eapply removeFirst_in_iff.
    eauto.
    rewrite <- rndListElem_support.
    eauto.

    intuition.
    
    (*

    eapply H4.

    simpl in *.
    intuition.
    discriminate.

    simpl in *.
    intuition.
    discriminate.
  
    repeat simp_in_support.
    destruct x1.
    repeat simp_in_support.
    destruct x1.
    simp_in_support.
    hypInv.
    trivial.
    simp_in_support.
    discriminate.
    simp_in_support.
    discriminate.

    destruct r0.
    destruct r1. 
     *)
    
    destruct a2.
    destruct b.
    repeat rewrite nth_listReplace_eq.
    simpl.
    destruct (eq_nat_dec n1 n0); subst.
    assert (Some n2 = Some n).
    intuition.
    hypInv.

    eapply comp_spec_seq; try eapply None.

    eapply (comp_spec_iso 
              (fun x => 
                 match x with
                     | None => None
                     | Some v =>  Some
                       (if (eq_nat_dec v n) then n0 else (if (eq_nat_dec v n0) then n else v))
                 end)
               (fun x => 
                 match x with
                     | None => None
                     | Some v =>  Some
                       (if (eq_nat_dec v n) then n0 else (if (eq_nat_dec v n0) then n else v))
                 end)); intuition.
    
    destruct x2.
    destruct (eq_nat_dec n1 n); subst.
    destruct (eq_nat_dec n0 n); subst; intuition.
    destruct (eq_nat_dec n0 n0); subst; intuition.
    destruct (eq_nat_dec n1 n0); subst.
    destruct (eq_nat_dec n n); subst; intuition.
    destruct (eq_nat_dec n1 n); subst.
    intuition.
    destruct (eq_nat_dec n1 n0); subst; intuition.
    trivial.

    destruct x2.
    destruct (eq_nat_dec n1 n); subst.
    destruct (eq_nat_dec n0 n); subst; intuition.
    destruct (eq_nat_dec n0 n0); subst; intuition.
    destruct (eq_nat_dec n1 n0); subst.
    destruct (eq_nat_dec n n); subst; intuition.
    destruct (eq_nat_dec n1 n); subst.
    intuition.
    destruct (eq_nat_dec n1 n0); subst; intuition.
    trivial.

    destruct x2.
    destruct (eq_nat_dec n1 n); subst.    
    rewrite <- rndListElem_support in *.
    exfalso.
    eapply removeFirst_NoDup_not_in; eauto.
    eapply nth_NoDup; intuition.
    eapply H3; intuition.

    destruct (eq_nat_dec n1 n0); subst.
    rewrite <- rndListElem_support in *.
    eapply removeFirst_in.
    trivial.
    intuition.

    rewrite <- rndListElem_support in *.
    eapply removeFirst_in.
    eapply removeFirst_in_iff.
    eauto.
    intuition.

    rewrite <- rndListElem_support in *.

    rewrite rndListElem_support_None in *.
    exfalso.
    eapply (@in_nil nat).
    rewrite <- H12.
    eapply H4.

    destruct x2.
    destruct (eq_nat_dec n1 n); subst.

    eapply rndListElem_uniform_gen.
    eapply removeFirst_NoDup.
    eapply H3.
    eapply nth_In.
    rewrite <- rndListElem_support in *.
    eapply lt_le_trans.
    eapply F_b_correct; eauto.
    unfold correctFreeList in *.
    intuition.

    eapply removeFirst_NoDup.
    eapply H3.
    eapply nth_In.
    rewrite <- rndListElem_support in *.
    eapply lt_le_trans.
    eapply F_b_correct; eauto.
    unfold correctFreeList in *.
    intuition.
    
    Theorem removeFirst_length_In : 
      forall (A : Set)(eqd : eq_dec A)(ls : list A)(x : A),
        In x ls ->
        length (removeFirst eqd ls x) = pred (length ls).

      induction ls; intuition; simpl in *.
      intuition; subst.
      destruct (eqd x x); try discriminate; intuition.

      destruct (eqd x a); subst; intuition.
      simpl.
      erewrite IHls; intuition.
      symmetry.
      eapply S_pred.
      destruct ls.
      simpl in *.
      intuition.
      simpl in *.
      assert (0 < S (length ls)).
      omega.
      eauto.
    Qed.
            
    Show.
    repeat erewrite removeFirst_length_In; eauto.
    eapply removeFirst_in_iff.
    eauto.
    trivial.

    eapply removeFirst_in; intuition.
    subst.
    eapply removeFirst_NoDup_not_in; eauto.
    eapply nth_NoDup; intuition.
    eapply H3; intuition.


    eapply rndListElem_uniform_gen.
    unfold correctFreeList in *.
    eapply removeFirst_NoDup.
    eapply H3.
    eapply nth_In.
    intuition.
    rewrite H13.
    eapply F_b_correct; eauto.

    unfold correctFreeList in *.
    eapply removeFirst_NoDup.
    eapply H3.
    eapply nth_In.
    intuition.
    rewrite H13.
    eapply F_b_correct; eauto.

    repeat rewrite removeFirst_length_In; intuition.
    eapply removeFirst_in_iff; eauto.
    rewrite <- rndListElem_support in *.
    destruct (eq_nat_dec n1 n0); subst.
    exfalso.
    eapply removeFirst_NoDup_not_in; eauto.
    eapply nth_NoDup; intuition.
    eapply H3; intuition.
    eapply removeFirst_in.
    eapply removeFirst_in_iff; eauto.
    intuition.
    
    rewrite <- rndListElem_support in *.
    eauto.

     (* contradiction.  There are at least two elements in the list, so None is not in the support after we remove one. *)
    rewrite <- rndListElem_support in *.
    rewrite rndListElem_support_None in *.
    exfalso.
    eapply (@in_nil nat).
    rewrite <- H12.
    eapply removeFirst_in.
    eapply H9.
    intuition.
    subst.
    eapply removeFirst_NoDup_not_in; eauto.
    eapply nth_NoDup; intuition.
    eapply H3; intuition.

    intuition.
    destruct a2.
    destruct (eq_nat_dec n1 n); subst.

    eapply comp_spec_ret; intuition.
    
    destruct (eq_nat_dec n1 n0); subst.
    eapply comp_spec_ret; intuition.
    hypInv; intuition.
    hypInv; intuition.

    eapply comp_spec_ret; intuition;
    hypInv; intuition.

    subst.
    eapply comp_spec_ret; intuition;
    discriminate.

    destruct (eq_nat_dec n2 n); subst; intuition.
    repeat hypInv.
    intuition.
    
    comp_irr_l.
    eapply rndListElem_wf.
    comp_irr_r.
    eapply rndListElem_wf.
    destruct a2;
    destruct b;
    eapply comp_spec_ret; intuition; hypInv; intuition; try discriminate.

    rewrite <- rndListElem_support in *.
    rewrite rndListElem_support_None in *.
    rewrite H9 in H1.
    simpl in *.
    intuition.

    destruct b.
    rewrite <- rndListElem_support in H9.
    rewrite rndListElem_support_None in *.
    rewrite H1 in H9.
    simpl in *.
    intuition.
    
    eapply comp_spec_ret; intuition.
    simpl in *; discriminate.
    discriminate.

    rewrite <- rndListElem_support in *.
    simp_in_support.
    comp_skip.
    destruct x2.
    comp_skip.
    destruct x2.
    repeat rewrite evalDist_ret_0; intuition.
    discriminate.
    simpl in *; discriminate.
    simpl; intuition.
    simpl; intuition.

    simp_in_support.
    comp_skip.
    destruct x2.
    comp_skip.
    destruct x2.
    simpl; intuition.
    simpl; intuition.
    simpl; intuition.
    

    repeat simp_in_support.
    destruct x3.
    repeat simp_in_support.
    destruct x3.
    repeat simp_in_support.
    unfold optSwap.

    destruct (eq_nat_dec n n0); subst.
    (* impossible, means we got the same location twice when sampling (without replacement) from the free list for the bucket *)
    rewrite <- rndListElem_support in *.
    rewrite nth_listReplace_eq in H4.
    exfalso.
    eapply removeFirst_NoDup_not_in.
    eapply H3.
    eapply nth_In.
    unfold correctFreeList in *.
    intuition.
    rewrite H1.
    eapply F_b_correct.
    eauto.
    eauto.

    repeat rewrite nth_listReplace_eq.
    eapply evalDist_ret_eq.
    f_equal.

    Lemma ESPADA_TSetSetup_tLoop_6'_comm : 
      forall tSet j1 j2
             len1 i1 s_i1 b1 bigL1 bigK1
             len2 i2 s_i2 b2 bigL2 bigK2,
        (b1 <> b2 \/ j1 <> j2) ->
        ESPADA_TSetSetup_tLoop_6' (ESPADA_TSetSetup_tLoop_6' tSet (len1, i1, s_i1, b1, bigL1, bigK1) j1) (len2, i2, s_i2, b2, bigL2, bigK2) j2 =
        ESPADA_TSetSetup_tLoop_6' (ESPADA_TSetSetup_tLoop_6' tSet (len2, i2, s_i2, b2, bigL2, bigK2) j2) (len1, i1, s_i1, b1, bigL1, bigK1) j1.


      unfold ESPADA_TSetSetup_tLoop_6'; intros.
      comp_simp.

      Lemma listReplace_comm : 
        forall (A : Set)(i1 i2 : nat)(ls : list A)(a1 a2 def : A),
          i1 <> i2 ->
          listReplace (listReplace ls i1 a1 def) i2 a2 def = 
          listReplace (listReplace ls i2 a2 def) i1 a1 def.

        induction i1; destruct i2; destruct ls; intuition; simpl in *.
        f_equal.
        eapply IHi1; omega.

        f_equal.
        eapply IHi1; omega.

      Qed. 

      Lemma tSetUpdate_comm : 
        forall tSet b1 b2 j1 j2 r1 r2,
          (b1 <> b2 \/ j1 <> j2) ->
          tSetUpdate (@tSetUpdate lambda tSet b2 j2 r2) b1 j1 r1 = 
          tSetUpdate (tSetUpdate tSet b1 j1 r1) b2 j2 r2.

        unfold tSetUpdate; intros.
        destruct (eq_nat_dec b1 b2); subst.
        intuition.

        repeat rewrite listReplace_twice.

        f_equal.

        repeat rewrite nth_listReplace_eq.
        apply  listReplace_comm ; intuition.

        clear H.

        repeat rewrite (@nth_listReplace_ne b1 b2); intuition.
        repeat rewrite (@nth_listReplace_ne b2 b1); intuition.

        apply listReplace_comm; intuition.
       

      Qed.

      eapply tSetUpdate_comm.
      intuition.
    Qed.
                   
    f_equal.

    eapply  ESPADA_TSetSetup_tLoop_6'_comm; intuition. 

    repeat rewrite listReplace_twice.
    f_equal.

    Lemma removeFirst_comm : 
      forall (A : Set)(eqd : eq_dec A)(ls : list A) (a1 a2 : A),
        removeFirst eqd (removeFirst eqd ls a1) a2 =
        removeFirst eqd (removeFirst eqd ls a2) a1.

      induction ls; intuition; simpl in *.
      destruct (eqd a1 a); subst.
      destruct (eqd a2 a); subst.
      trivial.
      simpl.
      destruct (eqd a a); subst; intuition.
      destruct (eqd a2 a); subst.
      simpl.
      destruct (eqd a a); intuition.
      
      simpl.
      destruct (eqd a2 a); subst; intuition.
      destruct (eqd a1 a); subst; intuition.

      f_equal.
      eapply IHls.

    Qed.

    eapply removeFirst_comm.

    simp_in_support.
    unfold optSwap.
    intuition.
  
    simp_in_support.
    simpl; intuition.

    (* Now we do the case in which the buckets are different.  These computations are independent, so we can just swap things around. *)
    eapply (evalDist_iso (fun x => optSwap x) (fun x => optSwap x)); intuition.
    apply optSwap_involutive.
    apply optSwap_involutive.
    repeat simp_in_support.
    destruct x3.
    simp_in_support.
    destruct x3.
    repeat simp_in_support.

    unfold optSwap.

    eapply getSupport_In_Seq.
    rewrite <- rndListElem_support in *.

    Theorem nth_listReplace_nil_ne :
      forall (A : Set)(i2 i1 : nat) (a : A) def,
        i1 <> i2 ->
        nth i1 (listReplace nil i2 a def) def = 
        def.

      induction i2; intuition; simpl in *.

      destruct i1; intuition.
      destruct i1; intuition.

      destruct i1; intuition.
    Qed.

    rewrite nth_listReplace_ne in H4; intuition.
    eauto.
    comp_simp.
    eapply getSupport_In_Seq.
    rewrite nth_listReplace_ne; intuition.
    eauto.
    simpl.
    intuition.

    simp_in_support.
    rewrite nth_listReplace_ne in H4; intuition.
    eapply getSupport_In_Seq.
    eauto.
    simpl.
    intuition.
    simp_in_support.
    
    edestruct (@rndListElem_support_exists nat).
    eapply getSupport_In_Seq.
    eauto.
    destruct x2.
    eapply getSupport_In_Seq.
    rewrite nth_listReplace_ne; intuition.
    eauto.
    simpl.
    intuition.
    simpl. intuition.
    
    eapply (trans
              _ (evalDist
                   (opt_j1 <-$ rndListElem nat_EqDec (nth b2 f nil);
                    opt_j2 <-$ rndListElem nat_EqDec (nth b8 f nil);
                    match opt_j1 with
                        | Some j1 =>
                          match opt_j2 with
                              | Some j2 => ret (Some (j1, j2))
                              | None => ret None
                              end
                        | None => ret None
                    end) (optSwap x2))).

    comp_skip.
    destruct x3.
    rewrite nth_listReplace_ne; intuition.
    comp_irr_r.
    eapply rndListElem_wf.

    eapply (trans
              _ (evalDist
                   (opt_j2 <-$ rndListElem nat_EqDec (nth b8 f nil);
                    opt_j1 <-$ rndListElem nat_EqDec (nth b2 f nil);
                    match opt_j1 with
                        | Some j1 =>
                          match opt_j2 with
                              | Some j2 => ret (Some (j1, j2))
                              | None => ret None
                              end
                        | None => ret None
                    end) (optSwap x2))).

    comp_swap leftc.
    comp_skip.

    comp_skip.
    destruct x3.
    rewrite nth_listReplace_ne; intuition.
    comp_skip.
    destruct x3; intuition.

    destruct x2.
    destruct p.
    unfold optSwap.
    destruct (EqDec_dec (option_EqDec (pair_EqDec nat_EqDec nat_EqDec))
         (Some (n3, n2)) (Some (n1, n0))).
    hypInv.
    repeat rewrite evalDist_ret_1; intuition.
    repeat rewrite evalDist_ret_0; intuition; hypInv; intuition.
    
    unfold optSwap.
    repeat rewrite evalDist_ret_0; intuition; discriminate.

    destruct x2.
    destruct p.
    unfold optSwap.

    repeat rewrite evalDist_ret_0; intuition; discriminate.

    simpl.
    intuition.

    comp_irr_l.
    eapply rndListElem_wf.
    destruct x3.
    destruct x2.
    destruct p.
    unfold optSwap.
    repeat rewrite evalDist_ret_0; intuition; discriminate.
    simpl.
    intuition.

    destruct x2.
    destruct p.
    unfold optSwap.
    repeat rewrite evalDist_ret_0; intuition; discriminate.

    unfold optSwap.
    intuition.

    repeat simp_in_support.
    destruct x3.
    repeat simp_in_support.
    destruct x3.
    repeat simp_in_support.
    unfold optSwap.

    repeat rewrite nth_listReplace_ne; intuition.
    eapply evalDist_ret_eq.
    f_equal.
    f_equal.

    eapply  ESPADA_TSetSetup_tLoop_6'_comm; intuition; eauto using F_b_correct.
    rewrite listReplace_comm; intuition.

    simp_in_support.
    unfold optSwap in *.
    intuition.
    simp_in_support.
    unfold optSwap.
    intuition.

    comp_simp.
    intuition.

    unfold foldBody_option in H3.
    destruct b5.
    destruct p.
    unfold ESPADA_TSetSetup_tLoop_6 in *.
    simp_in_support.
    destruct x1.
    simp_in_support.

    unfold correctFreeList in *; intuition.
    apply in_flatten in H1.
    destruct H1.
    intuition.
    eapply in_map_iff in H2.
    destruct H2.
    intuition.
    destruct x2.
    unfold numberedMap in *.
    subst.
    eapply in_map_iff in H6.
    destruct H6.
    intuition.
    destruct x1.
    remember (F b5 n0) as v1.
    destruct v1.
    destruct p.
    pairInv.

    rewrite listReplace_length; intuition.
    rewrite H3.
    eapply F_b_correct; eauto.

    apply in_flatten in H1.
    destruct H1.
    intuition.
    apply in_map_iff in H6.
    destruct H6.
    intuition.
    destruct x2.
    unfold numberedMap in *.
    subst.
    apply in_map_iff in H7.
    destruct H7.
    intuition.
    destruct x1.
    remember (F b5 n0) as v1.
    destruct v1.
    destruct p.
    pairInv.

    apply listReplace_in in H2; intuition.
    eapply H5.
    trivial.
    subst.

    eapply removeFirst_NoDup.
    eapply H5.
    eapply nth_In.
    rewrite H3.
   
    eapply F_b_correct.
    eauto.
    subst.
    econstructor.

    
    apply in_flatten in H1.
    destruct H1.
    intuition.
    apply in_map_iff in H7.
    destruct H7.
    destruct x2.
    intuition.
    subst.
    unfold numberedMap in *.
    apply in_map_iff in H8.
    destruct H8.
    intuition.
    destruct x1.
    remember (F b5 n0) as v1.
    destruct v1.
    destruct p.
    pairInv.

    apply listReplace_in in H2; intuition; subst.
    eapply H5; eauto.

    eapply H5.
    eapply nth_In.
    rewrite H3.
    eapply F_b_correct; eauto.
    eapply removeFirst_in_iff.
    eauto.
    simpl in H6.
    intuition.

    simp_in_support.
    trivial.

    simp_in_support.
    trivial.

    Theorem initFree_correct : 
      correctFreeList (initFree).

      unfold correctFreeList, initFree, ESPADA_TSet_Once_Games.initFree, ESPADA_TSet.initFree.
      split.
      rewrite map_length.
      eapply allNatsLt_length.

      intros.
      apply in_map_iff in H.
      destruct H.
      intuition; subst.
      eapply map_NoDup.
      eapply allNatsLt_NoDup.
      intuition.
      apply in_map_iff in H.
      destruct H.
      intuition. 
      subst.
      apply allNatsLt_lt; intuition.

    Qed.

    apply initFree_correct.

    eapply eqRat_eq.
    f_equal.
    f_equal.
    f_equal.
    repeat rewrite map_map.
    eapply map_ext_in.
    intuition.

    repeat erewrite nth_map_In;
    repeat erewrite nth_lookupIndex; intuition.
    eapply combineKeywords_in.
    left.
    eapply in_removeDups.
    trivial.
    eapply combineKeywords_in.
    right.
    eapply in_removeDups.
    trivial.

    eapply lookupIndex_lt_length.
    eapply combineKeywords_in.
    left.
    eapply in_removeDups.
    trivial.

    eapply lookupIndex_lt_length.
    eapply combineKeywords_in.
    right.
    eapply in_removeDups.
    trivial.


    Grab Existential Variables.
    apply nil.
    apply nil.


    Theorem firstn_combineKeywords : 
      forall ls1 ls2,
        firstn (length ls1) (combineKeywords ls1 ls2) = ls1.

      intuition.
      unfold combineKeywords.
      eapply firstn_app_eq.
    Qed.

  Qed.

  Definition ESPADA_TSet_PRF_A1 :=
    [t, q, s_A]<-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    ts <- map (arrayLookupList _ t) allQs;
    ret (allQs, (s_A, ts, allQs, q)).

  Definition ESPADA_TSet_PRF_A2 s_A1 allTags :=
    let '(s_A, ts, allQs, q) := s_A1 in 
      inds <-
    (foreach  (x in q)
     CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec)) allQs x 0);
    ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip allTags ts);
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) (Some (nil, initFree)) (flatten ts_recsList);
    tSet <- getTSet_opt loopRes;
    tags <- map (fun x => nth x allTags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).

  Definition ESPADA_TSet_8_1 :=
    [allQs, s_A1] <-$2 ESPADA_TSet_PRF_A1;
    allTags <-$ (k_T <-$ {0, 1} ^ lambda; ret (map (F_bar k_T) allQs));
    ESPADA_TSet_PRF_A2 s_A1 allTags.

   Definition ESPADA_TSet_8_2 :=
     [allQs, s_A1] <-$2 ESPADA_TSet_PRF_A1;
     [allTags, _] <-$2 oracleMap _ _ (F_bar_random lambda) nil allQs;
     ESPADA_TSet_PRF_A2 s_A1 allTags.
    
   
  Theorem ESPADA_TSet_8_1_equiv : 
    Pr[gInst ESPADA_TSet_7] == Pr[ESPADA_TSet_8_1].

    unfold ESPADA_TSet_7, ESPADA_TSet_8_1.
    unfold ESPADA_TSet_PRF_A1, ESPADA_TSet_PRF_A2.
    inline_first.
    comp_skip.
    inline_first.
    comp_simp.
    inline_first.
    comp_skip.
    comp_simp.
    comp_skip.
    eapply comp_spec_eq_impl_eq.
    eapply compFold_eq.
    eapply list_pred_eq.
    intuition.
    subst.
    eapply comp_spec_eq_refl.

    eapply eqRat_refl.

  Qed.

  Theorem ESPADA_TSet_8_2_equiv : 
    | Pr[ESPADA_TSet_8_1] - Pr[ESPADA_TSet_8_2] | <=
    (PRF_NA_Advantage (Rnd lambda) (Rnd lambda) F_bar _ _ ESPADA_TSet_PRF_A1 ESPADA_TSet_PRF_A2 ).

    eapply leRat_refl.
  Qed.

  Theorem ESPADA_TSet_8_equiv : 
    Pr[ESPADA_TSet_8_2] == Pr[gInst1 ESPADA_TSet_8].

    unfold ESPADA_TSet_8_2, ESPADA_TSet_8.
    unfold ESPADA_TSet_PRF_A1, ESPADA_TSet_PRF_A2.
    inline_first.
    do 2 (comp_skip; comp_simp).
    eapply eqRat_refl.

  Qed.

  Definition ESPADA_TSet_9_1 :=
    [t, q, s_A] <-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    inds <-
    (foreach  (x in q)
     CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec)) allQs x 0);
    allTags <-$ ([allTags, _] <-$2 oracleMap _ _ (F_bar_random lambda) nil allQs; ret allTags);
    ts <- map (arrayLookupList _ t) allQs;
    ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip allTags ts);
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) (Some (nil, initFree)) (flatten ts_recsList);
    tSet <- getTSet_opt loopRes;
    tags <- map (fun x => nth x allTags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).

  Theorem ESPADA_TSet_9_1_equiv : 
    Pr[gInst1 ESPADA_TSet_8] == Pr[ESPADA_TSet_9_1].

    unfold ESPADA_TSet_8, ESPADA_TSet_9_1.

    comp_skip; comp_simp.
    inline_first.
    comp_skip.
    comp_simp.
    reflexivity.

  Qed.

  Theorem ESPADA_TSet_9_equiv : 
    Pr[ESPADA_TSet_9_1] == Pr[gInst1 ESPADA_TSet_9].

    unfold ESPADA_TSet_9_1, ESPADA_TSet_9.

    comp_skip; comp_simp.
    comp_skip.
    unfold oracleMap.

    symmetry.
    rewrite <- evalDist_right_ident.
    unfold F_bar_random.
    unfold randomFunc.

    eapply eqRat_trans.
    comp_skip; comp_simp.
    eapply comp_spec_eq_impl_eq.
    eapply compMap_fold_equiv.
    eapply eqRat_refl.

    unfold compMap_fold.

    eapply comp_spec_impl_eq.
    eapply comp_spec_seq; eauto with inhabited.
    eapply (@compFold_spec _ _ _ (fun lsa p1 p2 => [rs, s] <-2 p2; p1 = rs /\ NoDup lsa /\ (forall a, In a lsa -> (s # a) = None))); intuition.

    eapply combineKeywords_NoDup.
    eapply removeDups_NoDup.
    unfold toW.
    eapply removeDups_NoDup.
    destruct d.
    intuition.
    subst.

    inversion H0; clear H0; subst.
    rewrite H3.
    inline_first.
    comp_skip.
    comp_simp.
    eapply comp_spec_ret; intuition.
    case_eq (eqb a1 a0); intuition.
    rewrite eqb_leibniz in H7.
    subst.
    intuition.
    simpl.
    rewrite H7.
    eapply H3.
    simpl.
    intuition.
    simpl; intuition.

    intuition.
    destruct b.
    intuition; subst.
    eapply comp_spec_ret; intuition.

    reflexivity.

  Qed.

  Definition ESPADA_TSet_10_1 :=
    [t, q, s_A] <-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t); 
    inds <-
    (foreach  (x in q)
     CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec)) allQs x 0);
    allTags <-$ (
              q_tags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
              other_tags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (skipn (length (removeDups _ q)) allQs);
              ret (q_tags ++ other_tags));
    ts <- map (arrayLookupList _ t) allQs;
    ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip allTags ts);
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) (Some (nil, initFree)) (flatten ts_recsList);
    tSet <- getTSet_opt loopRes;
    tags <- map (fun x => nth x allTags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).

  Definition ESPADA_TSet_10_2 :=
    [t, q, s_A] <-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    inds <-
    (foreach  (x in q)
     CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec)) allQs x 0);
    q_tags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
    other_tags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (skipn (length (removeDups _ q)) allQs);
    ts <- map (arrayLookupList _ t) allQs;
    ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip (q_tags ++ other_tags) ts);
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) (Some (nil, initFree)) (flatten ts_recsList);
    tSet <- getTSet_opt loopRes;
    tags <- map (fun x => nth x q_tags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).

  Definition ESPADA_TSet_10_3 :=
    [t, q, s_A] <-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    inds <-
    (foreach  (x in q)
     CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec)) allQs x 0);
    q_tags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
    other_tags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (skipn (length (removeDups _ q)) allQs);
    q_ts <- map (arrayLookupList _ t) (removeDups _ q);
    other_ts <- map (arrayLookupList _ t) (skipn (length (removeDups _ q)) allQs);
    q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip q_tags q_ts);
    other_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip other_tags other_ts);
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) (Some (nil, initFree)) (flatten q_ts_recsList);
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) loopRes (flatten other_ts_recsList);
    tSet <- getTSet_opt loopRes;
    tags <- map (fun x => nth x q_tags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).

  Theorem ESPADA_TSet_10_1_equiv : 
    Pr[gInst1 ESPADA_TSet_9] == Pr[ESPADA_TSet_10_1].

    unfold ESPADA_TSet_9, ESPADA_TSet_10_1.

    do 2 (comp_skip; comp_simp).
    unfold combineKeywords.
    rewrite skipn_app.
    eapply compMap_app.    

    reflexivity.
  Qed.

  Theorem ESPADA_TSet_10_2_equiv : 
    Pr[ESPADA_TSet_10_1] == Pr[ESPADA_TSet_10_2].

    unfold ESPADA_TSet_10_1, ESPADA_TSet_10_2.

    comp_skip; comp_simp.
    inline_first.
    comp_skip; comp_simp.
    inline_first.
    comp_skip.
    intuition.

    comp_skip.
    eapply eqRat_eq.
    f_equal.
    f_equal.
    f_equal.
    repeat rewrite map_map.
    eapply map_ext_in.
    intuition.

    erewrite app_nth1.
    trivial.
    eapply compMap_length in H0.
    rewrite H0.
    unfold combineKeywords.
    rewrite lookupIndex_app.
    eapply lookupIndex_lt_length.
    eapply in_removeDups.
    trivial.
    eapply in_removeDups.
    trivial.

  Qed.


  Theorem ESPADA_TSet_10_equiv : 
    Pr[ESPADA_TSet_10_2] == Pr[gInst1 ESPADA_TSet_10].

    unfold ESPADA_TSet_10_2, ESPADA_TSet_10.
    comp_skip; comp_simp.
    comp_skip; comp_simp.
    comp_swap_r.
    comp_skip; comp_simp.

    unfold combineKeywords.
    rewrite map_app.
    rewrite <- zip_app.
    rewrite map_app.
    
    rewrite flatten_app.
    
    eapply eqRat_trans.
    comp_skip.
    eapply compFold_app.
    eapply eqRat_refl.
    inline_first.
    comp_skip.

    eapply eqRat_refl.
    comp_skip.
    rewrite skipn_app.
    eapply eqRat_refl.
    reflexivity.

    rewrite map_length.
    eapply compMap_length; eauto.
    rewrite map_length.
    eapply eq_trans.
    eapply compMap_length.
    eauto.
    unfold combineKeywords.
    rewrite skipn_app.
    trivial.
  Qed.
  
   Definition ESPADA_TSet_11_1 :=
     [t, q, s_A] <-$3 A1;
     
    allQs <- combineKeywords (removeDups _ q) (toW t);
    inds <-
    (foreach  (x in q)
     CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec)) allQs x 0);
    qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
    q_ts <- map (arrayLookupList _ t) (removeDups _ q);
    q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip qTags q_ts);
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) (Some (nil, initFree)) (flatten q_ts_recsList);

    other_ts <- map (arrayLookupList _ t) (skipn (length (removeDups _ q)) allQs);
    otherTags_ts <-$ compMap _ (fun ls => tag <-$ {0, 1} ^ lambda; ret (tag, ls)) other_ts;
    other_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) otherTags_ts;
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) loopRes (flatten other_ts_recsList);
    
    tSet <- getTSet_opt loopRes;
    
    tags <- map (fun x => nth x qTags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).

   

   Lemma ESPADA_TSet_11_1_equiv : 
     Pr[gInst1 ESPADA_TSet_10] == Pr[ESPADA_TSet_11_1].

     unfold ESPADA_TSet_10, ESPADA_TSet_11_1.
     unfold initFree.

     do 3 (comp_skip; comp_simp).

     eapply comp_spec_impl_eq.
     eapply comp_spec_seq; eauto with inhabited.
     eapply (@compMap_spec _ _ _ _ _ _ _ (fun t p => t = fst p)); intuition.
     eapply list_pred_map_r.
     eapply list_pred_eq.

     intuition.
     destruct H4.
     intuition; subst.
     
     eapply comp_spec_eq_trans_l.
     eapply comp_spec_eq_symm.
     eapply comp_spec_right_ident.
     comp_skip; try eapply (oneVector lambda).
     eapply comp_spec_ret; intuition.

     intuition.
     eapply comp_spec_seq; eauto with inhabited.
     eapply compFold_eq.

     eapply list_pred_eq_gen.
     f_equal.
     f_equal.

     eapply compMap_support in H3.

     eapply list_pred_eq_impl_eq .
     eapply list_pred_impl.
     eapply list_pred_zip_l; eauto.

     eapply compMap_support in H2.
     eapply list_pred_map_r.
     
     eapply list_pred_symm.
     eapply H2.

     intuition.
     assert ((fun b a => True) b0 a1).
     trivial.
     eapply H7.

     intuition.
     simpl in *.
     subst.
     eapply H9.

     intuition.

     repeat simp_in_support.
     trivial.

     intuition.
     subst.
     eapply comp_spec_eq_refl.

     intuition.
     subst.
     eapply comp_spec_consequence.
     eapply comp_spec_eq_refl.
     intuition; subst; intuition.
   Qed.
     

  Definition ESPADA_TSet_11_2 :=
    [t, q, s_A] <-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
    q_ts <- map (arrayLookupList _ t) (removeDups _ q);
    q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip qTags q_ts);
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) (Some (nil, initFree)) (flatten q_ts_recsList);

    other_ts <- map (arrayLookupList _ t) (skipn (length (removeDups _ q)) allQs);
    ins_F <- map (fun ls => allNatsLt (length ls)) other_ts;
    outs_F <-$ (
           otherTags_ins <-$ compMap _ (fun ls => tag <-$ {0, 1} ^ lambda; ret (tag, ls)) ins_F;
           ret map (fun tag_ts => [tag,ins] <-2 tag_ts; map (F tag) ins) otherTags_ins);
    other_ts_recsList <- map (fun p => [outs_F_list, ls] <-2 p; numberedMap (fun i len p => [out_F, s_i] <-2 p; [b, bigL, bigK] <-3 out_F; (i, len, s_i, b, bigL, bigK)) (zip outs_F_list ls)) (zip outs_F other_ts);
 
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) loopRes (flatten other_ts_recsList);
    tSet <- getTSet_opt loopRes;
    inds <-
    (foreach  (x in q)
     CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec)) allQs x 0);
    tags <- map (fun x => nth x qTags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).

   
  Theorem ESPADA_TSet_11_2_equiv : 
    Pr[ESPADA_TSet_11_1] == Pr[ESPADA_TSet_11_2].

    unfold ESPADA_TSet_11_1, ESPADA_TSet_11_2.

    do 3 (comp_skip; comp_simp).

    inline_first.

    eapply comp_spec_eq_impl_eq.
    eapply comp_spec_seq; eauto with inhabited.
    eapply (@compMap_spec _ _ _ _ _ _ _ (fun p1 p2 => fst p1 = fst p2 /\ snd p2 = (allNatsLt (length (snd p1))))); intuition.
    eapply list_pred_map_r.
    eapply list_pred_eq.

    comp_skip; try eapply (oneVector lambda).
    destruct H4; intuition; subst.
    eapply comp_spec_ret; intuition.

    intuition.
    comp_simp.
    eapply comp_spec_seq; eauto with inhabited.
    eapply compFold_eq.

    eapply list_pred_eq_gen.

    eapply flatten_eq.
    eapply list_pred_eq_gen.

    eapply map_eq.
  
    eapply list_pred_impl.
    eapply list_pred_zip_r.
    eapply list_pred_map_l.

    eapply (@compMap_support _ _ (fun ls p => ls = snd p)) in H3.

    eapply list_pred_symm in H3.
    eapply list_pred_map_r_if in H3.
    eapply H3.

    intuition.
    repeat simp_in_support.
    trivial.

    eapply list_pred_map_l.
    eapply list_pred_symm in H4.
    eauto.

    eapply (compMap_support (fun a p => a = snd p)) in H2.
    eapply H2.

    intuition.
    repeat simp_in_support.
    trivial.

    intuition.

    Ltac exdest :=
      match goal with
          | [H : exists a : _, _ |- _ ] => destruct H
      end.

    repeat (try exdest; intuition).
    destruct x1.
    destruct x2.
    destruct b1; simpl in *; subst.
    
    eapply map_eq.
    eapply list_pred_impl.
    
    eapply list_pred_zip_r.
    
    eapply list_pred_allNatsLt.
    assert (length (zip (map (F b2) (allNatsLt (length b0))) b0) = length (zip (allNatsLt (length b0)) b0)).
    repeat rewrite zip_length.
    rewrite map_length.
    trivial.
    eapply allNatsLt_length.
    rewrite map_length.
    eapply allNatsLt_length.
    rewrite H6.
    eapply list_pred_allNatsLt.

    eapply list_pred_zip_l.
    eapply list_pred_map_l.
    eapply list_pred_allNatsLt.
    eapply list_pred_map_l.
    eapply list_pred_zip_r.
    eapply list_pred_allNatsLt.
    eapply list_pred_eq.
    eapply list_pred_symm.
    eapply list_pred_allNatsLt.
    eapply list_pred_zip_r.
    eapply list_pred_allNatsLt.
    eapply list_pred_allNatsLt.
    eapply list_pred_eq.

    intuition.
    repeat (try exdest; intuition).
    destruct b5; simpl in *; subst.
    destruct p; simpl in *; subst.

    remember (F b2 x1) as v1.
    destruct v1.
    destruct p.
    repeat f_equal.

    specialize (H6 (n, b6)).

    apply nth_zip in H6.
    intuition.
    subst.

    eapply nth_allNatsLt.

    eapply allNatsLt_length.

    rewrite zip_length.
    rewrite map_length.
    rewrite allNatsLt_length.
    trivial.

    rewrite map_length.
    eapply allNatsLt_length.

    intuition.
    subst.
    eapply comp_spec_eq_refl.
    intuition.
    subst.
    eapply comp_spec_eq_refl.
  Qed.

  Theorem ESPADA_TSet_11_equiv : 
    Pr[ESPADA_TSet_11_2] == Pr[gInst1 ESPADA_TSet_11].
    
    unfold ESPADA_TSet_11_2, ESPADA_TSet_11.
    unfold initFree.
    do 4 (comp_skip; comp_simp).
    
    specialize (@compMap_map_fission_eq (list nat) (Bvector lambda * list nat) (list (nat * Bvector lambda * Bvector (S lambda))) (list (nat * Bvector lambda * Bvector (S lambda))) _ _ _ 
                                     
                                     (map (fun ls : list (Bvector lambda) => allNatsLt (length ls))
                                          (map (arrayLookupList (list_EqDec bool_EqDec) t)
                                               (skipn (length (removeDups (list_EqDec bool_EqDec) l))
                                                      (combineKeywords (removeDups (list_EqDec bool_EqDec) l)
                                                                       (toW t)))))
                                     (fun ls => tag <-$ {0,1 } ^ lambda; ret (tag, ls))
                                     (fun ls : list nat => tag <-$ { 0 , 1 }^lambda; ret map (F tag) ls)
                                     (fun tag_ts : Bvector lambda * list nat =>
                                        [tag, ins]<-2 tag_ts; map (F tag) ins)
                                     (fun x => x)
               );
      intuition.
    
    eapply comp_spec_eq_impl_eq.
    eapply comp_spec_eq_trans.
    eapply H2.
    intuition.
    comp_skip; try eapply (oneVector lambda).
    eapply comp_spec_ret; intuition.

    eapply comp_spec_consequence.
    eapply compMap_spec.
    eapply list_pred_eq.
    intuition.
    subst.
    inline_first.
    comp_skip.

    eapply comp_spec_eq_refl.
    intuition.
    eapply list_pred_eq_impl_eq; trivial.
    reflexivity.

  Qed.

  Definition ESPADA_TSet_IPRF_A1 :=
    [t, q, s_A] <-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
    q_ts <- map (arrayLookupList _ t) (removeDups _ q);
    q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip qTags q_ts);
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) (Some (nil, initFree)) (flatten q_ts_recsList);
    other_ts <- map (arrayLookupList _ t) (skipn (length (removeDups _ q)) allQs);
    ins_F <- map (fun ls => allNatsLt (length ls)) other_ts;
    ret (ins_F, (s_A, qTags, loopRes, other_ts, allQs, q)).

  Definition ESPADA_TSet_IPRF_A2 s outs_F :=
    let '(s_A, qTags, loopRes, other_ts, allQs, q) := s in
    other_ts_recsList <- map (fun p => [locs, ls] <-2 p; numberedMap (fun i len loc_s_i => [loc, s_i] <-2 loc_s_i; [b, bigL, bigK] <-3 loc; (i, len, s_i, b, bigL, bigK)) (zip locs ls)) (zip outs_F other_ts);
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) loopRes (flatten other_ts_recsList);
    tSet <- getTSet_opt loopRes;
    inds <-
    (foreach  (x in q)
     CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec)) allQs x 0);
    tags <- map (fun x => nth x qTags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).

  Definition ESPADA_TSet_12_1 :=
    [ins_F, s] <-$2 ESPADA_TSet_IPRF_A1;
    outs_F <-$ compMap _ (fun ls => k <-$ {0, 1}^lambda; ret (map (F k) ls)) ins_F;
    ESPADA_TSet_IPRF_A2 s outs_F.

  Definition ESPADA_TSet_12_2 :=
    [ins_F, s] <-$2 ESPADA_TSet_IPRF_A1;
    outs_F <-$ compMap _ (fun lsD => [lsR, _] <-$2 oracleMap _ _ (F_random lambda bigB) nil lsD; ret lsR) ins_F;
    ESPADA_TSet_IPRF_A2 s outs_F.
    
  Theorem ESPADA_TSet_12_1_equiv : 
    Pr[gInst1 ESPADA_TSet_11] == Pr[ESPADA_TSet_12_1].

    unfold ESPADA_TSet_11, ESPADA_TSet_12_1.
    unfold ESPADA_TSet_IPRF_A1, ESPADA_TSet_IPRF_A2.

    inline_first; comp_skip.
    destruct x.
    destruct p.
    do 2 (inline_first; comp_skip).
    reflexivity.
    comp_ret_r.
    comp_skip.
    reflexivity.
 
  Qed.

  Theorem ESPADA_TSet_12_2_equiv : 
    | Pr[ESPADA_TSet_12_1] - Pr[ESPADA_TSet_12_2] | <= 
     (PRF_NAI_Advantage (Rnd lambda) (RndF_range lambda bigB) F _ _ ESPADA_TSet_IPRF_A1 ESPADA_TSet_IPRF_A2 ).

    reflexivity.

  Qed.

  Theorem ESPADA_TSet_12_equiv : 
    Pr[ESPADA_TSet_12_2] == Pr[gInst1 ESPADA_TSet_12].

    unfold ESPADA_TSet_12, ESPADA_TSet_12_2.
    unfold ESPADA_TSet_IPRF_A1, ESPADA_TSet_IPRF_A2.

    repeat (try inline_first; try comp_skip).
    (* comp_simp is slow again *)
    destruct x.
    destruct p.
    repeat (try inline_first; try comp_skip).
    eapply eqRat_refl.
    reflexivity.
    reflexivity.
  Qed.

  Theorem ESPADA_TSet_13_equiv : 
    Pr[gInst1 ESPADA_TSet_12] == Pr[gInst1 ESPADA_TSet_13].

    unfold ESPADA_TSet_12, ESPADA_TSet_13.
    unfold initFree.

    do 4 (comp_skip; comp_simp).

    eapply compMap_eq.
    eapply list_pred_map_l.
    eapply list_pred_eq.
    
    intuition.
    destruct H2.
    intuition; subst.
    unfold oracleMap.
    symmetry.
    eapply comp_spec_eq_impl_eq.
    eapply comp_spec_eq_trans.
    eapply compMap_fold_equiv.
    unfold compMap_fold.
    eapply comp_spec_eq_trans.
    eapply comp_spec_eq_symm.
    eapply comp_spec_right_ident.
    eapply comp_spec_eq_symm.
    
    eapply comp_spec_seq; try eapply nil.
    eapply (@compFold_spec' _ _ _ _ 
(fun lsa lsb p1 p2 => [rs, s] <-2 p1; rs = p2 /\ NoDup lsa /\ forall a, In a lsa -> (s # a) = None)); intuition.

    eapply allNatsLt_length.
    eapply allNatsLt_NoDup.
    
    subst.
    inversion H3; clear H3; subst.
    unfold F_random.
    unfold randomFunc.
    rewrite H6.
    unfold RndF_range.
    inline_first.
    comp_skip.
    inline_first.
    do 2 comp_skip.
    eapply comp_spec_ret; intuition.
    simpl.
    case_eq (eqb a3 a0); intuition.
    rewrite eqb_leibniz in H13.
    subst.
    intuition.
    simpl; intuition.

    intuition.
    subst.
    eapply comp_spec_eq_refl.

  Qed.

 
  Definition ESPADA_TSet_14_1 :=
    [t, q, s_A] <-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
    q_ts <- map (arrayLookupList _ t) (removeDups _ q);
    q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip qTags q_ts);
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) (Some (nil, initFree)) (flatten q_ts_recsList);
    
    other_ts <- map (fun q => ts <- arrayLookupList _ t q; numberedMap (fun i len s_i => (i, len, s_i)) ts) (skipn (length (removeDups _ q)) allQs);
    outs_F <-$ compMap _ (fun ls => compMap _ (fun _ => RndF_range lambda bigB) ls) other_ts;
    other_ts_recsList <- map (fun p => [locs, ls] <-2 p; map (fun loc_p => [loc, p] <-2 loc_p; [i, len, s_i] <-3 p; [b, bigL, bigK] <-3 loc; (i, len, s_i, b, bigL, bigK)) (zip locs ls)) (zip outs_F other_ts);
     loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) loopRes (flatten other_ts_recsList);
    tSet <- getTSet_opt loopRes;
    inds <-
    (foreach  (x in q)
     CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec)) allQs x 0);
    tags <- map (fun x => nth x qTags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).


  Theorem ESPADA_TSet_14_1_equiv : 
    Pr[gInst1 ESPADA_TSet_13] == Pr[ESPADA_TSet_14_1].

    unfold ESPADA_TSet_13, ESPADA_TSet_14_1.

    do 3 (comp_skip; comp_simp).
    reflexivity.

    assert ( forall x1, 
               eqRat
     (evalDist
        (compMap
           (list_EqDec
              (pair_EqDec (pair_EqDec nat_EqDec (Bvector_EqDec lambda))
                 (Bvector_EqDec (S lambda))))
           (fun ls : list (Bvector lambda) =>
            compMap
              (pair_EqDec (pair_EqDec nat_EqDec (Bvector_EqDec lambda))
                 (Bvector_EqDec (S lambda)))
              (fun _ : Bvector lambda => RndF_range lambda bigB) ls)
           (map (arrayLookupList (list_EqDec bool_EqDec) t)
              (skipn (length (removeDups (list_EqDec bool_EqDec) l))
                 (combineKeywords (removeDups (list_EqDec bool_EqDec) l)
                    (toW t))))) x1)
     (evalDist
        (compMap
           (list_EqDec
              (pair_EqDec (pair_EqDec nat_EqDec (Bvector_EqDec lambda))
                 (Bvector_EqDec (S lambda))))
           (fun ls : list (prod (prod nat nat) (Bvector lambda)) =>
            compMap
              (pair_EqDec (pair_EqDec nat_EqDec (Bvector_EqDec lambda))
                 (Bvector_EqDec (S lambda)))
              (fun _ : prod (prod nat nat) (Bvector lambda) =>
               RndF_range lambda bigB) ls)
           (map
              (fun q : Blist =>
               numberedMap
                 (fun (i len : nat) (s_i : Bvector lambda) =>
                  pair (pair i len) s_i)
                 (arrayLookupList (list_EqDec bool_EqDec) t q))
              (skipn (length (removeDups (list_EqDec bool_EqDec) l))
                 (combineKeywords (removeDups (list_EqDec bool_EqDec) l)
                    (toW t))))) x1)
     ).

    eapply (@compMap_eq).

    eapply list_pred_map_r.
    eapply list_pred_map_l.
    eapply list_pred_eq.

    intuition.
    repeat (try exdest; intuition).
    subst.
    eapply compMap_eq.
    unfold numberedMap.
    eapply list_pred_map_r.
    eapply list_pred_zip_r.
    eapply list_pred_allNatsLt.
    eapply list_pred_allNatsLt.
    eapply list_pred_eq.

    intuition.

    comp_skip.
    
    comp_skip.
    eapply comp_spec_eq_impl_eq.
    eapply (@compFold_eq _ _ eq).
    eapply list_pred_flatten_both.
    eapply list_pred_impl.
    eapply list_pred_eq_gen.
    eapply map_eq.

    assert (In x1
               (getSupport (compMap
               (list_EqDec
                  (pair_EqDec (pair_EqDec nat_EqDec (Bvector_EqDec lambda))
                     (Bvector_EqDec (S lambda))))
               (fun ls : list (prod (prod nat nat) (Bvector lambda)) =>
                compMap
                  (pair_EqDec (pair_EqDec nat_EqDec (Bvector_EqDec lambda))
                     (Bvector_EqDec (S lambda)))
                  (fun _ : prod (prod nat nat) (Bvector lambda) =>
                   RndF_range lambda bigB) ls)
               (map
                  (fun q : Blist =>
                   numberedMap
                     (fun (i len : nat) (s_i : Bvector lambda) =>
                      pair (pair i len) s_i)
                     (arrayLookupList (list_EqDec bool_EqDec) t q))
                  (skipn (length (removeDups (list_EqDec bool_EqDec) l))
                     (combineKeywords (removeDups (list_EqDec bool_EqDec) l)
                        (toW t))))))
            ).

    eapply getSupport_In_evalDist.
    intuition.
    eapply getSupport_In_evalDist.
    eauto.
    rewrite H2.
    intuition.

    apply (@compMap_support _ _ (fun p1 p2 => length p1 = length p2)) in H3.
    apply (@compMap_support _ _ (fun p1 p2 => length p1 = length p2)) in H4. 


    eapply list_pred_impl.
    eapply list_pred_zip_l.
    
    eapply list_pred_symm.
    eapply H3.

    eapply list_pred_zip_r.
    eapply list_pred_symm.

    eapply H4.
    eapply list_pred_eq.

    eapply H4.
    eapply list_pred_zip_r.
    eapply list_pred_symm.
    eapply H4.
    eapply list_pred_symm.
    eapply H3.

    eapply list_pred_map_l.
    eapply list_pred_map_r.
    eapply list_pred_eq.

    intuition.
    repeat (try exdest; intuition).
    destruct b0.
    simpl in *; subst.

    unfold numberedMap.
    eapply map_eq.

    eapply list_pred_impl.
    eapply list_pred_zip_l.
    eapply list_pred_allNatsLt.
    eapply list_pred_zip_r.
    eapply list_pred_map_r.
    unfold numberedMap in H11.
    rewrite map_length in H11.
    rewrite zip_length in H11.
    rewrite allNatsLt_length in H11.

    eapply list_pred_zip_r.
    eapply list_pred_allNatsLt.
    
    rewrite H11.
    eapply list_pred_allNatsLt.
    eapply list_pred_I.
    eauto.
    eapply allNatsLt_length.
    rewrite zip_length.
    eapply list_pred_symm.
    eapply list_pred_allNatsLt.
    
    unfold numberedMap in H11.
    rewrite map_length in H11.
    rewrite zip_length in H11.
    rewrite allNatsLt_length in H11.
    auto.
    eapply allNatsLt_length.

    eapply list_pred_map_l.
    eapply list_pred_zip_l.
    eapply list_pred_allNatsLt.
    
    unfold numberedMap in H11.
    rewrite map_length in H11.
    rewrite zip_length in H11.
    rewrite allNatsLt_length in H11.

    rewrite zip_length.
    rewrite H11.
    eapply list_pred_eq.
    rewrite H11.
    trivial.
    eapply allNatsLt_length.
    
    unfold numberedMap in H11.
    rewrite map_length in H11.
    rewrite zip_length in H11.
    rewrite allNatsLt_length in H11.
    rewrite zip_length.
    rewrite <- H11.
    eapply list_pred_symm.
    eapply list_pred_allNatsLt.
    auto.
    eapply allNatsLt_length.
    
    eapply list_pred_zip_r.
    eapply list_pred_map_r.
    eapply list_pred_zip_r.
    eapply list_pred_allNatsLt.
    
    unfold numberedMap in H11.
    rewrite map_length in H11.
    rewrite zip_length in H11.
    rewrite allNatsLt_length in H11.
    rewrite H11.
    eapply list_pred_allNatsLt.
    
    eapply allNatsLt_length.

    unfold numberedMap in H11.
    rewrite map_length in H11.
    rewrite zip_length in H11.
    rewrite allNatsLt_length in H11.
    eapply list_pred_I.
    auto.

    eapply allNatsLt_length.
    eapply list_pred_zip_r.
    unfold numberedMap in H11.
    rewrite map_length in H11.
    rewrite zip_length in H11.
    rewrite allNatsLt_length in H11.
    eapply list_pred_I.
    auto.
    eapply allNatsLt_length.
    eapply list_pred_eq.

    unfold numberedMap in H11.
    rewrite map_length in H11.
    rewrite zip_length in H11.
    rewrite allNatsLt_length in H11.
    eapply list_pred_I.
    auto.
    eapply allNatsLt_length.

    eapply list_pred_map_l.
    eapply list_pred_zip_l.
    eapply list_pred_allNatsLt.
    eapply list_pred_zip_r.

    unfold numberedMap in H11.
    rewrite map_length in H11.
    rewrite zip_length in H11.
    rewrite allNatsLt_length in H11.
    eapply list_pred_I.
    auto.
    eapply allNatsLt_length.

    unfold numberedMap in H11.
    rewrite map_length in H11.
    rewrite zip_length in H11.
    rewrite allNatsLt_length in H11.
    rewrite H11.
    eapply list_pred_symm.
    eapply list_pred_allNatsLt.
    eapply allNatsLt_length.
    eapply list_pred_symm.
    eapply list_pred_allNatsLt.

    eapply list_pred_zip_r.
    unfold numberedMap in H11.
    rewrite map_length in H11.
    rewrite zip_length in H11.
    rewrite allNatsLt_length in H11.
    eapply list_pred_I.
    auto.
    eapply allNatsLt_length.

    unfold numberedMap in H11.
    rewrite map_length in H11.
    rewrite zip_length in H11.
    rewrite allNatsLt_length in H11.
    eapply list_pred_I.
    auto.
    eapply allNatsLt_length.

    eapply list_pred_eq.

    intuition.
    repeat (try exdest; intuition).
    destruct b3.
    destruct x3.
    destruct x5.
    destruct x6.
    destruct x7.
    simpl in *; subst.
    pairInv.

    repeat f_equal.

    unfold numberedMap in H11.
    rewrite map_length in H11.
    rewrite zip_length in H11.
    rewrite allNatsLt_length in H11.
    rewrite zip_length.
    rewrite H11.
    trivial.
    rewrite H11.
    trivial.
    eapply allNatsLt_length.

    intuition.
    apply compMap_length in H6.
    auto.

    intuition.
    apply compMap_length in H6.
    auto.

    intuition.
   
    subst.
    eapply list_pred_eq.

    intuition; subst.
    eapply comp_spec_eq_refl.
    reflexivity.
  Qed.

   (* Now I can flatten the map *)
  Definition ESPADA_TSet_14_2 :=
    [t, q, s_A] <-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
    q_ts <- map (arrayLookupList _ t) (removeDups _ q);
    q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip qTags q_ts);
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) (Some (nil, initFree)) (flatten q_ts_recsList);  
    other_ts <- map (fun q => ts <- arrayLookupList _ t q; numberedMap (fun i len s_i => (i, len, s_i)) ts) (skipn (length (removeDups _ q)) allQs);
    outs_F <-$ compMap _ (fun _ => RndF_range lambda bigB) (flatten other_ts);
    other_ts_recsList <- map (fun e => [p1, p2] <-2 e; [i, len, s_i] <-3 p1; [b, bigL, bigK] <-3 p2; (i, len, s_i, b, bigL, bigK)) (zip (flatten other_ts) outs_F);
     loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) loopRes other_ts_recsList;
    tSet <- getTSet_opt loopRes;
    inds <-
    (foreach  (x in q)
     CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec)) allQs x 0);
    tags <- map (fun x => nth x qTags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).

  Theorem ESPADA_TSet_14_2_equiv : 
    Pr[ESPADA_TSet_14_1] == Pr[ESPADA_TSet_14_2].

    unfold ESPADA_TSet_14_1, ESPADA_TSet_14_2.

    do 3 (comp_skip; comp_simp).

    eapply comp_spec_eq_impl_eq.
    eapply comp_spec_seq; eauto with inhabited.
    eapply compMap_flatten; intuition.
    intuition.
    subst.

    eapply comp_spec_seq; eauto with inhabited.
    eapply compFold_eq.
    eapply list_pred_eq_gen.
    
    rewrite flatten_map_pair_eq.

    repeat rewrite unzip_zip_inv.
    unfold fst.
    unfold snd.
           
    eapply map_eq.

    eapply list_pred_impl.
    eapply list_pred_zip_eq_rev.

    eapply length_flatten_eq.
    eapply list_pred_symm.
    eapply compMap_support.
    eauto.

    intuition.
    apply compMap_length in H5.
    trivial.

    intuition.
    destruct b4.
    destruct p0.
    destruct p.
    intuition.
    repeat pairInv.
    trivial.

    apply compMap_length in H2.
    eapply H2.

    intuition.
    apply (@compMap_support _ _ (fun ls1 ls2 => length ls1 = length ls2)) in H2.

    eapply list_pred_zip_in in H2.
    eauto.

    eapply in_zip_swap;intuition.
    symmetry.
    eapply list_pred_length_eq.
    eauto.
    
    intuition.
    apply compMap_length in H6.
    auto.
  
    intuition.
    subst.
    eapply comp_spec_eq_refl.

    intuition.
    subst.
    eapply comp_spec_eq_refl.
  Qed.


  Definition ESPADA_TSet_14_3 :=
    [t, q, s_A] <-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
    q_ts <- map (arrayLookupList _ t) (removeDups _ q);
    q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip qTags q_ts);
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) (Some (nil, initFree)) (flatten q_ts_recsList);

    other_ts <- map (fun q => ts <- arrayLookupList _ t q; numberedMap (fun i len s_i => (i, len, s_i)) ts) (skipn (length (removeDups _ q)) allQs);
    outs_F <-$ compMap _ (fun p => [i, len, s_i] <-3 p; [b, bigL, bigK] <-$3 RndF_range lambda bigB; ret (i, len, s_i, b, bigL, bigK)) (flatten other_ts);
     loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) loopRes outs_F;
    tSet <- getTSet_opt loopRes;
    inds <-
    (foreach  (x in q)
     CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec)) allQs x 0);
    tags <- map (fun x => nth x qTags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).

  Theorem ESPADA_TSet_14_3_equiv : 
    Pr[ESPADA_TSet_14_2] == Pr[ESPADA_TSet_14_3].

    unfold ESPADA_TSet_14_2, ESPADA_TSet_14_3.

    do 3 (comp_skip; comp_simp).

    eapply comp_spec_eq_impl_eq.
    eapply comp_spec_seq; eauto with inhabited.
    eapply (@compMap_spec _ _ _ _ _ _ _ (fun p1 p2 => [b1, bigL1, bigK1] <-3 p1; let '(i, len, s_i, b2, bigL2, bigK2) := p2 in b1 = b2 /\ bigL1 = bigL2 /\ bigK1 = bigK2)); intuition.

    eapply list_pred_eq.

    subst.
    eapply comp_spec_eq_trans_l.
    eapply comp_spec_eq_symm.
    eapply comp_spec_right_ident.

    comp_skip; try eapply (oneVector (S lambda)).
    eapply comp_spec_ret; intuition.
 
    intuition.
     eapply (@compMap_support _ _ (fun p1 p2 => [i1, len1, s_i1] <-3 p1; let '(i2, len2, s_i2, b, bigL, bigK) := p2 in i1 = i2 /\ len1 = len2 /\ s_i1 = s_i2 )) in H3.
    eapply (@compMap_support _ _ (fun p1 p2 => True)) in H2.

    eapply comp_spec_seq; eauto with inhabited.
    eapply (@compFold_eq).

    eapply list_pred_map_l.
    eapply list_pred_zip_l.
    eapply list_pred_I.
    eapply eq_trans.
    eapply list_pred_length_eq.
    eapply H2.
    trivial.
    eapply H3.
    eauto.

    intuition.

    repeat (try exdest; intuition).
    destruct x1.
    destruct a3.
    simpl in *.
    destruct p0.
    destruct p1.
    destruct p0.
    destruct p1.
    destruct p0.
    destruct p0.
    intuition; subst.
    destruct p.
    destruct p.
    pairInv.
    simpl in *.
    
    intuition; subst.
    eapply comp_spec_eq_refl.

    intuition.
    subst.
    eapply comp_spec_eq_refl.

    intuition.
    intuition.

    repeat simp_in_support.
    destruct x1.
    destruct p.
    repeat simp_in_support.
    intuition.

  Qed.

  Definition ESPADA_TSet_14_4 :=
    [t, q, s_A] <-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
    q_ts <- map (arrayLookupList _ t) (removeDups _ q);
    q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip qTags q_ts);
    loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) (Some (nil, initFree)) (flatten q_ts_recsList);

    other_ts <- map (fun q => ts <- arrayLookupList _ t q; numberedMap (fun i len s_i => (i, len, s_i)) ts) (skipn (length (removeDups _ q)) allQs);
     loopRes <-$ compFold _ (foldBody_option _ (@ESPADA_TSetSetup_tLoop_14 lambda bigB)) loopRes (flatten other_ts);
    tSet <- getTSet_opt loopRes;
    inds <-
    (foreach  (x in q)
     CompFold.lookupIndex (EqDec_dec (list_EqDec bool_EqDec)) allQs x 0);
    tags <- map (fun x => nth x qTags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).


  Theorem ESPADA_TSet_14_4_equiv : 
    Pr[ESPADA_TSet_14_3] == Pr[ESPADA_TSet_14_4].

    unfold ESPADA_TSet_14_3, ESPADA_TSet_14_4.

    do 3 (comp_skip; comp_simp).
    rewrite <- evalDist_assoc.
    comp_skip.
    symmetry.
    eapply comp_spec_eq_impl_eq.
    eapply fold_map_fission_spec;
    intuition.

    subst.
    unfold foldBody_option.
    unfold ESPADA_TSetSetup_tLoop_6, ESPADA_TSetSetup_tLoop_14.

    destruct e.
    comp_simp.
    unfold RndF_range.
    inline_first.
    comp_skip.
    inline_first.
    comp_skip.
    inline_first.
    comp_skip.
    comp_simp.
    eapply comp_spec_eq_refl.

    comp_irr_r.
    eapply pair_EqDec; intuition.
    unfold RndF_range.
    wftac.
    
    intuition.

  Qed.

  Theorem ESPADA_TSet_14_equiv : 
    Pr[ESPADA_TSet_14_4] == Pr[gInst1 ESPADA_TSet_14].

    unfold ESPADA_TSet_14_4, ESPADA_TSet_14.

    do 3 (comp_skip; comp_simp).

    eapply comp_spec_eq_impl_eq.
    eapply (@compFold_eq _ _ 
            (fun p1 p2 => let '(i1, len1, v1, b, bigL, bigK) := p1 in 
                         let '(i2, len2, tag, v2) := p2 in
                         i1 = i2 /\ len1 = len2 /\  v1 = v2 /\ (b, bigL, bigK) = F tag i1)).
    eapply list_pred_flatten_both.
    eapply list_pred_map_l'.
    eapply list_pred_map_r'.
    eapply list_pred_impl.
    eapply list_pred_eq.
    
    intuition.
    subst.
    eapply list_pred_map_r'.
    eapply list_pred_map_l'.
    eapply list_pred_impl.
    eapply list_pred_eq.

    intuition.
    subst.
    remember (F a1 a2) as v1.
    destruct v1.
    destruct p.
    intuition.

    intuition.
    destruct a2.
    destruct p.
    destruct p.
    intuition.
    subst.
    unfold ESPADA_TSetSetup_tLoop_6, ESPADA_TSetSetup_tLoop_4.

    unfold foldBody_option.
    destruct acc.
    destruct p.
    remember (F b5 n) as v1.
    destruct v1.
    destruct p.

    comp_simp.
    pairInv.
    eapply comp_spec_eq_refl.
    eapply comp_spec_eq_refl.

    comp_skip.
    eapply comp_spec_eq_impl_eq.
    eapply compFold_eq.
    eapply list_pred_flatten_both.
    eapply list_pred_map_r'.
    eapply list_pred_map_l'.
    eapply list_pred_map_r'.
    eapply list_pred_impl.
    eapply list_pred_eq.

    intuition.
    subst.
    eapply list_pred_eq.

    intuition.
    subst.
    eapply comp_spec_eq_refl.
    reflexivity.
   Qed.

  Variable maxKeywords : nat.
  Hypothesis maxKeywords_correct : 
    (forall db q s_A,
      In (db, q, s_A) (getSupport A1) ->
      length (combineKeywords (removeDups _ q) (toW db)) <= maxKeywords)%nat.

  Variable PRF_NA_Adv : Rat.
  Hypothesis PRF_NA_Adv_correct_1 :
    (PRF_NA_Advantage (Rnd lambda) (Rnd lambda) F_bar _ _ ESPADA_TSet_PRF_A1 ESPADA_TSet_PRF_A2 ) <= PRF_NA_Adv.

  Hypothesis PRF_NA_Adv_correct_2: 
    forall i, 
      PRF_NA_Advantage (Rnd lambda) (@RndF_range lambda bigB) F _ _                       
        (B1 nil _ _ ESPADA_TSet_IPRF_A1 i) 
        (B2 (fun lsD => k <-$ {0, 1}^lambda; ret (map (F k) lsD))
            (fun lsD => [lsR, _] <-$2 oracleMap _ _ (RndR_func (@RndF_range lambda bigB) _) nil lsD; ret lsR)
            _ ESPADA_TSet_IPRF_A2
        )
      <= PRF_NA_Adv.

  Theorem ESPADA_TSet_once_secure : 
      | Pr[TSetReal _ (@ESPADA_TSetSetup_once lambda bigB bigS F F_bar) (@ESPADA_TSetGetTag lambda F_bar) A1 A2] -
      Pr[TSetIdeal (@L_T lambda) A1 A2 (@ESPADA_TSet_Sim_once lambda bigB bigS F)] | 
      <=  PRF_NA_Adv + (maxKeywords / 1) * PRF_NA_Adv.
      
      rewrite ESPADA_TSet_1_equiv.
      rewrite ESPADA_TSet_2_equiv.
      rewrite ESPADA_TSet_3_1_equiv.
      rewrite ESPADA_TSet_3_2_equiv.
      rewrite ESPADA_TSet_3_equiv.
      rewrite ESPADA_TSet_4_equiv.
      rewrite ESPADA_TSet_6_equiv.
      rewrite ESPADA_TSet_7_equiv.
      rewrite ESPADA_TSet_8_1_equiv.
      eapply leRat_trans.
      eapply ratDistance_le_trans.
      eapply ESPADA_TSet_8_2_equiv.
      rewrite ESPADA_TSet_8_equiv.
      rewrite ESPADA_TSet_9_1_equiv.
      rewrite ESPADA_TSet_9_equiv.
      rewrite ESPADA_TSet_10_1_equiv.
      rewrite ESPADA_TSet_10_2_equiv.
      rewrite ESPADA_TSet_10_equiv.
      rewrite ESPADA_TSet_11_1_equiv.
      rewrite ESPADA_TSet_11_2_equiv.
      rewrite ESPADA_TSet_11_equiv.
      rewrite ESPADA_TSet_12_1_equiv.
      eapply ratDistance_le_trans.
      eapply ESPADA_TSet_12_2_equiv.
      eapply eqRat_impl_leRat.
      rewrite <- ratIdentityIndiscernables.
      rewrite ESPADA_TSet_12_equiv.
      rewrite ESPADA_TSet_13_equiv.
      rewrite ESPADA_TSet_14_1_equiv.
      rewrite ESPADA_TSet_14_2_equiv.
      rewrite ESPADA_TSet_14_3_equiv.
      rewrite ESPADA_TSet_14_4_equiv.
      rewrite ESPADA_TSet_14_equiv.
      rewrite ESPADA_TSet_15_equiv.
      rewrite ESPADA_TSet_16_equiv.
      rewrite ESPADA_TSet_17_equiv.
      rewrite ESPADA_TSet_18_equiv.
      rewrite ESPADA_TSet_19_equiv.
      rewrite Ideal_equiv.

      intuition.

      rewrite <- ratAdd_0_r.
      eapply ratAdd_leRat_compat; intuition.
      rewrite PRF_NA_impl_NAI.
      reflexivity.
      intuition.
      unfold ESPADA_TSet_IPRF_A1 in *.
      repeat simp_in_support.
      destruct x.
      destruct p.
      repeat simp_in_support.
      repeat rewrite map_length.

      Theorem skipn_length : 
        forall (A : Type)(ls : list A)(n : nat),
          (length (skipn n ls) <= length ls - n)%nat.

        induction ls; intuition; simpl in *.
        destruct n; simpl; trivial.
        destruct n; simpl; trivial.
  
      Qed.

      rewrite skipn_length.
      eapply minus_le.
      eapply maxKeywords_correct.
      eauto.
      unfold RndF_range.
      wftac.
      wftac.

      eauto.
    Qed.

  Print Assumptions ESPADA_TSet_once_secure.

  (* State the previous theorem in terms of DistMult so it can be more easily used in the next stage of the proof. *)

  Require Import RepeatCore.

  Definition Repeat_Real t_q :=
    [t, q] <-2 t_q;
    [tSet, k_T] <-$2 ESPADA_TSetSetup_once bigB bigS F F_bar t;
    tags <-$ compMap (Bvector_EqDec lambda) (ESPADA_TSetGetTag lambda F_bar k_T) q;
    ret (tSet, tags).
  
  Definition Repeat_Ideal t_q :=
    [t, q] <-2 t_q;
    T_qs <- map (arrayLookupList (list_EqDec bool_EqDec) t) q;
    ESPADA_TSet_Sim_once lambda bigB bigS F (@L_T lambda t q) T_qs.

  Theorem ESPADA_TSet_once_eq_DistSingle : 
    (| Pr[TSetReal _ (@ESPADA_TSetSetup_once lambda bigB bigS F F_bar) (@ESPADA_TSetGetTag lambda F_bar) A1 A2] -
      Pr[TSetIdeal (@L_T lambda) A1 A2 (@ESPADA_TSet_Sim_once lambda bigB bigS F)] |) ==
    DistSingle_Adv Repeat_Real Repeat_Ideal A1 A2.

    unfold DistSingle_Adv, DistSingle_G, TSetReal, TSetIdeal, Repeat_Real, Repeat_Ideal.

    eapply ratDistance_eqRat_compat;
    repeat (inline_first; comp_skip; comp_simp; try reflexivity).
  Qed.

  
  Theorem ESPADA_TSet_DistSingle_secure : 
    DistSingle_Adv Repeat_Real Repeat_Ideal A1 A2  
    <= PRF_NA_Adv + (maxKeywords / 1) * PRF_NA_Adv.

    rewrite <- ESPADA_TSet_once_eq_DistSingle.
    apply ESPADA_TSet_once_secure.

  Qed.

End ESPADA_TSet_once.