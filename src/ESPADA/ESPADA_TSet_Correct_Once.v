Set Implicit Arguments.

Require Import FCF.

Require Import ESPADA_TSet_Once.
Require Import ESPADA_TSet_Once_Games.
Require Import TSet.
Require Import Array.
Require Import CompFold.
Require Import HasDups.
Require Import ESPADA_TSet_Correct_Once_Games.

Local Open Scope list_scope.


Section ESPADA_TSet_Once_correct.

  Variable lambda : posnat.
  Variable tSize bigB bigS maxMatches : posnat.

  Variable F : Bvector lambda -> nat -> nat * Bvector lambda * Bvector (S lambda).
  Variable F_bar : Bvector lambda -> Blist -> Bvector lambda.

  Hypothesis F_b_correct : 
    forall k b i v1 v2,
      (b, v1, v2) = F k i ->
      b < bigB.

  Variable A1 : Comp ((T lambda * list Blist)).
  Hypothesis A1_wf : well_formed_comp A1.
  
  Definition maxMatch (t : T lambda) n :=
    forall p, 
      In p t ->
      (length (snd p) <= n)%nat.
  
  Hypothesis maxMatches_correct : 
    forall t q,
      In (t, q) (getSupport A1) ->
      maxMatch t maxMatches.

  Definition ESPADA_TSetRetrieve := ESPADA_TSetRetrieve lambda maxMatches F.
  Notation "'gInst' g" := (@g lambda bigB bigS maxMatches F F_bar A1) (at level 90).
  Notation "'gInst1' g" := (@g lambda bigB bigS maxMatches F A1) (at level 90).

   Theorem G1_secure_1_equiv : 
      Pr[gInst ESPADA_TSetCorr_G1] == 
      Pr[ESPADA_TSet_1 bigB bigS F F_bar
           ([t, l] <-$2 A1; ret (t, l, (t, l))) 
           (fun s p => [t, q] <-2 s; [tSet_opt, tags] <-2 p;
             tSet <- match tSet_opt with | None => nil | Some x => x end;
            ret ((if tSet_opt then true else false) && negb
         (eqb (foreach  (x in tags)ESPADA_TSetRetrieve tSet x)
             (foreach  (x in q)arrayLookupList (list_EqDec bool_EqDec) t x))))].

     intuition.
     unfold ESPADA_TSetCorr_G1, ESPADA_TSet_1, ESPADA_TSetSetup_trial.
     comp_simp.
     do 3 (inline_first; comp_skip; comp_simp).
     reflexivity.
     eapply evalDist_ret_eq.
     unfold getTSet_opt.
     destruct x0; simpl.
     unfold  ESPADA_TSetRetrieve.
     f_equal.

     trivial.
  
   Qed.

   Theorem G3_secure_9_equiv : 
       Pr[ESPADA_TSet_9 bigB bigS F
            ([t, l] <-$2 A1; ret (t, l, (t, l))) 
           (fun s p => [t, q] <-2 s; [tSet_opt, tags] <-2 p;
             tSet <- match tSet_opt with | None => nil | Some x => x end;
            ret ((if tSet_opt then true else false) && negb
         (eqb (foreach  (x in tags)ESPADA_TSetRetrieve tSet x)
             (foreach  (x in q)arrayLookupList (list_EqDec bool_EqDec) t x))))]
         == Pr[ gInst1 ESPADA_TSetCorr_G3].

     intuition.
     unfold ESPADA_TSet_9, ESPADA_TSetCorr_G3.
     comp_simp.
     do 3 (inline_first; comp_skip; comp_simp).
     reflexivity.

     unfold getTSet_opt.
     destruct x0.
     simpl.
     reflexivity.
     simpl.
     intuition.
   Qed.

   Theorem ESPADA_TSetCorr_G1_G3_close : 
       | Pr[gInst ESPADA_TSetCorr_G1] - Pr[gInst1 ESPADA_TSetCorr_G3] | 
       <= 
       PRF.PRF_NA_Advantage ({ 0 , 1 }^lambda) ({ 0 , 1 }^lambda) F_bar
                            _ _
     (ESPADA_TSet_PRF_A1 _ ([t, l] <-$2 A1; ret (t, l, (t, l))))
     (ESPADA_TSet_PRF_A2 bigB bigS F
        (fun (s : (T lambda * list Blist))
           (p : option (TSet lambda) * list (Bvector lambda)) =>
           [t, q0] <-2 s;
         [tSet_opt, tags]<-2 p;
         tSet <- match tSet_opt with
                 | Some x => x
                 | None => nil
                 end;
         ret ((if tSet_opt then true else false) && negb
               (eqb (foreach  (x in tags)ESPADA_TSetRetrieve tSet x)
                  (foreach  (x in q0)
                   arrayLookupList (list_EqDec bool_EqDec) t x))))).

     intuition.
     rewrite G1_secure_1_equiv.
     rewrite <- G3_secure_9_equiv.
     rewrite ESPADA_TSet_2_equiv.
     rewrite ESPADA_TSet_3_1_equiv.
     rewrite ESPADA_TSet_3_2_equiv.
     rewrite ESPADA_TSet_3_equiv.
     rewrite ESPADA_TSet_4_equiv.
     rewrite ESPADA_TSet_6_equiv.
     rewrite ESPADA_TSet_7_equiv.
     rewrite ESPADA_TSet_8_1_equiv.
     
     rewrite <- ESPADA_TSet_9_equiv.
     rewrite <- ESPADA_TSet_9_1_equiv.
     rewrite <- ESPADA_TSet_8_equiv.
     
     eapply ESPADA_TSet_8_2_equiv.
     apply F_bar.

     apply (fun x => (pos 1, pos 1)).
     apply (fun x => (pos 1, pos 1)).

     intuition.

     apply (fun x => (pos 1, pos 1)).
     apply (fun x => (pos 1, pos 1)).
     apply (fun x => (pos 1, pos 1)).
   Qed.

   Theorem ESPADA_TSetCorr_G3_G4_equiv : 
     Pr[gInst1 ESPADA_TSetCorr_G3] == Pr[gInst1 ESPADA_TSetCorr_G4].

     intuition.
     unfold ESPADA_TSetCorr_G3, ESPADA_TSetCorr_G4.
     comp_simp.
     comp_skip; comp_simp.
     comp_skip.
     comp_skip.
     eapply evalDist_ret_eq.
     f_equal.
     
     repeat rewrite map_map.
     unfold combineKeywords.

     assert (
         (@map Blist (list (Vector.t bool (posnatToNat lambda)))
           (fun x1 : Blist =>
            ESPADA_TSetRetrieve (@getTSet lambda x0)
              (@nth (Bvector (posnatToNat lambda))
                 (@lookupIndex Blist
                    (@EqDec_dec Blist (@list_EqDec bool bool_EqDec))
                    (@app Blist
                       (@removeDups Blist (@list_EqDec bool bool_EqDec) l)
                       (@removePresent Blist
                          (@EqDec_dec Blist (@list_EqDec bool bool_EqDec))
                          (@removeDups Blist (@list_EqDec bool bool_EqDec) l)
                          (@toW lambda t))) x1 O) x
                 (@Vector.const bool false (posnatToNat lambda)))) l)

           =
           (foreach  (x1 in l)
      ESPADA_TSetRetrieve (getTSet x0)
        (nth
           (lookupIndex (EqDec_dec (list_EqDec bool_EqDec))
              (removeDups (list_EqDec bool_EqDec) l) x1 0) x (Vector.const false lambda)))
             ).

     eapply map_ext_in.
     intuition.
  
     rewrite lookupIndex_app.
     trivial.
     apply (fun x => (pos 1, pos 1)).
     eapply in_removeDups.
     trivial.
     
     unfold ESPADA_TSetRetrieve in *.
     rewrite H2.
     clear H2.

     assert (
         (@map (Bvector (posnatToNat lambda))
           (list (Vector.t bool (posnatToNat lambda)))
           (fun x1 : Bvector (posnatToNat lambda) =>
            ESPADA_TSetRetrieve (@getTSet lambda x0) x1)
           (@firstn (Bvector (posnatToNat lambda))
              (@length Blist
                 (@removeDups Blist (@list_EqDec bool bool_EqDec) l)) x))
           =
             (foreach  (x1 in (removeDups _ l))
                       ESPADA_TSetRetrieve (getTSet x0)
                       (nth
           (lookupIndex (EqDec_dec (list_EqDec bool_EqDec))
              (removeDups (list_EqDec bool_EqDec) l) x1 0) x
           (Vector.const false lambda)))
               ).

     eapply map_eq.

     eapply list_pred_impl.
  
     Theorem lp_G3_G4_equiv :
       forall q x,
         NoDup q ->
         length x >= length q ->
       list_pred
         (fun (a : Bvector lambda) (b : list bool) =>
            a =
            nth
              (lookupIndex (EqDec_dec (list_EqDec bool_EqDec))
                           q b 0) x
              (Vector.const false lambda))
         (firstn (length q) x)
         q.
       
       induction q; destruct x; intuition; simpl in *.
       econstructor.
       econstructor.
       omega.

       econstructor.
       destruct (EqDec_dec (list_EqDec bool_EqDec) a a); trivial.
       congruence.

       inversion H; clear H; subst.

       eapply list_pred_impl'.
       eapply IHq.
       trivial.
       omega.
       intuition.
       subst.
       destruct ( EqDec_dec (list_EqDec bool_EqDec) b a).
       subst.
       intuition.

       trivial.

     Qed.

     eapply lp_G3_G4_equiv.
     eapply removeDups_NoDup.
     eapply compMap_length in H0.
     eapply Nat.le_stepr.
     Focus 2.
     symmetry.
     eapply H0.
     unfold combineKeywords.
     rewrite app_length.
     rewrite <- plus_0_r at 1.
     eapply plus_le_compat; intuition.

     intuition.
     subst.
     trivial.

     unfold ESPADA_TSetRetrieve in *.
     rewrite H2.
     clear H2.

     case_eq (eqb (foreach  (x1 in l)
      ESPADA_TSet_Correct_Once_Games.ESPADA_TSetRetrieve lambda maxMatches F (getTSet x0)
        (nth
           (lookupIndex (EqDec_dec (list_EqDec bool_EqDec))
              (removeDups (list_EqDec bool_EqDec) l) x1 0) x
           (Vector.const false lambda)))
     (foreach  (x1 in l)arrayLookupList (list_EqDec bool_EqDec) t x1)); intuition.
     rewrite eqb_leibniz in H2.
   
     unfold ESPADA_TSetRetrieve in *.
     eapply map_eq_subset in H2.
     rewrite H2.
     repeat rewrite eqb_refl.
     trivial.
     intuition.
     eapply removeDups_in.
     trivial.

     case_eq (eqb
                         (@map (list bool) (list (Vector.t bool (posnatToNat lambda)))
           (fun x1 : list bool =>
             ESPADA_TSet_Correct_Once_Games.ESPADA_TSetRetrieve lambda maxMatches F 
                                                                (@getTSet lambda x0)
              (@nth (Bvector (posnatToNat lambda))
                 (@lookupIndex (list bool)
                    (@EqDec_dec (list bool) (@list_EqDec bool bool_EqDec))
                    (@removeDups (list bool) (@list_EqDec bool bool_EqDec) l)
                    x1 O) x (@Vector.const bool false (posnatToNat lambda))))
           (@removeDups Blist (@list_EqDec bool bool_EqDec) l))
        (@map (list bool) (list (Bvector (posnatToNat lambda)))
           (fun x1 : list bool =>
            @arrayLookupList (list bool) (Bvector (posnatToNat lambda))
              (@list_EqDec bool bool_EqDec) t x1)
           (@removeDups Blist (@list_EqDec bool bool_EqDec) l))
        ); intuition.
     
     rewrite eqb_leibniz in H3.
     eapply map_eq_subset in H3.
     rewrite H3 in H2.
     rewrite eqb_refl  in H2.
     discriminate.
     intuition.
     eapply in_removeDups; eauto.
   Qed.
  

   Definition tSet_6_Corr_5_equiv (t1 : TSet lambda)(t2 : TSetCorr_5 lambda) := 
     list_pred 
       (fun x y =>
          list_pred 
            (fun a b =>
               match a with
                 | None => b = None
                 | Some z1 =>
                   match b with
                     | None => False
                     | Some z2 =>
                       fst z1 = fst z2 /\
                       snd z1 = snd (snd z2)
                   end
               end) x y)
       t1 t2.

   Theorem ESPADA_TSetSetup_6_Corr_5_tLoop_equiv : 
     forall t1 t2,
       tSet_6_Corr_5_equiv t1 t2 ->
       forall a1 a2 f,
         (let  '(q0, tag, i, len, s_i, b, bigL, bigK) := a2 in
                    (i, len, s_i, b, bigL, bigK) = a1) ->
       comp_spec (fun a b => 
                 match a with
                   | None => b = None
                   | Some x => 
                     match b with
                       | None => False
                       | Some y =>
                         snd x = snd y /\
                         tSet_6_Corr_5_equiv (fst x) (fst y)
                     end
                 end) 
     (ESPADA_TSetSetup_tLoop_6 (t1, f) a1)
     (ESPADA_TSetSetup_tLoop_Corr_5 (t2, f) a2).

     intuition.
     unfold ESPADA_TSetSetup_tLoop_6, ESPADA_TSet_Once_Games.ESPADA_TSetSetup_tLoop_6 , ESPADA_TSetSetup_tLoop_Corr_5.
     pairInv.
     unfold setLet.
     comp_skip.
     apply None.
     apply None.
     destruct b4.
     eapply comp_spec_ret; intuition.
     unfold fst.
     unfold tSetUpdate, tSetUpdate_Corr_5.
     unfold tSet_6_Corr_5_equiv.

     eapply list_pred_listReplace.
     eapply H.

     eapply list_pred_listReplace.

     eapply list_pred_nth.
     eapply H.
     econstructor.

    
     unfold fst, snd.
     intuition.
     trivial.

     econstructor.

     eapply comp_spec_ret; intuition.

   Qed.
       
   Theorem ESPADA_TSetSetup_6_Corr_5_equiv : 
     forall ls1 ls2,
       list_pred (fun x y =>
                    let '(q0, tag, i, len, s_i, b, bigL, bigK) := y in
                    (i, len, s_i, b, bigL, bigK) = x)
                 ls1 ls2 ->
       forall t1 t2 f,
       tSet_6_Corr_5_equiv t1 t2 ->
       comp_spec (fun a b => 
                 match a with
                   | None => b = None
                   | Some x => 
                     match b with
                       | None => False
                       | Some y =>
                         snd x = snd y /\
                         tSet_6_Corr_5_equiv (fst x) (fst y)
                     end
                 end) 
     (compFold _
        (foldBody_option _ (@ESPADA_TSetSetup_tLoop_6 lambda)) (Some (t1, f)) ls1)
     (compFold _
        (foldBody_option _
           (@ESPADA_TSetSetup_tLoop_Corr_5 lambda)) (Some (t2, f)) ls2).

     induction 1; intuition. simpl in *.

     eapply comp_spec_ret; intuition.
   
     eapply comp_spec_eq_trans_l.
     eapply compFold_cons.
     eapply comp_spec_eq_trans_r.
     Focus 2.
     eapply comp_spec_eq_symm.
     eapply compFold_cons.
     comp_skip.
     eapply None.
     eapply None.
     unfold foldBody_option.
     eapply ESPADA_TSetSetup_6_Corr_5_tLoop_equiv.

     trivial.
     intuition.

     simpl in H4.
     destruct a.
     destruct b.
     destruct p, p0.
     intuition.
     simpl in H5.
     subst.
     eapply IHlist_pred.
     trivial.
     intuition.
     subst.


     eapply comp_spec_consequence.
     eapply (@compFold_spec' _ _ _ _ (fun _ _ c d => c = None /\ d = None)).
     eapply list_pred_length_eq.
     eapply H0.
     intuition.

     intuition.
     subst.
     unfold foldBody_option.
     eapply comp_spec_ret; intuition.
     
     intuition.
     intuition.
     subst.
     trivial.

   Qed.

   Theorem ESPADA_TSetCorr_G4_G5_equiv : 
       Pr[ gInst1 ESPADA_TSetCorr_G4] == Pr[ESPADA_TSetCorr_G5 bigB bigS maxMatches F A1].

     intuition.
     unfold ESPADA_TSetCorr_G4, ESPADA_TSetCorr_G5.
     comp_simp.
     comp_skip; comp_simp.
     comp_skip.
     eapply comp_spec_eq_impl_eq.
     comp_skip.
     eapply ESPADA_TSetSetup_6_Corr_5_equiv.
   
     assert (length (combineKeywords (removeDups (list_EqDec bool_EqDec) l) (toW t)) =
   length x).
     eapply compMap_length in H0.
     intuition.

     eapply list_pred_flatten_both.
     eapply list_pred_map_l'.
     eapply list_pred_map_r'.
     eapply list_pred_impl.
     eapply list_pred_zip_r.
     eapply list_pred_zip_l.
     eapply list_pred_I; intuition.
  
     eapply list_pred_map_r.
     eapply list_pred_eq.
     eapply list_pred_map_r.
     eapply list_pred_I; intuition.

     eapply list_pred_zip_l.
     eapply list_pred_I; intuition.
 
     eapply list_pred_zip_r.
     eapply list_pred_map_r.
     eapply list_pred_I; intuition.

     eapply list_pred_I; intuition.
 
     eapply list_pred_map_l.
     eapply list_pred_eq.
     eapply list_pred_zip_r.
     eapply list_pred_map_r.
     eapply list_pred_I; intuition.

     eapply list_pred_eq.
     eapply list_pred_map_l.
     eapply list_pred_I; intuition.

     eapply list_pred_map_l.
     eapply list_pred_zip_r.
     eapply list_pred_map_r.
     eapply list_pred_I; intuition.

     eapply list_pred_I; intuition.
  
     eapply list_pred_map_l.
     eapply list_pred_eq.
     intuition.
     
     Ltac exdest :=
       match goal with
         | [H : exists _ : _, _ |- _] => destruct H
       end.

     repeat exdest; intuition; simpl in *; subst.
     repeat exdest; intuition; simpl in *; subst.
     destruct b0.
     simpl in *. subst.
     
     unfold numberedMap.
     destruct p.
     eapply list_pred_map_l'.
     eapply list_pred_map_r'.
     rewrite H12.
     eapply list_pred_impl.
     eapply list_pred_eq.
     intuition.
     subst.
     simpl.

     remember ( F b0 a0) as z.
     destruct z.
     destruct p.
     trivial.

     econstructor.
     
     eapply comp_spec_ret; intuition.
     destruct a.
     destruct b.
     destruct p, p0.
     simpl in *.
     intuition; subst.
     f_equal.
     f_equal.
     
     eapply map_ext_in.
     intuition.

     Theorem ESPADA_TSetRetrieve_Corr_5_arrayLookup_eq: 
       forall t1 t2,
         tSet_6_Corr_5_equiv t1 t2 ->
         forall n a,
         arrayLookupOpt (Bvector_EqDec lambda) (nth n t1 nil) a =
         match (arrayLookupOpt (Bvector_EqDec lambda) (nth n t2 nil) a) with
           | Some (x, y) => Some y
           | None => None
         end.
                 
       intuition.

       eapply (@list_pred_nth _ _ _ (fun x y => arrayLookupOpt _ x a = 
                                         match arrayLookupOpt (Bvector_EqDec lambda) y a with
                                           | Some (_, y) => Some y
                                           | None => None
                                         end)).
       eapply list_pred_impl.
       eapply H.
       intuition.

       specialize (@list_pred_arrayLookupOpt _ _ _ (fun z1 z2 => z1 = snd (z2)) _ _ _ H1 a); intuition.
       case_eq (arrayLookupOpt (Bvector_EqDec lambda) a0 a ); intuition;
       rewrite H3 in H2.
       destruct H2.
       intuition.
       subst.
       rewrite H4.
       destruct x.
       trivial.

       rewrite H2.
       trivial.

       simpl.
       trivial.

     Qed.


     Theorem ESPADA_TSetRetrieve_tLoop_Corr_5_equiv : 
       forall i t1 t2 a,
         tSet_6_Corr_5_equiv t1 t2 ->
         ESPADA_TSetRetrieve_tLoop lambda F t1 a i = ESPADA_TSetRetrieve_tLoop_Corr_5 F t2 a i.

       intuition.
       unfold  ESPADA_TSetRetrieve_tLoop,  ESPADA_TSetRetrieve_tLoop_Corr_5.
       remember (F a i).
       comp_simp.
       rewrite (@ESPADA_TSetRetrieve_Corr_5_arrayLookup_eq _ t2).
       case_eq ( arrayLookupOpt (Bvector_EqDec lambda) (nth n t2 nil) b0); intuition.
       destruct p.
       trivial.
       trivial.
     Qed.

     Theorem ESPADA_TSetRetrieve_h_Corr_5_equiv : 
       forall fuel i t1 t2 a,
         tSet_6_Corr_5_equiv t1 t2 ->
         ESPADA_TSetRetrieve_h lambda F t1 a i fuel = ESPADA_TSetRetrieve_h_Corr_5 F t2 a i fuel.

       induction fuel; intuition; simpl in *.
       rewrite (@ESPADA_TSetRetrieve_tLoop_Corr_5_equiv _ _ t2).
       remember (ESPADA_TSetRetrieve_tLoop_Corr_5 F t2 a i).
       destruct o; trivial.
       comp_simp.
       f_equal.
       destruct b; trivial.
       eauto.
       trivial.
     Qed.

     Theorem ESPADA_TSetRetrieve_Corr_5_equiv : 
       forall t1 t2 a,
         tSet_6_Corr_5_equiv t1 t2 ->
         ESPADA_TSetRetrieve t1 a = ESPADA_TSetRetrieve_Corr_5 maxMatches F t2 a.

       intuition.
       unfold ESPADA_TSetRetrieve, ESPADA_TSetRetrieve_Corr_5, ESPADA_TSet_Correct_Once_Games.ESPADA_TSetRetrieve.
       unfold ESPADA_TSet.ESPADA_TSetRetrieve.
       eapply ESPADA_TSetRetrieve_h_Corr_5_equiv.
       trivial.

     Qed.
     
     eapply ESPADA_TSetRetrieve_Corr_5_equiv.
     trivial.
     intuition.
     subst.
     trivial.
   Qed.
    

   Theorem ESPADA_TSetCorr_G5_le_G6 : 
       Pr[ gInst1 ESPADA_TSetCorr_G5 ] <= Pr[ gInst1 ESPADA_TSetCorr_G6 ].

     intuition.
     unfold ESPADA_TSetCorr_G5, ESPADA_TSetCorr_G6.
     comp_simp.
     comp_skip; comp_simp.
     comp_skip.
     comp_skip.
     eapply comp_spec_impl_le.
     eapply comp_spec_ret.
     intuition.
     destruct x0; simpl in *; trivial.

     destruct ( labelCollision_6 (fst p)); trivial.
     
   Qed.
   

   Definition ESPADA_TSetSetup_tLoop_Corr_6_1 (tSet : TSetCorr_7 lambda)
  (e :  Blist * Bvector lambda * nat * nat * Vector.t bool lambda * nat * Bvector lambda *
       Vector.t bool (S lambda)) :=
     (let '(q, tag, i, len, s_i, b, bigL, bigK) := e in
        bet <- (if eq_nat_dec (S i) len then false else true);
        newRecord <- (bigL, ((q, tag, i, len, s_i, b, bigK), (Vector.cons bool bet lambda s_i xor bigK)));
        newBucket <- (nth b tSet nil) ++ (newRecord :: nil); 
        ret listReplace tSet b newBucket nil
      ).

   Definition ESPADA_TSetCorr_G6_1 :=
     [t, q] <-$2 A1;
     q <- removeDups _ q;
     allQs <- combineKeywords q (toW t);
     allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
     ts <- map (arrayLookupList _ t) allQs;
     ts_recsList <- map (fun p => [q, tag, ls] <-3 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (q, tag, i, len, s_i, b, bigL, bigK)) ls) (zip (zip allQs allTags) ts);
     tSet <-$ compFold _ ( ESPADA_TSetSetup_tLoop_Corr_6_1) nil (flatten ts_recsList);
     tags <- firstn (length q) allTags;
     bad <- negb
         (eqb (foreach  (x in tags)ESPADA_TSetRetrieve_Corr_7 maxMatches F tSet x)
             (foreach  (x in q)arrayLookupList (list_EqDec bool_EqDec) t x));
     ret (labelCollision_7 ( tSet) || bad).

 
   Require Import Permutation.
   Require Import RndListElem.

   Theorem TSetSetup_5_6_1_spec : 
     forall d p x,
       (forall n, Permutation (getSomes (nth n (fst p) nil)) (nth n d nil)) /\
       (forall b n, In n (nth b (snd p) nil) -> nth n (nth b (fst p) nil) None = None) /\
       (forall n, NoDup (nth n (snd p) nil)) ->

     comp_spec
     (fun (a : option (list (list (option (TSetCorr_5_Record lambda))) * FreeList))
        (b6 : list (list (TSetCorr_5_Record lambda))) =>
      match a with
      | Some p0 =>
        (forall n, Permutation (getSomes (nth n (fst p0) nil)) (nth n b6 nil)) /\ 
      
           (forall b n, In n (nth b (snd p0) nil) -> nth n (nth b (fst p0) nil) None = None) /\
           (forall n, NoDup (nth n (snd p0) nil))
      | None => True
      end) (ESPADA_TSetSetup_tLoop_Corr_5 p x)
     (ESPADA_TSetSetup_tLoop_Corr_6_1 d x).

     intros.
     unfold ESPADA_TSetSetup_tLoop_Corr_5, ESPADA_TSetSetup_tLoop_Corr_6_1.
     comp_simp.
     comp_irr_l.
     eapply RndListElem.rndListElem_wf.
   
     destruct a.
     eapply comp_spec_ret; intros.
     unfold tSetUpdate_Corr_5.
     
     unfold fst.
     intuition.
     
     destruct (eq_nat_dec n3 n). subst.
     repeat rewrite nth_listReplace_eq.

     eapply perm_trans.
     eapply listReplace_getSomes_Permutation.
     eapply H.
     eapply rndListElem_support.
     trivial.
     trivial.
     eapply Permutation_cons_append.

     rewrite nth_listReplace_ne; intuition.
     rewrite nth_listReplace_ne; intuition.

     unfold snd in *.
     destruct (eq_nat_dec b2 n); subst.
     rewrite nth_listReplace_eq in *.
     destruct (eq_nat_dec n3 n2); subst.
     
     exfalso.
     eapply removeFirst_NoDup_not_in.
     eapply H2.
     eauto.

     rewrite nth_listReplace_ne; intuition.
     eapply H.
     eapply removeFirst_in_iff.
     eapply H4.

     rewrite nth_listReplace_ne in H4; intuition.
     rewrite nth_listReplace_ne; intuition.
     unfold snd.
     destruct (eq_nat_dec n3 n); subst.
     rewrite nth_listReplace_eq.
     eapply removeFirst_NoDup.
     eauto.
     rewrite nth_listReplace_ne.
     eauto.
     intuition.

     eapply comp_spec_ret; intuition.
   Qed.
     
   Theorem perm_labelIn_7_eq : 
     forall ls1 ls2,
       Permutation ls1 ls2 ->
       forall b,
         (@labelIn_7 lambda) ls1 b = labelIn_7 ls2 b.
     
     induction 1; intuition; simpl in *.
     
     destruct x.
     case_eq (eqbBvector b b0); intuition.
     
     destruct y.
     destruct x.
     case_eq (eqbBvector b b0); intuition.
     destruct (eqbBvector b b1); intuition.

     rewrite IHPermutation1.
     eapply IHPermutation2.
     
   Qed.

   Theorem perm_bucketCollision_7_eq : 
     forall ls1 ls2,
       Permutation ls1 ls2 ->
       (@bucketLabelCollision_7 lambda) ls1 = 
       bucketLabelCollision_7 ls2.
     
     induction 1; intuition; simpl in *.
     
     destruct x.
     erewrite perm_labelIn_7_eq.
     f_equal.
     intuition.
     trivial.
     
     destruct y.
     destruct x.
     case_eq (eqbBvector b b0); intuition.
     simpl.
     apply eqbBvector_sound in H.
     subst.
     rewrite eqbBvector_complete.
     simpl.
     trivial.
     
     case_eq (eqbBvector b0 b); intuition.
     apply eqbBvector_sound in H0.
     subst.
     rewrite eqbBvector_complete in H.
     discriminate.
     
     destruct (labelIn_7 l b); destruct (labelIn_7 l b0); simpl; trivial.
     
     rewrite IHPermutation1.
     eapply IHPermutation2.
   Qed.
      
   Theorem noBucketCollision_arrayLookup_eq : 
     forall ls1 ls2,
       Permutation ls1 ls2 ->
       (@bucketLabelCollision_7 lambda) ls1 = false ->
       forall b,
         arrayLookup _ ls1 b = arrayLookup _ ls2 b.
     
     induction 1; intuition; simpl in *.
     
     destruct x.
     case_eq (eqbBvector b b0); intuition.
     eapply IHPermutation.
     eapply orb_false_iff in H0.
     intuition.
     
     destruct y.
     destruct x.
     case_eq (eqbBvector b0 b1); intuition;
     rewrite H1 in H.
     simpl in *. discriminate.
     apply orb_false_iff in H.
     intuition.
     apply orb_false_iff in H3.
     intuition.
     case_eq (eqbBvector b b0); intuition.
     apply eqbBvector_sound in H3.
     subst.
     case_eq (eqbBvector b0 b1); intuition.
     apply eqbBvector_sound in H3.
     subst.
     rewrite eqbBvector_complete in H1.
     discriminate.
     
     rewrite H2.
     eapply IHPermutation2.
     erewrite perm_bucketCollision_7_eq; eauto.
     eapply Permutation_sym.
     trivial.
   Qed.
   
   Theorem TSetRetrieve_tLoop_Corr_5_7_arrayLookup_eq :
     forall ls1 ls2 b0,
       Permutation (getSomes ls1) ls2 ->
       (@bucketLabelCollision_7 lambda) ls2 = false ->
       arrayLookupOpt _ ls1 b0 = 
       arrayLookup _ ls2 b0.

     intuition.
     rewrite arrayLookupOpt_getSomes_eq.
     eapply noBucketCollision_arrayLookup_eq ; intuition.
     erewrite perm_bucketCollision_7_eq; eauto.
   Qed.

   Theorem TSetRetrieve_tLoop_Corr_5_7_eq :
     forall i t1 t2 a,
       labelCollision_7 t2 = false ->
       (forall n, Permutation (getSomes (nth n t1 nil)) (nth n t2 nil)) ->
       ESPADA_TSetRetrieve_tLoop_Corr_5 F t1 a i = ESPADA_TSetRetrieve_tLoop_Corr_7 F t2 a i.
     
     intuition.
     unfold  ESPADA_TSetRetrieve_tLoop_Corr_5,  ESPADA_TSetRetrieve_tLoop_Corr_7.
     
     remember (F a i).
     comp_simp.
     rewrite (@TSetRetrieve_tLoop_Corr_5_7_arrayLookup_eq _ (nth n t2 nil)).
     trivial.
     
     eauto.
     
     Theorem labelCollision_7_false_all : 
       forall ls,
         (@labelCollision_7 lambda) ls = false ->
         forall n, 
           bucketLabelCollision_7 (nth n ls nil) = false.
       
       induction ls; intuition; simpl in *.
       destruct n; trivial.
       
       apply orb_false_iff in H.
       intuition.
       destruct n; intuition.
       
     Qed.
     
     eapply labelCollision_7_false_all.
     trivial.
   Qed.

   Theorem labelCollision_6_false_all_if : 
       forall ls,
         (forall n, 
           (@bucketLabelCollision_6 lambda) (nth n ls nil) = false) ->
         labelCollision_6 ls = false.

     induction ls; intuition; simpl in *.

     eapply orb_false_iff.
     intuition.
     specialize (H O).
     simpl in *.
     intuition.

     eapply IHls.
     intuition.
     specialize (H (S n)).
     simpl in *.
     intuition.

   Qed.
   
   Theorem TSetRetrieve_Corr_5_7_eq :
     forall fuel i t1 t2 a,
       labelCollision_7 t2 = false ->
       (forall n, Permutation (getSomes (nth n t1 nil)) (nth n t2 nil)) ->
       ESPADA_TSetRetrieve_h_Corr_5 F t1 a i fuel = ESPADA_TSetRetrieve_h_Corr_7 F t2 a i fuel.
     
     induction fuel; intuition; simpl in *.
     
     assert (ESPADA_TSetRetrieve_tLoop_Corr_5 F t1 a i = 
             ESPADA_TSetRetrieve_tLoop_Corr_7 F t2 a i).
     eapply TSetRetrieve_tLoop_Corr_5_7_eq; intuition.
     rewrite H2.
     clear H2.
     
     remember (ESPADA_TSetRetrieve_tLoop_Corr_7 F t2 a i).
     destruct o.
     comp_simp.
     f_equal.
     destruct b; trivial.
     eapply IHfuel; intuition.   
     trivial.
   Qed.
   
   Theorem ESPADA_TSetCorr_G6_1_equiv :
       Pr[ gInst1 ESPADA_TSetCorr_G6] <= Pr[ ESPADA_TSetCorr_G6_1].

     unfold  ESPADA_TSetCorr_G6,  ESPADA_TSetCorr_G6_1.

     intuition.
     comp_simp.
     comp_skip; comp_simp.
     comp_skip.

     eapply comp_spec_impl_le.
     comp_skip.
     eapply (@compFold_spec _ _ _ 
                            (fun ls a b => 
                               match a with 
                                 | None => True 
                                 | Some p => 
                                   (forall n, Permutation (getSomes (nth n (fst p) nil)) (nth n b nil)) /\ 
      
           (forall b n, In n (nth b (snd p) nil) -> nth n (nth b (fst p) nil) None = None) /\
           (forall n, NoDup (nth n (snd p) nil))
                               end)).

     intuition.
     simpl.
     destruct n;
     simpl;
     econstructor.

     simpl.
     destruct b;
     simpl;
     destruct n; trivial.

     simpl.
     destruct (lt_dec n (length (initFree bigB bigS))).
     eapply initFree_correct.
     apply (fun x => (pos 1, pos 1)).
     eapply nth_In.
     eapply l0.
     rewrite nth_overflow.
     econstructor.
     omega.
   
     intuition.
     destruct c.
     unfold foldBody_option.
     eapply TSetSetup_5_6_1_spec.

     intuition.
     unfold foldBody_option.
     eapply comp_spec_ret; intuition.

     simpl in *.
     eapply comp_spec_ret; intuition.
     destruct a; simpl in *.
     intuition.

     case_eq (labelCollision_7 b); intuition.
     rewrite orb_false_l.
     
     eapply negb_true_iff.

     assert (labelCollision_6 (fst p) = false).

     eapply labelCollision_6_false_all_if.
     intuition.
     eapply labelCollision_7_false_all in H6.
     
     Theorem labelIn_6_7_eq : 
       forall ls a,
         (@labelIn_6 lambda) ls a = labelIn_7 (getSomes ls) a.

       induction ls; intuition; simpl in *.
       destruct a.
       destruct t.
       simpl.
       destruct (eqbBvector a0 b); intuition.
       eauto.

     Qed.

     Theorem bucketLabelCollision_6_7_eq : 
       forall ls,
         (@bucketLabelCollision_6 lambda) ls = bucketLabelCollision_7 (getSomes ls).

       induction ls; intuition; simpl in *.
       destruct a.
       destruct t.
       simpl.
       f_equal.
       eapply labelIn_6_7_eq.

       intuition.
       intuition.
     Qed.
    
     rewrite bucketLabelCollision_6_7_eq.
     erewrite perm_bucketCollision_7_eq .
     eauto.
     eauto.

     rewrite H8 in H4.
     rewrite orb_false_l in H4.
     eapply negb_true_iff in H4.

     eapply  eqb_false_iff .
     eapply  eqb_false_iff  in H4.
     intuition.
     eapply H4.
     
     rewrite <- H9.
     eapply map_ext_in.
     intuition.

      eapply TSetRetrieve_Corr_5_7_eq; intuition.

      discriminate.

   Qed.

   
   Theorem ESPADA_TSetCorr_G6_1_G7_equiv :
       Pr[ ESPADA_TSetCorr_G6_1] == Pr[ ESPADA_TSetCorr_G7 maxMatches F A1 ].

     intuition.
     unfold ESPADA_TSetCorr_G6_1, ESPADA_TSetCorr_G7.
     comp_simp.
     comp_skip; comp_simp.
     comp_skip.
     comp_irr_l.
     eapply compFold_wf.
     intuition.
     unfold ESPADA_TSetSetup_tLoop_Corr_6_1.
     wftac.
     eapply evalDist_ret_eq.

     eapply (@compFold_support _ _ _ (fun t ls1 ls2 => t = fold_left (@ESPADA_TSetSetup_tLoop_Corr_7 lambda) ls1 nil)) in H1.
     subst.
     trivial.
     trivial.

     intuition.
     subst.
     unfold ESPADA_TSetSetup_tLoop_Corr_6_1 in *.
     unfold setLet in *.
     repeat simp_in_support.
     rewrite fold_left_app.
     
     trivial.

   Qed.

   Theorem ESPADA_TSetCorr_G6_G7_equiv :
       Pr[ gInst1 ESPADA_TSetCorr_G6 ] <= Pr[ ESPADA_TSetCorr_G7 maxMatches F A1 ].

     intuition.
     rewrite ESPADA_TSetCorr_G6_1_equiv.
     rewrite ESPADA_TSetCorr_G6_1_G7_equiv .
     intuition.

   Qed.
 
   Definition labelCollision_7_1 (ls : list (list (TSetCorr_8_Record lambda))) :=
     labelCollision_8 lambda (flatten ls).

   Definition TSetCorr_7_1 := list (list (TSetCorr_8_Record lambda)).

   Definition ESPADA_TSetSetup_tLoop_Corr_7_1 (tSet : TSetCorr_7_1)
  (e :  Blist * Bvector lambda * nat * nat * Vector.t bool lambda * nat * Bvector lambda *
       Vector.t bool (S lambda)) :=
     (let '(q, tag, i, len, s_i, b, bigL, bigK) := e in
        bet <- (if eq_nat_dec (S i) len then false else true);
        newRecord <- ((b, bigL), ((q, tag, i, len, s_i, b, bigK), (Vector.cons bool bet lambda s_i xor bigK)));
        newBucket <- (nth b tSet nil) ++ ( newRecord :: nil); 
        listReplace tSet b newBucket nil
      ).


   Definition ESPADA_TSetRetrieve_tLoop_Corr_7_1 (tSet : TSetCorr_7_1) stag i :=
    [b, L, K] <-3 F stag i;
    x <- nth b tSet nil;
    t <- arrayLookup _ x (b, L);
    match t with
        | None => None
        | Some p => 
          [_, u] <-2 p;
          v <- u xor K;
            bet <- Vector.hd v;
            s <- Vector.tl v;
            Some (s, bet)
    end.

  Fixpoint ESPADA_TSetRetrieve_h_Corr_7_1 (tSet : TSetCorr_7_1) stag i (fuel : nat) :=
    match fuel with
      | O => nil
      | S fuel' =>
        match (ESPADA_TSetRetrieve_tLoop_Corr_7_1 tSet stag i) with
          | Some (v, bet) =>
          v :: (if (bet) then (ESPADA_TSetRetrieve_h_Corr_7_1 tSet stag (S i) fuel') else nil)
          | None => nil
        end
      end.
    
  Definition ESPADA_TSetRetrieve_Corr_7_1 tSet stag :=
    ESPADA_TSetRetrieve_h_Corr_7_1 tSet stag O maxMatches.

   Definition ESPADA_TSetCorr_G7_1 :=
     [t, q] <-$2 A1;
     q <- removeDups _ q;
     allQs <- combineKeywords q (toW t);
     allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
     ts <- map (arrayLookupList _ t) allQs;
     ts_recsList <- map (fun p => [q, tag, ls] <-3 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (q, tag, i, len, s_i, b, bigL, bigK)) ls) (zip (zip allQs allTags) ts);
     tSet <- fold_left ( ESPADA_TSetSetup_tLoop_Corr_7_1) (flatten ts_recsList) nil;
     tags <- firstn (length q) allTags;
     bad <- negb
         (eqb (foreach  (x in tags)ESPADA_TSetRetrieve_Corr_7_1 tSet x)
             (foreach  (x in q)arrayLookupList (list_EqDec bool_EqDec) t x));
     ret (labelCollision_7_1 ( tSet) || bad).
   
   
   Theorem ESPADA_TSetCorr_G7_1_equiv : 
       Pr[ESPADA_TSetCorr_G7 maxMatches F A1] == Pr[ESPADA_TSetCorr_G7_1].

     intuition.
     unfold ESPADA_TSetCorr_G7, ESPADA_TSetCorr_G7_1.
     comp_simp.
     comp_skip; comp_simp.
     comp_skip.

     Theorem labelCollision_7_1_eq : 
       forall ls1 ls2,
         list_pred 
           (fun a b =>
              list_pred 
                (fun x y => 
                   fst x = snd (fst y) /\ snd x = snd y) a b)
           ls1 ls2 ->
         (forall n a, In a (nth n ls2 nil) -> fst (fst a) = n) ->
         labelCollision_7 ls1 = 
         labelCollision_7_1 ls2.
     
       induction ls1 using rev_ind; intuition; simpl in *.
       inversion H; clear H; subst.

       unfold labelCollision_7_1.
       simpl.
       trivial.

       specialize (@ls_last_exists _ ls2 (length ls1)); intuition.
       edestruct H1.
       eapply list_pred_length_eq in H.
       rewrite app_length in H.
       simpl in H.
       rewrite plus_comm in H.
       simpl in *.
       intuition.
       destruct H2.
       intuition.
       subst.
       
       Theorem labelCollision_7_app : 
         forall ls1 ls2,
           (@labelCollision_7 lambda) (ls1 ++ ls2) = 
           labelCollision_7 ls1 || labelCollision_7 ls2.

         induction ls1; intuition; simpl in *.
         rewrite IHls1.
         rewrite orb_assoc.
         trivial.

       Qed.


       Theorem labelIn_8_app_l_false : 
         forall Z ls1 ls2 y,
           @labelIn_8 lambda Z ls2 y = false ->
           labelIn_8 lambda (ls1 ++ ls2) y =  labelIn_8 lambda ls1 y.

         induction ls1; intuition; simpl in *.
         destruct ( eqbPair nat_EqDec (Bvector_EqDec lambda) y (a, b0)); intuition.

       Qed.

       Theorem labelIn_8_app_r_true : 
         forall Z ls1 ls2 y,
           @labelIn_8 lambda Z ls2 y = true ->
           labelIn_8 lambda (ls1 ++ ls2) y = true.

         induction ls1; intuition; simpl in *.
         destruct ( eqbPair nat_EqDec (Bvector_EqDec lambda) y (a, b0)); intuition.

       Qed.

       Theorem labelCollision_8_app : 
         forall Z ls1 ls2,
           (forall x, labelIn_8 lambda ls1 x  = true -> @labelIn_8 lambda Z ls2 x = false) ->
           labelCollision_8 lambda (ls1 ++ ls2) = 
           labelCollision_8 lambda ls1 || labelCollision_8 lambda ls2.

         induction ls1; intuition; simpl in *.
         
         rewrite IHls1.
         rewrite orb_assoc.
         f_equal.
         f_equal.
         specialize (H0 (a, b0)).
         eapply labelIn_8_app_l_false.
         eapply H0.
         unfold eqbPair.
         repeat rewrite eqb_refl.
         trivial.

         intuition.
         eapply H0.
         destruct (eqbPair nat_EqDec (Bvector_EqDec lambda) x (a, b0)); intuition.

       Qed.
       
       Theorem labelCollision_7_1_skipn : 
         forall ls n,
           (forall j j' b, 
              j' > j ->
              labelIn_8 lambda (nth j ls nil) b = true ->
              labelIn_8 lambda (flatten (skipn j' ls)) b = false) ->
           labelCollision_7_1 ls = 
           labelCollision_7_1 (firstn n ls) || labelCollision_7_1 (skipn n ls).

         induction ls; intuition; simpl in *.

         unfold labelCollision_7_1.
         simpl.
         rewrite firstn_nil.

        
         rewrite skipn_nil.
         simpl.
         trivial.
         
         unfold labelCollision_7_1 in *.
         simpl.
         destruct n; simpl in *.
         trivial.
         rewrite labelCollision_8_app.
         rewrite labelCollision_8_app.
         rewrite <- orb_assoc.
         f_equal.
         eapply IHls.
         intuition.
         specialize (H (S j) (S j')%nat b).
         simpl in *.
         intuition.

         intuition.

         Theorem labelIn_8_app_false : 
           forall Z ls1 ls2 a,
             @labelIn_8 lambda Z (ls1 ++ ls2) a = false <->
             labelIn_8 lambda ls1 a = false /\
             labelIn_8 lambda ls2 a = false.

           induction ls1; intros; simpl in *.
           destruct a.
           intuition.
           destruct a.
           destruct (eqbPair nat_EqDec (Bvector_EqDec lambda) a0 p).
           intuition.
           discriminate.
           eapply IHls1; intuition.
         Qed.

         Theorem labelIn_8_false_firstn : 
           forall Z ls x n,
             @labelIn_8 lambda Z (flatten ls) x = false ->
             labelIn_8 lambda (flatten (firstn n ls)) x = false.

           induction ls; intuition; simpl in *.
           rewrite firstn_nil.
           simpl.
           trivial.

           destruct n; simpl in *.
           trivial.
           eapply labelIn_8_app_false  in H0.
           intuition.
           eapply labelIn_8_app_false.
           intuition.

         Qed.          

         specialize (H O 1%nat x).
         simpl in *.

         eapply labelIn_8_false_firstn.
         eapply H.
         omega.
         intuition.
    
         intuition.
         specialize (H O 1%nat x).
         simpl in *.
         intuition.

       Qed.

  
       rewrite (@labelCollision_7_1_skipn _ (length x1)).
       rewrite skipn_app.
       rewrite firstn_app; intuition.
       rewrite firstn_eq_all_gen; intuition.
       
       rewrite labelCollision_7_app.
       f_equal.
       eapply IHls1.

       eapply list_pred_app_both_if in H.
       intuition.
       intuition.
       intuition.
       eapply H0.
       destruct (lt_dec n (length x1)).
       rewrite app_nth1; intuition.
       rewrite nth_overflow in H2.
       simpl in *.
       intuition.
       omega.

       unfold labelCollision_7_1.
       simpl.
       rewrite app_nil_r.
       rewrite orb_false_r.

       Theorem bucketLabelCollision_7_8_eq : 
         forall Z ls1 ls2,
           list_pred (fun x y => fst x = snd (fst y)) ls1 ls2 ->
           (exists b, 
           (forall a, In a ls2 -> fst (fst a) = b)) ->
           bucketLabelCollision_7 ls1 = 
           @labelCollision_8 lambda Z ls2.

         induction 1; intuition; simpl in *.
         destruct a1.
         destruct a2.
         simpl in *.
         subst.
         f_equal.

         Theorem labelIn_7_8_eq : 
           forall Z ls1 ls2 q p,
             list_pred (fun x y => fst x = snd (fst y)) ls1 ls2 ->
             (forall a, In a ls2 -> fst (fst a) = p) ->
             labelIn_7 ls1 q = 
             @labelIn_8 lambda Z ls2 (p, q).

           induction 1; intuition; simpl in *.
           destruct a1.
           destruct a2.
           simpl in *.
           subst.
           destruct p1.
           simpl in *.
           unfold eqbPair.
           simpl.

           case_eq (eqb p n); intuition.
           simpl.
       
           destruct (eqbBvector q b);
           trivial.
           eapply IHlist_pred.
           intuition.
           
           specialize (H1 (n, b, z)).
           intuition.
           simpl in *.
           subst.
           rewrite eqb_refl in H.
           discriminate.
           
         Qed.

         destruct p0.
         destruct H1.
         assert (fst (fst (n, b, z)) = x).
         eapply H.
         intuition.
         simpl in *.
         subst.

         eapply labelIn_7_8_eq .
         trivial.
         intuition.

         eapply IHlist_pred.
         destruct H1.
         econstructor.
         intuition.

       Qed.

       eapply list_pred_app_both_if in H.
       intuition.
       inversion H4; clear H4; subst.
       eapply bucketLabelCollision_7_8_eq.
       eapply list_pred_impl.
       eapply H7.
       intuition.
       econstructor.
       intuition.
       eapply H0.
       rewrite app_nth2.
       rewrite minus_diag.
       simpl.
       trivial.
       intuition.
       intuition.
       
       intuition.
       assert (fst b = j).

       Theorem labelIn_8_exists : 
         forall Z ls x,
           @labelIn_8 lambda Z ls x = true ->
           exists z,
             In (x, z) ls.

         induction ls; intuition; simpl in *.
         discriminate.
         
         case_eq (eqbPair nat_EqDec (Bvector_EqDec lambda) x (a, b0)); intuition.
         rewrite H1 in H0.
         unfold eqbPair in *.
         rewrite andb_true_iff in H1.
         intuition.
         rewrite eqb_leibniz in H2.
         rewrite eqb_leibniz in H3.
         destruct x.
         simpl in *; subst.
         econstructor.
         intuition.

         rewrite H1 in H0.
         edestruct IHls.
         eauto.
         econstructor.
         right.
         eauto.
       Qed.
     
       eapply labelIn_8_exists in H4.
       destruct H4.
       specialize (H0 j (b, x2)).
       eapply H0.
       trivial.
       subst.
       
       subst.
       
       Theorem labelIn_8_all_false : 
         forall Z ls b,
           (forall x y, In (x, y) ls -> x <> b) ->
           @labelIn_8 lambda Z ls b = false.

         induction ls; intuition; simpl in *.
         case_eq (eqbPair nat_EqDec (Bvector_EqDec lambda) b1 (a, b0)); intuition.
         unfold eqbPair in *.
         destruct b1.
         simpl in *.
         apply andb_true_iff in H1.
         intuition.
         rewrite eqb_leibniz in H2.
         apply eqbBvector_sound in H3.
         subst.
         exfalso.
         eapply H0.
         left.
         reflexivity.
         trivial.

         eapply IHls; intuition.
         subst.
         eapply H0.
         right.
         eauto.
         trivial.

       Qed.

       eapply labelIn_8_all_false .
       intuition.
       subst.
       eapply in_flatten in H6.
       simpl in *.
       destruct H6.
       intuition.

       eapply nth_In_exists in H7.
       destruct H7.

       rewrite nth_skipn_eq in H6.
       rewrite <- H6 in H8.
       clear H6.
  
       specialize (H0 (x3 + j')%nat (a, b0, y)).
       simpl in H0.
       assert (a = (x3 + j')%nat).
       eapply H0.
       eauto.
       subst.
       omega.
     Qed.
       
     eapply evalDist_ret_eq.
     f_equal.
     eapply labelCollision_7_1_eq.

     Theorem ESPADA_TSetSetup_tLoop_Corr_7_1_pred : 
       forall t1 t2,
         list_pred
         (fun a b6  =>
            list_pred
              (fun x0 y =>
                 fst x0 = snd (fst y) /\ snd x0 = snd y) a b6)
         t1 t2 ->
         forall p,
       list_pred
         (fun a b6  =>
            list_pred
              (fun x0 y =>
                 fst x0 = snd (fst y) /\ snd x0 = snd y) a b6)
         (ESPADA_TSetSetup_tLoop_Corr_7 t1 p)
         (ESPADA_TSetSetup_tLoop_Corr_7_1 t2 p).

       intuition.
       
       unfold ESPADA_TSetSetup_tLoop_Corr_7, ESPADA_TSetSetup_tLoop_Corr_7_1.
       comp_simp.

       eapply list_pred_listReplace.
       intuition.

       eapply list_pred_app_both.

       eapply list_pred_nth.
       eapply list_pred_impl.
       eapply H.
       intuition.
       econstructor.
       
       econstructor.
       unfold fst, snd.
       intuition.
       econstructor.
       econstructor.
     Qed.

     Theorem ESPADA_TSetSetup_Corr_7_1_pred : 
       forall ls t1 t2,
         list_pred
           (fun a b =>
              list_pred
                (fun x0 y =>
                   fst x0 = snd (fst y) /\ snd x0 = snd y) 
                a b)
           t1 t2 ->
         list_pred
           (fun a b =>
              list_pred
                (fun x0 y =>
                   fst x0 = snd (fst y) /\ snd x0 = snd y) 
                a b)
           (fold_left (@ESPADA_TSetSetup_tLoop_Corr_7 lambda) ls t1)
           (fold_left ESPADA_TSetSetup_tLoop_Corr_7_1 ls t2).

       induction ls; intuition.

       Theorem fold_left_cons : 
         forall (A B : Type)(ls : list A)(a : A)(b : B) f,
           fold_left f (a :: ls) b = fold_left f ls (f b a).

         intuition.
       Qed.

       rewrite fold_left_cons.
       rewrite fold_left_cons.
       eapply IHls.

       eapply  ESPADA_TSetSetup_tLoop_Corr_7_1_pred.
       trivial. 

     Qed.

     eapply ESPADA_TSetSetup_Corr_7_1_pred .
     econstructor.

     intuition.

     Theorem ESPADA_TSetSetup_tLoop_Corr_7_1_bucket_label : 
       forall n t a b,
         (forall a n, In a (nth n t nil) -> fst (fst a) = n) ->
         In a (nth n (ESPADA_TSetSetup_tLoop_Corr_7_1 t b) nil) ->
         fst (fst a) = n.

       intuition.
       
       unfold ESPADA_TSetSetup_tLoop_Corr_7_1 in *.
       destruct b.
       repeat (destruct p).
       unfold setLet in *.
       destruct (eq_nat_dec n n0).
       subst.
       rewrite nth_listReplace_eq in H0.

       eapply in_app_or in H0.
       intuition.
       simpl in *; intuition.
       inversion H0; trivial.
       rewrite nth_listReplace_ne in H0; intuition.
     Qed.
       
     Theorem ESPADA_TSetSetup_Corr_7_1_bucket_label : 
       forall ls a n t,
         (forall a n, In a (nth n t nil) -> fst (fst a) = n) ->
         In a (nth n (fold_left ESPADA_TSetSetup_tLoop_Corr_7_1 ls t) nil) ->
         fst (fst a) = n.

       induction ls; intros.
       intuition.
       rewrite fold_left_cons in H0.
       eapply (IHls _ _ (ESPADA_TSetSetup_tLoop_Corr_7_1 t a)).
       intros.
       eapply ESPADA_TSetSetup_tLoop_Corr_7_1_bucket_label; eauto.

       trivial.

     Qed.

     eapply ESPADA_TSetSetup_Corr_7_1_bucket_label.
     intuition.
     rewrite nth_nil in H2.
     simpl in *.
     intuition.
     eauto.

     f_equal.
     f_equal.

     eapply map_ext_in.
     intuition.
     
     Theorem ESPADA_TSetRetrieve_tLoop_Corr_7_1_equiv : 
       forall t1 t2,
         list_pred 
           (fun a b => 
              list_pred 
                (fun x y =>
                      fst x = snd (fst y) /\ snd x = snd y) a b)
           t1 t2 ->
         (forall p n, In p (nth n t2 nil) -> fst (fst p) = n) ->
         forall i z,
         (ESPADA_TSetRetrieve_tLoop_Corr_7 F) t1 z i = ESPADA_TSetRetrieve_tLoop_Corr_7_1 t2 z i.

       intuition.
       unfold  ESPADA_TSetRetrieve_tLoop_Corr_7,  ESPADA_TSetRetrieve_tLoop_Corr_7_1.
       remember (F z i).
       comp_simp.

       Theorem ESPADA_TSetRetrieve_Corr_7_1_arrayLookup_equiv : 
       forall (t1 : TSetCorr_7 lambda) (t2 : TSetCorr_7_1),
         list_pred 
           (fun a b => 
              list_pred 
                (fun x y =>
                      fst x = snd (fst y) /\ snd x = snd y) a b)
           t1 t2 ->
         forall n1 n2 z,
           (forall p, In p (nth n1 t2 nil) -> fst (fst p) = n2) ->
         arrayLookup _ (nth n1 t1 nil) z = 
         arrayLookup _ (nth n1 t2 nil) (n2, z).

         induction 1; intuition; simpl in *.
         destruct n1;
         simpl;
         trivial.

         destruct n1; simpl.

         Theorem arrayLookup_pair_const_eq : 
           forall a1 a2,
             list_pred
               (fun
                   (x : Bvector lambda *
                        (Blist * Bvector lambda * nat * nat * Bvector lambda * nat *
                         Bvector (S lambda) * Bvector (S lambda)))
                   (y : nat * Bvector lambda *
                        (Blist * Bvector lambda * nat * nat * Bvector lambda * nat *
                 Bvector (S lambda) * Bvector (S lambda))) =>
                   fst x = snd (fst y) /\ snd x = snd y) a1 a2 ->
             forall c z,
               (forall x, In x a2 -> fst (fst x) = c) ->
             arrayLookup _ a1 z = 
             arrayLookup _ a2 (c, z).

           induction 1; intuition; simpl in *.
           destruct a1. destruct a2.
           unfold eqbPair.
           simpl in *.
           destruct p0.
           simpl in *.
           subst.
           case_eq (eqb c n); intuition.
           simpl.
           case_eq (eqbBvector z b0); intuition.
           specialize (H (n, b0, p1)).
           intuition.
           subst.
           simpl in *.
           rewrite eqb_refl in H1.
           discriminate.
         
         Qed.
               
         eapply arrayLookup_pair_const_eq;
         intuition.
         eapply IHlist_pred.
         intuition.

       Qed.

       erewrite ESPADA_TSetRetrieve_Corr_7_1_arrayLookup_equiv; intuition.
     Qed.


     Theorem ESPADA_TSetRetrieve_h_Corr_7_1_equiv : 
       forall n t1 t2,
         list_pred 
           (fun a b => 
              list_pred 
                (fun x y =>
                      fst x = snd (fst y) /\ snd x = snd y) a b)
           t1 t2 ->
         (forall n p, In p (nth n t2 nil) -> fst (fst p) = n) ->
         forall i z,
         ESPADA_TSetRetrieve_h_Corr_7 F t1 z i n = ESPADA_TSetRetrieve_h_Corr_7_1 t2 z i n.

       induction n; intuition; simpl in *.
       case_eq (ESPADA_TSetRetrieve_tLoop_Corr_7_1 t2 z i); intuition;
       erewrite <- ESPADA_TSetRetrieve_tLoop_Corr_7_1_equiv in H2.
       erewrite H2.
       comp_simp.
       f_equal.
       destruct b; trivial.
       eapply IHn; intuition.
       eapply H.
       intuition.
       
       rewrite H2.
       trivial.
       eapply H.
       intuition.

     Qed.

     Theorem ESPADA_TSetRetrieve_Corr_7_1_equiv : 
       forall t1 t2,
         list_pred 
           (fun a b => 
              list_pred 
                (fun x y =>
                      fst x = snd (fst y) /\ snd x = snd y) a b)
           t1 t2 ->
         (forall n p, In p (nth n t2 nil) -> fst (fst p) = n) ->
         forall z,
         ESPADA_TSetRetrieve_Corr_7 maxMatches F t1 z = ESPADA_TSetRetrieve_Corr_7_1 t2 z.

       intuition.
       eapply ESPADA_TSetRetrieve_h_Corr_7_1_equiv ; intuition.
  
     Qed.

     eapply ESPADA_TSetRetrieve_Corr_7_1_equiv .
     eapply ESPADA_TSetSetup_Corr_7_1_pred .
     econstructor.
     intuition.

     eapply ESPADA_TSetSetup_Corr_7_1_bucket_label.
     intuition.
     rewrite nth_nil in H2.
     simpl in *.
     intuition.
     eauto.
   Qed.
     

   Theorem ESPADA_TSetCorr_G7_1_G8_equiv :
       Pr[ESPADA_TSetCorr_G7_1] == Pr[ESPADA_TSetCorr_G8 maxMatches F A1].

     intuition.
     unfold ESPADA_TSetCorr_G7_1, ESPADA_TSetCorr_G8.
     comp_simp.
     comp_skip.
     comp_simp.
     comp_skip.
     eapply evalDist_ret_eq.
     
     f_equal.

     Theorem labelCollision_8_perm_eq : 
       forall Z ls1 ls2,
         Permutation ls1 ls2 ->
         @labelCollision_8 lambda Z ls1 = 
         labelCollision_8 lambda ls2.

       induction 1; intuition; simpl in *.

       Theorem labelIn_8_perm_eq : 
         forall Z ls1 ls2,
           Permutation ls1 ls2 ->
           forall p,
             @labelIn_8 lambda Z ls1 p = labelIn_8 lambda ls2 p.

         induction 1; intuition; simpl in *.
         destruct (eqbPair nat_EqDec (Bvector_EqDec lambda) (a, b1) (a0, b0)); intuition.

         destruct (eqbPair nat_EqDec (Bvector_EqDec lambda) (a0, b3) (a, b2)).
         destruct (eqbPair nat_EqDec (Bvector_EqDec lambda) (a0, b3) (a1, b1)); intuition.
         trivial.

         rewrite IHPermutation1.
         eauto.

       Qed.

       f_equal.
       eapply labelIn_8_perm_eq; intuition.

       trivial.

       rewrite eqbPair_symm.
       destruct (eqbPair nat_EqDec (Bvector_EqDec lambda) (a1, b1) (a, b2)); intuition.

       destruct (labelIn_8 lambda l (a1, b1)); destruct ((labelIn_8 lambda l (a, b2) )); intuition.
             
       rewrite IHPermutation1.
       trivial.

     Qed.

     eapply labelCollision_8_perm_eq.
   
   
     Theorem setup_tLoop_Corr_7_1_8_eq : 
       forall t1 t2 a,
         Permutation (flatten t1) t2 ->
         Permutation (flatten (ESPADA_TSetSetup_tLoop_Corr_7_1 t1 a))
         (t2 ++ (ESPADA_TSetSetup_tLoop_Corr_8 lambda a) :: nil).

       intuition.
       unfold ESPADA_TSetSetup_tLoop_Corr_7_1, ESPADA_TSetSetup_tLoop_Corr_8.
       comp_simp.

       eapply perm_trans.

       eapply  perm_flatten_listReplace.
       eauto.

       eapply Permutation_cons_append.
     Qed.

       
     Theorem setup_Corr_7_1_8_eq_h : 
       forall ls t1 t2,
         Permutation (flatten t1) t2 ->
         Permutation (flatten (fold_left ESPADA_TSetSetup_tLoop_Corr_7_1 ls t1))  
         (t2 ++ (map (@ESPADA_TSetSetup_tLoop_Corr_8 lambda) ls)).

       induction ls; intuition.
       simpl.
       rewrite app_nil_r.
       trivial.
       
       repeat rewrite fold_left_cons.

       rewrite map_cons.
       rewrite app_cons_eq.
       eapply IHls.

       eapply setup_tLoop_Corr_7_1_8_eq.
       trivial.
     Qed.

     Theorem setup_Corr_7_1_8_eq : 
       forall ls,
         Permutation (flatten (fold_left ESPADA_TSetSetup_tLoop_Corr_7_1 ls nil))  
                     ((map (@ESPADA_TSetSetup_tLoop_Corr_8 lambda) ls)).

       intuition.
       eapply perm_trans.
       eapply setup_Corr_7_1_8_eq_h.
       simpl.
       eapply Permutation_refl.
       simpl.
       eapply Permutation_refl.
       
     Qed.
     
     eapply  setup_Corr_7_1_8_eq.

     f_equal.
     f_equal.
     
     eapply map_ext_in.
     intuition.

   
     Theorem retrieve_tLoop_Corr_7_1_8_eq : 
       forall i t1 t2 x,
         (forall b l, arrayLookup _ (nth b t1 nil) (b, l) = arrayLookup _ t2 (b, l)) ->
        ESPADA_TSetRetrieve_tLoop_Corr_7_1 t1 x i =
        ESPADA_TSetRetrieve_tLoop_Corr_8 F t2 x i.
       
       intuition.
       unfold  ESPADA_TSetRetrieve_tLoop_Corr_7_1,  ESPADA_TSetRetrieve_tLoop_Corr_8.
       remember (F x i).
       comp_simp.

       rewrite H.
       destruct (arrayLookup (pair_EqDec nat_EqDec (Bvector_EqDec lambda)) t2 (n, b0)); intuition.
      
     Qed.

     Theorem retrieve_h_Corr_7_1_8_eq : 
       forall fuel i t1 t2 x,
         (forall b l, arrayLookup _ (nth b t1 nil) (b, l) = arrayLookup _ t2 (b, l)) ->
        ESPADA_TSetRetrieve_h_Corr_7_1 t1 x i fuel =
        ESPADA_TSetRetrieve_h_Corr_8 F t2 x i fuel.

       induction fuel; intuition; simpl in *.
       case_eq (ESPADA_TSetRetrieve_tLoop_Corr_7_1 t1 x i); intuition;   
       erewrite retrieve_tLoop_Corr_7_1_8_eq in H1.
       rewrite H1.
       comp_simp.
       f_equal.
       destruct b; trivial.
       eapply IHfuel.
       intuition.
       intuition.
       rewrite H1.
       trivial.
       intuition.
       
     Qed.


     Theorem retrieve_Corr_7_1_8_eq : 
       forall t1 t2 x,
         (forall b l, arrayLookup _ (nth b t1 nil) (b, l) = arrayLookup _ t2 (b, l)) ->
        ESPADA_TSetRetrieve_Corr_7_1 t1 x =
        ESPADA_TSetRetrieve_Corr_8 maxMatches F t2 x.

       intuition.
       eapply retrieve_h_Corr_7_1_8_eq .
       intuition.
       
     Qed.


     eapply retrieve_Corr_7_1_8_eq.
     intuition.

     Theorem setup_tLoop_Corr_7_1_8_arrayLookup_eq : 
       forall t1 t2 a,
         (forall b l, arrayLookup _ (nth b t1 nil) (b, l) = arrayLookup _ t2 (b, l)) ->
         (forall b l, arrayLookup _ (nth b (ESPADA_TSetSetup_tLoop_Corr_7_1 t1 a) nil) (b, l) =
                      arrayLookup _ (t2 ++ ((@ESPADA_TSetSetup_tLoop_Corr_8 lambda) a :: nil)) (b, l)).

       intuition.
       unfold ESPADA_TSetSetup_tLoop_Corr_7_1, ESPADA_TSetSetup_tLoop_Corr_8.
       comp_simp.
       destruct (eq_nat_dec b6 b1).
       subst.
       rewrite nth_listReplace_eq.

       case_eq (arrayLookup _ (nth b1 t1 nil) (b1, l)); intuition.

       erewrite arrayLookup_app_Some; eauto.
       rewrite H in H0.
       erewrite arrayLookup_app_Some; eauto.

       erewrite arrayLookup_app_None; eauto.
       rewrite H in H0.
       erewrite arrayLookup_app_None; eauto.

       rewrite nth_listReplace_ne; intuition.

       rewrite H.
       rewrite arrayLookup_app_ne; intuition.
       pairInv.
       intuition.
     Qed.


     Theorem setup_Corr_7_1_8_arrayLookup_eq_h : 
       forall ls t1 t2,
         (forall b l, arrayLookup _ (nth b t1 nil) (b, l) = arrayLookup _ t2 (b, l)) ->
         (forall b l, arrayLookup _ (nth b (fold_left ESPADA_TSetSetup_tLoop_Corr_7_1 ls t1) nil) (b, l) =
                      arrayLookup _ (t2 ++ (map (@ESPADA_TSetSetup_tLoop_Corr_8 lambda) ls)) (b, l)).
 
       induction ls; intuition.
       simpl in *.
       rewrite app_nil_r.
       trivial.

       repeat rewrite fold_left_cons.
       rewrite map_cons.
       rewrite app_cons_eq.
       eapply IHls.
       eapply setup_tLoop_Corr_7_1_8_arrayLookup_eq.
       trivial.
     Qed.

     Theorem setup_Corr_7_1_8_arrayLookup_eq : 
       forall ls,
         (forall b l, arrayLookup _ (nth b (fold_left ESPADA_TSetSetup_tLoop_Corr_7_1 ls nil) nil) (b, l) =
                      arrayLookup _ (map (@ESPADA_TSetSetup_tLoop_Corr_8 lambda) ls) (b, l)).
       
       intuition.
       erewrite setup_Corr_7_1_8_arrayLookup_eq_h.
       rewrite app_nil_l.
       trivial.
       intuition.
       simpl.
       destruct b0; trivial.
     Qed.

     eapply setup_Corr_7_1_8_arrayLookup_eq.
 
   Qed.

   Theorem ESPADA_TSetCorr_G7_G8_equiv : 
       Pr[ESPADA_TSetCorr_G7 maxMatches F A1] == Pr[ESPADA_TSetCorr_G8 maxMatches F A1].

     intuition.

     rewrite ESPADA_TSetCorr_G7_1_equiv.
     eapply ESPADA_TSetCorr_G7_1_G8_equiv .

   Qed.

   (* check results for all queries---this simplifies things a bit. *)
   Definition ESPADA_TSetCorr_G8_1 :=
     [t, q] <-$2 A1;
     q <- removeDups _ q;
     allQs <- combineKeywords q (toW t);
     allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
     ts <- map (arrayLookupList _ t) allQs;
     ts_recsList <- map (fun p => [q, tag, ls] <-3 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (q, tag, i, len, s_i, b, bigL, bigK)) ls) (zip (zip allQs allTags) ts);
     tSet <- map (@ESPADA_TSetSetup_tLoop_Corr_8 lambda) (flatten ts_recsList) ;
     bad <- negb
         (eqb (foreach  (x in allTags) (ESPADA_TSetRetrieve_Corr_8 maxMatches F tSet x))
             (foreach  (x in allQs)arrayLookupList (list_EqDec bool_EqDec) t x));
     ret (labelCollision_8 _ (tSet) || bad).

   Theorem ESPADA_TSetCorr_G8_8_1_equiv:
       Pr[ESPADA_TSetCorr_G8 maxMatches F A1] <= Pr[ESPADA_TSetCorr_G8_1].

     intuition.
     unfold ESPADA_TSetCorr_G8, ESPADA_TSetCorr_G8_1.
     comp_simp.
     comp_skip.
     comp_simp.
     comp_skip.
     eapply comp_spec_impl_le.
     eapply comp_spec_ret.
     intuition.
     eapply orb_true_iff in H1.
     intuition.
     eapply orb_true_iff.
     right.
     
     eapply negb_true_iff in H2.
     eapply eqb_false_iff in H2.

     eapply negb_true_iff.
     eapply eqb_false_iff.
     intuition.
     eapply H2.
     
     rewrite <- (@firstn_skipn _ (length (removeDups (list_EqDec bool_EqDec) l)) x) in H1 at 1.
     unfold combineKeywords in H1.
     repeat rewrite map_app in H1.

     Show.
     eapply app_eq_inv in H1.
     intuition.
     clear H4.
     unfold combineKeywords.
     repeat rewrite map_app.
     eapply H3.

     repeat rewrite map_length.
     rewrite firstn_length.
     eapply min_l.
     eapply compMap_length in H0.
     rewrite H0.
     unfold combineKeywords.
     rewrite app_length.
     omega.    

   Qed.

    Theorem ESPADA_TSetCorr_G8_1_9_equiv:
       Pr[ESPADA_TSetCorr_G8_1] <= Pr[ESPADA_TSetCorr_G9 maxMatches F A1].

      intuition.
      unfold ESPADA_TSetCorr_G8_1, ESPADA_TSetCorr_G9.
      comp_simp.
      comp_skip; comp_simp.
      comp_skip.
      eapply comp_spec_impl_le.
      eapply comp_spec_ret.
      intuition.
      eapply orb_true_iff in H1.
      intuition.

      eapply orb_true_iff.
      left.
         
         Theorem labelIn_8_In : 
           forall Z ls p,
             @labelIn_8 lambda Z ls p = true <->
             In p (fst (split ls)).

           induction ls; intuition; simpl in *.
           discriminate.
           remember (split ls) as z.
           destruct z.
           simpl in *.
           case_eq (eqbPair nat_EqDec (Bvector_EqDec lambda) (a0, b1) (a, b0)); intuition.
           unfold eqbPair in *.
           simpl in *.
           eapply andb_true_iff in H1.
           intuition.
           rewrite eqb_leibniz in H2.
           eapply eqbBvector_sound in H3.
           subst.
           intuition.
          
           rewrite H1 in H0.
           right.
           eapply IHls.
           trivial.

           remember (split ls) as z.
           destruct z.
           simpl in *.
           intuition.
           pairInv.
           unfold eqbPair; simpl.
           rewrite eqb_refl.
           rewrite eqbBvector_complete.
           simpl.
           trivial.

           destruct ( eqbPair nat_EqDec (Bvector_EqDec lambda) (a0, b1) (a, b0)); trivial.
           eapply IHls.
           trivial.
                                                                                   
         Qed.

         Theorem labelCollision_8_false_NoDup : 
           forall Z ls,
             @labelCollision_8 lambda Z ls = false <->
             NoDup (fst (split ls)).

           induction ls; intuition; simpl in *.
           econstructor.
           remember (split ls) as z.
           destruct z.
           simpl in *.
           eapply orb_false_iff in H2.
           intuition.
           
           econstructor.
           intuition.
           specialize (@labelIn_8_In _ ls (a, b0)); intuition.
           rewrite <- Heqz in H7.
           simpl in *.
           intuition.
           rewrite H5 in H3.
           discriminate.

           trivial.

           remember (split ls) as z.
           destruct z.
           simpl in *.
           inversion H2; clear H2; subst.
           intuition.
           case_eq (labelIn_8 _ ls (a, b0)); intuition.
           exfalso.
           eapply H5.
           specialize (@labelIn_8_In _ ls (a, b0)); intuition.
           rewrite <- Heqz in H3.
           simpl in *.
           trivial.
           
         Qed.
         
         case_eq (labelCollision_9 _ maxMatches F x); intuition.
         eapply hasDups_false_NoDup in H1.

         match goal with
           | [H : labelCollision_8 _ ?a = true |- _ ] => assert (labelCollision_8 _ a = false)
         end.

         Fixpoint labelIn_9_1 (ls : list (Blist * Bvector lambda * nat * nat * Bvector lambda * nat * Bvector lambda * Bvector (S lambda))) p :=
           match ls with
             | nil => false
             | (_, _, _, _, _, b', l', _) :: ls' =>
               eqb p (b', l') || labelIn_9_1 ls' p
           end.

         Fixpoint labelCollision_9_1 (ls : list (Blist * Bvector lambda * nat * nat * Bvector lambda * nat * Bvector lambda * Bvector (S lambda))) :=
           match ls with
             | nil => false
             | (_, _, _, _, _, b, l, _) :: ls' =>
               labelIn_9_1 ls' (b, l) || labelCollision_9_1 ls'
           end.
                       
         Theorem labelIn_8_9_1_equiv : 
           forall ls b l ,
             labelIn_8 _ (map (@ESPADA_TSetSetup_tLoop_Corr_8 lambda) ls) (b, l) = labelIn_9_1 ls (b, l).

           induction ls; intuition; simpl in *.
           case_eq (eqbPair nat_EqDec (Bvector_EqDec lambda) (b6, l) (b1, b0)); intuition.
           
           simpl.
           eapply IHls; eauto.
         Qed.

         Theorem labelCollision_8_9_1_equiv : 
           forall ls,
             labelCollision_8 _ (map (@ESPADA_TSetSetup_tLoop_Corr_8 lambda) ls) = labelCollision_9_1 ls.

           induction ls; intuition; simpl in *.
           f_equal.
           eapply labelIn_8_9_1_equiv .
           eauto.

         Qed.

         rewrite labelCollision_8_9_1_equiv.
         
         Theorem labelIn9_1_In_eq : 
           forall ls1 (ls2 : list (nat * Bvector lambda)) p,
             list_pred (fun x y => let '(_, _, _, _, _, b, l, _) := x in (b, l) = y) ls1 ls2 -> 
             labelIn_9_1 ls1 p = 
             if (in_dec (EqDec_dec _) p ls2) then true else false.

           induction 1; intuition; simpl in *.
           destruct a1.
           repeat (destruct p0).
           
           destruct (EqDec_dec (pair_EqDec nat_EqDec (Bvector_EqDec lambda)) a2 p).
           subst.
           subst.
           unfold eqbPair; simpl.
           repeat rewrite eqb_refl.
           rewrite eqbBvector_complete.
           simpl.
           trivial.
           subst.
           case_eq ( eqbPair nat_EqDec (Bvector_EqDec lambda) p (n, b0)); intuition.
           unfold eqbPair in *; simpl in *.
           eapply andb_true_iff in H.
           intuition.
           rewrite 
             eqb_leibniz in H1.
           apply eqbBvector_sound in H3.
           subst.
           exfalso; destruct p; simpl in *; intuition.

           simpl.
           rewrite IHlist_pred.
           destruct ( in_dec (EqDec_dec (pair_EqDec nat_EqDec (Bvector_EqDec lambda))) p ls2); intuition.
           
         Qed.

         Theorem labelCollision_9_1_hasDups_eq : 
           forall ls1 (ls2 : list (nat * Bvector lambda)),
             list_pred (fun x y => let '(_, _, _, _, _, b, l, _) := x in (b, l) = y) ls1 ls2 -> 
             labelCollision_9_1 ls1 = 
             hasDups _ ls2.

           induction 1; intuition; simpl in *.
           destruct a1.
           repeat (destruct p).
           subst.
           rewrite (@labelIn9_1_In_eq _ ls2).
           destruct (in_dec (EqDec_dec (pair_EqDec nat_EqDec (Bvector_EqDec lambda)))
         (n, b0) ls2); intuition.
           intuition.

         Qed.

         rewrite (@labelCollision_9_1_hasDups_eq _ 
                  (flatten
                     (foreach  (p in
                                   (zip x
                                        (map  (fun z => length (arrayLookupList (list_EqDec bool_EqDec) t z))
                                              (combineKeywords (removeDups (list_EqDec bool_EqDec) l)
                                                               (toW t)))
                                        )
                                   )
                                     [tag, n]<-2 p;
         numberedMap
           (fun (i len : nat) (s_i : nat) =>
            [b, bigL, bigK]<-3 F tag i; (b, bigL))
           (allNatsLt n)))
                 ).

         eapply hasDups_false_NoDup.
         
         Definition getAllLabels_8_1 tags :=
           map (fun t => map (fun i => fst (F t i)) (allNatsLt (S maxMatches))) tags.

   
         Theorem getAllLabels_8_1_equiv : 
           forall ls,
             getAllLabels _ maxMatches F ls = flatten (getAllLabels_8_1 ls).

           induction ls; intuition; simpl in *.
           f_equal.
           eauto.

         Qed.

         rewrite getAllLabels_8_1_equiv in H1.
            
         eapply (@NoDup_flatten_subset _ (getAllLabels_8_1 x)).
         unfold getAllLabels_8_1.
         eapply list_pred_map_l'.
         eapply list_pred_map_r'.
         eapply list_pred_impl.
         eapply list_pred_zip_r.
         
         assert (list_pred (fun a b => b <= maxMatches)%nat x
     (foreach  (z
      in combineKeywords (removeDups (list_EqDec bool_EqDec) l) (toW t))
      length (arrayLookupList (list_EqDec bool_EqDec) t z))).
         eapply list_pred_map_r'.
         eapply list_pred_impl.
         eapply list_pred_I.
         eapply compMap_length.
         eauto.
         intuition.
        
         eapply arrayLookupList_pred.
         intuition.
         eapply  maxMatches_correct.
         eauto.
         trivial.
         simpl; intuition.

         eapply H3.
         eapply list_pred_eq.
         eapply list_pred_I.
         rewrite map_length.
         symmetry.
         eapply compMap_length.
         eauto.
         
         intuition.
         intuition.
         subst.
         exists (snd b).
         destruct b.
         unfold numberedMap.
         simpl.
         
         rewrite firstn_map.
         rewrite allNatsLt_length.

         eapply map_eq.
         rewrite (@firstn_allNatsLt _ (S maxMatches)).
         eapply list_pred_impl.
         eapply list_pred_zip_l.
         eapply list_pred_eq.
         eapply list_pred_eq.
         eapply list_pred_eq.
         intuition.
         simpl in *; subst.
         destruct (F b b1).
         destruct p.
         trivial.
         simpl in *.
         omega.

         trivial.

         eapply list_pred_flatten_both.
         eapply list_pred_map_l'.
         eapply list_pred_map_r'.
         eapply list_pred_impl.
         eapply list_pred_zip_l.
         eapply list_pred_zip_l.
         eapply list_pred_I.
         symmetry.
         eapply compMap_length; eauto.
         eapply list_pred_map_r.
         eapply list_pred_eq.
         eapply list_pred_I.
         rewrite map_length.
         eapply compMap_length; eauto.
         
         eapply list_pred_zip_l.
         eapply list_pred_I.
         symmetry.
         eapply compMap_length; eauto.
         eapply list_pred_zip_r.
         eapply list_pred_map_r.
         eapply list_pred_I.
         eapply compMap_length; eauto.
         eapply list_pred_I.
         eapply compMap_length; eauto.
         
         eapply list_pred_map_l.
         eapply list_pred_eq.

         eapply list_pred_zip_r.
         eapply list_pred_I.
         rewrite map_length.
         eapply compMap_length; eauto.
         eapply list_pred_eq.

         eapply list_pred_I.
         symmetry.
         rewrite map_length.
         eapply compMap_length; eauto.

         eapply list_pred_zip_r.
         eapply list_pred_I.
         rewrite map_length.
         eapply compMap_length; eauto.

         eapply list_pred_I.
         rewrite map_length.
         eapply compMap_length; eauto.
         
         eapply list_pred_map_both.
         eapply list_pred_eq.

         intuition.
         destruct H6.
         destruct H13.
         destruct H13.
         destruct H11.
         destruct H16.
         intuition; simpl in *; subst.
         destruct b1; simpl in *; subst.

         unfold numberedMap.
         eapply list_pred_map_l'.
         eapply list_pred_map_r'.

         rewrite allNatsLt_length.

         eapply list_pred_impl.
         eapply list_pred_zip_l.
         eapply list_pred_I.
         apply allNatsLt_length.

         eapply list_pred_zip_r.
         eapply list_pred_eq.
         rewrite H21.
         eapply list_pred_eq.
         rewrite H21.
         eapply list_pred_eq.

         eapply list_pred_zip_r.
         eapply list_pred_eq.
         rewrite H21.
         eapply list_pred_I.
         apply allNatsLt_length.
         rewrite H21.
         eapply list_pred_I.
         apply allNatsLt_length.
         
         intuition.
         destruct b1.
         simpl in *; subst.
         remember (F b a0) as z.
         destruct z.
         destruct p.
         trivial.

         rewrite H3 in H2.
         discriminate.
    Qed.

   Theorem ESPADA_TSetCorr_G9_G10_equiv : 
       Pr[ESPADA_TSetCorr_G9 maxMatches F A1] == Pr[ESPADA_TSetCorr_G10 maxMatches F A1].

     intuition.
     unfold ESPADA_TSetCorr_G9, ESPADA_TSetCorr_G10.
     comp_simp.
     comp_skip; comp_simp.
     comp_skip.

     eapply evalDist_ret_eq.
     eapply orb_same_eq_if.
     intuition.

     f_equal.
     f_equal.
     eapply map_ext_in.
     intuition.


     Theorem tSetRetrieve_tLoop_Corr_8_10_eq : 
       forall (ls : TSetCorr_8 lambda) a i,
         (forall  n b0 b4 a' i' n1 b3 n0 b2 b1,
            In  (n, b0, (b4, a', i', n1, b3, n0, b2, b1)) ls -> 
         (n, b0) = fst (F a' i') /\ b2 = (snd (F a' i')) /\ b1 = (Vector.cons _ (if (eq_nat_dec (S i') n1) then false else true) _ b3) xor b2 /\
         (fst (F a' i') = fst (F a i) -> a = a' /\ i = i')) ->  
         ESPADA_TSetRetrieve_tLoop_Corr_8 F ls a i = 
         ESPADA_TSetRetrieve_tLoop_Corr_10 F ls a i.

       intuition.
       unfold ESPADA_TSetRetrieve_tLoop_Corr_8, ESPADA_TSetRetrieve_tLoop_Corr_10.
       remember (F a i).
       comp_simp.
       match goal with
         | [|- match ?a with | Some _ => _ | None => _ end = _ ] => case_eq a; intuition
       end.

       repeat (destruct p).
       
       eapply arrayLookup_Some_impl_In in H1.
       eapply H0 in H1.
       intuition.
       subst.
       simpl in H5.
       symmetry in H2.
       intuition.
       subst.
       
       rewrite <- Heqp.
       unfold snd.
       rewrite BVxor_assoc.
       rewrite BVxor_same_id.
       rewrite BVxor_id_r.
       trivial.

     Qed.

     Theorem tSetRetrieve_h_Corr_8_10_eq : 
       forall fuel i ls a,
        ( i + fuel <= maxMatches)%nat ->
         (forall n b0 b4 a' i' n1 b3 n0 b2 b1,
            forall i,
              (i <= maxMatches)%nat -> 
            In  (n, b0, (b4, a', i', n1, b3, n0, b2, b1)) ls -> 
         (n, b0) = fst (F a' i') /\ b2 = (snd (F a' i')) /\ b1 =  (Vector.cons _ (if (eq_nat_dec (S i') n1) then false else true) _ b3) xor b2 /\
         (fst (F a' i') = fst (F a i) -> a = a' /\ i = i')) ->
         ESPADA_TSetRetrieve_h_Corr_8 F ls a i fuel = 
         ESPADA_TSetRetrieve_h_Corr_10 F ls a i fuel.

       induction fuel; intuition.
       simpl.
       erewrite tSetRetrieve_tLoop_Corr_8_10_eq .
       remember (ESPADA_TSetRetrieve_tLoop_Corr_10 F ls a i).
       destruct o.
       destruct p.
       f_equal.
       destruct b0.
       
       eapply IHfuel.
       omega.

       eauto.
       trivial.
       trivial.

       intros.
       eapply H0.
       omega.
       eauto.

     Qed.
    

     Theorem tSetRetrieve_Corr_8_10_eq : 
       forall ls a,
          (forall n b0 b4 a' i' n1 b3 n0 b2 b1,
            forall i,
              (i <= maxMatches)%nat -> 
            In  (n, b0, (b4, a', i', n1, b3, n0, b2, b1)) ls -> 
         (n, b0) = fst (F a' i') /\ b2 = (snd (F a' i')) /\ b1 = (Vector.cons _ (if (eq_nat_dec (S i') n1) then false else true) _ b3) xor b2 /\
         (fst (F a' i') = fst (F a i) -> a = a' /\ i = i')) ->
         ESPADA_TSetRetrieve_Corr_8 maxMatches F ls a = 
         ESPADA_TSetRetrieve_Corr_10 maxMatches F ls a.

       intuition.

       eapply tSetRetrieve_h_Corr_8_10_eq; intuition.
  
     Qed.

     eapply tSetRetrieve_Corr_8_10_eq; intros.
     

     Theorem labelCollision_F_1_to_1 : 
       forall ls a1 a2 i1 i2,
         NoDup (getAllLabels _ maxMatches F ls) ->
         In a1 ls -> 
         In a2 ls ->
         (i1 <= maxMatches)%nat ->
         (i2 <= maxMatches)%nat ->
         fst (F a1 i1) = fst (F a2 i2) ->
         a1 = a2 /\ i1 = i2.

       induction ls; intros.
       simpl in *.
       intuition.
       
       simpl in *.
       destruct H0.
       subst.
       destruct H1.
       subst.


       eapply NoDup_app_l in H.

       eapply  NoDup_map in H.
       intuition.
       eapply H1.
       eapply (@allNatsLt_lt_if (S maxMatches)).
       omega.
       eapply (@allNatsLt_lt_if (S maxMatches)).
       omega.
       trivial.

       eapply NoDup_app in H.
       destruct H.
       destruct H1.
       exfalso.
       eapply H5.
       eapply in_map_iff.
       exists (i1).
       intuition.
       eapply (@allNatsLt_lt_if (S maxMatches)).
       omega.

       assert (In (fst (F a2 i2)) (getAllLabels _ maxMatches F ls)).
       
       Theorem In_getAllLabels : 
         forall ls a i, 
           In a ls ->
           (i <= maxMatches)%nat ->
           In (fst (F a i)) (getAllLabels _ maxMatches F ls).

         induction ls; intuition; simpl in *.
         
         intuition; subst.
         eapply in_or_app.
         left.
         eapply in_map_iff.
         econstructor.
         intuition.
         eapply (@allNatsLt_lt_if (S maxMatches)).
         omega.
 
       Qed.

       eapply In_getAllLabels; intuition.

       eauto.
       trivial.

       destruct H1.
       subst.
       eapply NoDup_app in H.
       destruct H.
       destruct H1.
       exfalso.
       eapply H5.
       eapply in_map_iff.
       exists i2.
       intuition.
       eapply (@allNatsLt_lt_if (S maxMatches)).
       omega.
  
       eapply In_getAllLabels.
       eapply H0.
       eapply H2.

       symmetry.
       trivial.
       
       eapply IHls; intuition.
       eapply NoDup_app in H.
       intuition.
     Qed.
       
     Ltac intac :=
       match goal with
         | [H: In _ (map _ _) |- _ ] => eapply in_map_iff in H
         | [H: exists _, _ |- _] => destruct H
         | [H: In _ (flatten _) |- _ ] => eapply in_flatten in H
         | [H: In _ (zip _ _) |- _ ] => eapply In_zip in H
         | [H: _ /\ _ |- _ ] => destruct H
       end.

     repeat (intac; subst).
     destruct x2.
     destruct p.
     unfold numberedMap, ESPADA_TSet_Once_Games.numberedMap in*.
     repeat (intac; subst).
     destruct x1.
     remember (F b5 n2) as z.
     destruct z.
     destruct p.
     unfold ESPADA_TSetSetup_tLoop_Corr_8 in *.

     Ltac pairInv_once' :=
       match goal with
         | [H : (_, _) = (_, _) |- _] => eapply pair_eq_inv in H
         | [H : _ /\ _ |- _ ] => destruct H
       end.

     Ltac pairInv' := repeat (pairInv_once'; subst).

     pairInv'.
     
     specialize (@labelCollision_F_1_to_1 x a a' i i'); intuition.

     rewrite <- Heqz.
     trivial.
     rewrite <- Heqz.
     trivial.
   
     eapply H5; intros; eauto.
     eapply  hasDups_false_NoDup.
     eapply H1.
     eapply In_zip in H7.
     intuition.
     
     eapply allNatsLt_lt in H11.
     eapply le_trans.
     eapply lt_le_weak.
     eapply H11.

     eapply arrayLookupList_pred.
     intuition.
     eapply maxMatches_correct.
     eauto.
     trivial.
     simpl; intuition.

     eapply H5; intros; eauto.
     eapply hasDups_false_NoDup.
     eapply H1.
     eapply In_zip in H7.
     intuition.
     
     eapply allNatsLt_lt in H11.
     eapply le_trans.
     eapply lt_le_weak.
     eapply H11.

     eapply arrayLookupList_pred.
     intuition.
     eapply maxMatches_correct.
     eauto.
     trivial.
     simpl; intuition.

   Qed.

   Theorem ESPADA_TSetCorr_G8_le_G9:
     Pr  [ESPADA_TSetCorr_G8 maxMatches F A1] <= Pr  [ESPADA_TSetCorr_G9 maxMatches F A1].
     
     intuition.
     rewrite ESPADA_TSetCorr_G8_8_1_equiv.
     eapply ESPADA_TSetCorr_G8_1_9_equiv.
   Qed.

  
  Theorem TSetRetrieve_tLoop_Corr_10_11_equiv :
    forall i t1 t2 x,
      list_pred (fun x y => fst x = fst y /\ (snd y) = fst (fst (fst (snd x)))) t2 t1 ->
      ESPADA_TSetRetrieve_tLoop_Corr_10 F t2 x i = 
      ESPADA_TSetRetrieve_tLoop_Corr_11 F t1 x i.
    
    intuition.
    unfold ESPADA_TSetRetrieve_tLoop_Corr_10, ESPADA_TSetRetrieve_tLoop_Corr_11.
    remember (F x i).
    comp_simp.
    
    eapply (@list_pred_impl_arrayLookup _ _ _ (fun x y => y = fst (fst (fst x)))) in H.
    intuition.
    case_eq (arrayLookup (pair_EqDec nat_EqDec (Bvector_EqDec lambda)) t2 (n, b0)); intuition.
    repeat (destruct p).
    eapply H1 in H.
    destruct H.
    intuition.
    simpl in H4.
    subst.
    rewrite H3.
    trivial.
    
    rewrite H2;
      trivial.
    
  Qed.
    
  Theorem TSetRetrieve_h_Corr_10_11_equiv :
    forall fuel i t1 t2 x,
      list_pred (fun x y => fst x = fst y /\ (snd y) = fst (fst (fst (snd x)))) t2 t1 ->
      ESPADA_TSetRetrieve_h_Corr_10 F t2 x i fuel = 
      ESPADA_TSetRetrieve_h_Corr_11 F t1 x i fuel.
    
    induction fuel; intuition; simpl in *.
    rewrite (@TSetRetrieve_tLoop_Corr_10_11_equiv _ t1).
    destruct (ESPADA_TSetRetrieve_tLoop_Corr_11 F t1 x i).
    destruct p.
    f_equal.
    destruct b0.
    eapply IHfuel; intuition.
    trivial.
    trivial.
    trivial.
    
  Qed.
  
  Theorem TSetRetrieve_Corr_10_11_equiv :
    forall t1 t2 x,
      list_pred (fun x y => fst x = fst y /\ (snd y) = fst (fst (fst (snd x)))) t2 t1 ->
      ESPADA_TSetRetrieve_Corr_10 maxMatches F t2 x = 
      ESPADA_TSetRetrieve_Corr_11 maxMatches F t1 x.
    
    eapply TSetRetrieve_h_Corr_10_11_equiv; intuition.
    
  Qed.
  
  Theorem ESPADA_TSetCorr_G10_G11_equiv :
    Pr[ ESPADA_TSetCorr_G10 maxMatches F A1] == Pr[ ESPADA_TSetCorr_G11 maxMatches F A1].
    
    unfold ESPADA_TSetCorr_G10, ESPADA_TSetCorr_G11.
    comp_skip.
    comp_simp.
    comp_skip.
    eapply evalDist_ret_eq.
    f_equal.
    f_equal.
    f_equal.
    eapply map_ext_in.
    intuition.
    eapply  TSetRetrieve_Corr_10_11_equiv.
    
    eapply list_pred_map_l'.
    eapply list_pred_flatten_both.
    eapply list_pred_map_l'.
    eapply list_pred_map_r'.
    eapply list_pred_impl.
    eapply list_pred_eq.
    
     intuition; subst.
     unfold numberedMap.
     eapply list_pred_map_l'.
     eapply list_pred_map_r'.
     eapply list_pred_impl.
     eapply list_pred_eq.
     intuition; subst.

     unfold ESPADA_TSetSetup_tLoop_Corr_8.
     remember (F b0 a2); intuition.
     destruct p.
     destruct p.
     trivial.
     
     unfold ESPADA_TSetSetup_tLoop_Corr_8.
     remember (F b0 a2); intuition.
     destruct p.
     destruct p.
     trivial.

  Qed.
 
  
  Theorem TSetRetrieve_tLoop_Corr_11_12_equiv :
    forall i (t1 : TSetCorr_11 lambda) t2 x,
      
      list_pred (fun x y => 
                   let '(b1, l1, (q1, z1, n1, c1, s1)) := x in 
                let '(z2, n2, (q2, c2, s2)) := y in 
                z1 = z2 /\ n1 = n2 /\ q1 = q2 /\ c1 = c2 /\ s1 = s2 /\
                (b1, l1) = fst (F z1 n1)) t1 t2 ->
      NoDup (fst (split t1)) -> 
      (In (fst (F x i)) (fst (split t1)) -> In (x, i) (fst (split t2))) ->
      ESPADA_TSetRetrieve_tLoop_Corr_11 F t1 x i = 
      ESPADA_TSetRetrieve_tLoop_Corr_12 t2 x i.

    intuition.
    unfold ESPADA_TSetRetrieve_tLoop_Corr_11, ESPADA_TSetRetrieve_tLoop_Corr_12.
    remember (F x i); intuition.
    destruct p.
    destruct p.

    case_eq (arrayLookup _ t2 (x, i)); intuition.
    apply arrayLookup_Some_impl_In in H3.
    eapply list_pred_symm in H.
    eapply list_pred_In_exists in H; eauto.
    destruct H.
    intuition.
    destruct x0.
    destruct p0.
    destruct p1.
    repeat (destruct p0).
    repeat (destruct p).
    intuition; subst.

    rewrite <- Heqp in H10.
    simpl in H10.
    pairInv.
    erewrite arrayLookup_In_NoDup; eauto.
    unfold setLet.
    trivial.

    case_eq (arrayLookup (pair_EqDec nat_EqDec (Bvector_EqDec lambda)) t1 (n, b0)); intuition.
    exfalso.
   

    eapply arrayLookup_None_not_In in H3.
    intuition.
    eapply H1.
    simpl.
    apply arrayLookup_Some_impl_In in H4.
    eapply in_split_l in H4.
    trivial.
   
  Qed.
    
  Theorem TSetRetrieve_h_Corr_11_12_equiv :
    forall fuel i t1 t2 x,
      list_pred (fun x y => 
                   let '(b1, l1, (q1, z1, n1, c1, s1)) := x in 
                let '(z2, n2, (q2, c2, s2)) := y in 
                z1 = z2 /\ n1 = n2 /\ q1 = q2 /\ c1 = c2 /\ s1 = s2 /\
                (b1, l1) = fst (F z1 n1)) t1 t2  ->
      NoDup (fst (split t1)) ->
      (i + fuel <= maxMatches)%nat ->
      (forall i, 
        (i <= maxMatches)%nat ->
        (In (fst (F x i)) (fst (split t1)) -> In (x, i) (fst (split t2)))) ->
      ESPADA_TSetRetrieve_h_Corr_11 F t1 x i fuel = 
      ESPADA_TSetRetrieve_h_Corr_12 t2 x i fuel.
    
    induction fuel; intuition; simpl in *.
    rewrite (@TSetRetrieve_tLoop_Corr_11_12_equiv _ _ t2).
    destruct (ESPADA_TSetRetrieve_tLoop_Corr_12 t2 x i).
    destruct p.
    f_equal.
    destruct b0.
    eapply IHfuel; intuition.
    trivial.
    trivial.
    trivial.
    trivial.
    eapply H2.
    omega.
    
  Qed.
  
  Theorem TSetRetrieve_Corr_11_12_equiv :
    forall t1 t2 x,
       list_pred (fun x y => 
                   let '(b1, l1, (q1, z1, n1, c1, s1)) := x in 
                let '(z2, n2, (q2, c2, s2)) := y in 
                z1 = z2 /\ n1 = n2 /\ q1 = q2 /\ c1 = c2 /\ s1 = s2 /\
                (b1, l1) = fst (F z1 n1)) t1 t2  ->
      NoDup (fst (split t1)) ->
      (forall i, 
        (i <= maxMatches)%nat ->
        (In (fst (F x i)) (fst (split t1)) -> In (x, i) (fst (split t2)))) ->

      ESPADA_TSetRetrieve_Corr_11 maxMatches F t1 x = 
      ESPADA_TSetRetrieve_Corr_12 maxMatches t2 x.
    
    intuition.
    eapply TSetRetrieve_h_Corr_11_12_equiv; intuition.
    
  Qed.

  Theorem ESPADA_TSetCorr_G11_G12_equiv :
    Pr[ESPADA_TSetCorr_G11 maxMatches F A1] == Pr[ESPADA_TSetCorr_G12 maxMatches F A1].
    
    unfold ESPADA_TSetCorr_G11, ESPADA_TSetCorr_G12.
    
    comp_skip; comp_simp.
    comp_skip.
    eapply evalDist_ret_eq.
    case_eq (labelCollision_9 lambda maxMatches F x); intuition.
    simpl.
    f_equal.
    f_equal.
    eapply map_ext_in.
    intuition.
    eapply TSetRetrieve_Corr_11_12_equiv.

    eapply list_pred_flatten_both.
    eapply list_pred_map_r'.
    eapply list_pred_map_l'.
    eapply list_pred_impl.
    eapply list_pred_eq.
    intuition; subst.
    unfold numberedMap.
    eapply list_pred_map_l'.
    eapply list_pred_map_r'.
    eapply list_pred_impl.
    eapply list_pred_eq.
    intuition; subst.
    remember (F b0 a2).
    destruct p.
    destruct p.
    intuition.
    rewrite <- Heqp.
    trivial.

    rewrite fst_split_flatten_eq.
    unfold labelCollision_9 in *.
    rewrite getAllLabels_8_1_equiv in H1.
    eapply hasDups_false_NoDup in H1.
    eapply NoDup_flatten_subset; eauto.
    eapply list_pred_map_r'.
    eapply list_pred_map_r'.


    eapply list_pred_impl.

    assert (list_pred (fun a b => a = fst (split (map (F (snd (fst b))) (allNatsLt (S maxMatches)))) /\ length (snd b) <= maxMatches)%nat
                      (getAllLabels_8_1 x)
     (zip
        (zip (combineKeywords (removeDups (list_EqDec bool_EqDec) l) (toW t))
           x)
        (foreach  (x
         in combineKeywords (removeDups (list_EqDec bool_EqDec) l) (toW t))
         arrayLookupList (list_EqDec bool_EqDec) t x))
     ).

    eapply list_pred_impl.
    eapply list_pred_zip_r.
    eapply list_pred_map_r.
    eapply list_pred_zip_l.
    eapply list_pred_I.
    symmetry.
    eapply compMap_length.
    eauto.
    eapply list_pred_eq.
    eapply list_pred_I.
    eapply compMap_length; eauto.
    eapply list_pred_zip_l.
    eapply list_pred_I.
    symmetry.
    eapply compMap_length.
    eauto.
    eapply list_pred_I.

    unfold getAllLabels_8_1.    
    rewrite map_length.
    symmetry.
    eapply compMap_length.
    eauto.
    
    Theorem getAllLabels_8_1_list_pred : 
      forall x,
        list_pred 
          (fun a b => b = fst (split (map (F a) (allNatsLt (S maxMatches)))))
          x (getAllLabels_8_1 x).

      induction x; intuition; simpl in *.
      econstructor.
      econstructor.
      symmetry.
      eapply fst_split_map_eq.
      trivial.
    Qed.

    eapply getAllLabels_8_1_list_pred.
    eapply list_pred_map_l.
    eapply list_pred_I.
    unfold getAllLabels_8_1.
    rewrite map_length.
    symmetry.
    eapply compMap_length.
    eauto.
    intuition.
    intuition.
    intuition.
    destruct H5.
    destruct H7.
    intuition.
    subst.
    rewrite H11.
    eapply arrayLookupList_pred.
    eapply maxMatches_correct.
    eauto.
    simpl.
    intuition.

    eapply H4.
    intuition.
    intuition.
    subst.
    destruct b.
    destruct p.
    simpl in *.
    exists (length l0).
    unfold ESPADA_TSet_Once_Games.numberedMap.
    
    rewrite fst_split_map_eq.
    rewrite fst_split_map_eq.
    rewrite firstn_map.
    eapply map_eq.
    eapply list_pred_impl.
    eapply list_pred_zip_l.
    eapply list_pred_I.
    eapply allNatsLt_length.
    eapply list_pred_eq_gen.

    symmetry.
    eapply (@firstn_allNatsLt _ (S maxMatches)).
    omega.
    eapply list_pred_I.
    rewrite (@firstn_allNatsLt _ (S maxMatches)).
    symmetry.
    eapply allNatsLt_length.
    omega.
    intuition.
    simpl in *; subst.
    destruct (F b0 b2).
    destruct p.
    trivial.

    intuition.

    eapply in_split_l_if in H5.
    destruct H5.
    eapply in_flatten in H5.
    destruct H5.
    intuition.
    eapply in_map_iff in H6.
    destruct H6.
    intuition.
    destruct x2.
    destruct p.
    subst.
    unfold ESPADA_TSet_Once_Games.numberedMap in *.
    eapply in_map_iff in H7.
    destruct H7.
    intuition.
    destruct x1.

    eapply in_fst_split_if.
    eapply in_flatten.
    econstructor.
    split.
    eapply in_map_iff.
    econstructor.
    split.
    reflexivity.
    eauto.
    simpl.
    eapply in_map_iff.
    econstructor.
    split; eauto.
    simpl.
    remember (F b0 n) as z.
    destruct z.
    destruct p.
    pairInv.

    Theorem labelCollision_9_coll_eq : 
      forall ls a1 a2 i1 i2,
        (NoDup (getAllLabels _ maxMatches F ls) ->
        In a1 ls ->
        In a2 ls ->
        i1 <= maxMatches ->
        i2 <= maxMatches ->
        fst (F a1 i1) = fst (F a2 i2) ->
        (a1, i1) = (a2, i2))%nat.

      induction ls; intuition; simpl in *.
      intuition.

      intuition; subst.
      subst.
      
      eapply NoDup_app in H0.
      intuition; subst.

      assert (i1 = i2).
      eapply NoDup_map.
      eapply H1.
      eapply (@allNatsLt_lt_if (S maxMatches)).
      omega.
      eapply (@allNatsLt_lt_if (S maxMatches)).
      omega.
      simpl.
      trivial.
      subst.
      trivial.
      
     
      eapply NoDup_app in H0.
      intuition; subst.

      exfalso.
      eapply H7.
      eapply in_map_iff.
      exists i1.
      split.
      reflexivity.
      eapply (@allNatsLt_lt_if (S maxMatches)).
      omega.
      Focus 2.
      eapply H5.
      eapply In_getAllLabels;
      eauto.

      eapply NoDup_app in H0.
      intuition; subst.

      exfalso.
      eapply H7.
      eapply in_map_iff.
      exists i2.
      split.
      reflexivity.
      eapply (@allNatsLt_lt_if (S maxMatches)).
      omega.
      Focus 2.
      symmetry.
      eapply H5.
      eapply In_getAllLabels;
      eauto.

      eapply NoDup_app in H0.
      intuition; subst.
      
    Qed.

    assert ((b0, n) = (a, i)).
    eapply labelCollision_9_coll_eq; eauto.
    eapply hasDups_false_NoDup.
    eauto.
    eapply In_zip in H8.
    intuition.
    eapply In_zip in H3.
    intuition.
    eapply In_zip in H7.
    intuition.
    
    eapply In_zip in H8.
    intuition.
    eapply In_zip in H7.
    intuition.
    eapply in_map_iff in H10.
    destruct H10.
    intuition.
    subst.
    eapply allNatsLt_lt in H3.
    eapply le_trans.
    eapply Nat.lt_le_incl.
    eapply H3.
    
    eapply arrayLookupList_pred.
    eapply   maxMatches_correct.
    eauto.
    simpl.
    intuition.
    rewrite <- Heqz.
    trivial.
    pairInv.
    eauto.
  Qed.

   Theorem ESPADA_TSetCorr_G12_G13_equiv :
     Pr[ESPADA_TSetCorr_G12 maxMatches F A1 ] == Pr[ESPADA_TSetCorr_G13 maxMatches F A1].

     unfold ESPADA_TSetCorr_G12, ESPADA_TSetCorr_G13.

     comp_skip.
     comp_simp.
     comp_skip.
     eapply evalDist_ret_eq.
     
     case_eq (labelCollision_9 lambda maxMatches F x); intuition.
     simpl.
     f_equal.
     f_equal.
  
     rewrite (@map_snd_eq _ (combineKeywords (removeDups (list_EqDec bool_EqDec) l) (toW t))).
     symmetry.
     rewrite (@map_fst_eq _ x).
     symmetry.
     eapply map_ext_in.
     intuition.

     destruct a.
     simpl.
     

     Theorem TSetRetrieve_tLoop_Corr_12_13_equiv :
       forall i (t1 : TSetCorr_12 lambda) (t2 : TSetCorr_13 lambda) m x y,
         (forall a b c, In (a, c) m -> In (b, c) m -> a = b) ->
         (forall a b c, In (a, b) m -> In (a, c) m -> b = c) ->
         In (y, x) m ->
         NoDup (fst (split t2)) -> 
         list_pred (fun a b =>
                      let '(t1, i1, (q1, l1, s1)) := a in
                      let '(q2, i2, (l2, s2)) := b in
                      q1 = q2 /\ i1 = i2 /\ l1 = l2 /\ s1 = s2 /\
                      In (q1, t1) m) t1 t2
             -> 
         ESPADA_TSetRetrieve_tLoop_Corr_12 t1 x i = 
         ESPADA_TSetRetrieve_tLoop_Corr_13 t2 y i.

       intuition.
       unfold ESPADA_TSetRetrieve_tLoop_Corr_12, ESPADA_TSetRetrieve_tLoop_Corr_13.
       case_eq ( arrayLookup (pair_EqDec (Bvector_EqDec lambda) nat_EqDec) t1 (x, i)); intuition.
       eapply arrayLookup_Some_impl_In in H.
       specialize (list_pred_In_exists H4 _ H); intuition.
       destruct H6.
       intuition.
       destruct p.
       destruct p.
       destruct x0.
       destruct p.
       destruct p0.
       intuition.
       subst.
       assert (y = b1).
       eapply H0; eauto.
       subst.
       erewrite arrayLookup_In_NoDup; eauto.
       comp_simp.
       trivial.

       comp_simp.
       case_eq ( @arrayLookup (prod Blist nat)
         (prod nat (Bvector (posnatToNat lambda)))
         (@pair_EqDec Blist nat (@list_EqDec bool bool_EqDec) nat_EqDec) t2
         (@pair Blist nat y i)); intuition.
       destruct p.
       eapply list_pred_symm in H4.
       eapply arrayLookup_Some_impl_In in H6.
       specialize (list_pred_In_exists H4 _ H6); intuition.
       destruct H7.
       intuition.
       destruct x0.
       destruct p.
       destruct p0.
       destruct p.
       intuition.
       subst.
       assert (x = b0).
       eapply H1; eauto.
       subst.
       eapply arrayLookup_None_not_In in H.
       intuition.
       eapply in_fst_split_if.
       eauto.
     Qed.

     Theorem TSetRetrieve_h_Corr_12_13_equiv :
       forall fuel i t1 t2 m x y,
          (forall a b c, In (a, c) m -> In (b, c) m -> a = b) ->
         (forall a b c, In (a, b) m -> In (a, c) m -> b = c) ->
         In (y, x) m ->
         NoDup (fst (split t2)) ->
         list_pred (fun a b =>
                      let '(t1, i1, (q1, l1, s1)) := a in
                      let '(q2, i2, (l2, s2)) := b in
                      q1 = q2 /\ i1 = i2 /\ l1 = l2 /\ s1 = s2 /\
                      In (q1, t1) m) t1 t2
             -> 
         (@ESPADA_TSetRetrieve_h_Corr_12 lambda) t1 x i fuel = 
         ESPADA_TSetRetrieve_h_Corr_13 t2 y i fuel.

        induction fuel; intuition; simpl in *.
        rewrite  (@TSetRetrieve_tLoop_Corr_12_13_equiv _ _ t2 m _ y).
        destruct (ESPADA_TSetRetrieve_tLoop_Corr_13 t2 y i).
        destruct p.
        f_equal.
        destruct b0.
        eauto.
        trivial.
        trivial.

        eauto.
        eauto.
        trivial.
        trivial.
        trivial.       

     Qed.

     Theorem TSetRetrieve_Corr_12_13_equiv :
       forall t1 t2 m x y,
         (forall a b c, In (a, c) m -> In (b, c) m -> a = b) ->
         (forall a b c, In (a, b) m -> In (a, c) m -> b = c) ->
         In (y, x) m ->
         NoDup (fst (split t2)) ->
         list_pred (fun a b =>
                      let '(t1, i1, (q1, l1, s1)) := a in
                      let '(q2, i2, (l2, s2)) := b in
                      q1 = q2 /\ i1 = i2 /\ l1 = l2 /\ s1 = s2 /\
                      In (q1, t1) m) t1 t2
             -> 
         (@ESPADA_TSetRetrieve_Corr_12 lambda) maxMatches t1 x = 
         ESPADA_TSetRetrieve_Corr_13 maxMatches t2 y.
       
       intuition.
       
       eapply TSetRetrieve_h_Corr_12_13_equiv; eauto.
    
     Qed.

     Show.
     eapply TSetRetrieve_Corr_12_13_equiv; eauto.
     
     intuition.
     
     

     eapply In_combine_NoDup_eq_l; eauto.
     
     Theorem NoDup_labels_NoDup : 
       forall ls,
         NoDup (getAllLabels _ maxMatches F ls) ->
         NoDup ls.

       induction ls; intuition; simpl in *.
       econstructor.

       eapply NoDup_app in H.
       intuition.

       econstructor.
       intuition.
       eapply (@H3 (fst (F a maxMatches)) (fst (F a maxMatches))).
       eapply in_map_iff.
       exists maxMatches.
       intuition.

       eapply In_getAllLabels; intuition.
       trivial.
       trivial.
     Qed.

     eapply NoDup_labels_NoDup .
     eapply hasDups_false_NoDup.
     trivial.

     intuition.
     eapply In_combine_NoDup_eq_r; eauto.
     eapply combineKeywords_NoDup.
     eapply removeDups_NoDup.
     eapply toW_NoDup.

     rewrite fst_split_flatten_eq.

     rewrite map_map.

     Require Import NoDup_gen.
     

     eapply flatten_NoDup_gen.

     eapply (@map_NoDup_gen _ _ (fun a b => (snd a) <> nil /\ length (snd a) = length (snd b) /\ fst (fst a) = fst (fst b))); intros.
     intuition.
     destruct a1; destruct a2; simpl in *.
     subst.
     destruct l0; simpl in *; try omega.
     intuition.
     intuition.
     destruct a1; destruct a2; destruct a3; simpl in *.
     destruct p; destruct p0; destruct p1; simpl in *.
     subst.
     trivial.

     destruct a1; destruct a2; simpl in *.
     destruct p; destruct p0; simpl in *.
     intuition; subst.
     unfold ESPADA_TSet_Once_Games.numberedMap in *.
     rewrite fst_split_map_eq in H5.
     eapply map_eq_nil in H5.
     eapply H4.
     
     eapply  zip_eq_nil_l  in H5.
     destruct l0; simpl in *; trivial.
     eapply app_eq_nil in H5.
     simpl in *; intuition; discriminate.
     eapply allNatsLt_length.

     unfold ESPADA_TSet_Once_Games.numberedMap.
     repeat rewrite fst_split_map_eq.
     assert (
          map
     (fun a : nat * Bvector lambda =>
      fst ([i, a0]<-2 a; [_, _, _]<-3 F b2 i; (b3, i, (length l0, a0))))
     (zip (allNatsLt (length l0)) l0)
     =
      map
     (fun a => (b3, a))
     (allNatsLt (length l0))
     ).

     eapply map_eq.
     eapply list_pred_impl.
     eapply list_pred_zip_l.
     eapply list_pred_I.
     eapply allNatsLt_length.
     eapply list_pred_eq.
     eapply list_pred_I.
     symmetry.
     eapply allNatsLt_length.
     intuition.
     subst.
     comp_simp.
     trivial.
     rewrite H5.
     clear H5.
     
     assert (
          map
     (fun a : nat * Bvector lambda =>
      fst ([i, a0]<-2 a; [_, _, _]<-3 F b4 i; (b3, i, (length l1, a0))))
     (zip (allNatsLt (length l1)) l1)
     =
      map
     (fun a => 
      (b3, a))
     (allNatsLt (length l1))
     ).

     eapply map_eq.
     eapply list_pred_impl.
     eapply list_pred_zip_l.
     eapply list_pred_I.
     eapply allNatsLt_length.
     eapply list_pred_eq.
     eapply list_pred_I.
     symmetry.
     eapply allNatsLt_length.
     intuition.
     subst.
     comp_simp.
     trivial.
     rewrite H5.
     clear H5.
     rewrite H3.
     trivial.

     intuition.
     subst.
     intuition.

     intuition.
     subst.
     trivial.

     destruct a.
     destruct p.
     simpl in *.
     intuition.
     eapply H4.
     unfold numberedMap.
     subst.
     simpl.
     trivial.

     destruct a1.
     destruct p.
     destruct a2.
     destruct p.
     simpl in *.
     unfold ESPADA_TSet_Once_Games.numberedMap in *.
     repeat rewrite fst_split_map_eq in *.
     
     assert (
         map
         (fun a : nat * Bvector lambda =>
          fst ([i, a0]<-2 a; [_, _, _]<-3 F b2 i; (b1, i, (length l0, a0))))
         (zip (allNatsLt (length l0)) l0)
         =
         map
         (fun a =>
          (b1, a))
         (allNatsLt (length l0))
         ).
     
     eapply map_eq.
     eapply list_pred_impl.
     eapply list_pred_zip_l.
     eapply list_pred_I.
     eapply allNatsLt_length.
     eapply list_pred_eq.
     eapply list_pred_I.
     symmetry.
     eapply allNatsLt_length.
     intuition.
     subst.
     comp_simp.
     trivial.
     rewrite H4 in H3.
     clear H4.

     assert (
         map
         (fun a : nat * Bvector lambda =>
          fst ([i, a0]<-2 a; [_, _, _]<-3 F b4 i; (b3, i, (length l1, a0))))
         (zip (allNatsLt (length l1)) l1)
         =
         map
         (fun a =>
           (b3, a))
         (allNatsLt (length l1))
         ).

     eapply map_eq.
     eapply list_pred_impl.
     eapply list_pred_zip_l.
     eapply list_pred_I.
     eapply allNatsLt_length.
     eapply list_pred_eq.
     eapply list_pred_I.
     symmetry.
     eapply allNatsLt_length.
     intuition.
     subst.
     comp_simp.
     trivial.
     rewrite H4 in H3.
     clear H4.
     
     intuition.
     subst.
     eapply H4.
     trivial.

     rewrite <- (@allNatsLt_length (length l0)).
     rewrite <- (@map_length _ _ (fun a : nat => (b1, a))).
     rewrite H5.
     rewrite map_length.
     eapply allNatsLt_length.

     eapply map_pair_fst_eq .
     eapply H5.
     destruct l0; simpl in *; intuition.
     eapply app_eq_nil in H3.
     simpl in *; intuition; discriminate.

     eapply (@NoDup_gen_weaken _ (fun a b => fst (fst a) = fst (fst b))).

     eapply (@NoDup_gen_zip_fst _ _ (fun a b => fst a = fst b)).
     eapply NoDup_gen_zip_fst.
     eapply NoDup_gen_eq .
     eapply combineKeywords_NoDup.
     eapply removeDups_NoDup.
     eapply toW_NoDup.
     
     intuition.
     intuition.
     eapply in_map_iff in H3.
     destruct H3.
     intuition.
     subst.
     unfold ESPADA_TSet_Once_Games.numberedMap.
     destruct x1.
     destruct p.
     rewrite fst_split_map_eq.
     eapply NoDup_gen_eq.
     eapply (@map_NoDup_gen _ _ (fun a b => fst a = fst b));
     intuition; simpl in *; subst; trivial.
     comp_simp.
     trivial.
     destruct a2.
     destruct (F b2 a).
     destruct p.
     destruct (F b2 n).
     destruct p.
     simpl in *.
     pairInv.
     trivial.

     eapply NoDup_gen_zip_fst.
     eapply NoDup_gen_eq .
     eapply allNatsLt_NoDup.

     intuition.
     eapply app_NoDup.
     eapply in_map_iff in H3.
     destruct H3.
     intuition.
     subst.
     comp_simp.
     unfold ESPADA_TSet_Once_Games.numberedMap.
     rewrite fst_split_map_eq.
     eapply NoDup_gen_eq.
     eapply (@map_NoDup_gen _ _ (fun a b => fst a = fst b));
       intuition; simpl in *; subst; trivial.
     comp_simp.
     trivial.
     destruct (F b2 a).
     destruct p.
     destruct a2.
     destruct (F b2 n0).
     destruct p.
     simpl in *.
     pairInv.
     trivial.
     eapply NoDup_gen_zip_fst.
     eapply NoDup_gen_eq .
     eapply allNatsLt_NoDup.

     repeat intac; subst.
     unfold ESPADA_TSet_Once_Games.numberedMap.
     destruct x0.
     destruct p.
     rewrite fst_split_map_eq.
     eapply NoDup_gen_eq.
     eapply (@map_NoDup_gen _ _ (fun a b => fst a = fst b));
     intuition; simpl in *; subst; trivial.
     comp_simp.
     trivial.
     destruct a2.
     destruct (F b2 a).
     destruct p.
     destruct (F b2 n).
     destruct p.
     simpl in *.
     pairInv.
     trivial.

     eapply NoDup_gen_zip_fst.
     eapply NoDup_gen_eq .
     eapply allNatsLt_NoDup.

     intuition.
     eapply H6.
     clear H6.
     
     repeat intac; subst.
     
     destruct x3.
     destruct p.
     destruct x0.
     destruct p.
     unfold ESPADA_TSet_Once_Games.numberedMap in *.
     repeat rewrite fst_split_map_eq in *.
     eapply in_map_iff in H8.
     eapply in_map_iff in H7.
     destruct H8.
     destruct H7.
     intuition.
     subst.
     destruct x1.
     destruct x0.
     destruct (F b2 n).
     destruct (F b4 n0).
     destruct p.
     destruct p0.
     simpl in *.
     pairInv.

     Theorem In_zip_3 : 
       forall (A B C : Set)(lsa : list A)(lsb : list B)(lsc : list C) a b c,
         In (a, b, c) (zip (zip lsa lsb) lsc) ->
         In (a, c) (zip lsa lsc).

       induction lsa; intuition; simpl in *.
       destruct lsb;
       simpl in *.
       intuition.

       destruct lsc; simpl in *.
       intuition.

       intuition.
       pairInv.
       intuition.
       right.
       eapply IHlsa.
       eauto.

     Qed.

     eapply In_zip_3 in H6.
     eapply In_zip_3 in H9.
     eapply In_zip_strong in H6.
     eapply In_zip_strong in H9.
     intuition.
     subst.
     eapply map_ext_in.
     intuition.
     comp_simp.
     trivial.

     intuition.
     repeat intac; subst.
     eapply H6.
     clear H6.
     comp_simp.
     eapply In_zip_3 in H10.
     eapply In_zip_3 in H9.
     eapply In_zip_strong in H10.
     eapply In_zip_strong in H9.
     intuition.
     subst.
     unfold ESPADA_TSet_Once_Games.numberedMap in *.
     repeat rewrite fst_split_map_eq in *.
     repeat intac; subst.
     destruct x0.
     destruct (F b2 n).
     destruct p.
     destruct x1.
     destruct (F b4 n1).
     destruct p.
     simpl in *.
     pairInv.
     eapply map_ext_in.
     intuition.
     comp_simp.
     trivial.

     eapply list_pred_flatten_both.
     eapply list_pred_map_r'.
     eapply list_pred_map_l'.

     eapply list_pred_impl.

     eapply list_pred_eq_in.
     intuition.
     subst.
     unfold numberedMap.
     eapply list_pred_map_l'.
     eapply list_pred_map_r'.
     eapply list_pred_impl.
     eapply list_pred_eq_in.
     intuition.
     subst.
     destruct (F b2 a1).
     destruct p.
     intuition.

     eapply In_zip in H7.
     intuition.

     rewrite <- zip_combine_eq.
     eauto.

     symmetry.
     eapply compMap_length.
     eauto.

     eapply compMap_length.
     eauto.
   Qed.
    
   Definition ESPADA_TSetCorr_G13_1  :=
     [t, q] <-$2 A1;
     q <- removeDups _ q;
     allQs <- combineKeywords q (toW t);
     allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
      ts <- map (arrayLookupList _ t) allQs;
      ts_recsList <- map 
                  (fun p => [q, ls] <-2 p; numberedMap 
                                             (fun i len s_i =>
                                                ((q, i), (len, s_i))) ls) (zip allQs ts);
      tSet <- (flatten ts_recsList) ;
      bad <- negb
          (eqb (foreach  (x in allQs)ESPADA_TSetRetrieve_Corr_13 maxMatches tSet x)
               (foreach  (x in allQs)arrayLookupList (list_EqDec bool_EqDec) t x));
      ret ((labelCollision_9 _ maxMatches F allTags) || bad).
   
    Definition TSetCorr_13_2_Record := (nat * (nat * (Bvector lambda)))%type.

    Definition TSetCorr_13_2 := list (Blist * list TSetCorr_13_2_Record).
    
    
    Definition ESPADA_TSetRetrieve_tLoop_Corr_13_2 (tSet : list TSetCorr_13_2_Record) i :=
    t <- arrayLookup _ tSet i;
    match t with
        | None => None
        | Some (len, s_i) => 
            Some (s_i, if (eq_nat_dec (S i) len) then false else true)
    end.

  Fixpoint ESPADA_TSetRetrieve_h_Corr_13_2 (tSet : list TSetCorr_13_2_Record) i (fuel : nat) :=
    match fuel with
      | O => nil
      | S fuel' =>
        match (ESPADA_TSetRetrieve_tLoop_Corr_13_2 tSet i) with
          | Some (v, b) =>
          v :: (if b then (ESPADA_TSetRetrieve_h_Corr_13_2 tSet (S i) fuel') else nil)
          | None => nil
        end
      end.

  Definition ESPADA_TSetRetrieve_Corr_13_2 tSet (q : Blist) :=
    ls <- arrayLookupList _ tSet q;
    ESPADA_TSetRetrieve_h_Corr_13_2 ls O maxMatches.

    Definition ESPADA_TSetCorr_G13_2  :=
      [t, q] <-$2 A1;
      q <- removeDups _ q;
      allQs <- combineKeywords q (toW t);
      allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
      ts <- map (arrayLookupList _ t) allQs;
      ts_recsList <- map 
                  (fun p => [q, ls] <-2 p; numberedMap 
                                             (fun i len s_i =>
                                                (i, (len, s_i))) ls) (zip allQs ts);
      tSet <- combine allQs ts_recsList ;
      bad <- negb
          (eqb (foreach  (x in allQs)ESPADA_TSetRetrieve_Corr_13_2 tSet x)
               (foreach  (x in allQs)arrayLookupList (list_EqDec bool_EqDec) t x));
      ret ((labelCollision_9 _ maxMatches F allTags) || bad).

    Theorem ESPADA_TSetCorr_G13_1_equiv :
      Pr[ESPADA_TSetCorr_G13 maxMatches F A1] == Pr[ESPADA_TSetCorr_G13_1].
      
      unfold ESPADA_TSetCorr_G13, ESPADA_TSetCorr_G13_1.
      
      comp_skip.
      comp_simp.
      comp_skip.
      
      eapply evalDist_ret_eq.
      f_equal.
      f_equal.
      f_equal.
      eapply map_ext_in.
      intuition.
      f_equal.
      f_equal.
      eapply map_eq.
      eapply list_pred_impl.
      eapply list_pred_zip_l.
      eapply list_pred_map_r.
      eapply list_pred_zip_l.
      eapply list_pred_I.
      symmetry.
      eapply compMap_length.
      eauto.
      eapply list_pred_eq.
      eapply list_pred_I.
      eapply compMap_length.
      eauto.
      eapply list_pred_zip_r.
      eapply list_pred_map_r.
      eapply list_pred_eq.
      eapply list_pred_zip_r.
      eapply list_pred_I.
      symmetry.
      eapply compMap_length.
      eauto.
      eapply list_pred_eq.
      eapply list_pred_I.
      eapply compMap_length.
      eauto.
      eapply list_pred_map_l.
      eapply list_pred_zip_r.
      eapply list_pred_I.
      symmetry.
      eapply compMap_length.
      eauto.
      eapply list_pred_eq.
      eapply list_pred_I.
      eapply compMap_length.
      eauto.
      eapply list_pred_zip_r.
      eapply list_pred_map_r.
      eapply list_pred_eq.
      eapply list_pred_map_r.
      eapply list_pred_eq.
      eapply list_pred_eq.
      intuition.
      repeat exdest.
      simpl in *.
      subst.
      intuition.
      subst.
      destruct b1.
      simpl in *.
      subst.
      unfold numberedMap.
      eapply map_ext_in.
      intuition.
      comp_simp.
      trivial.
    Qed.

    Theorem ESPADA_TSetCorr_G13_1_2_equiv :
      Pr[ESPADA_TSetCorr_G13_1] == Pr[ESPADA_TSetCorr_G13_2].
      
      unfold ESPADA_TSetCorr_G13_1, ESPADA_TSetCorr_G13_2.

      comp_skip; comp_simp.
      comp_skip.
      eapply evalDist_ret_eq.
      f_equal.
      f_equal.
      f_equal.
      eapply map_ext_in.
      intuition.
      
      Theorem TSetRetrieve_tLoop_Corr_13_2_equiv : 
        forall i ls1 ls2 q,
          (arrayLookup _ (flatten ls1) (q, i) = 
          arrayLookup _ (arrayLookupList _ ls2 q) i) ->
        ESPADA_TSetRetrieve_tLoop_Corr_13 (flatten ls1) q i =
        ESPADA_TSetRetrieve_tLoop_Corr_13_2
          (arrayLookupList (list_EqDec bool_EqDec) ls2 q) i.

        intuition.
        unfold ESPADA_TSetRetrieve_tLoop_Corr_13, ESPADA_TSetRetrieve_tLoop_Corr_13_2.
        rewrite H.
        comp_simp.
        unfold Blist in *.
        destruct ( arrayLookup nat_EqDec (arrayLookupList (list_EqDec bool_EqDec) ls2 q) i); intuition.
      Qed.


      Theorem TSetRetrieve_h_Corr_13_2_equiv : 
        forall fuel i ls1 ls2 q,
          (forall i, (arrayLookup _ (flatten ls1) (q, i) = 
          arrayLookup _ (arrayLookupList _ ls2 q) i)) ->
        ESPADA_TSetRetrieve_h_Corr_13 (flatten ls1) q i fuel =
        ESPADA_TSetRetrieve_h_Corr_13_2
          (arrayLookupList (list_EqDec bool_EqDec) ls2 q) i fuel.

        induction fuel; intuition; simpl in *.
        rewrite (@TSetRetrieve_tLoop_Corr_13_2_equiv _ _ ls2) .
        destruct (ESPADA_TSetRetrieve_tLoop_Corr_13_2
       (arrayLookupList (list_EqDec bool_EqDec) ls2 q) i).
        comp_simp.
        f_equal.
        destruct b0; trivial.
        eapply IHfuel; intuition.
        trivial.
        eauto.

      Qed.

      Theorem TSetRetrieve_Corr_13_2_equiv : 
        forall ls1 ls2 q,
          (forall i, (arrayLookup _ (flatten ls1) (q, i) = 
          arrayLookup _ (arrayLookupList _ ls2 q) i)) ->
          ESPADA_TSetRetrieve_Corr_13 maxMatches (flatten ls1) q = 
          ESPADA_TSetRetrieve_Corr_13_2 ls2 q.

        intuition.
        unfold ESPADA_TSetRetrieve_Corr_13, ESPADA_TSetRetrieve_Corr_13_2.
        unfold setLet.
        apply TSetRetrieve_h_Corr_13_2_equiv.
        eauto.
 
      Qed.

      eapply  TSetRetrieve_Corr_13_2_equiv.
      intuition.

     
      erewrite (@arrayLookup_flatten_eq _ _ _ _ _ _ (combineKeywords (removeDups (list_EqDec bool_EqDec) l) (toW t))).

      eapply arrayLookup_pair_snd .

      eapply arrayLookup_pred_2 .
      repeat rewrite <- zip_combine_eq.
      eapply list_pred_impl.

      Ltac predtac :=
        match goal with
          | [ |- _ ] => eapply list_pred_eq
          | [ |- list_pred _ _ (map _ _ ) ] => eapply list_pred_map_r
          | [ |- list_pred _ (map _ _ ) _ ] => eapply list_pred_map_l
          | [ |- list_pred _ _ (zip _ _ ) ] => eapply list_pred_zip_r
          | [ |- list_pred _ (zip _ _ ) _ ] => eapply list_pred_zip_l
        end.

      repeat predtac.

      intuition.
      repeat (exdest; intuition); simpl in *; subst.
      subst.
      trivial.
      subst.
      repeat (exdest; intuition); simpl in *; subst.
      destruct x0.
      destruct b0.
      simpl in *.
      subst.
      destruct x6.
      unfold numberedMap.
      eapply list_pred_map_r'.
      eapply list_pred_map_l'.
      simpl in *.
      subst.
      eapply list_pred_impl.
      eapply list_pred_eq.
      intuition.
      subst.
      simpl.
      trivial.
      subst.
      simpl.
      trivial.
      repeat (exdest; intuition); simpl in *; subst.
      trivial.
      repeat (exdest; intuition); simpl in *; subst.
      destruct x0.
      destruct b0.
      simpl in *; subst.
      destruct x6.
      simpl in *.
      subst.
      unfold numberedMap.
      eapply list_pred_map_l'.
      eapply list_pred_map_r'.
      eapply list_pred_impl.
      eapply list_pred_eq.

      intuition.
      subst.
      simpl.
      trivial.
      subst.
      simpl.
      trivial.
      econstructor.
      
      eapply list_pred_map_r'.
      eapply list_pred_impl.
      eapply list_pred_zip_r.
      eapply list_pred_map_r.
      eapply list_pred_eq.
      eapply list_pred_eq.
      eapply list_pred_map_l.
      eapply list_pred_eq.
      
      intuition.
      intuition.
      repeat (exdest; intuition).
      subst.
      destruct b.
      destruct x0.
      destruct p.
      simpl in *.
      unfold numberedMap in *.
      eapply in_map_iff in H3.
      exdest.
      intuition.
      destruct x0.
      pairInv.
      trivial.

      eapply combineKeywords_NoDup.
      eapply removeDups_NoDup.
      eapply toW_NoDup.

    Qed.

    Definition TSetCorr_13_3_Record := (nat * ( (Bvector lambda)))%type.
    
    Definition TSetCorr_13_3 := list (Blist * list TSetCorr_13_3_Record). 
 
    
    Definition ESPADA_TSetRetrieve_tLoop_Corr_13_3 (tSet : list TSetCorr_13_3_Record) i :=
      arrayLookup _ tSet i.
    
    Fixpoint ESPADA_TSetRetrieve_h_Corr_13_3 (tSet : list TSetCorr_13_3_Record) i (fuel : nat) :=
      match fuel with
        | O => nil
        | S fuel' =>
          match (ESPADA_TSetRetrieve_tLoop_Corr_13_3 tSet i) with
            | Some v =>
              v :: (ESPADA_TSetRetrieve_h_Corr_13_3 tSet (S i) fuel')
            | None => nil
          end
      end.
    
    Definition ESPADA_TSetRetrieve_Corr_13_3 tSet (q : Blist) :=
      ls <- arrayLookupList _ tSet q;
      ESPADA_TSetRetrieve_h_Corr_13_3 ls O maxMatches.

    Definition ESPADA_TSetCorr_G13_3  :=
      [t, q] <-$2 A1;
      q <- removeDups _ q;
      allQs <- combineKeywords q (toW t);
      allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
      ts <- map (arrayLookupList _ t) allQs;
      ts_recsList <- map 
                  (fun p => [q, ls] <-2 p; numberedMap 
                                             (fun i len s_i =>
                                                (i, s_i)) ls) (zip allQs ts);
      tSet <- combine allQs ts_recsList ;
      bad <- negb
          (eqb (foreach  (x in allQs)ESPADA_TSetRetrieve_Corr_13_3 tSet x)
               (foreach  (x in allQs)arrayLookupList (list_EqDec bool_EqDec) t x));
      ret ((labelCollision_9 _ maxMatches F allTags) || bad).


    Theorem ESPADA_TSetCorr_G13_2_3_equiv :
      Pr[ESPADA_TSetCorr_G13_2] == Pr[ESPADA_TSetCorr_G13_3].

      unfold ESPADA_TSetCorr_G13_2, ESPADA_TSetCorr_G13_3.
      comp_skip; comp_simp.
      comp_skip.
      eapply evalDist_ret_eq.
      f_equal.
      f_equal.
      f_equal.
      eapply map_ext_in.
      intuition.
      
       Theorem TSetRetrieve_tLoop_13_2_3_equiv : 
        forall i t1 t2,
          (arrayLookup _ t2 i = 
           match (arrayLookup _ t1 i) with
             | Some (_, b) => Some b
             | None => None
           end) ->
          ESPADA_TSetRetrieve_tLoop_Corr_13_3 t2 i = 
          match (ESPADA_TSetRetrieve_tLoop_Corr_13_2 t1 i) with
            | Some (x, b) => Some x
            | None => None
          end.

         intuition.
         unfold  ESPADA_TSetRetrieve_tLoop_Corr_13_3,  ESPADA_TSetRetrieve_tLoop_Corr_13_2.
         unfold setLet.
         rewrite H.
         case_eq (arrayLookup nat_EqDec t1 i); intuition.
         destruct p.
         trivial.

       Qed.
          
      
      Theorem TSetRetrieve_h_13_2_3_equiv : 
        forall fuel i t1 t2,
          list_pred (fun x y => fst x = fst y /\ snd (snd x) = (snd y) /\
                    (S (fst x) = fst (snd x) -> arrayLookup _ t2 (S (fst x)) = None)) t1 t2 ->
          NoDup (fst (split t1)) ->
          (forall n, In n (fst (split (snd (split t1)))) -> n = length t1) ->
          ESPADA_TSetRetrieve_h_Corr_13_2 t1 i fuel = 
          ESPADA_TSetRetrieve_h_Corr_13_3 t2 i fuel.

        induction fuel; intuition; simpl in *.
        unfold ESPADA_TSetRetrieve_tLoop_Corr_13_2, ESPADA_TSetRetrieve_tLoop_Corr_13_3.
        unfold setLet.
        
        case_eq (arrayLookup nat_EqDec t1 i); intuition.
        destruct p.
        eapply arrayLookup_Some_impl_In in H2.
        specialize (list_pred_In_exists H _ H2); intuition.
        destruct H3.
        intuition.
        destruct (eq_nat_dec (S i) n).
        simpl in *.
        subst.
        destruct x.
        simpl in *.
        erewrite arrayLookup_In_NoDup; eauto.
        f_equal.
        destruct fuel; simpl in *; trivial.
        unfold ESPADA_TSetRetrieve_tLoop_Corr_13_3.
        rewrite H8.
        trivial.
        trivial.

        rewrite (@list_pred_fst_split_eq _ _ _ _ t1).
        trivial.
        eapply list_pred_symm.
        eapply list_pred_impl.
        eauto.
        intuition.

        simpl in *.
        subst.
        destruct x.
        simpl in *.
        erewrite arrayLookup_In_NoDup; eauto.
        f_equal.
        eauto.
        rewrite (@list_pred_fst_split_eq _ _ _ _ t1).
        trivial.
        eapply list_pred_symm.
        eapply list_pred_impl.
        eauto.
        intuition.
        
        rewrite notInArrayLookupNone.
        trivial.
        intuition.

        rewrite  unzip_eq_split  in H3.
        rewrite (@list_pred_fst_split_eq _ _ _ _ t1) in H3.
        eapply arrayLookup_None_not_In.
        eauto.
        trivial.
        eapply list_pred_symm.
        eapply list_pred_impl.
        eauto.
        intuition.
      Qed.

      Theorem TSetRetrieve_13_2_3_equiv : 
        forall t1 t2 a,
          (list_pred
     (fun (x : nat * (nat * Bvector lambda)) (y : nat * Bvector lambda) =>
      fst x = fst y /\
      snd (snd x) = snd y /\
      (S (fst x) = fst (snd x) ->
       arrayLookup nat_EqDec (arrayLookupList (list_EqDec bool_EqDec) t2 a)
         (S (fst x)) = None)) (arrayLookupList (list_EqDec bool_EqDec) t1 a)
     (arrayLookupList (list_EqDec bool_EqDec) t2 a)) ->

          NoDup (fst (split (arrayLookupList (list_EqDec bool_EqDec) t1 a))) ->

          (forall n : nat,
   In n
     (fst
        (split (snd (split (arrayLookupList (list_EqDec bool_EqDec) t1 a))))) ->
   n = length (arrayLookupList (list_EqDec bool_EqDec) t1 a)) ->

          ESPADA_TSetRetrieve_Corr_13_2 t1 a = 
          ESPADA_TSetRetrieve_Corr_13_3 t2 a.

        intuition.
        unfold ESPADA_TSetRetrieve_Corr_13_2, ESPADA_TSetRetrieve_Corr_13_3.
        unfold setLet.
        eapply TSetRetrieve_h_13_2_3_equiv ;
        eauto.
      Qed.

      eapply TSetRetrieve_13_2_3_equiv.
      intuition.

      eapply arrayLookup_pred_2.
      repeat rewrite <- zip_combine_eq.
      eapply list_pred_impl.
      repeat predtac.
      intuition.
      repeat (exdest; intuition); simpl in *; subst.
      trivial.
      repeat (exdest; intuition); simpl in *; subst.
      destruct b0; simpl in *; subst.
      destruct x0; destruct x6.
      unfold numberedMap.
      eapply list_pred_map_l'.
      eapply list_pred_map_r'.
      simpl in *; subst.
      eapply list_pred_impl.
      eapply list_pred_eq.
      intuition; subst.
      trivial.
      simpl.
      trivial.
      
      simpl in *.
      subst.
      eapply notInArrayLookupNone.
      intuition.

      rewrite unzip_eq_split in H2.
      eapply in_split_l_if in H2.
      destruct H2.

      destruct x13; simpl in *; subst.
      destruct x3; simpl in *; subst.
      destruct x10; simpl in *; subst.

      eapply In_arrayLookupList in H2.
      destruct H2.
      intuition.
      eapply list_pred_zip_in in H5.
      Focus 2.
      eapply list_pred_map_r.
      eapply list_pred_zip_r.
      eapply list_pred_map_r.
      eapply list_pred_eq.
      eapply list_pred_eq.
      eapply list_pred_map_l.
      eapply list_pred_eq.
      simpl in *.
      repeat (exdest; intuition); simpl in *; subst.
      destruct x2.
      eapply in_map_iff in H6.
      destruct H6.
      intuition.
      destruct x1.
      pairInv.
      simpl in *.
      subst.
      eapply In_zip in H6.
      intuition.
     
      eapply allNatsLt_lt in H2.
      omega.

      repeat (exdest; intuition). simpl in *; subst.
      trivial.

      repeat (exdest; intuition). simpl in *; subst.
      destruct b0; simpl in *.
      subst.
      destruct x0.
      destruct x6.
      simpl in *; subst.
      unfold numberedMap.
      eapply list_pred_map_r'.
      eapply list_pred_map_l'.
      eapply list_pred_impl.
      eapply list_pred_eq.
      intuition; subst.
      trivial.
      trivial.

      simpl in *; subst.
      destruct x3, x13, x10; simpl in *; subst.
      eapply notInArrayLookupNone.
      intuition.
      rewrite unzip_eq_split in H3.
      eapply in_split_l_if in H3.
      destruct H3.
      eapply In_arrayLookupList in H2.
      destruct H2.
      intuition.
      eapply list_pred_zip_in in H3.
      Focus 2.
      eapply list_pred_map_r.
      eapply list_pred_zip_r.
      eapply list_pred_map_r.
      eapply list_pred_eq.
      eapply list_pred_eq.
      eapply list_pred_map_l.
      eapply list_pred_eq.
      simpl in *.
      repeat (exdest; intuition); simpl in *; subst.
      destruct x2.
      eapply in_map_iff in H6.
      destruct H6.
      intuition.
      destruct x1.
      pairInv.
      simpl in *.
      subst.
      eapply In_zip in H6.
      intuition.
     
      eapply allNatsLt_lt in H2.
      omega.
      
      econstructor.
      eapply arrayLookupList_pred.
      intuition.
      destruct x0.
      simpl.
      eapply in_combine_r in H2.
      repeat intac.
      destruct x0.
      subst.
      unfold numberedMap.
      rewrite fst_split_map_eq.
      eapply NoDup_gen_eq.
      eapply (@map_NoDup_gen _ _ (fun a b => fst a = fst b)); intuition; simpl in *; subst.
      destruct a2; simpl in *; trivial.
      destruct a2; simpl in *; trivial.
      eapply NoDup_gen_zip_fst.
      eapply NoDup_gen_eq.
      eapply allNatsLt_NoDup.
      simpl.
      econstructor.

      intuition.
      eapply in_split_l_if in H2.
      destruct H2.

      eapply in_split_r_if in H2.
      destruct H2.
      eapply In_arrayLookupList in H2.
      destruct H2.
      intuition.
      rewrite <- zip_combine_eq in H3.
      eapply list_pred_zip_in in H3.
      Focus 2.
      repeat predtac.
      simpl in *.
      repeat (exdest; intuition).
      simpl in *; subst.
      destruct x3.
      simpl in *; subst.
      unfold numberedMap in *.
      repeat intac.
      destruct x2.
      pairInv.

      symmetry.
      eapply arrayLookupList_pred'.
      intuition.
      rewrite <- zip_combine_eq in H2.
      eapply list_pred_zip_in in H2.
      Focus 2.
      repeat predtac.
      simpl in *.
      repeat (exdest; intuition).
      subst.
      destruct x3; simpl in *; subst.
      rewrite map_length.
      rewrite zip_length.
      eapply allNatsLt_length.
      eapply allNatsLt_length.
      intuition.
      eapply arrayLookup_None_not_In in H2;
      intuition.
      rewrite combine_split.
      simpl.
      trivial.
      rewrite map_length.
      rewrite zip_length.
      trivial.
      rewrite map_length.
      trivial.
    Qed.

    Theorem ESPADA_TSetCorr_G13_3_G14_equiv : 
      Pr[ESPADA_TSetCorr_G13_3] == Pr[ESPADA_TSetCorr_G14 maxMatches F A1].

      unfold ESPADA_TSetCorr_G13_3, ESPADA_TSetCorr_G14.
      comp_skip; comp_simp.
      comp_skip.
      eapply evalDist_ret_eq.
      f_equal.
      f_equal.
      f_equal.
      eapply map_ext_in.
      intuition.
      
      unfold  ESPADA_TSetRetrieve_Corr_13_3,  ESPADA_TSetRetrieve_Corr_14.
      unfold setLet.
      
      Theorem skipn_length_nil : 
        forall (A : Type)(ls : list A) n,
          n >= length ls ->
          skipn n ls = nil.
        
        induction ls; destruct n; simpl in *; intuition.
        omega.

      Qed.

      Theorem ESPADA_TSetRetrieve_tLoop_Corr_13_3_eq : 
        forall ls i,
          fst (split ls) = allNatsLt (length ls) ->
          ESPADA_TSetRetrieve_tLoop_Corr_13_3 ls i = 
          match (nth_option ls i) with
              | None => None
              | Some (_, v) => Some v
          end.

        intuition.
        unfold  ESPADA_TSetRetrieve_tLoop_Corr_13_3.

        eapply arrayLookup_allNats_eq .
        trivial.

      Qed.

      Theorem ESPADA_TSetRetrieve_h_Corr_13_3_eq : 
        forall fuel i ls,
          fst (split ls) = allNatsLt (length ls) -> 
          fuel + i >= length ls->
          ESPADA_TSetRetrieve_h_Corr_13_3 ls i fuel = 
          skipn i (snd (split ls)).
        
        induction fuel; intuition; simpl in *.
        symmetry.
        eapply skipn_length_nil.
        rewrite split_length_r.
        trivial.

        rewrite ESPADA_TSetRetrieve_tLoop_Corr_13_3_eq.
        case_eq ( @nth_option (prod nat (Bvector (posnatToNat lambda))) ls i); intuition.
        destruct p.
        rewrite IHfuel.

        symmetry.
        eapply  skipn_S_eq .

        eapply nth_option_snd_split.
        eauto.
        trivial.
        omega.

        eapply nth_option_None_ge in H1.
        rewrite skipn_length_nil.
        trivial.
        rewrite split_length_r.
        trivial.
       
        trivial.

      Qed.

      rewrite ESPADA_TSetRetrieve_h_Corr_13_3_eq.
      simpl.
      eapply arrayLookupList_pred'.
      intuition.
      repeat rewrite <- zip_combine_eq in H2.
      eapply list_pred_zip_in in H2.
      Focus 2.
      repeat predtac.
      simpl in *.
      repeat (exdest; intuition).
      subst.
      destruct x1.
      simpl in *; subst.
      symmetry.
      eapply arrayLookupList_pred'.
      intuition.
      repeat rewrite <- zip_combine_eq in H2.
      eapply list_pred_zip_in in H2.
      Focus 2.
      eapply list_pred_map_r.
      eapply list_pred_eq.
      simpl in *.
      exdest.
      intuition.
      subst.
      unfold numberedMap.
      
      rewrite snd_split_map_eq.
      
      assert (
          (@map (prod nat (Bvector (posnatToNat lambda)))
        (Bvector (posnatToNat lambda))
        (fun p : prod nat (Bvector (posnatToNat lambda)) =>
         @snd nat (Bvector (posnatToNat lambda))
           match p return (prod nat (Bvector (posnatToNat lambda))) with
           | pair i a => @pair nat (Bvector (posnatToNat lambda)) i a
           end)
        (@zip nat (Bvector (posnatToNat lambda))
           (allNatsLt
              (@length (Bvector (posnatToNat lambda))
                 (@arrayLookupList Blist (Bvector (posnatToNat lambda))
                    (@list_EqDec bool bool_EqDec) t x1)))
           (@arrayLookupList Blist (Bvector (posnatToNat lambda))
              (@list_EqDec bool bool_EqDec) t x1)))
     =
     map (@snd _ _ )
     (zip (allNatsLt (length (arrayLookupList (list_EqDec bool_EqDec) t x1)))
        (arrayLookupList (list_EqDec bool_EqDec) t x1))
     ).
      eapply map_ext.
      intuition.
      rewrite H2.
      clear H2.
      rewrite map_snd_zip.
      trivial.
      eapply allNatsLt_length.
      
      intuition.
      eapply arrayLookup_None_not_In in H2.
      intuition.
      rewrite combine_split.
      simpl.
      trivial.
      
      rewrite map_length.
      trivial.

      intuition.
      eapply arrayLookup_None_not_In in H2.
      intuition.
      rewrite combine_split.
      simpl.
      trivial.

      rewrite map_length.
      rewrite zip_length.
      trivial.
      rewrite map_length.
      trivial.

      eapply arrayLookupList_pred'.
      intuition.
      repeat rewrite <- zip_combine_eq in H2.
      repeat intac.
      subst.
      destruct x1.
      unfold numberedMap.
      assert (
          (map (fun p : nat * Bvector lambda => [i, a0]<-2 p; (i, a0))
           (zip (allNatsLt (length l0)) l0))
             =
             (map (fun p => p)
           (zip (allNatsLt (length l0)) l0))
        ).
      eapply map_ext.
      intuition.
      rewrite H3.
      clear H3.
      rewrite map_id.
      rewrite zip_combine_eq.
      rewrite combine_split.
      simpl.
      rewrite combine_length.
      rewrite allNatsLt_length.
      rewrite Min.min_idempotent.
      trivial.
      eapply allNatsLt_length.

      intuition.
      
      eapply arrayLookupList_pred.
      intuition.
      destruct x0.
      eapply in_combine_r in H2.
      repeat intac.
      subst.
      simpl.
      destruct x0.
      unfold numberedMap.
      rewrite map_length.
      eapply In_zip in H3.
      intuition.
      repeat intac.
      subst.
      rewrite zip_length.
      rewrite allNatsLt_length.
      rewrite plus_0_r.
      unfold maxMatch in *.
      eapply arrayLookupList_pred.
      eauto.
      simpl.
      omega.
      eapply allNatsLt_length.

      simpl.
      omega.

    Qed.

    Theorem ESPADA_TSetCorr_G13_G14_equiv : 
      Pr[ESPADA_TSetCorr_G13 maxMatches F A1] == Pr[ESPADA_TSetCorr_G14 maxMatches F A1].

      rewrite ESPADA_TSetCorr_G13_1_equiv.
      rewrite ESPADA_TSetCorr_G13_1_2_equiv.
      rewrite ESPADA_TSetCorr_G13_2_3_equiv.
      apply ESPADA_TSetCorr_G13_3_G14_equiv.

    Qed.

   Theorem ESPADA_TSetCorr_G14_G15_equiv :
     Pr[ESPADA_TSetCorr_G14 maxMatches F A1] == Pr[ESPADA_TSetCorr_G15 maxMatches F A1].

     unfold ESPADA_TSetCorr_G14, ESPADA_TSetCorr_G15.

     comp_skip.
     comp_simp.
     comp_skip.

     case_eq (labelCollision_9 _ maxMatches F x); intuition.
     simpl.
     intuition.
     
     rewrite evalDist_ret_0.
     rewrite evalDist_ret_0;
     intuition.
     
     simpl.
     intuition.
     eapply negb_true_iff in H2.
     eapply eqb_false_iff in H2.
     
     eapply map_ne_same_ex in H2.
     destruct H2.
     intuition.
     eapply H4.
     clear H4.
     unfold ESPADA_TSetRetrieve_Corr_14.
     eapply arrayLookupList_pred'.
     intuition.
     repeat rewrite <- zip_combine_eq in H2.
     eapply list_pred_zip_in in H2.
     Focus 2.
     eapply list_pred_map_r.
     eapply list_pred_eq.
     simpl in *.
     exdest.
     intuition.
     subst.
     trivial.

     intuition.
     eapply arrayLookup_None_not_In in H2.
     intuition.
     rewrite combine_split.
     simpl.
     trivial.

     rewrite map_length.
     trivial.

     unfold eq_dec.
     intuition.
     eapply (EqDec_dec _).

   Qed.

   
   Require Import PRF.


   Definition ESPADA_TSetCorr_G15_1  :=
     [t, q] <-$2 A1;
     q <- removeDups _ q;
     allQs <- combineKeywords q (toW t);
     allLabels <-$ 
               (allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
                ret (map (fun x => map (F x) (allNatsLt (S maxMatches))) allTags));
     ret (hasDups _ (fst (split (flatten allLabels)))).

    Theorem ESPADA_TSetCorr_G15_1_equiv : 
     Pr[ESPADA_TSetCorr_G15 maxMatches F A1] == Pr[ESPADA_TSetCorr_G15_1].

     unfold ESPADA_TSetCorr_G15, ESPADA_TSetCorr_G15_1.

     comp_skip.
     comp_simp.
     inline_first.
     comp_skip.
     comp_simp.
     unfold labelCollision_9.
     rewrite getAllLabels_8_1_equiv.
     unfold getAllLabels_8_1.

     eapply evalDist_ret_eq.
     f_equal.
     rewrite fst_split_flatten_eq.
     f_equal.
     rewrite map_map.
     eapply map_ext.
     intuition.
     rewrite fst_split_map_eq.
     reflexivity.

    Qed.

   Theorem ESPADA_TSetCorr_G15_1_G16_equiv : 
     Pr[ESPADA_TSetCorr_G15_1] == Pr[ESPADA_TSetCorr_G16 maxMatches F A1].

     unfold ESPADA_TSetCorr_G15_1, ESPADA_TSetCorr_G16.
     unfold PRFI_A1, PRFI_A2.
     inline_first.
     comp_skip.
     comp_simp.
     comp_skip.     

     eapply comp_spec_eq_impl_eq.
     eapply comp_spec_eq_trans.
     Focus 2.
     eapply comp_spec_eq_symm.
     eapply compMap_seq_map .
     cbv beta.
     simpl.

     eapply compMap_map_fission_eq.
     intuition.
     eapply comp_spec_consequence.
     eapply comp_spec_eq_refl.
     intuition; subst.
     trivial.
   Qed.

   Theorem ESPADA_TSetCorr_G15_G16_equiv : 
     Pr[ESPADA_TSetCorr_G15 maxMatches F A1] ==
     Pr[ESPADA_TSetCorr_G16 maxMatches F A1].

     rewrite ESPADA_TSetCorr_G15_1_equiv.
     eapply ESPADA_TSetCorr_G15_1_G16_equiv.

   Qed.

   Theorem ESPADA_TSetCorr_G16_G17_equiv : 
     | Pr[ESPADA_TSetCorr_G16 maxMatches F A1] - Pr[(ESPADA_TSetCorr_G17 bigB maxMatches A1)] |
     == 
     PRF_NAI_Advantage (Rnd lambda) (RndF_R lambda bigB) F _ _ (PRFI_A1 maxMatches A1) (@PRFI_A2 lambda).

     unfold ESPADA_TSetCorr_G16, ESPADA_TSetCorr_G17, PRF_NAI_Advantage.
     reflexivity.
 
   Qed.

   Theorem ESPADA_TSetCorr_G17_G18_equiv : 
     Pr[ESPADA_TSetCorr_G17 bigB maxMatches A1] == Pr[ESPADA_TSetCorr_G18 bigB maxMatches A1].

     unfold ESPADA_TSetCorr_G17, ESPADA_TSetCorr_G18 .
     unfold PRFI_A1, PRFI_A2.
     inline_first.
     comp_skip.
     comp_simp.
     comp_skip.
     eapply compMap_eq.
     eapply list_pred_eq_in.
     intuition.
     intuition.
     subst.
     eapply in_map_iff in H3.
     destruct H3.
     intuition.
     subst.
     clear H0.
     symmetry.
     rewrite <- evalDist_right_ident.
     eapply comp_spec_eq_impl_eq.
     comp_skip.
     unfold oracleMap.
     eapply comp_spec_eq_trans_l.
     eapply compMap_fold_equiv.
     unfold compMap_fold.
     specialize (compFold_spec); intuition.
     eapply (@compFold_spec _ _ _ (fun ls a b => a = fst b /\ NoDup ls /\ forall x, In x ls -> arrayLookup _ (snd b) x = None)).
     intuition.
     eapply allNatsLt_NoDup.
     intuition.
     subst.
     inversion H1; clear H1; subst.
     comp_simp.
     unfold RndR_func, randomFunc.
     simpl in *.
     rewrite H5.
     inline_first.
     comp_skip.
     comp_simp.
     eapply comp_spec_ret; intuition.
     simpl.
     case_eq (eqb x2 a); intuition.
     rewrite eqb_leibniz in H9.
     subst.
     intuition.
     intuition.

     comp_simp.
     intuition; simpl in *; subst.
     eapply comp_spec_eq_refl.
   Qed.

   Variable maxKeywords : nat.
   Hypothesis maxKeywords_correct : 
     forall t l, 
       In (t, l) (getSupport A1) ->
       (length (combineKeywords (removeDups (list_EqDec bool_EqDec) l) (toW t)) <= maxKeywords)%nat.


   Definition ESPADA_TSetCorr_G18_1  :=
     [t, q] <-$2 A1;
     q <- removeDups _ q;
     allQs <- combineKeywords q (toW t);
     lsD <- map (fun _ => allNatsLt (S maxMatches)) allQs;
     allLabels <-$ compMap _ (fun lsD => compMap _ (fun _ => (RndF_R lambda bigB)) lsD) lsD;
     allQs' <- allNatsLt (maxKeywords - (length allQs));
     lsD' <- map (fun _ => allNatsLt (S maxMatches)) allQs';
     allLabels' <-$ compMap _ (fun lsD => compMap _ (fun _ => (RndF_R lambda bigB)) lsD) lsD';
     ret (hasDups _ (fst (split (flatten allLabels))) || hasDups _ (fst (split (flatten allLabels')))).

   Theorem ESPADA_TSetCorr_G18_1_equiv : 
     Pr[ ESPADA_TSetCorr_G18 bigB maxMatches A1] <=  Pr[ESPADA_TSetCorr_G18_1 ].

     unfold  ESPADA_TSetCorr_G18,  ESPADA_TSetCorr_G18_1 .
     comp_skip.
     comp_simp.
     comp_skip.
     comp_irr_r.
     eapply compMap_wf.
     intuition.
     eapply compMap_wf.
     intuition.
     unfold RndF_R.
     wftac.
     eapply comp_spec_impl_le.
     eapply comp_spec_ret; intuition.
 
   Qed.

   Definition ESPADA_TSetCorr_G18_2  :=
     [t, q] <-$2 A1;
     q <- removeDups _ q;
     allQs <- combineKeywords q (toW t);
     lsD <- map (fun _ => allNatsLt (S maxMatches)) allQs;
     allQs' <- allNatsLt (maxKeywords - (length allQs));
     lsD' <- map (fun _ => allNatsLt (S maxMatches)) allQs';
     allLabels <-$
     (allLabels <-$ compMap _ (fun lsD => compMap _ (fun _ => (RndF_R lambda bigB)) lsD) lsD;
     allLabels' <-$ compMap _ (fun lsD => compMap _ (fun _ => (RndF_R lambda bigB)) lsD) lsD';
     ret (allLabels ++ allLabels'));
     ret (hasDups _ (fst (split (flatten allLabels)))).

   Theorem ESPADA_TSetCorr_G18_1_2_equiv : 
     Pr[ ESPADA_TSetCorr_G18_1] <=  Pr[ESPADA_TSetCorr_G18_2 ].

     unfold ESPADA_TSetCorr_G18_1, ESPADA_TSetCorr_G18_2.
     comp_skip.
     comp_simp.
     inline_first.
     comp_skip.
     inline_first.
     comp_skip.
     comp_simp.
     eapply comp_spec_impl_le.
     eapply comp_spec_ret.
     intuition.

     eapply hasDups_true_not_NoDup.
     intuition.
     eapply orb_true_iff in H2.
     intuition.
     eapply hasDups_true_not_NoDup in H4.
     intuition.
     eapply H4.
     clear H4.

     rewrite fst_split_flatten_eq.
     rewrite fst_split_flatten_eq in H3.
     rewrite map_app in H3.
     rewrite flatten_app in H3.
     eapply NoDup_app_l.
     eauto.

     eapply hasDups_true_not_NoDup in H4.
     eapply H4.
     clear H4.
     rewrite fst_split_flatten_eq.
     rewrite fst_split_flatten_eq in H3.
     rewrite map_app in H3.
     rewrite flatten_app in H3.
     eapply NoDup_app in H3.
     intuition.
   Qed.

   Definition ESPADA_TSetCorr_G18_3 :=
     [t, q] <-$2 A1;
     q <- removeDups _ q;
     allQs <- combineKeywords q (toW t);
     lsD <- map (fun _ => allNatsLt (S maxMatches)) allQs;
     allQs' <- allNatsLt (maxKeywords - (length allQs));
     lsD' <- map (fun _ => allNatsLt (S maxMatches)) allQs';  
     allLabels <-$ compMap _ (fun lsD => compMap _ (fun _ => (RndF_R lambda bigB)) lsD) (lsD ++ lsD');
     ret (hasDups _ (fst (split (flatten allLabels)))).

   Theorem ESPADA_TSetCorr_G18_2_3_equiv : 
     Pr[ESPADA_TSetCorr_G18_2] == Pr[ESPADA_TSetCorr_G18_3].
     
     unfold ESPADA_TSetCorr_G18_2, ESPADA_TSetCorr_G18_3.
     comp_skip.
     comp_simp.
     comp_skip.
     symmetry.
     apply compMap_app.
     
   Qed.

   Definition ESPADA_TSetCorr_G18_4 :=
     allQs <- allNatsLt maxKeywords;
     lsD <- map (fun _ => allNatsLt (S maxMatches)) allQs;  
     allLabels <-$ compMap _ (fun lsD => compMap _ (fun _ => (RndF_R lambda bigB)) lsD) (lsD);
     ret (hasDups _ (fst (split (flatten allLabels)))).

   Theorem ESPADA_TSetCorr_G18_3_4_equiv : 
     Pr[ESPADA_TSetCorr_G18_3] == Pr[ESPADA_TSetCorr_G18_4].
     
     unfold ESPADA_TSetCorr_G18_3, ESPADA_TSetCorr_G18_4.
     comp_irr_l.
     comp_simp.
     comp_skip.
     
     eapply compMap_eq.

     eapply list_pred_I_in.
     rewrite app_length.
     repeat rewrite map_length.
     rewrite allNatsLt_length.

     specialize (maxKeywords_correct _ _ H).
     unfold Blist in *.

     remember ((@length (list bool)
           (combineKeywords
              (@removeDups (list bool) (@list_EqDec bool bool_EqDec) l)
              (@toW lambda t)))).
     rewrite le_plus_minus_r.
     symmetry.
     eapply allNatsLt_length.
     trivial.

     intuition.
     intuition.
     eapply in_app_or in H1.
     intuition.
     repeat intac.
     subst.
     reflexivity.
     repeat intac.
     subst.
     reflexivity.
   Qed.

   Definition ESPADA_TSetCorr_G18_5 :=
     allQs <- allNatsLt maxKeywords;
     lsD <- map (fun _ => allNatsLt (S maxMatches)) allQs;  
     allLabels <-$ compMap _ (fun lsD => compMap _ (fun _ => b <-$ RndNat bigB; l <-$ {0, 1}^lambda; ret (b, l)) lsD) (lsD);
     ret (hasDups _ (flatten allLabels)).

   Theorem ESPADA_TSetCorr_G18_4_5_equiv : 
     Pr[ESPADA_TSetCorr_G18_4] == Pr[ESPADA_TSetCorr_G18_5].

     unfold ESPADA_TSetCorr_G18_4, ESPADA_TSetCorr_G18_5.
     comp_simp.
     eapply comp_spec_eq_impl_eq.
     comp_skip.
     eapply compMap_spec.
     eapply list_pred_eq.
     intuition.
     subst.
     eapply compMap_spec.
     eapply list_pred_eq.
     intuition.
     subst.

     assert (
         comp_spec (fun a b => fst a = b) (RndF_R lambda bigB)
     (b1 <-$ [ 0  .. bigB); l <-$ { 0 , 1 }^lambda; ret (b1, l))
     ).
     unfold RndF_R.

     assert (Bvector lambda).
     eapply (oneVector lambda).
     assert (Bvector (S lambda)).
     eapply (oneVector (S lambda)).

     comp_skip.
     comp_skip.
     comp_irr_l.
     eapply comp_spec_ret; intuition.
     eauto.

     eapply comp_spec_ret.

     symmetry.
     erewrite list_pred_fst_split_flatten_eq_l.
     reflexivity.
     eauto.
   Qed.

    Definition ESPADA_TSetCorr_G18_6 :=
     allQs <- allNatsLt maxKeywords;
     lsD <- map (fun _ => allNatsLt (S maxMatches)) allQs;  
     allLabels <-$ 
               (x <-$ compMap _ (fun lsD => compMap _ (fun _ => b <-$ RndNat bigB; l <-$ {0, 1}^lambda; ret (b, l)) lsD) lsD;
                ret (flatten x));
     ret (hasDups _ allLabels).

    Theorem ESPADA_TSetCorr_G18_5_6_equiv : 
     Pr[ESPADA_TSetCorr_G18_5] == Pr[ESPADA_TSetCorr_G18_6].

      unfold ESPADA_TSetCorr_G18_5.
      unfold ESPADA_TSetCorr_G18_6.

      comp_simp.
      inline_first.
      comp_skip.
      comp_simp.
      reflexivity.

    Qed.

    Definition ESPADA_TSetCorr_G18_7 :=
     allQs <- allNatsLt maxKeywords;
     lsD <- map (fun _ => allNatsLt (S maxMatches)) allQs;  
     allLabels <-$ compMap _ (fun _ => b <-$ RndNat bigB; l <-$ {0, 1}^lambda; ret (b, l)) (flatten lsD);
     ret (hasDups _ allLabels).

    Theorem ESPADA_TSetCorr_G18_6_7_equiv : 
     Pr[ESPADA_TSetCorr_G18_6] == Pr[ESPADA_TSetCorr_G18_7].

      unfold ESPADA_TSetCorr_G18_6.
      unfold ESPADA_TSetCorr_G18_7.

      comp_simp.
      comp_skip.
      
      symmetry.
      rewrite <- evalDist_right_ident.
      symmetry.
      eapply comp_spec_eq_impl_eq.
      comp_skip.
      eapply compMap_flatten.
      simpl in *.
      subst.
      eapply comp_spec_eq_refl.
    Qed.

    Theorem ESPADA_TSetCorr_G18_7_G19_equiv : 
     Pr[ESPADA_TSetCorr_G18_7] == Pr[ESPADA_TSetCorr_G19 lambda bigB maxMatches maxKeywords].

      unfold ESPADA_TSetCorr_G18_7, ESPADA_TSetCorr_G19.

      comp_simp.
      comp_skip.
      eapply compMap_eq.
      eapply list_pred_I.

      rewrite length_flatten.
      rewrite fold_left_map_eq.
      rewrite allNatsLt_length.

      rewrite fold_add_const_mult.
      rewrite plus_0_r.
      repeat rewrite allNatsLt_length.
      trivial.

      intuition.

    Qed.

    Theorem ESPADA_TSetCorr_G18_G19_equiv : 
     Pr[ESPADA_TSetCorr_G18 bigB maxMatches A1] <= Pr[ESPADA_TSetCorr_G19 lambda bigB maxMatches maxKeywords].

      rewrite ESPADA_TSetCorr_G18_1_equiv.
      rewrite ESPADA_TSetCorr_G18_1_2_equiv.
      rewrite ESPADA_TSetCorr_G18_2_3_equiv.
      rewrite ESPADA_TSetCorr_G18_3_4_equiv.
      rewrite ESPADA_TSetCorr_G18_4_5_equiv.
      rewrite ESPADA_TSetCorr_G18_5_6_equiv.
      rewrite ESPADA_TSetCorr_G18_6_7_equiv.
      rewrite ESPADA_TSetCorr_G18_7_G19_equiv.
      reflexivity.
    Qed.

    Theorem ESPADA_TSetCorr_G19_G20_equiv :
      Pr[ESPADA_TSetCorr_G19 lambda bigB maxMatches maxKeywords] <= 
      Pr[ESPADA_TSetCorr_G20 lambda maxMatches maxKeywords].

      unfold ESPADA_TSetCorr_G19, ESPADA_TSetCorr_G20.

      eapply comp_spec_impl_le.
      comp_skip.
      eapply compMap_spec.
      eapply list_pred_eq.
      intuition.
      subst.
      comp_irr_l.
      eapply comp_spec_eq_trans_r.
      Focus 2.
      eapply comp_spec_right_ident.
      comp_skip.
      apply (oneVector lambda).
      apply (oneVector lambda).
      assert (
          comp_spec (fun x y => snd x = y) (ret (a, b0)) (ret b0)
        ).
      eapply comp_spec_ret.
      trivial.
      eauto.

      eapply comp_spec_ret.
      intuition.

      eapply list_pred_snd_split_eq_l in H1.
      subst.
      eapply hasDups_true_not_NoDup.
      intuition.
      eapply hasDups_true_not_NoDup in H2.
      eapply H2.
 
      eapply NoDup_snd_split_if.
      trivial.

    Qed.

    Theorem ESPADA_TSetCorr_G20_small :
      Pr[ESPADA_TSetCorr_G20 lambda maxMatches maxKeywords] <= 
      (maxKeywords * S maxMatches) ^ 2 / 2 ^ lambda.
      
      unfold ESPADA_TSetCorr_G20.
      rewrite dupProb.
      rewrite allNatsLt_length.
      reflexivity.
    Qed.

    Theorem ESPADA_TSetCorr_once_IPRF :
     Pr[gInst ESPADA_TSetCorr_G1 ] <=  (maxKeywords * (S maxMatches))^2 / 2 ^ lambda 
                                                                 + 
                                                                 PRF_NAI_Advantage ({ 0 , 1 }^lambda) (RndF_R lambda bigB) F nat_EqDec
     (pair_EqDec (pair_EqDec nat_EqDec (Bvector_EqDec lambda))
        (Bvector_EqDec (S lambda))) (PRFI_A1 maxMatches A1) (@PRFI_A2 lambda)
     +
     
                                                                 PRF.PRF_NA_Advantage ({ 0 , 1 }^lambda) ({ 0 , 1 }^lambda) F_bar
     (list_EqDec bool_EqDec) (Bvector_EqDec lambda)
     (ESPADA_TSet_PRF_A1
        (pair_EqDec
           (list_EqDec
              (pair_EqDec (list_EqDec bool_EqDec)
                 (list_EqDec (Bvector_EqDec lambda))))
           (list_EqDec (list_EqDec bool_EqDec)))
        (z <-$ A1; [t, l]<-2 z; ret (t, l, (t, l))))
     (ESPADA_TSet_PRF_A2 bigB bigS F
        (fun (s : (T lambda * list Blist))
           (p : option (TSet lambda) * list (Bvector lambda)) =>
           [t, q0] <-2 s;
         [tSet_opt, tags]<-2 p;
         tSet <- match tSet_opt with
                 | Some x => x
                 | None => nil
                 end;
         ret ((if tSet_opt then true else false) && negb
               (eqb (foreach  (x in tags)ESPADA_TSetRetrieve tSet x)
                  (foreach  (x in q0)
                   arrayLookupList (list_EqDec bool_EqDec) t x)))))

    .

     eapply leRat_trans.
     eapply ratDistance_le_sum.
     eapply ESPADA_TSetCorr_G1_G3_close.
     eapply ratAdd_leRat_compat; [ idtac | reflexivity].

     rewrite ESPADA_TSetCorr_G3_G4_equiv.
     rewrite ESPADA_TSetCorr_G4_G5_equiv.
     rewrite ESPADA_TSetCorr_G5_le_G6.
     rewrite ESPADA_TSetCorr_G6_G7_equiv.
     rewrite ESPADA_TSetCorr_G7_G8_equiv.
     
     rewrite ESPADA_TSetCorr_G8_le_G9.
     rewrite ESPADA_TSetCorr_G9_G10_equiv.
     rewrite ESPADA_TSetCorr_G10_G11_equiv.
     rewrite ESPADA_TSetCorr_G11_G12_equiv.
     rewrite ESPADA_TSetCorr_G12_G13_equiv.
     rewrite ESPADA_TSetCorr_G13_G14_equiv.
     rewrite ESPADA_TSetCorr_G14_G15_equiv.
     rewrite ESPADA_TSetCorr_G15_G16_equiv.

     eapply leRat_trans.
     eapply ratDistance_le_sum.
     eapply eqRat_impl_leRat.
     eapply ESPADA_TSetCorr_G16_G17_equiv.
     eapply ratAdd_leRat_compat; [idtac | reflexivity].
     rewrite ESPADA_TSetCorr_G17_G18_equiv.
     rewrite ESPADA_TSetCorr_G18_G19_equiv.
     rewrite ESPADA_TSetCorr_G19_G20_equiv.
     eapply ESPADA_TSetCorr_G20_small.

    Qed.

    Variable PRF_NA_Adv : Rat.

    Hypothesis PRF_NA_Adv_correct_1 :
        PRF.PRF_NA_Advantage ({ 0 , 1 }^lambda) ({ 0 , 1 }^lambda) F_bar
     (list_EqDec bool_EqDec) (Bvector_EqDec lambda)
     (ESPADA_TSet_PRF_A1
        (pair_EqDec
           (list_EqDec
              (pair_EqDec (list_EqDec bool_EqDec)
                 (list_EqDec (Bvector_EqDec lambda))))
           (list_EqDec (list_EqDec bool_EqDec)))
        (z <-$ A1; [t, l]<-2 z; ret (t, l, (t, l))))
     (ESPADA_TSet_PRF_A2 bigB bigS F
        (fun (s : (T lambda * list Blist))
           (p : option (TSet lambda) * list (Bvector lambda)) =>
           [t, q0] <-2 s;
         [tSet_opt, tags]<-2 p;
         tSet <- match tSet_opt with
                 | Some x => x
                 | None => nil
                 end;
         ret ((if tSet_opt then true else false) && negb
               (eqb (foreach  (x in tags)ESPADA_TSetRetrieve tSet x)
                  (foreach  (x in q0)
                   arrayLookupList (list_EqDec bool_EqDec) t x)))))
     <= PRF_NA_Adv.

  Hypothesis PRF_NA_Adv_correct_2: 
    forall i, 
      PRF_NA_Advantage ({ 0 , 1 }^lambda) (RndF_R lambda bigB) F _ _  
                        (Hybrid.B1 nil _ _ (PRFI_A1 maxMatches A1) i)
                        (Hybrid.B2 
                           (fun lsD => k <-$ {0, 1}^lambda; ret (map (F k) lsD))
            (fun lsD => [lsR, _] <-$2 oracleMap _ _ (RndR_func (@RndF_range lambda bigB) _) nil lsD; ret lsR) _
            (PRFI_A2 lambda))
                         <= PRF_NA_Adv.

    Theorem ESPADA_TSetCorr_once :
     Pr[gInst ESPADA_TSetCorr_G1 ] <=  
     (maxKeywords * (S maxMatches))^2 / 2 ^ lambda 
                                            + 
                                            (maxKeywords / 1) * PRF_NA_Adv
     +
     
     PRF_NA_Adv.

      rewrite  ESPADA_TSetCorr_once_IPRF.
      eapply ratAdd_leRat_compat; intuition.
      eapply ratAdd_leRat_compat; intuition.
      eapply PRF_NA_impl_NAI.
      
      intuition.
      unfold PRFI_A1 in *.
      repeat simp_in_support.
      destruct x.
      repeat simp_in_support.
      rewrite map_length.
      eauto.
      unfold RndF_R.
      wftac.
      wftac.

      eauto.

    Qed.


End ESPADA_TSet_Once_correct.