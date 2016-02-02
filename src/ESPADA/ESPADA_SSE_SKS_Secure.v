(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by a BSD-style		*
 * license that can be found in the LICENSE file at the root	*
 * of the source tree.						*)

Set Implicit Arguments. 

Require Import FCF.
Require Import SSE.
Require Import TSet.
Require Import RndPerm.
Require Import CompFold.
Require Import Array.
Require Import PRF.
Require Import Encryption.
Require Import OracleCompFold.
Require Import ESPADA_SSE_SKS.

Local Open Scope list_scope.


Section ESPADA_SSE_SKS_Secure.

  Variable lambda : posnat.

  (* PRF *)
  Variable F : Bvector lambda -> Keyword -> Bvector lambda.
  
  (* Encryption scheme *)
  Variable Enc : Bvector lambda -> Bvector lambda -> Comp (Bvector lambda).
  Variable Dec : Bvector lambda -> Bvector lambda -> Bvector lambda.

  (* TSet *)
  Variable TSet : Set.
  Hypothesis TSet_EqDec : EqDec TSet.
  Variable TSetKey : Set.
  Hypothesis TSetKey_EqDec : EqDec TSetKey.
  Variable Tag : Set.
  Hypothesis Tag_EqDec : EqDec Tag.
  Variable TSetSetup : T (pos (lambda)) -> Comp (TSet * TSetKey).
  Variable TSetGetTag : TSetKey -> Keyword -> Comp Tag. 
  Variable TSetRetrieve : TSet -> Tag -> (list (Bvector (lambda))).
  Variable Leakage_T : Set.
  Hypothesis Leakage_T_EqDec : EqDec Leakage_T.
  Variable L_T : T (pos (lambda)) -> list Keyword -> Leakage_T.
  Variable Sim_T : Leakage_T -> list (list (Bvector lambda)) -> Comp (TSet * list Tag).

  Definition EDB := EDB TSet.
  Definition SearchTranscript := SearchTranscript lambda Tag.
  Definition SKS_EDBSetup := SKS_EDBSetup F Enc _ _ TSetSetup.
  Definition SKS_Search := @SKS_Search lambda F Dec TSet TSetKey Tag _ 
                                       TSetGetTag TSetRetrieve.

  Variable A_State : Set.
  Hypothesis A_State_EqDec : EqDec A_State.
  Variable A1 : Comp (DB lambda * list Query * A_State).
  Variable A2 : A_State -> EDB -> list SearchTranscript -> Comp bool.
  Hypothesis A1_wf : well_formed_comp A1.
  Hypothesis A2_wf : forall x y z, well_formed_comp (A2 x y z).

    
   Notation "'gInst' g" := (g lambda F Enc TSet TSetKey Tag _ TSetSetup TSetGetTag TSetRetrieve _ A1 A2) (at level 90).

  (* Step 1: inline and simplify *)
  Theorem Real_G1_equiv : 
    Pr[SSE_Sec_NA_Real SKS_EDBSetup _ SKS_Search A1 A2] == Pr[gInst G1].

    unfold G1, SSE_Sec_NA_Real, SKS_EDBSetup.
    do 4 (inline_first; comp_skip; comp_simp).
    
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply (@compMap_spec _ _ _ _ _ _ eq (fun a b => snd a = b)).
    eapply list_pred_eq.
    intuition; subst.
    unfold SKS_Search, SKS_Search_1.
    comp_skip.
    eapply comp_base_exists; intuition.
    eapply comp_base_exists; intuition.
    eapply comp_spec_ret; intuition.
    erewrite snd_split_eq_list_pred.
    eapply comp_spec_eq_refl.
    intuition.

  Qed.

  (* Step 2: factor out some TSet computations and prepare to apply TSet correctness*)

  Definition SKS_EDBSetup_wLoop := SKS_EDBSetup_wLoop F Enc.

  Definition G1_1 :=
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0, 1}^lambda;
    t <-$ compMap _ (SKS_EDBSetup_wLoop db k_S) (toW db);
    [tSet, k_T] <-$2 TSetSetup t;
    ls <-$ (
      tags <-$ compMap _ (TSetGetTag k_T) q;
      ret (map (fun z => (z, TSetRetrieve tSet z)) tags)
    );
    A2 s_A tSet ls.


  Theorem G1_G1_1_equiv : 
    Pr[gInst G1] == Pr[G1_1].

    unfold G1, G1_1, SKS_EDBSetup_wLoop.
    do 4 (comp_skip; comp_simp).
    comp_skip.
    symmetry.
    eapply comp_spec_eq_impl_eq.
    
    eapply compMap_map_fission_eq; intuition.
    eapply comp_spec_consequence.
    eapply comp_spec_eq_refl.
    intuition; subst.
    trivial.

  Qed.
  
  Theorem G1_1_G2_equiv : 
    Pr[G1_1] == Pr[gInst G2].

    unfold G1_1, G2, SKS_EDBSetup_wLoop.
    do 4 (comp_skip; comp_simp).
    inline_first.
    comp_skip.
    rewrite combine_map_eq.
    eapply eqRat_refl_eq.
    f_equal.
    f_equal.
    eapply (@map_ext_pred _ _ _ (fun a b => a = fst b /\ a = snd b)).
    eapply list_pred_symm.
    eapply list_pred_impl.
    eapply (@list_pred_combine_l _ _ _ (fun a b => a = b) (fun a b => a = b)).
    eapply list_pred_eq.
    eapply list_pred_eq.
    intuition.
    
    intuition; subst.
    rewrite H8.
    trivial.
   
  Qed.

  Theorem G1_G2_equiv : 
    Pr[gInst G1] == Pr[gInst G2].

    rewrite G1_G1_1_equiv.
    eapply G1_1_G2_equiv.

  Qed.

  (* Step 3: apply TSet correctness. *)
  Definition G2_1 :=
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0, 1}^lambda;
    t <-$ compMap _ (SKS_EDBSetup_wLoop db k_S) (toW db);
    [tSet, k_T] <-$2 TSetSetup t;
    tags <-$ compMap _ (TSetGetTag k_T) q;
    rs <- map (TSetRetrieve tSet) tags;
    rs' <- map (arrayLookupList _ t) q;
    ls <- combine tags rs;
    v <-$ A2 s_A tSet ls;
    ret (v, negb (eqb rs rs')).

  Definition G2_2 :=
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0, 1}^lambda;
    t <-$ compMap _ (SKS_EDBSetup_wLoop db k_S) (toW db);
    [tSet, k_T] <-$2 TSetSetup t;
    tags <-$ compMap _ (TSetGetTag k_T) q;
    rs <- map (TSetRetrieve tSet) tags;
    rs' <- map (arrayLookupList _ t) q;
    ls <- combine tags rs';
    v <-$ A2 s_A tSet ls;
    ret (v, negb (eqb rs rs')).

  Theorem G2_G2_1_equiv : 
    Pr[gInst G2] == Pr[x <-$ G2_1; ret fst x].

    unfold G2, G2_1, SKS_EDBSetup_wLoop.
    repeat (inline_first; comp_skip; comp_simp).
    inline_first.
    rewrite <- evalDist_right_ident.
    comp_skip.
    comp_simp.
    simpl; intuition.

  Qed.
  
  Theorem G2_1_G2_2_eq_until_bad : 
    forall x,
      evalDist G2_1 (x, false) == evalDist G2_2 (x, false).

    intuition.
    unfold G2_1, G2_2.
    do 5 (comp_skip; comp_simp).
    case_eq ((@eqb (list (list (Bvector (posnatToNat lambda))))
                    (@list_EqDec (list (Bvector (posnatToNat lambda)))
                       (@list_EqDec (Bvector (posnatToNat lambda))
                          (Bvector_EqDec (posnatToNat lambda))))
                    (@map Tag (list (Bvector (posnatToNat lambda)))
                       (TSetRetrieve t) x2)
                    (@map Keyword (list (Bvector (posnatToNat lambda)))
                       (@arrayLookupList Keyword
                          (Bvector (posnatToNat lambda))
                          (@list_EqDec bool bool_EqDec) x1) l))); intuition.
    rewrite eqb_leibniz in H6.
    rewrite H6.
    eapply eqRat_refl.
    
    comp_irr_l.
    comp_irr_r.

    repeat rewrite evalDist_ret_0; intuition.
    pairInv.
    pairInv.

  Qed.

  Theorem G2_1_G2_2_bad_same : 
    Pr[x <-$ G2_1; ret snd x] == Pr[x <-$ G2_2; ret snd x].
    
    unfold G2_1, G2_2.
    do 5 (inline_first; comp_skip; comp_simp).
    inline_first.
    comp_irr_l.
    comp_irr_r.
    comp_simp.
    simpl.
    intuition.

  Qed.

  Definition G2_1_bad :=
    [t, q] <-$2 (TSetCor_A F Enc A1);
    [tSet, k_T] <-$2 TSetSetup t;
    tags <-$ compMap _ (TSetGetTag k_T) q;
    rs <- map (TSetRetrieve tSet) tags;
    rs' <- map (arrayLookupList _ t) q;
    ret (negb (eqb rs rs')).

  Theorem G2_1_bad_equiv : 
    Pr[x <-$ G2_1; ret snd x] == Pr[G2_1_bad].

    unfold G2_1, G2_1_bad, TSetCor_A.
    repeat (inline_first; comp_skip; comp_simp).
    reflexivity.
    inline_first.
    comp_irr_l.
    simpl; intuition.

  Qed.

  Theorem G2_1_bad_small : 
    Pr[G2_1_bad] <= AdvCor _ TSetSetup TSetGetTag TSetRetrieve (TSetCor_A F Enc A1).

    eapply leRat_refl.

  Qed. 

  Theorem G2_1_G2_2_close : 
    | Pr[x <-$ G2_1; ret fst x] - Pr[x <-$ G2_2; ret fst x] | <= AdvCor _ TSetSetup TSetGetTag TSetRetrieve (TSetCor_A F Enc A1).

    intuition.
    eapply leRat_trans.
    eapply fundamental_lemma_h.
    eapply G2_1_G2_2_bad_same.
    eapply G2_1_G2_2_eq_until_bad.
    rewrite G2_1_bad_equiv.
    eapply G2_1_bad_small.
    
  Qed.

  Notation "'gInst1' g" := (g lambda F Enc TSet TSetKey Tag _ TSetSetup TSetGetTag _ A1 A2) (at level 90).

  Theorem G2_2_G3_equiv : 
    Pr[x <-$ G2_2; ret fst x] == Pr[gInst1 G3].

    unfold G2_2, G3.
    repeat (inline_first; comp_skip; comp_simp).
    reflexivity.
    inline_first.
    symmetry.
    rewrite <- evalDist_right_ident.
    comp_skip.
    comp_simp.
    simpl; intuition.

  Qed.

  Theorem G2_G3_equiv : 
    | Pr[gInst G2] - Pr[gInst1 G3] | <= AdvCor _ TSetSetup TSetGetTag TSetRetrieve (TSetCor_A F Enc A1).

    rewrite G2_G2_1_equiv.
    rewrite <- G2_2_G3_equiv.
    eapply G2_1_G2_2_close.
    
  Qed.
    

  (* Step 4: apply TSet security. *)
  Definition TSetSec_A1 := TSetSec_A1 F Enc _ A1.
  Definition TSetSec_A2 := TSetSec_A2 A2.
  Definition G3_1 :=
    [t, q, s] <-$3 TSetSec_A1;
    [tSet, k_T] <-$2 TSetSetup t;
    tags <-$ compMap _ (TSetGetTag k_T) q;
    TSetSec_A2 s (tSet, tags).

  Definition G3_2 := 
    [t, q, s] <-$3 TSetSec_A1;
    inds <- map (lookupAnswers _ t) q;
    [tSet, tags] <-$2 Sim_T (L_T t q) inds;
    TSetSec_A2 s (tSet, tags).

  Theorem G3_G3_1_equiv : 
    Pr[gInst1 G3] == Pr[G3_1].

    unfold G3, G3_1, TSetSec_A1, TSetSec_A2.
    repeat (inline_first; comp_skip; comp_simp).
    reflexivity.

  Qed.

  Theorem G3_1_G3_2_close: 
    | Pr[G3_1] - Pr[G3_2] | <= TSetAdvantage _ TSetSetup TSetGetTag L_T TSetSec_A1 TSetSec_A2 Sim_T.

    eapply leRat_refl.

  Qed.

  Notation "'gInst2' g" := (g lambda F Enc TSet Tag _ L_T Sim_T _ A1 A2) (at level 90).

  Theorem G3_2_G4_equiv : 
    Pr[G3_2] == Pr[gInst2 G4].

    unfold G3_2, G4, TSetSec_A1, TSetSec_A2.
    repeat (inline_first; comp_skip; comp_simp).
    reflexivity.
  Qed.

  Theorem G3_G4_equiv : 
    | Pr[gInst1 G3] - Pr[gInst2 G4] | <= TSetAdvantage _ TSetSetup TSetGetTag L_T TSetSec_A1 TSetSec_A2 Sim_T.

    rewrite G3_G3_1_equiv.
    rewrite <- G3_2_G4_equiv.
    eapply G3_1_G3_2_close.

  Qed.

  (* Step 5-6: apply PRF definition. *)
  Definition G4_1 := 
    k_S <-$ {0, 1}^lambda;
    [db, q, s_A] <-$3 A1;
    t <-$ compMap _ (SKS_EDBSetup_wLoop db k_S) (toW db);
    inds <- map (lookupAnswers _ t) q;
    [tSet, tags] <-$2 Sim_T (L_T t q) inds;
    rs <- map (arrayLookupList _ t) q;
    ls <- combine tags rs;
    A2 s_A tSet ls.

  Definition SKS_EDBSetup_wLoop_5 := SKS_EDBSetup_wLoop_5 Enc.

  Theorem SKS_EDBSetup_5_spec :
    forall d b z x,
    comp_spec
     (fun (x0 : Keyword * list (Bvector lambda))
        (y : Keyword * list (Bvector lambda) * unit) => 
       x0 =  (fst y)) (SKS_EDBSetup_wLoop d x b)
     ((SKS_EDBSetup_wLoop_5 d b) unit unit_EqDec
        (f_oracle F (Bvector_EqDec lambda) x) z).

    intuition.
    unfold SKS_EDBSetup_wLoop, SKS_EDBSetup_wLoop_5.
    simpl.
    unfold f_oracle.
    comp_simp.
    inline_first.
    comp_skip.
    comp_simp.
    eapply comp_spec_ret; intuition.
    
  Qed.

  Theorem G4_G4_1_equiv : 
    Pr[gInst2 G4] == Pr[G4_1].

    unfold G4, G4_1.
    comp_swap_r.
    repeat (comp_skip; comp_simp).
    reflexivity.
  Qed.

  Theorem G4_1_G5_equiv : 
    Pr[G4_1] == Pr[gInst2 G5].

    Local Opaque evalDist.

    unfold G4_1, G5, PRF_A.
    repeat (inline_first; comp_skip; comp_simp; simpl).
    inline_first.
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply compMap_oc_spec.
    eapply list_pred_eq.
    intuition; subst.
    eapply SKS_EDBSetup_5_spec.

    comp_simp.
    simpl in H4.
    eapply list_pred_eq_impl_eq in H4.
    subst.
    inline_first.
    comp_skip.
    comp_simp.
    simpl.
    inline_first.
    eapply comp_spec_eq_trans.
    eapply comp_spec_eq_symm.
    eapply comp_spec_right_ident.
    comp_skip.
    comp_simp.
    eapply comp_spec_eq_refl.

  Qed.

  Theorem G4_G5_equiv : 
    Pr[gInst2 G4] == Pr[gInst2 G5].

    rewrite G4_G4_1_equiv.
    eapply G4_1_G5_equiv.

  Qed.

  Notation "'gInst3' g" := (g lambda Enc TSet Tag _ L_T Sim_T _ A1 A2) (at level 90).
  Definition PRF_A := PRF_A Enc L_T Sim_T A1 A2.

  Theorem G5_G6_equiv : 
    | Pr[gInst2 G5] - Pr[gInst3 G6] | <= PRF_Advantage (Rnd lambda) (Rnd lambda) F _ _ PRF_A.

    eapply leRat_refl.

  Qed.

  Definition SKS_EDBSetup_wLoop_6_f db w k_e :=
    inds <- lookupInds db w;
    t <-$ compMap _ (SKS_EDBSetup_indLoop _ Enc k_e) inds;
    ret (w, t).

  Definition SKS_EDBSetup_wLoop_6 db w :=
    k_e <--$ query w;
    $ (SKS_EDBSetup_wLoop_6_f db w k_e).

  Definition PRF_A_6 :=
    [db, q, s_A] <--$3$ A1;
    t <--$ oc_compMap _ (SKS_EDBSetup_wLoop_6 db) (toW db);
    inds <- map (lookupAnswers _ t) q;
    [tSet, tags] <--$2$ Sim_T (L_T t q) inds;
    rs <- map (arrayLookupList _ t) q;
    ls <- combine tags rs;
    $ A2 s_A tSet ls.

  Definition G6_1 :=
    [b, _] <-$2 PRF_A_6 _ _ (RndR_func (Rnd lambda) _) nil;
    ret b.


  Theorem G6_G6_1_equiv : 
    Pr[gInst3 G6] == Pr[G6_1].

    unfold G6, G6_1.

    unfold PRF_A, PRF_A_6.
    do 2 (simpl; inline_first; comp_skip; comp_simp).
    eapply comp_spec_eq_impl_eq.
    eapply  oc_compMap_eq .
    intuition.
    unfold SKS_EDBSetup_wLoop_5, SKS_EDBSetup_wLoop_6.
    simpl.
    comp_skip.
    unfold SKS_EDBSetup_wLoop_6_f.
    comp_simp.
    inline_first.
    comp_skip.
    comp_simp.
    eapply comp_spec_ret; intuition.
  Qed.

  Definition G6_2 :=
    [b, _] <-$2 PRF_A_6 _ _ (fun s a => x <-$ Rnd lambda; ret (x, s)) tt;
    ret b.

  Theorem G6_1_G6_2_equiv : 
    Pr[G6_1] == Pr[G6_2].

    unfold G6_1, G6_2, PRF_A_6.
    simpl; inline_first.
    comp_skip.
    comp_simp.
    simpl; inline_first.
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply compMap_randomFunc_NoDup.
    unfold toW.
    eapply removeDups_NoDup.
    intuition.
    
    inline_first.
    comp_simp.
    inline_first.
    simpl in *.
    subst.
    comp_skip.
    simpl; inline_first.
    comp_simp.
    simpl; inline_first.
    comp_skip.
    comp_simp.

    eapply comp_spec_eq_refl.

  Qed.


  (* Step 7: replace RF outputs with random values. *)

  Theorem EDBSetup_7_spec : 
    forall d b z,
    comp_spec
     (fun (x : Keyword * list (Bvector lambda))
        (y : Keyword * list (Bvector lambda) * unit) => 
      x = (fst y)) (SKS_EDBSetup_wLoop_7 Enc d b)
     ((SKS_EDBSetup_wLoop_6 d b) unit unit_EqDec
        (fun (s : unit) (_ : Keyword) => x <-$ { 0 , 1 }^lambda; ret (x, s))
        z).

    intuition.
    unfold SKS_EDBSetup_wLoop_6, SKS_EDBSetup_wLoop_7.
    simpl.
    inline_first.
    comp_skip.
    comp_simp.
    unfold SKS_EDBSetup_wLoop_6_f.
    inline_first.
    comp_skip.
    comp_simp.
    eapply comp_spec_ret; intuition.

  Qed.

  Theorem G6_2_G7_equiv : 
    Pr[G6_2] == Pr[gInst3 G7].

    unfold G6_2, G7.
    unfold PRF_A_6.
    simpl; inline_first.
    comp_skip.
    comp_simp.
    simpl; inline_first.
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply comp_spec_symm.
    eapply compMap_oc_spec.
    eapply list_pred_eq.
    intuition; subst.
    eapply EDBSetup_7_spec.
    inline_first.
    simpl in *.
    eapply list_pred_eq_impl_eq in H2.
    subst.
    comp_skip.
    simpl; inline_first.
    eapply comp_spec_eq_trans.
    Focus 2.
    eapply comp_spec_right_ident.
    comp_skip.

  Qed.

  Theorem G6_G7_equiv :
    Pr[gInst3 G6] == Pr[gInst3 G7].

    rewrite G6_G6_1_equiv.
    rewrite G6_1_G6_2_equiv.
    eapply G6_2_G7_equiv.

  Qed.

  (* Step 8: apply encryption security definition. *)
  Definition SKS_EDBSetup_wLoop_7_1 db w :=
    k_e <-$ (Rnd lambda);
    inds <- lookupInds db w;
    compMap _ (SKS_EDBSetup_indLoop _ Enc k_e) inds.

  Definition G7_1 :=
    [db, q, s_A] <-$3 A1;
    t <-$ compMap _ (SKS_EDBSetup_wLoop_7_1 db) (toW db);
    t <- combine (toW db) t;
    inds <- map (lookupAnswers _ t) q;
    [tSet, tags] <-$2 Sim_T (L_T t q) inds;
    rs <- map (arrayLookupList _ t) q;
    ls <- combine tags rs;
    A2 s_A tSet ls.

  Theorem EDBSetup_7_1_spec : 
    forall d b,
    comp_spec (fun a b => snd a = b) (SKS_EDBSetup_wLoop_7 Enc d b) (SKS_EDBSetup_wLoop_7_1 d b).

    intuition.
    unfold SKS_EDBSetup_wLoop_7, SKS_EDBSetup_wLoop_7_1.
    comp_skip.
    eapply comp_spec_eq_trans_r.
    Focus 2.
    eapply comp_spec_right_ident.
    comp_skip.
    eapply comp_spec_ret; intuition.
    
  Qed.

  Theorem G7_G7_1_equiv : 
    Pr[gInst3 G7] == Pr[G7_1].

    unfold G7, G7_1.
    comp_skip; comp_simp.
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply compMap_spec.
    eapply list_pred_eq.
    intuition; subst.
    eapply EDBSetup_7_1_spec.
    eapply (@compMap_support _ _ (fun a b => fst b = a)) in H0.
    assert (a0 = (combine (toW d) b)).
    
    apply snd_split_eq_list_pred in H2.
    subst.
    eapply list_pred_symm in H0.
    eapply fst_split_eq_list_pred in H0.
    rewrite <- H0.
    symmetry.
    specialize (split_combine a0); intuition.
    remember (split a0) as z.
    destruct z.
    trivial.

    subst.
    comp_skip.
    
    intuition.
    unfold SKS_EDBSetup_wLoop_7 in *.
    repeat simp_in_support.
    trivial.

  Qed.


  Definition SKS_EDBSetup_wLoop_7_2 w :=
    k_e <-$ (Rnd lambda);
    [b, _] <-$2 (Enc_A2 w) _ _ (EncryptOracle Enc _ k_e) tt;
    ret b.

  Definition G7_2 :=
    [lsa, s_A] <-$2 (Enc_A1 _ A1);
    t <-$ compMap _ (SKS_EDBSetup_wLoop_7_2) lsa;
    Enc_A3 L_T Sim_T A2 s_A t.
  
  Theorem EncOracle_spec : 
    forall b0 z x1,
    comp_spec
     (fun (x2 : Bvector lambda) (y : Bvector lambda * unit) =>
       x2 = (fst y)) (Enc x1 b0)
     ((query b0) unit unit_EqDec
        (EncryptOracle Enc (Bvector_EqDec lambda) x1) z).

    intuition.
    unfold EncryptOracle.
    simpl.
    eapply comp_spec_eq_trans_l.
    eapply comp_spec_eq_symm.
    eapply comp_spec_right_ident.
    comp_skip.
    eapply comp_spec_ret; intuition.
    
  Qed.

  Theorem G7_1_G7_2_equiv :
    Pr[G7_1] == Pr[G7_2].

    unfold G7_1, G7_2.
    unfold Enc_A1.
    inline_first.
    comp_skip.
    comp_simp.
    comp_skip.
    eapply (@compMap_eq _ _ (fun a b => fst b = d /\ a = snd b)).
    eapply list_pred_map_r'.
    eapply list_pred_impl.
    eapply list_pred_eq.
    intuition.
    intuition; subst.
    unfold SKS_EDBSetup_wLoop_7_1, SKS_EDBSetup_wLoop_7_2.
    comp_skip.
    unfold Enc_A2.
    rewrite <- evalDist_right_ident.
    eapply comp_spec_eq_impl_eq.
    destruct b; simpl.
    comp_skip.
    eapply compMap_oc_spec.
    eapply list_pred_eq.
    intuition; subst.
    unfold SKS_EDBSetup_indLoop.
    eapply EncOracle_spec.
    comp_simp.
    eapply comp_spec_ret; intuition.
    simpl in *.
    eapply list_pred_eq_impl_eq; intuition.

    unfold Enc_A3.
    comp_simp.
    eapply eqRat_refl.

  Qed.

  Definition SKS_EDBSetup_wLoop_7_3 w :=
    k_e <-$ (Rnd lambda);
    [b, _] <-$2 (Enc_A2 w) _ _ (EncryptNothingOracle Enc _ (zeroVector lambda) k_e) tt;
    ret b.

  Definition G7_3 :=
    [lsa, s_A] <-$2 Enc_A1 _ A1;
    t <-$ compMap _ (SKS_EDBSetup_wLoop_7_3) lsa;
    Enc_A3 L_T Sim_T A2 s_A t.

  Theorem G7_2_G7_3_close : 
    | Pr[G7_2] - Pr[G7_3] | <=
      IND_CPA_SecretKey_OI_Advantage (Rnd lambda) Enc (Enc_A1 _ A1) (@Enc_A2 lambda) (Enc_A3 L_T Sim_T A2) _ _(zeroVector lambda).

    eapply leRat_refl.
  Qed.

  
  Theorem EncNothing_spec : 
    forall b0 z x1,
      comp_spec
      (fun (x2 : Bvector lambda) (y : Bvector lambda * unit) =>
        x2 = (fst y)) (Enc x1 (zeroVector lambda))
      ((query b0) unit unit_EqDec
        (EncryptNothingOracle Enc (Bvector_EqDec lambda) 
          (zeroVector lambda) x1) z).
    
    intuition.
    unfold EncryptNothingOracle.
    simpl.
    eapply comp_spec_eq_trans_l.
    eapply comp_spec_eq_symm.
    eapply comp_spec_right_ident.
    comp_skip.
    eapply comp_spec_ret; intuition.
  Qed.

  
  Notation "'gInst4' g" := (g _ Enc _ _ _ L_T Sim_T _ A1 A2) (at level 90).
  
  Theorem G7_3_G8_equiv : 
    Pr[G7_3] == Pr[gInst4 G8].

    unfold G7_3, G8.
    unfold Enc_A1.
    inline_first.
    comp_skip.
    comp_simp.
    comp_skip.
    eapply (@compMap_eq _ _ (fun a b => fst a = d /\ b = snd a)).
    eapply list_pred_map_l'.
    eapply list_pred_impl.
    eapply list_pred_eq.
    intuition.
    intuition; subst.
    unfold SKS_EDBSetup_wLoop_7_3, SKS_resultsStruct.
    comp_skip.
    unfold Enc_A2.
    symmetry.
    rewrite <- evalDist_right_ident.
    eapply comp_spec_eq_impl_eq.
    simpl.
    comp_skip.
    eapply compMap_oc_spec.
    eapply list_pred_eq.
    intuition; subst.

    eapply EncNothing_spec.
    comp_simp.
    simpl in *.
    eapply comp_spec_ret.
    eapply list_pred_eq_impl_eq; intuition.

    unfold Enc_A3.
    comp_simp.
    eapply eqRat_refl.

  Qed.
  
  Theorem G7_G8_equiv : 
    | Pr[gInst3 G7] - Pr[gInst4 G8] | <= 
      IND_CPA_SecretKey_OI_Advantage (Rnd lambda) Enc (Enc_A1 _ A1) (@Enc_A2 lambda) (Enc_A3 L_T Sim_T A2) _ _(zeroVector lambda).

    rewrite G7_G7_1_equiv.
    rewrite G7_1_G7_2_equiv.
    rewrite <- G7_3_G8_equiv.
    eapply G7_2_G7_3_close.

  Qed.


  Theorem G8_Ideal_equiv : 
    Pr[gInst4 G8] == Pr[SSE_Sec_NA_Ideal A1 A2 (L Enc _ L_T) (SKS_Sim _ _ _ Sim_T)].

    Local Opaque evalDist.

    unfold G8, SSE_Sec_NA_Ideal, L, SKS_Sim.
    comp_skip.
    comp_simp.
    inline_first.
    comp_skip.
    comp_simp.
    simpl.
    inline_first.
    comp_skip.
    
    reflexivity.

    comp_simp.
    eapply eqRat_refl.

  Qed.

  Variable IND_CPA_Adv : Rat.
  
  Hypothesis IND_CPA_Adv_correct : 
    (forall i,
       IND_CPA_SecretKey_O_Advantage ({0,1}^lambda) Enc
         (A_c 
            (B1 (nil, nil) _ _ (Enc_A1 _ A1) i) 
            (@Enc_A2 lambda)
            (B2
               (fun x =>
                  key <-$ {0,1}^lambda;
           z <-$
             (Enc_A2 x) _ _ (EncryptOracle Enc _ key) tt;
           [b, _]<-2 z; ret b)
               (fun x  =>
           key <-$ {0,1}^lambda;
                z <-$
                  (Enc_A2 x) unit unit_EqDec
                  (EncryptNothingOracle Enc _ (zeroVector lambda) key) tt;
                [b, _]<-2 z; ret b) _ (Enc_A3 L_T Sim_T A2))
         )
         _ 
         (zeroVector lambda)
      <= IND_CPA_Adv)%rat.

  Variable maxKeywords : nat.
  Hypothesis maxKeywords_correct : 
    forall db q s,
      In (db, q, s) (getSupport A1) ->
      (length (toW db) <= maxKeywords)%nat.

  Hypothesis Enc_wf : 
    forall k p,
      well_formed_comp (Enc k p).

  Theorem ESPADA_SKS_Secure_concrete : 
    SSE_NA_Advantage SKS_EDBSetup _ SKS_Search A1 A2 (L Enc _ L_T) (SKS_Sim _ _ _ Sim_T) <= 
    AdvCor _ TSetSetup TSetGetTag TSetRetrieve (TSetCor_A F Enc A1) + 
    TSetAdvantage _ TSetSetup TSetGetTag L_T TSetSec_A1 TSetSec_A2 Sim_T + 
    PRF_Advantage (Rnd lambda) (Rnd lambda) F _ _ PRF_A + 
    (maxKeywords / 1) * IND_CPA_Adv.

    unfold SSE_NA_Advantage.
    rewrite Real_G1_equiv.
    rewrite G1_G2_equiv.
    eapply leRat_trans.
    eapply ratDistance_le_trans.
    eapply G2_G3_equiv.
    eapply ratDistance_le_trans.
    eapply G3_G4_equiv.
    rewrite G4_G5_equiv.
    eapply ratDistance_le_trans.
    eapply G5_G6_equiv.
    rewrite G6_G7_equiv.
    rewrite <- G8_Ideal_equiv.
    eapply G7_G8_equiv.
    repeat rewrite <- ratAdd_assoc.

    eapply ratAdd_leRat_compat; intuition.
    eapply IND_CPA_OI_impl_O.
    intuition.
    wftac.
    intuition.
    unfold Enc_A2.

    eapply oc_compMap_wf.
    intuition.
    econstructor.
    intuition.
    unfold Enc_A1 in *.
    repeat simp_in_support.
    destruct x.
    destruct p.
    repeat simp_in_support.
    rewrite map_length.
    eauto.

    eauto.
    
    intuition.
    
  Qed.

  Print Assumptions ESPADA_SKS_Secure_concrete.

End ESPADA_SSE_SKS_Secure.


(* Just to make sure everything fits together, let's combine the result above with the results about the T-Set instantiation.  This is just a sanity check to make sure everything unifies and we can derive the bounds.  There is a lot of room for improvement in the proof below.  *)
Require Import ESPADA_TSet.
Require Import ESPADA_TSet_Secure.
Require Import ESPADA_TSet_Correct.
Require Import ESPADA_TSet_Once_Games.
Require Import ESPADA_TSet_Once.
Require Import ESPADA_TSet_Correct_Once_Games.

Section ESPADA_SSE_SKS_Secure_inst.

  Variable lambda : posnat.

  (* PRF *)
  Variable F : Bvector lambda -> Keyword -> Bvector lambda.
  
  (* Encryption scheme *)
  Variable Enc : Bvector lambda -> Bvector lambda -> Comp (Bvector lambda).
  Hypothesis Enc_wf : 
    forall k p,
      well_formed_comp (Enc k p).
  Variable Dec : Bvector lambda -> Bvector lambda -> Bvector lambda.

  Variable bigB bigS : posnat.
  Variable F_T : Bvector lambda -> nat -> nat * Bvector lambda * Bvector (Datatypes.S lambda).
  Variable F_bar_T : Bvector lambda -> Blist -> Bvector lambda.
  Variable maxMatches maxKeywords : posnat.

  Definition TSetSetup := @ESPADA_TSetSetup lambda bigB bigS F_T F_bar_T.
  Definition TSetGetTag := ESPADA_TSetGetTag lambda F_bar_T.
  Definition TSetRetrieve := ESPADA_TSetRetrieve lambda maxMatches F_T.

  Definition TSetKey := Bvector lambda.

  Definition TSet := TSet lambda.
  Definition EDB_T := EDB TSet.
  Definition Tag := Bvector lambda.
  Definition SearchTranscript_T := SearchTranscript lambda Tag.
  Definition SKS_EDBSetup_T := SKS_EDBSetup F Enc _ _ TSetSetup.
  Definition SKS_Search_T := @SKS_Search lambda F Dec TSet TSetKey Tag _ 
                                       TSetGetTag TSetRetrieve.

  Definition Sim_T := @ESPADA_TSet_Sim lambda bigB bigS F_T.
  Definition L_T := @L_T lambda.

  Variable A_State : Set.
  Hypothesis A_State_EqDec : EqDec A_State.
  Variable A1 : Comp (DB lambda * list Query * A_State).
  Variable A2 : A_State -> EDB_T -> list SearchTranscript_T -> Comp bool.
  Hypothesis A1_wf : well_formed_comp A1.
  Hypothesis A2_wf : forall x y z, well_formed_comp (A2 x y z).

  Variable IND_CPA_Adv : Rat.
  Hypothesis IND_CPA_Adv_correct : 
    (forall i,
       IND_CPA_SecretKey_O_Advantage ({0,1}^lambda) Enc
         (A_c 
            (B1 (nil, nil) _ _ (Enc_A1 _ A1) i) 
            (@Enc_A2 lambda)
            (B2
               (fun x =>
                  key <-$ {0,1}^lambda;
           z <-$
             (Enc_A2 x) _ _ (EncryptOracle Enc _ key) tt;
           [b, _]<-2 z; ret b)
               (fun x  =>
           key <-$ {0,1}^lambda;
                z <-$
                  (Enc_A2 x) unit unit_EqDec
                  (EncryptNothingOracle Enc _ (zeroVector lambda) key) tt;
                [b, _]<-2 z; ret b) _ (Enc_A3 L_T Sim_T A2))
         )
         _ 
         (zeroVector lambda)
      <= IND_CPA_Adv)%rat.

  Variable PRF_NA_Adv failProb : Rat.
  Variable numTrials : posnat.

  Hypothesis failProb_pos : 
    ~(1 <= failProb).

  Hypothesis failProb_correct_Cor : 
    forall (t : T lambda) (l : list Blist),
      In (t, l) (getSupport (TSetCor_A F Enc A1)) ->
      Pr 
        [x <-$ ESPADA_TSet_Correct.ESPADA_TSetSetup_trial bigB bigS F_T F_bar_T t;
          ret (if fst x then false else true) ] <= failProb.


  Definition PRF_A_T := @PRF_A lambda Enc TSet Tag _ L_T Sim_T _ A1 A2.

  Hypothesis PRF_NA_Adv_correct_1 :
    PRF_NA_Advantage ({ 0 , 1 }^lambda) ({ 0 , 1 }^lambda) F_bar_T
     (list_EqDec bool_EqDec) (Bvector_EqDec lambda)
     (ESPADA_TSet_PRF_A1
        (pair_EqDec
           (list_EqDec
              (pair_EqDec (list_EqDec bool_EqDec)
                 (list_EqDec (Bvector_EqDec lambda))))
           (list_EqDec (list_EqDec bool_EqDec)))
        (z <-$ (TSetCor_A F Enc A1); [t, l]<-2 z; ret (t, l, (t, l))))
     (ESPADA_TSet_PRF_A2 bigB bigS F_T
        (fun (s : T lambda * list Blist)
           (p : option (TSet) * list (Bvector lambda)) =>
         [t, q0]<-2 s;
         [tSet_opt, tags]<-2 p;
         tSet <- match tSet_opt with
                 | Some x => x
                 | None => nil
                 end;
         ret (if tSet_opt then true else false) &&
             negb
               (eqb (foreach  (x in tags)TSetRetrieve tSet x)
                  (foreach  (x in q0)
                   arrayLookupList (list_EqDec bool_EqDec) t x))))
                         <= PRF_NA_Adv.

  Hypothesis PRF_NA_Adv_correct_2: 
    forall i, 
      PRF_NA_Advantage ({ 0 , 1 }^lambda) (RndF_R lambda bigB) F_T _ _  
                        (Hybrid.B1 nil _ _ (PRFI_A1 maxMatches (TSetCor_A F Enc A1)) i)
                        (Hybrid.B2 
                           (fun lsD => k <-$ {0, 1}^lambda; ret (map (F_T k) lsD))
            (fun lsD => [lsR, _] <-$2 oracleMap _ _ (RndR_func (@RndF_range lambda bigB) _) nil lsD; ret lsR) _
            (PRFI_A2 lambda))
                         <= PRF_NA_Adv.


  Hypothesis maxKeywords_correct : 
    forall db q s,
      In (db, q, s) (getSupport A1) ->
      (length (ESPADA_SSE_SKS.toW db) <= maxKeywords)%nat.

  Hypothesis maxKeywords_correct_Cor : 
    forall (t : T lambda) (l : list Blist),
      In (t, l) (getSupport (TSetCor_A F Enc A1)) ->
      (length (combineKeywords (removeDups (list_EqDec bool_EqDec) l) (toW t)) <=
       maxKeywords)%nat.

  Hypothesis maxMatches_correct_Cor : 
    forall (t : T lambda) (q : list Blist),
      In (t, q) (getSupport (TSetCor_A F Enc A1)) ->
      ESPADA_TSet_Correct_Once.maxMatch t maxMatches.

  Hypothesis bigB_correct : 
    forall (k : Bvector lambda) (b i : nat) (v1 : Bvector lambda)
     (v2 : Bvector (S lambda)), (b, v1, v2) = F_T k i -> b < bigB.


  Hypothesis failProb_correct_sec_A1:
    forall (t : T lambda) (qs : list Blist) (s_A : (A_State * list (list (Bvector lambda)))),
      In (t, qs, s_A) (getSupport  (TSetSec_A1 F Enc A_State_EqDec A1)) ->
      Pr[p <-$ ESPADA_TSetSetup_trial bigB bigS F_T F_bar_T t; ret !setupSuccess p ] <=
      failProb.

  Hypothesis failProb_correct_sim_sec_A1 : 
    forall (t : T lambda) (qs : list Blist)
     (s_A : A_State * list (list (Bvector lambda))),
   In (t, qs, s_A) (getSupport (TSetSec_A1 F Enc A_State_EqDec A1)) ->
   Pr 
   [p <-$
    ESPADA_TSet_Sim_trial lambda bigB bigS F_T
      (ESPADA_TSet_Once_Games.L_T t qs)
      (map (arrayLookupList (list_EqDec bool_EqDec) t) qs);
    ret !simSetupSuccess p ] <= failProb.

  Hypothesis maxKeywords_correct_Sec : 
    forall (db : T lambda) (q : list Blist)
     (s_A : A_State * list (list (Bvector lambda))),
   In (db, q, s_A) (getSupport (TSetSec_A1 F Enc A_State_EqDec A1)) ->
   (length (combineKeywords (removeDups (list_EqDec bool_EqDec) q) (toW db)) <=
    maxKeywords)%nat.

  Hypothesis PRF_NA_Adv_correct_sec1 : 
    PRF_NA_Advantage ({ 0 , 1 }^lambda) ({ 0 , 1 }^lambda) F_bar_T
     (list_EqDec bool_EqDec) (Bvector_EqDec lambda)
     (Repeat_PRF_A1
        (pair_EqDec A_State_EqDec
           (list_EqDec (list_EqDec (Bvector_EqDec lambda))))
        (TSetSec_A1 F Enc A_State_EqDec A1))
     (Repeat_PRF_A2 bigB bigS F_T F_bar_T (TSetSec_A2 A2) numTrials) <=
    PRF_NA_Adv.

  Hypothesis PRF_NA_Adv_correct_sec2 : 
     forall i : nat,
   PRF_NA_Advantage ({ 0 , 1 }^lambda) (RndF_range lambda bigB) F_T nat_EqDec
     (pair_EqDec (pair_EqDec nat_EqDec (Bvector_EqDec lambda))
        (Bvector_EqDec (S lambda)))
     (B1 nil (list_EqDec nat_EqDec)
        (pair_EqDec
           (pair_EqDec
              (pair_EqDec
                 (pair_EqDec
                    (pair_EqDec
                       (pair_EqDec
                          (pair_EqDec
                             (list_EqDec
                                (pair_EqDec (list_EqDec bool_EqDec)
                                   (list_EqDec (Bvector_EqDec lambda))))
                             (list_EqDec (list_EqDec bool_EqDec)))
                          (pair_EqDec A_State_EqDec
                             (list_EqDec (list_EqDec (Bvector_EqDec lambda)))))
                       (list_EqDec (Bvector_EqDec lambda)))
                    (option_EqDec
                       (pair_EqDec
                          (list_EqDec
                             (list_EqDec
                                (option_EqDec
                                   (pair_EqDec (Bvector_EqDec lambda)
                                      (Bvector_EqDec (S lambda))))))
                          (list_EqDec (list_EqDec nat_EqDec)))))
                 (list_EqDec (list_EqDec (Bvector_EqDec lambda))))
              (list_EqDec (list_EqDec bool_EqDec)))
           (list_EqDec (list_EqDec bool_EqDec)))
        (Repeat_IPRF_A1
           (pair_EqDec A_State_EqDec
              (list_EqDec (list_EqDec (Bvector_EqDec lambda)))) bigB bigS F_T
           (TSetSec_A1 F Enc A_State_EqDec A1)) i)
     (B2 (fun lsD : list nat => k <-$ { 0 , 1 }^lambda; ret map (F_T k) lsD)
        (fun lsD : list nat =>
         z <-$
         oracleMap
           (list_EqDec
              (pair_EqDec nat_EqDec
                 (pair_EqDec (pair_EqDec nat_EqDec (Bvector_EqDec lambda))
                    (Bvector_EqDec (S lambda)))))
           (pair_EqDec (pair_EqDec nat_EqDec (Bvector_EqDec lambda))
              (Bvector_EqDec (S lambda)))
           (RndR_func (RndF_range lambda bigB) nat_EqDec) nil lsD;
         [lsR, _]<-2 z; ret lsR)
        (list_EqDec
           (pair_EqDec (pair_EqDec nat_EqDec (Bvector_EqDec lambda))
              (Bvector_EqDec (S lambda))))
        (Repeat_IPRF_A2 bigB bigS F_T F_bar_T (TSetSec_A2 A2) numTrials)) <=
   PRF_NA_Adv.


  Theorem ESPADA_SKS_Secure_concrete_T : 
    SSE_NA_Advantage SKS_EDBSetup_T _ SKS_Search_T A1 A2 (L Enc _ L_T) (SKS_Sim _ _ _ Sim_T) <= ((lambda / 1) * ((maxKeywords * (S maxMatches))^2 / 2 ^ lambda + 
     (maxKeywords / 1) * PRF_NA_Adv                                                      
     +
    PRF_NA_Adv)  + (expRat failProb lambda)) + 
                                                                                                (numTrials / 1 * 
      (PRF_NA_Adv  + 
       (maxKeywords / 1) * 
       PRF_NA_Adv) + 
      expRat failProb numTrials + expRat failProb numTrials) + 
                                                                                                PRF_Advantage (Rnd lambda) (Rnd lambda) F _ _ PRF_A_T + 
    (maxKeywords / 1) * IND_CPA_Adv.

    eapply leRat_trans.
    eapply ESPADA_SKS_Secure_concrete; eauto.
    eapply ratAdd_leRat_compat; intuition.
    eapply ratAdd_leRat_compat; intuition.
    eapply ratAdd_leRat_compat; intuition.
    specialize ESPADA_TSet_Correct; intuition.
    unfold TSetSetup, TSetGetTag, TSetRetrieve.
    eapply leRat_trans.
    Focus 2.    
    eapply H;
    eauto.

    (* well-formedness *)
    admit.

    reflexivity.

    specialize (@ESPADA_TSet_secure lambda (A_State * list (list (Bvector lambda))) _ bigB bigS F_T F_bar_T bigB_correct (TSetSec_A1 F Enc A_State_EqDec A1) (TSetSec_A2 A2)); intuition.
    eapply leRat_trans.
    eapply H; eauto.

    (* well-formedness*)
    admit.
    admit.

    reflexivity.

    reflexivity.
  Qed.


End ESPADA_SSE_SKS_Secure_inst.