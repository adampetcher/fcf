
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
Require Import ESPADA_SSE_SKS_Secure_tacs.

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

    unfold G1, SSE_Sec_NA_Real, SKS_EDBSetup, SKS_Search, SKS_Search_1, ESPADA_SSE_SKS.SKS_Search.
    do 4 skip.

    eapply comp_spec_eq_impl_eq.

    repeat specTac.

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
    do 4 skip.
    comp_skip.

    symmetry.
    eapply comp_spec_eq_impl_eq.
    
    eapply compMap_map_fission_eq; intuition.
    repeat specTac.

  Qed.
  
  Theorem G1_1_G2_equiv : 
    Pr[G1_1] == Pr[gInst G2].

    unfold G1_1, G2, SKS_EDBSetup_wLoop.
    do 5 skip.

    eapply eqRat_refl_eq.
    f_equal.
    f_equal.

    repeat lpTac.
      
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
    repeat skip.
    inline_first.

    identSkip_l; comp_simp; simpl; intuition.

  Qed.
  
  Theorem combine_eq_parts : 
    forall (A B : Set)(a1 a2 : list A)(b1 b2 : list B),
      a1 = a2 ->
      b1 = b2 ->
      combine a1 b1 = combine a2 b2.
    
    intuition.
    subst.
    trivial.
    
  Qed.
  
  Theorem G2_1_G2_2_eq_until_bad : 
    forall x,
      evalDist G2_1 (x, false) == evalDist G2_2 (x, false).

    intuition.
    unfold G2_1, G2_2.
    do 5 skip.

    repeat distTac; eauto using combine_eq_parts.

  Qed.

  Theorem G2_1_G2_2_bad_same : 
    Pr[x <-$ G2_1; ret snd x] == Pr[x <-$ G2_2; ret snd x].
    
    unfold G2_1, G2_2.
    do 5 skip.
    inline_first.
    comp_irr_l. comp_irr_r.
    comp_simp; simpl; intuition.

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
    repeat skip.
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

    eauto using leRat_trans, fundamental_lemma_h, eqRat_impl_leRat, 
    G2_1_bad_equiv, G2_1_bad_small, G2_1_G2_2_eq_until_bad, G2_1_G2_2_bad_same.
    
  Qed.

  Notation "'gInst1' g" := (g lambda F Enc TSet TSetKey Tag _ TSetSetup TSetGetTag _ A1 A2) (at level 90).

  Theorem G2_2_G3_equiv : 
    Pr[x <-$ G2_2; ret fst x] == Pr[gInst1 G3].

    unfold G2_2, G3.
    repeat skip.
    reflexivity.
    inline_first.

    identSkip_r.
    comp_simp; simpl; intuition.

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
    repeat skip.
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
    unfold SKS_EDBSetup_wLoop, SKS_EDBSetup_wLoop_5, f_oracle.
    simpl. comp_simp.
    skip.
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
    comp_skip; [specTac | idtac].
    eapply SKS_EDBSetup_5_spec.
    comp_simp.
    lpTac.
    skip.
    simpl. inline_first.
    identSkip_l. comp_simp. specTac.

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

    unfold PRF_A, PRF_A_6, SKS_EDBSetup_wLoop_5, SKS_EDBSetup_wLoop_6, SKS_EDBSetup_wLoop_6_f.
    do 2 (simpl; inline_first; comp_skip; comp_simp).
    eapply comp_spec_eq_impl_eq.
    specTac; simpl.
    repeat skip.
    eapply comp_spec_ret; intuition.
  Qed.

  Definition G6_2 :=
    [b, _] <-$2 PRF_A_6 _ _ (fun s a => x <-$ Rnd lambda; ret (x, s)) tt;
    ret b.

  Theorem G6_1_G6_2_equiv : 
    Pr[G6_1] == Pr[G6_2].

    unfold G6_1, G6_2, PRF_A_6.
    simpl; skip.
    simpl; inline_first.
    eapply comp_spec_eq_impl_eq.
    specTac.
    eapply compMap_randomFunc_NoDup; intuition; eapply removeDups_NoDup.
    
    inline_first. comp_simp. inline_first. simpl in *. subst.
    repeat (skip; simpl).
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
    unfold SKS_EDBSetup_wLoop_6, SKS_EDBSetup_wLoop_7, SKS_EDBSetup_wLoop_6_f.
    repeat (simpl; skip).
    eapply comp_spec_ret; intuition.

  Qed.

  Theorem G6_2_G7_equiv : 
    Pr[G6_2] == Pr[gInst3 G7].

    unfold G6_2, G7, PRF_A_6.
    eapply comp_spec_eq_impl_eq.
    do 2 (simpl; skip).
    specTac.
    eapply EDBSetup_7_spec.
    inline_first; simpl in *; lpTac.
    skip. simpl. inline_first.

    identSkip_r.

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
    skip.
    identSkip_r.
    eapply comp_spec_ret; intuition.
    
  Qed.

  Theorem G7_G7_1_equiv : 
    Pr[gInst3 G7] == Pr[G7_1].

    unfold G7, G7_1, SKS_EDBSetup_wLoop_7.
    eapply comp_spec_eq_impl_eq.
    do 2 skip.
    specTac.
    eapply EDBSetup_7_1_spec.
    lpTac.
    eapply (@compMap_support _ _ (fun a b => fst b = a)) in H1.  
    lpTac.
    specialize (split_combine a0); intuition.
    remember (split a0) as z. destruct z. simpl in *. subst.
    specTac.

    intuition. repeat simp_in_support. trivial.

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
    identSkip_l.
    eapply comp_spec_ret; intuition.
    
  Qed.

  Theorem G7_1_G7_2_equiv :
    Pr[G7_1] == Pr[G7_2].

    unfold G7_1, G7_2, Enc_A1, SKS_EDBSetup_wLoop_7_1, SKS_EDBSetup_wLoop_7_2, Enc_A2,  Enc_A3.
    do 2 skip.
    distTac. repeat lpTac. intuition.
    destruct H0. intuition. subst.
    distTac.
    eapply comp_spec_eq_impl_eq.
    identSkip_l.
    specTac.
    eapply EncOracle_spec.
    comp_simp. lpTac.
    eapply comp_spec_eq_refl.
    reflexivity.
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
    simpl. identSkip_l.
    eapply comp_spec_ret; intuition.
  Qed.
  
  Notation "'gInst4' g" := (g _ Enc _ _ _ L_T Sim_T _ A1 A2) (at level 90).
  
  Theorem G7_3_G8_equiv : 
    Pr[G7_3] == Pr[gInst4 G8].

    unfold G7_3, G8, Enc_A1, SKS_EDBSetup_wLoop_7_3, SKS_resultsStruct, Enc_A2, Enc_A3.
    do 2 skip. distTac. repeat lpTac. intuition.
    destruct H0; intuition; pairInv.
    skip.
    eapply comp_spec_eq_impl_eq.
    identSkip_r.
    specTac.
    eapply EncNothing_spec.
    simpl in *. lpTac.
    reflexivity.

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
    do 3 skip;
    reflexivity.

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

    eapply ratAdd_leRat_compat. intuition.
    Ltac oc_wftac :=
      match goal with
        | [|- well_formed_oc _ ] => eapply oc_compMap_wf; intuition
        | [|- well_formed_oc (OC_Query _ _)] => econstructor
      end.
    eapply IND_CPA_OI_impl_O. intuition. wftac. intuition.
    repeat oc_wftac.
    intuition.
    unfold Enc_A1 in *.
    repeat simp_in_support.
    destruct x. destruct p.
    repeat simp_in_support.
    rewrite map_length.
    eauto.

    eauto.
    
    intuition.
    
  Qed.

  Print Assumptions ESPADA_SKS_Secure_concrete.

End ESPADA_SSE_SKS_Secure.


