(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* Definitions related to pseudoradom functions.  This file copies some items from ConstructedFunc.v, so we probably need to refactor this in the future. *)

Set Implicit Arguments.
Require Import FCF.FCF.
Require Import FCF.CompFold. 
Require Export FCF.Array.
Require Export FCF.Hybrid.

Local Open Scope list_scope.
Local Open Scope array_scope.

Theorem fst_split_map_eq : forall (A B : Type)(ls : list (A * B)),
  fst (split ls) = map fst ls.

  induction ls; intuition idtac; simpl in *.
  remember (split ls) as z. destruct z.
  simpl in *.
  congruence.

Qed.

Theorem any_dec_arrayLookup_swap : 
  forall (A B : Set)(eqda : EqDec A)(ls1 ls2 : list (A * B)),
  any_dec (fun x => if (arrayLookup _ ls1 x) then true else false) (fst (split ls2)) = 
  any_dec (fun x => if (arrayLookup _ ls2 x) then true else false) (fst (split ls1)).

  unfold any_dec in *.
  induction ls1; intuition idtac; simpl in *.
  eapply fold_left_orb_all_false.
  remember (split ls1) as z.
  destruct z.
  simpl in *.
  case_eq (arrayLookup eqda ls2 a0); intros.
  rewrite fold_left_orb_true.
  eapply (fold_left_orb_ex).
  rewrite eqb_refl.
  trivial.
  eapply arrayLookup_In_split.
  eauto.
  rewrite <- IHls1.
  eapply fold_left_f_eq.
  intuition.
  case_eq (eqb b0 a0); intros.
  rewrite eqb_leibniz in H1.
  subst.
  exfalso.
  eapply arrayLookup_None_not_In; eauto.
  reflexivity.

Qed.


Definition oracleMap(D R S: Set)(eqds : EqDec S)(eqdr : EqDec R)(oracle : S  -> D -> Comp (R * S))(s : S)(ds : list D) :=
  compFold _ 
  (fun acc d => [rs, s] <-2 acc; [r, s] <-$2 oracle s d; ret (rs ++ r :: nil, s)) 
  (nil, s) ds.

Theorem oracleMap_wf : 
  forall (D R S : Set)(eqds : EqDec S)(eqdr : EqDec R) (oracle : S -> D -> Comp (R * S))ds s,
  (forall s x, well_formed_comp (oracle s x)) ->
  well_formed_comp (@oracleMap D R S _ _ oracle s ds).

  intuition.
  unfold oracleMap.
  eapply compFold_wf; intuition.
  wftac.

Qed.


Section RandomFunc.
  
  Variable D R : Set.
  Variable RndR : Comp R.

  Hypothesis EqDec_D : EqDec D.
  Instance EqDec_R : EqDec R.
    eapply comp_EqDec.
    eauto.
  Qed.

  Hypothesis RndR_wf : well_formed_comp RndR.
  
    (* A random function *)
  Definition randomFunc (f : (list (D * R))) (d : D) : Comp (R * list (D * R)) :=
      match (arrayLookup _ f d) with
        | None => (r <-$ RndR; ret (r, (d, r) :: f))
        | Some r => ret (r, f)
      end.  
  
  Lemma randomFunc_wf : forall f d, 
    well_formed_comp (randomFunc f d).
    
    intuition.
    unfold randomFunc.
    case_eq (f#d); intuition; wftac.
    
  Qed.    
  
  Hint Resolve randomFunc_wf : wftac.

  (* Eager random functions with finite domain *)
  Definition RndFunc(lsd : list D) : Comp (list (D * R)) :=
    compFold _ (fun f d => r <-$ RndR; ret (d, r)::f) nil lsd. 

  Definition lookupEq (ls1 ls2 : list (D * R)) :=
    forall d, arrayLookup _ ls1 d = arrayLookup _ ls2 d.
  
End RandomFunc.

Theorem randomFunc_lookupEq_spec : forall (D R : Set)(eqdd : EqDec D)(eqdr : EqDec R)(RndR : Comp R)(ls1 ls2 : list (D * R)),
  lookupEq _ ls1 ls2 ->
  forall d, comp_spec (fun p1 p2 => fst p1 = fst p2 /\ lookupEq _ (snd p1) (snd p2)) (randomFunc RndR _ ls1 d) (randomFunc RndR _ ls2 d).

  intros.
  unfold randomFunc.
  rewrite H.
  case_eq (arrayLookup _ ls2 d); intros.
  fcf_simp.
  eapply comp_spec_ret; intuition idtac.

  fcf_skip.
  eapply comp_base_exists; eauto.
  eapply comp_base_exists; eauto.
  eapply comp_spec_ret; intuition idtac.
  unfold lookupEq; intuition idtac; simpl.
  rewrite H.
  reflexivity.

Qed.

Section RandomFunc_hist.

  Variable D R : Set.

  Hypothesis EqDec_D : EqDec D.
  Hypothesis EqDec_R : EqDec R.

  Variable RndR : Comp R.

  Hypothesis RndR_wf : well_formed_comp RndR.

  (* a random function that keeps track of all call history *)
  Definition randomFunc_hist (ls : list (D * R))(d : D) :=
    r <-$ match (arrayLookup _ ls d) with
    | None => RndR
    | Some r => ret r
    end;
    ret (r, ((d,r):: ls)).

  Theorem randomFunc_hist_wf : forall ls d,
    well_formed_comp (randomFunc_hist ls d).

    unfold randomFunc_hist.
    intuition idtac.
    destruct (arrayLookup _ ls d);
    wftac.

  Qed.
  Hint Resolve randomFunc_hist_wf : wf.

  Theorem randomFunc_hist_spec : forall (ls1 ls2 : list (D * R)),
    lookupEq _ ls1 ls2 ->
    forall d, comp_spec (fun p1 p2 => fst p1 = fst p2 /\ lookupEq _ (snd p1) (snd p2)) (randomFunc RndR _ ls1 d) (randomFunc_hist ls2 d).

    intros.
    unfold randomFunc, randomFunc_hist.
    rewrite H.
    case_eq (arrayLookup _ ls2 d); intros.
    fcf_simp.
    eapply comp_spec_ret; intuition idtac.
    unfold lookupEq.
    intuition idtac.
    simpl.
    case_eq (eqb d0 d); intros.
    rewrite eqb_leibniz in H1.
    subst.
    rewrite H.
    trivial.
    eauto.

    fcf_skip.
    eapply comp_base_exists; eauto.
    eapply comp_base_exists; eauto.
    eapply comp_spec_ret; intuition idtac.
    unfold lookupEq; intuition idtac; simpl.
    rewrite H.
    reflexivity.

  Qed.

  (* nested random functions--- always track call history and have two separate lists, allowing the proof to
    identify whether a query was made after some point in time. *)
  Definition nestedRandomFunc (st : list (D * R)) s q :=
    match (arrayLookup _ st q) with
    | None => randomFunc RndR _ s q
    | Some r => ret (r, (q, r)::s)
    end.

  Theorem nestedRandomFunc_wf : forall (ls s : list (D * R)) d,
    well_formed_comp (nestedRandomFunc ls s d).

    intros.
    unfold nestedRandomFunc.
    destruct (arrayLookup _ ls d); wftac.
    eapply randomFunc_wf.
    trivial.
    
  Qed.

  Definition nestedRandomFunc_pred (st s1 s2 : list (D * R)) : Prop :=
    (forall d, arrayLookup _ s1 d = arrayLookup _ (st ++ s2) d).

  Theorem nestedRandomFunc_spec : forall st s1 s2 (d : D),
    (nestedRandomFunc_pred st s1 s2) ->
    comp_spec (fun p1 p2 => fst p1 = fst p2 /\ 
      (nestedRandomFunc_pred st (snd p1) (snd p2)))
    (randomFunc RndR _ s1 d)
    (nestedRandomFunc st s2 d).

    unfold nestedRandomFunc_pred in *;
    intros.
    unfold nestedRandomFunc.
    case_eq (arrayLookup _ st d); intros.
    unfold randomFunc.
    rewrite H.
    erewrite arrayLookup_app_Some; eauto.
    eapply comp_spec_ret; intuition idtac.
    simpl in *.
    rewrite H.
    case_eq (eqb d0 d); intros.
    rewrite eqb_leibniz in H1.
    subst.
    repeat erewrite (arrayLookup_app_Some); eauto.
    case_eq (arrayLookup _ st d0); intros.
    repeat erewrite (arrayLookup_app_Some); eauto.
    repeat rewrite (arrayLookup_app_None); eauto.
    simpl.
    rewrite H1.
    trivial.

    unfold randomFunc.
    rewrite H.
    rewrite arrayLookup_app_None.
    case_eq (arrayLookup _ s2 d); intros.
    eapply comp_spec_ret; intuition idtac.
    fcf_skip.
    eapply comp_base_exists; eauto.
    eapply comp_base_exists; eauto.
    eapply comp_spec_ret; intuition idtac.
    simpl.
    rewrite H.
    case_eq (eqb d0 d); intros.
    rewrite eqb_leibniz in H4.
    subst.
    rewrite arrayLookup_app_None; eauto.
    simpl.
    rewrite eqb_refl.
    trivial.
    case_eq (arrayLookup _ st d0); intros.
    repeat erewrite (arrayLookup_app_Some); eauto.
    repeat rewrite arrayLookup_app_None; eauto.
    simpl.
    rewrite H4.
    trivial.
    trivial.

  Qed.

  Theorem nestedRandomFunc_app_spec : forall ls ls1 x1 x2 a,
    (forall y, arrayLookup _ x1 y = arrayLookup _ x2 y) ->
    comp_spec
    (fun y1 y2  =>
     any_dec
       (fun y =>
        if
         arrayLookup _ ls (fst y)
        then true
        else false) (snd y1) =
     any_dec
       (fun y =>
        if
         arrayLookup _ ls (fst y)
        then true
        else false) (snd y2) /\
     (any_dec
        (fun y =>
         if
          arrayLookup _ ls (fst y)
         then true
         else false) (snd y1) = false ->
      (forall z,
       arrayLookup _ (snd y1) z =
       arrayLookup _ (snd y2) z) /\
      fst y1 = fst y2))
    (nestedRandomFunc 
       (ls ++ ls1) x1 a)
    (nestedRandomFunc ls1 x2 a).

    intros.
    unfold nestedRandomFunc.

    match goal with
    | [|- context[match ?a with | Some _ => _ | None => _ end] ] =>
        case_eq a; intros
    end.
    match goal with
    | [H: arrayLookup ?eqd (?ls1 ++ ?ls2) ?a = Some _ |- _] =>
      case_eq (arrayLookup eqd ls1 a); intros
    end.
    erewrite arrayLookup_app_Some in H0; eauto.
    inversion H0; clear H0; subst.

    match goal with
    | [|- context[match ?a with | Some _ => _ | None => _ end] ] =>
        case_eq a; intros
    end.
    eapply comp_spec_ret; intuition idtac.
    simpl in *.
    repeat rewrite any_dec_cons.
    simpl.
    match goal with
    | [|- context[if ?a then _ else _] ] =>
      cutrewrite (a = Some r)
    end;
    simpl; trivial.

    simpl in *.
    rewrite any_dec_cons in *.
    apply orb_false_elim in H2.
    intuition.
    simpl in *.
    match goal with
    | [H: (if ?a then _ else _) = false |- _] =>
      cutrewrite (a = Some r) in H
    end; trivial.
    discriminate.
    simpl in *.

    rewrite any_dec_cons in *.
    apply orb_false_elim in H2.
    intuition idtac.
    simpl in *.
    match goal with
    | [H: (if ?a then _ else _) = false |- _] =>
      cutrewrite (a = Some r) in H
    end; trivial.
    discriminate.

    unfold randomFunc.
    match goal with
    | [|- context[match ?a with | Some _ => _ | None => _ end] ] =>
        case_eq a; intros
    end.
    eapply comp_spec_ret; intuition idtac.
    simpl in *.
    rewrite any_dec_cons.
    simpl.
    match goal with
    | [|- context[if ?a then _ else _] ] =>
      cutrewrite (a = Some r)
    end; trivial.
    simpl.
    symmetry.
    eapply ex_any_dec.
    eapply arrayLookup_Some_impl_In.
    eauto.
    simpl.  
    match goal with
    | [|- context[if ?a then _ else _] ] =>
      cutrewrite (a = Some r)
    end;
    simpl; trivial.

    simpl in *.
    rewrite any_dec_cons in *.
    apply orb_false_elim in H3.
    intuition idtac.
    simpl in *.
    match goal with
    | [H: (if ?a then _ else _) = false |- _] =>
      cutrewrite (a = Some r) in H
    end; trivial.
    discriminate.

    simpl in *.
    rewrite any_dec_cons in *.
    apply orb_false_elim in H3.
    intuition idtac.
    simpl in *.
    match goal with
    | [H: (if ?a then _ else _) = false |- _] =>
      cutrewrite (a = Some r) in H
    end; trivial.
    discriminate.

    fcf_irr_r.
    eapply comp_spec_ret; intuition idtac.
    simpl in *.
    repeat rewrite any_dec_cons.
    simpl in *.
    repeat rewrite (any_dec_map fst (fun y =>if (arrayLookup _ ls y) then true else false)).
    repeat rewrite <- fst_split_map_eq.
    rewrite any_dec_arrayLookup_swap.
    symmetry.
    rewrite any_dec_arrayLookup_swap.
    symmetry.
    f_equal.
    eapply any_dec_f_eq.
    intuition idtac.
    rewrite H.
    reflexivity.
    simpl in *.
    rewrite any_dec_cons in *.
    apply orb_false_elim in H4.
    intuition idtac.
    simpl in *.
    match goal with
    | [H: (if ?a then _ else _) = false |- _] =>
      cutrewrite (a = Some r) in H
    end; trivial.
    discriminate.
    simpl in *.
    rewrite any_dec_cons in *.
    apply orb_false_elim in H4.
    intuition idtac.
    simpl in *.
    match goal with
    | [H: (if ?a then _ else _) = false |- _] =>
      cutrewrite (a = Some r) in H
    end; trivial.
    discriminate.

    rewrite arrayLookup_app_None in H0.
    rewrite H0.
    eapply comp_spec_ret; intuition idtac.
    simpl in *.
    repeat rewrite any_dec_cons.
    simpl in *.
    repeat rewrite (any_dec_map fst (fun y =>if (arrayLookup _ ls y) then true else false)).
    repeat rewrite <- fst_split_map_eq.
    rewrite any_dec_arrayLookup_swap.
    symmetry.
    rewrite any_dec_arrayLookup_swap.
    symmetry.
    f_equal.
    eapply any_dec_f_eq.
    intuition idtac.
    rewrite H.
    reflexivity.
    simpl in *.
    rewrite H.
    reflexivity.
    trivial.

    match goal with
    | [H: arrayLookup ?eqd (?ls1 ++ ?ls2) ?a = None |- _] =>
      case_eq (arrayLookup eqd ls1 a); intros
    end.
    erewrite arrayLookup_app_Some in H0; eauto.
    discriminate.
    rewrite arrayLookup_app_None in H0.
    rewrite H0.

    unfold randomFunc.
    rewrite H.

    match goal with
    | [|- context[match ?a with | Some _ => _ | None => _ end] ] =>
        case_eq a; intros
    end.
    eapply comp_spec_ret; intuition idtac.
    simpl in *.
    repeat rewrite (any_dec_map fst (fun y =>if (arrayLookup _ ls y) then true else false)).
    repeat rewrite <- fst_split_map_eq.
    rewrite any_dec_arrayLookup_swap.
    symmetry.
    rewrite any_dec_arrayLookup_swap.
    symmetry.
    eapply any_dec_f_eq.
    intuition idtac.
    rewrite H.
    reflexivity.

    fcf_skip.
    eapply comp_base_exists; eauto.
    eapply comp_base_exists; eauto.
    eapply comp_spec_ret; intuition idtac.
    simpl in *.
    repeat rewrite any_dec_cons.
    repeat rewrite (any_dec_map fst (fun y =>if (arrayLookup _ ls y) then true else false)).
    repeat rewrite <- fst_split_map_eq.
    rewrite any_dec_arrayLookup_swap.
    symmetry.
    rewrite any_dec_arrayLookup_swap.
    symmetry.
    f_equal.
    eapply any_dec_f_eq.
    intuition idtac.
    rewrite H.
    reflexivity.

    simpl.
    rewrite H.
    reflexivity.
    trivial.
  
   Qed.

  (* a list of random values with history *)
  Definition rndHist (ls : list (D * R))(d : D) :=
    r <-$ RndR;
    ret (r, (d,r)::ls).
  Theorem rndHist_wf : forall ls d,
    well_formed_comp (rndHist ls d).

    unfold rndHist.
    intuition idtac; wftac.

  Qed.

  Hint Resolve rndHist_wf : wf.
  
End RandomFunc_hist.

Local Open Scope type_scope.
Local Open Scope comp_scope.

Section PRF_concrete.
  
  Variable D R Key : Set.
  Variable RndKey : Comp Key.
  Variable RndR : Comp R.
  Variable f : Key -> D -> R.

  Hypothesis D_EqDec : EqDec D.
  Hypothesis R_EqDec : EqDec R.

  Definition RndR_func : (list (D * R) -> D -> Comp (R * list (D * R))) :=
    (randomFunc RndR _).

  Section PRF_NA_concrete.
  (* A PRF that is secure against a non-adaptive adversary. *)
      
    Variable State : Set.
    Variable A1 : Comp (list D * State).
    Variable A2 : State -> list R -> Comp bool.

    Definition PRF_NA_G_A : Comp bool := 
      [lsD, s_A] <-$2 A1; 
      lsR <-$ (k <-$ RndKey; ret (map (f k) lsD));
      A2 s_A lsR.
    
    Definition PRF_NA_G_B : Comp bool := 
      [lsD, s_A] <-$2 A1;
      [lsR, _] <-$2 oracleMap _ _ RndR_func nil lsD;
      A2 s_A lsR.
    
    Definition PRF_NA_Advantage := 
    | Pr[PRF_NA_G_A] - Pr[PRF_NA_G_B] |.  

  End PRF_NA_concrete.

  Section PRF_NAI_concrete.

    Variable A_state : Set.
    Variable A1 : Comp ((list (list D)) * A_state).
    Variable A2 : A_state -> list (list R) -> Comp bool.

    Definition PRF_NAI_G0 :=
      [lsDs, s_A] <-$2 A1;
      lsRs <-$ compMap _ (fun lsD => k <-$ RndKey; ret (map (f k) lsD)) lsDs;
      A2 s_A lsRs.

    Definition PRF_NAI_G1 :=
      [lsDs, s_A] <-$2 A1;
      lsRs <-$ compMap _ (fun lsD => [lsR, _] <-$2 oracleMap _ _ RndR_func nil lsD; ret lsR) lsDs;
      A2 s_A lsRs.

    Definition PRF_NAI_Advantage := 
    | Pr[PRF_NAI_G0] - Pr[PRF_NAI_G1] |.   
                         
  Section PRF_NA_impl_NAI.

    Variable maxLists : nat.
    Hypothesis maxLists_correct : 
      forall ls s_A, 
        In (ls, s_A) (getSupport A1) ->
        (length ls <= maxLists)%nat.

    Hypothesis A_state_EqDec : EqDec A_state.
    Hypothesis RndR_wf : well_formed_comp RndR.
    Hypothesis RndKey_wf : well_formed_comp RndKey.

    Variable maxDistance : Rat.
    Hypothesis maxDistance_correct : 
      forall i, 
      PRF_NA_Advantage (B1 nil _ _ A1 i) (B2 (fun lsD => k <-$ RndKey; ret (map (f k) lsD))
              (fun lsD => [lsR, _] <-$2 oracleMap _ _ RndR_func nil lsD; ret lsR)
              _ A2) <= maxDistance.

    Theorem PRF_NAI_Advantage_eq_Hybrid:
      PRF_NAI_Advantage == ListHybrid_Advantage 
                             (fun lsD => k <-$ RndKey; ret (map (f k) lsD))
                             (fun lsD => [lsR, _] <-$2 oracleMap _ _ RndR_func nil lsD; ret lsR)
                             _ A1 A2.

      reflexivity.

    Qed.

     
    Theorem PRF_NA_impl_NAI : 
      PRF_NAI_Advantage <= (maxLists / 1 * maxDistance)%rat.


      rewrite PRF_NAI_Advantage_eq_Hybrid.
      rewrite Single_impl_ListHybrid.
      reflexivity.
      
      intuition.
      wftac.

      intuition.
      wftac.
      eapply oracleMap_wf.
      intuition.
      eapply randomFunc_wf; intuition.
      intuition.

      intuition.

      assert (DistSingle_Adv (fun lsD : list D => k <-$ RndKey; ret map (f k) lsD)
     (fun lsD : list D =>
      z <-$
      oracleMap (list_EqDec (pair_EqDec D_EqDec R_EqDec)) R_EqDec RndR_func
        nil lsD; [lsR, _]<-2 z; ret lsR)
     (B1 nil (list_EqDec D_EqDec) A_state_EqDec A1 i)
     (B2 (fun lsD : list D => k <-$ RndKey; ret map (f k) lsD)
        (fun lsD : list D =>
         z <-$
         oracleMap (list_EqDec (pair_EqDec D_EqDec R_EqDec)) R_EqDec
           RndR_func nil lsD; [lsR, _]<-2 z; ret lsR) 
        (list_EqDec R_EqDec) A2)
     ==
     PRF_NA_Advantage
                          (B1 nil (list_EqDec D_EqDec) A_state_EqDec A1 i)
                          (B2
                             (fun lsD : list D =>
                              k <-$ RndKey; ret map (f k) lsD)
                             (fun lsD : list D =>
                              z <-$
                              oracleMap
                                (list_EqDec (pair_EqDec D_EqDec R_EqDec))
                                R_EqDec RndR_func nil lsD;
                              [lsR, _]<-2 z; ret lsR) 
                             (list_EqDec R_EqDec) A2)
                          ).
      unfold DistSingle_Adv, PRF_NA_Advantage, DistSingle_G, PRF_NA_G_A, PRF_NA_G_B.
      eapply ratDistance_eqRat_compat;
        repeat (try comp_skip; try reflexivity; comp_simp; inline_first).
      rewrite H.
      clear H.
      intuition.
    Qed.

  End PRF_NA_impl_NAI.

  End PRF_NAI_concrete.

  Section PRF_Full_concrete.
    
    Variable A : OracleComp D R bool.
    
    Definition f_oracle(k : Key)(x : unit)(d : D) :=
      ret (f k d, tt).
    
    Definition PRF_G_A : Comp bool := 
      k <-$ RndKey;
      [b, _] <-$2 A _ _ (f_oracle k) tt;
      ret b.
    
    Definition PRF_G_B : Comp bool := 
      [b, _] <-$2 A _ _ (RndR_func) nil;
      ret b.
    
    Definition PRF_Advantage := 
    | Pr[PRF_G_A] - Pr[PRF_G_B] |.  
    
  End PRF_Full_concrete.

  Section PRF_Finite_concrete.

    Variable dom : list D.
    Variable def : R.
    Variable A : (D -> R) -> Comp bool.

    Definition PRF_Fin_G_A : Comp bool := 
      k <-$ RndKey;
      A (f k).
    
    Definition PRF_Fin_G_B : Comp bool := 
      f <-$ @RndFunc D R RndR _ dom;
      A (fun d => arrayLookupDef _ f d def).

    Definition PRF_Fin_Advantage := 
    | Pr[PRF_Fin_G_A] - Pr[PRF_Fin_G_B] |.

  End PRF_Finite_concrete.
  
End PRF_concrete.

Require Import FCF.Asymptotic.
Require Import FCF.Admissibility.

Section PRF.

  Variable D R Key : DataTypeFamily.
  Variable RndKey : forall n, Comp (Key n).
  Variable RndR : forall n, Comp (R n).
  Variable f : forall n, Key n -> D n -> R n.

  Hypothesis D_EqDec : forall n, EqDec (D n).
  Hypothesis R_EqDec : forall n, EqDec (R n).

  Section PRF_NA.
    Variable admissible_A1 : pred_comp_fam.
    Variable admissible_A2 : pred_comp_func_2_fam.
    
    Definition PRF_NA :=
      forall (State : DataTypeFamily) A1 A2,
        admissible_A1 _ A1 -> 
        admissible_A2 State _ _ A2 ->
        negligible (fun n => PRF_NA_Advantage (RndKey n) (RndR n) (@f n) _ _ (A1 n) (@A2 n)).
  End PRF_NA.

  Section PRF_Full.
    Variable admissible_A : pred_oc_fam.
    
    Definition PRF :=
      forall (A : forall n, OracleComp (D n) (R n) bool),
        admissible_A _ _ _ A -> 
        negligible (fun n => PRF_Advantage (RndKey n) (RndR n) (@f n) _ _ (A n)).
  End PRF_Full.
      
End PRF.
