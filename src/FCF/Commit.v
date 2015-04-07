Set Implicit Arguments.

Require Import FCF.
Require Import GroupTheory.

Local Open Scope group_scope.

Section DLP.
  Context `{FiniteCyclicGroup}.
  Hypothesis GroupElement_EqDec : EqDec GroupElement.

  Variable A : GroupElement -> Comp nat.

  Definition DLP_G :=
    x <-$ [0 .. order);
    x' <-$ A (g ^ x);
    ret (eqb x x').
  
End DLP.

Section CommitmentScheme.

  Variable PublicParam PrivateParam : Set.
  Variable Setup : Comp (PublicParam * PrivateParam).

  Variable Value : Set.
  Hypothesis Value_EqDec : EqDec Value.
  Variable Commitment : Set.
  Variable RevealValue : Set.
  Variable Commit : PublicParam -> Value -> Comp (Commitment * RevealValue).

  Variable Reveal : PrivateParam -> Commitment -> RevealValue -> Value -> bool.

  Section ComputationalBinding.

    Variable A : PublicParam -> Comp (Commitment * (Value * RevealValue) * (Value * RevealValue)).

    Definition ComputationallyBindingCommit_G := 
      [pub, pri] <-$2 Setup;
      [c, p1, p2] <-$3 A pub;
      [v1, r1] <-2 p1;
      [v2, r2] <-2 p2;
      ret ((negb (eqb v1 v2)) && (Reveal pri c r1 v1) && (Reveal pri c r2 v2)).
      
  End ComputationalBinding.
    
End CommitmentScheme.


Section Pedersen.

  Context `{FiniteCyclicGroup}.
  Hypothesis GroupElement_EqDec : EqDec GroupElement.

  Definition PedersenSetup :=
    a <-$ [0 .. order);
    ret (g ^ a, a).

  Definition PedersenCommit (h : GroupElement) (x : nat) :=
    r <-$ [0 .. order);
    ret (g ^ x * (h ^ r), r).

  Definition PedersenReveal (a : nat)(c : GroupElement)(r : nat)(x : nat) :=
    eqb c (g^x * ((g^a)^r)).

  Variable A :  GroupElement -> Comp (GroupElement * (nat * nat) * (nat * nat)).

  Variable multInverseModOrder : nat -> nat.
  Hypothesis multInverseCorrect :
    forall a,
      (modNat (a * (multInverseModOrder a)) order = 1)%nat. 
           

  Definition B (x : GroupElement) :=
    [c, p1, p2] <-$3 A x;
    [v1, r1] <-2 p1;
    [v2, r2] <-2 p2;
    ret (modNat ((v1 + (modNatAddInverse v2 order)) * (multInverseModOrder (r2 + (modNatAddInverse r1 order)))) order)%nat. 

  Theorem PedersenComputionallyBinding : 
    Pr[ComputationallyBindingCommit_G PedersenSetup _ PedersenReveal A] <= 
    Pr[(@DLP_G _ groupOp _ _ _ g order B)].

    unfold ComputationallyBindingCommit_G, PedersenSetup, PedersenReveal, B, DLP_G.
    inline_first.
    comp_skip.
    inline_first.
    comp_skip.
    reflexivity.
    comp_simp.
    
    Local Opaque evalDist.

    case_eq (eqb n n1); intuition;
    simpl.
    rewrite evalDist_ret_0.
    eapply rat0_le_all.
    intuition.

    case_eq (eqb g0 (g ^ n * (g ^ x) ^ n0)); intuition.
    simpl.
    rewrite eqb_leibniz in H3.
    case_eq ( eqb g0 (g ^ n1 * (g ^ x) ^ n2)); intuition.
    rewrite eqb_leibniz in H4.
    subst.


    case_eq (eqb x
          (modNat ((n + modNatAddInverse n1 order) *
           multInverseModOrder (n2 + modNatAddInverse n0 order)) order)%nat); intuition.
    exfalso.
    eapply eqb_false_iff in H3.
    eapply H3.
    clear H3.
    repeat rewrite groupExp_mult in H4.
    repeat rewrite <- groupExp_plus in H4.
    apply groupExp_eq in H4.

    Local Open Scope nat_scope.

    Theorem plus_add_same_r_if : 
      forall (c a b : nat),
        a = b ->
        a + c = b + c.

      intuition; omega.
      
    Qed.

    apply (plus_add_same_r_if (modNatAddInverse n1 order)) in H4.

    Theorem modNat_eq_compat_gen : 
      forall c a b,
        a = b ->
        modNat a c = modNat b c.

      intuition.
      subst.
      intuition.

    Qed.

    eapply (modNat_eq_compat_gen order) in H4.

    repeat rewrite <- modNat_plus in H4.
    rewrite <- (plus_comm  (x * n2)) in H4.
    rewrite <- (plus_assoc _ n1) in H4.
    rewrite (plus_comm (x * n2)) in H4.
    symmetry in H4.
    rewrite modNat_plus in H4.
    rewrite modNatAddInverse_correct in H4.
    rewrite plus_0_l in H4.
    symmetry in H4.
    rewrite (plus_comm) in H4.
    rewrite plus_assoc in H4.
    eapply (plus_add_same_r_if (modNatAddInverse (x * n0) order)) in H4.
    eapply (modNat_eq_compat_gen order) in H4.
    rewrite <- modNat_plus in H4.
    rewrite <- plus_assoc in H4.
    rewrite plus_comm in H4.
    rewrite modNat_plus in H4.
    rewrite modNatAddInverse_correct in H4.
    rewrite plus_0_l in H4.
    rewrite <- modNat_plus in H4.

    SearchAbout modNatAddInverse mult.

    Theorem modNat_0 : 
      forall c,
        modNat 0 c = 0.

      induction c; intuition; simpl in *.

    Qed.

    Theorem modNat_mult_eq : 
      forall a b c,
        modNat (a * b) c = 
        modNat (a * modNat b c) c.

      intuition.
      destruct (modNat_correct b c).
      rewrite H0.
      clear H0;
      rewrite mult_plus_distr_l.
      rewrite modNat_plus.
      rewrite mult_assoc.
      rewrite modNat_mult.
      rewrite plus_0_l.
      symmetry.
      rewrite modNat_plus.
      rewrite modNat_mult.
      rewrite plus_0_l.
      rewrite (@modNat_eq _ (modNat b c)).
      trivial.
      eapply modNat_lt.

    Qed.

    Theorem modNatAddInverse_mult : 
      forall a b c,
        modNat (modNatAddInverse (a * b) c) c = 
        modNat (a * modNatAddInverse b c) c.

      intuition.

      unfold modNatAddInverse.
      rewrite mult_minus_distr_l.
      rewrite modNat_mult_eq.
      remember (modNat b c) as z.
      eapply (modNat_add_same_r (modNat (a * z) c)).
      rewrite Nat.sub_add.
      rewrite modNat_arg_eq.
      rewrite plus_comm.
      rewrite <- modNat_plus.
      rewrite plus_comm.
      rewrite Nat.sub_add.
      symmetry.
      apply modNat_mult.
      eapply mult_le_compat; intuition.
      subst.
      eapply lt_le_weak.
      apply modNat_lt.
      eapply lt_le_weak.
      apply modNat_lt.
    Qed.

    Show.

    symmetry in H4.
    rewrite (plus_comm (x * n2)) in H4.
    rewrite modNat_plus in H4.
    rewrite modNatAddInverse_mult in H4.
    rewrite <- modNat_plus in H4.
    rewrite <- mult_plus_distr_l in H4.
    
    Theorem modNat_mult_same_r : 
      forall a b c d,
        modNat a d = modNat b d ->
        modNat (a * c) d = modNat (b * c) d.
        
      intuition.
      rewrite mult_comm.
      rewrite modNat_mult_eq.
      rewrite H0.
      rewrite <- modNat_mult_eq.
      rewrite mult_comm.
      intuition.
    Qed.

    apply (modNat_mult_same_r _ _ (multInverseModOrder (n2 + modNatAddInverse n0 order)))in H4.
    rewrite <- mult_assoc in H4.
    rewrite modNat_mult_eq in H4.
    rewrite (plus_comm n2) in H4.
    rewrite multInverseCorrect in H4.
    rewrite mult_1_r in H4.
    rewrite modNat_eq in H4.
    rewrite H4.
    clear H4.
    rewrite (plus_comm (modNatAddInverse n1 order)).
    rewrite (plus_comm n2).
    trivial.

    eapply RndNat_support_lt; intuition.

    eapply H.
    
    rewrite evalDist_ret_0.
    eapply rat0_le_all.
    intuition.

    simpl.
    rewrite evalDist_ret_0.
    eapply rat0_le_all.
    intuition.
  Qed.

  Print Assumptions PedersenComputionallyBinding.

End Pedersen.