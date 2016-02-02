Set Implicit Arguments.

Require Import FCF.
Require Import GroupTheory.

Theorem modNat_mult_eq : 
  forall a b c,
    modNat (a * b) c = 
    modNat (a * modNat b c) c.
  
  intuition.
  destruct (modNat_correct b c).
  rewrite H.
  clear H;
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

  Section Binding.

    Variable A : PublicParam -> Comp (Commitment * (Value * RevealValue) * (Value * RevealValue)).

    Definition BindingCommit_G := 
      [pub, pri] <-$2 Setup;
      [c, p1, p2] <-$3 A pub;
      [v1, r1] <-2 p1;
      [v2, r2] <-2 p2;
      ret ((negb (eqb v1 v2)) && (Reveal pri c r1 v1) && (Reveal pri c r2 v2)).
      
  End Binding.

  Section Hiding.

    Variable A_State : Set.
    Variable A1 : PublicParam -> Comp (Value * Value * A_State).
    Variable A2 : A_State -> Commitment -> Comp bool.

    Definition HidingCommit_G := 
      [pub, pri] <-$2 Setup;
      [v1, v2, s_A] <-$3 A1 pub;
      b <-$ {0, 1};
      v <- if b then v1 else v2;
      [c, r] <-$2 Commit pub v;                  
      b' <-$ A2 s_A c;
      ret (eqb b b').
      
  End Hiding.
    
End CommitmentScheme.


Require Import OTP.
Require Import RndNat.
Require Import RndGrpElem.

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

  Local Open Scope nat_scope.

  Variable multInverseModOrder : nat -> nat.
  Hypothesis multInverseCorrect :
    forall a,
      (modNat (a * (multInverseModOrder a)) order = 1)%nat.
 
  Theorem group_OTP_exp : 
    forall (x : nat),
      comp_spec eq (RndG) (r <-$ [0 .. order) ; ret (g ^ x) ^r)%group.

    intuition.
    eapply comp_spec_seq; intuition.
    eapply comp_spec_symm.
    eapply (comp_spec_iso (fun z => modNat (x * z) order) (fun z => modNat (z * multInverseModOrder x) order)).
  
    intuition.
    rewrite (mult_comm x0).
    rewrite <- modNat_mult_eq.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite modNat_mult_eq.
    rewrite  multInverseCorrect.
    rewrite mult_1_r.
    eapply modNat_eq.
    eapply RndNat_support_lt.
    trivial.

    intuition.
    rewrite mult_comm.
    rewrite <- modNat_mult_eq.
    rewrite mult_assoc.
    rewrite mult_comm.
    rewrite modNat_mult_eq.
    rewrite (mult_comm _ x).
    rewrite  multInverseCorrect.
    rewrite mult_1_r.
    eapply modNat_eq.
    eapply RndNat_support_lt.
    trivial.

    intuition.
    eapply in_getSupport_RndNat.
    eapply modNat_lt.
    
    intuition.
    eapply eq_impl_comp_spec.
    eapply well_formed_RndNat.
    intuition.
    eapply well_formed_RndNat.
    intuition.
    eapply RndNat_uniform.
    eapply modNat_lt.
    eapply RndNat_support_lt.
    trivial.

    simpl in H2.
    subst.
    eapply comp_spec_ret.
    rewrite <- groupExp_mod.
    symmetry.
    apply groupExp_mult.
    eapply H.
  Qed.

  Local Open Scope rat_scope.
  Local Open Scope group_scope.

  Section PedersenHiding.

    Variable A_State : Set.
    Variable A1 : GroupElement -> Comp (nat * nat * A_State).
    Hypothesis A1_wf : forall p, well_formed_comp (A1 p).
    Variable A2 : A_State -> GroupElement -> Comp bool.
    Hypothesis A2_wf : 
      forall s c, well_formed_comp (A2 s c).

    Definition PedersenHiding_G0 :=
      a <-$ [ 0  .. order);
      [v1, v2, s_A] <-$3 A1 (g^a);
      b <-$ {0,1};
      v <- (if b then v1 else v2);
      z <-$
        (r <-$ [ 0  .. order);
         ret (g^a)^r);
      b' <-$ A2 s_A (g ^ v * z); 
      ret eqb b b'.

    Definition PedersenHiding_G1 :=
      a <-$ [ 0  .. order);
      [v1, v2, s_A] <-$3 A1 (g^a);
      b <-$ {0,1};
      v <- (if b then v1 else v2);
      z <-$ 
        (x <-$ RndGrpElem;
         ret (g ^ v * x));
      b' <-$ A2 s_A z; 
      ret eqb b b'.

    Definition PedersenHiding_G2 :=
      a <-$ [ 0  .. order);
      [v1, v2, s_A] <-$3 A1 (g^a);
      b <-$ {0,1};
      x <-$ RndGrpElem;
      b' <-$ A2 s_A x; 
      ret eqb b b'.

    Definition PedersenHiding_G3 :=
      a <-$ [ 0  .. order);
      [v1, v2, s_A] <-$3 A1 (g^a);
      x <-$ RndGrpElem;
      b' <-$ A2 s_A x; 
      b <-$ {0,1};
      ret eqb b b'.
    
    Theorem PedersenHiding_G0_equiv : 
      Pr[HidingCommit_G PedersenSetup PedersenCommit A1 A2] ==
      Pr[PedersenHiding_G0].

      unfold HidingCommit_G, PedersenSetup, PedersenCommit, PedersenHiding_G0.
      repeat (inline_first; comp_skip; comp_simp).

    Qed.

    Theorem PedersenHiding_G1_equiv : 
      Pr[PedersenHiding_G0] ==
      Pr[PedersenHiding_G1].

      unfold PedersenHiding_G0, PedersenHiding_G1.
      do 3 (inline_first; comp_skip; comp_simp).
      comp_inline_r.
      comp_skip.
      symmetry.
      eapply comp_spec_eq_impl_eq.
      apply group_OTP_exp.
      comp_simp.
      intuition.

    Qed.

    Theorem PedersenHiding_G2_equiv : 
      Pr[PedersenHiding_G1] ==
      Pr[PedersenHiding_G2].

      unfold PedersenHiding_G1, PedersenHiding_G2.
      do 3 (inline_first; comp_skip; comp_simp).
      comp_skip.
      symmetry.
      eapply comp_spec_eq_impl_eq.
      eapply group_OTP_l.
    Qed.

    Theorem PedersenHiding_G3_equiv : 
      Pr[PedersenHiding_G2] ==
      Pr[PedersenHiding_G3].

      unfold PedersenHiding_G2, PedersenHiding_G3.
      do 2 (inline_first; comp_skip; comp_simp).
      comp_swap_l.
      comp_skip.
      comp_swap_l.
      comp_skip.
    Qed.

    Theorem PedersenHiding_G3_half : 
      Pr[PedersenHiding_G3] == 1/2.

      unfold PedersenHiding_G3.
      do 2 comp_irr_l; comp_simp.
      do 2 comp_irr_l.
      dist_compute.
    Qed.

    Theorem PedersenInfoTheoreticHiding : 
      Pr[HidingCommit_G PedersenSetup PedersenCommit A1 A2] == 1/2.
      
      rewrite PedersenHiding_G0_equiv.
      rewrite PedersenHiding_G1_equiv.
      rewrite PedersenHiding_G2_equiv.
      rewrite PedersenHiding_G3_equiv.
      apply PedersenHiding_G3_half.
      
    Qed.

  End PedersenHiding.

  Section PedersenBinding.

    Variable A :  GroupElement -> Comp (GroupElement * (nat * nat) * (nat * nat)).

    Definition B (x : GroupElement) :=
      [c, p1, p2] <-$3 A x;
      [v1, r1] <-2 p1;
      [v2, r2] <-2 p2;
      ret (modNat ((v1 + (modNatAddInverse v2 order)) * (multInverseModOrder (r2 + (modNatAddInverse r1 order)))) order)%nat. 
    
    Theorem PedersenComputionallyBinding : 
      Pr[BindingCommit_G PedersenSetup _ PedersenReveal A] <= 
      Pr[(@DLP_G _ groupOp _ _ _ g order B)].
      
      unfold BindingCommit_G, PedersenSetup, PedersenReveal, B, DLP_G.
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

      Theorem modNat_0 : 
        forall c,
          modNat 0 c = 0.
        
        induction c; intuition; simpl in *.
        
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
    
  End PedersenBinding.

End Pedersen.