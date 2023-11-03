(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
(* Definitions and theory of natural numbers that is useful in cryptographi proofs. *)

Set Implicit Arguments.

Require Export Arith.
Require Export micromega.Lia.
Require Import Coq.NArith.BinNat.

Local Ltac Tauto.intuition_solver ::= auto with crelations arith.

Lemma mult_same_r : forall n1 n2 n3,
  n3 > 0 ->
  n1 * n3 = n2 * n3 ->
  n1 = n2.

  induction n1; destruct n2; intuition idtac; simpl in *.
  remember (n2 * n3) as x.
  lia.
  remember (n1 * n3) as x.
  lia.
  
  f_equal.
  eapply IHn1; eauto.
  
  eapply Nat.add_cancel_l. eauto.
Qed.

Lemma mult_same_l : forall n3 n1 n2,
  n3 > 0 ->
  n3 * n1 = n3 * n2 ->
  n1 = n2.
  
  intuition.
  eapply mult_same_r; eauto.
  rewrite Nat.mul_comm.
  rewrite (Nat.mul_comm n2 n3).
  trivial.
Qed.

Lemma mult_gt_0 : forall n1 n2,
  n1 > 0 ->
  n2 > 0 ->
  n1 * n2 > 0.
  destruct n1; intuition idtac; simpl in *.
  remember (n1 * n2) as x.
  lia.
Qed.

Lemma minus_eq_compat : forall n1 n2 n3 n4,
  n1 = n2 ->
  n3 = n4 ->
  n1 - n3 = n2 - n4.
  
  intuition.
Qed.

Lemma plus_eq_compat : forall n1 n2 n3 n4,
  n1 = n2 ->
  n3 = n4 ->
  n1 + n3 = n2 + n4.
  
  intuition.
Qed.

Lemma minus_diag_eq : forall n1 n2,
  n1 = n2 ->
  n1 - n2 = 0.
  
  intuition.
  lia.
Qed.

Lemma le_eq : forall n1 n2,
  n1 = n2 ->
  n1 <= n2.
  
  intuition.
  lia.
Qed.

Lemma minus_add_assoc : forall n1 n2 n3,
  (n3 <= n2)%nat ->
  (n1 + (n2 - n3) = n1 + n2 - n3)%nat.
  
  intuition.
  lia.
Qed.


Class nz (a : nat) := {
  agz : a > 0
}.

#[export] Instance nz_nat : forall (n : nat), nz (S n).
intuition.
econstructor.
lia.
Defined.

Definition posnat := {n : nat | n > 0}.

Definition posnatToNat(p : posnat) :=
  match p with
    | exist _ n _ => n
  end.

Inductive posnatEq : posnat -> posnat -> Prop :=
  | posnatEq_intro : 
    forall (n1 n2 : nat) pf1 pf2,
      n1 = n2 ->
      posnatEq (exist _ n1 pf1) (exist _ n2 pf2).

Definition posnatMult(p1 p2 : posnat) : posnat :=
    match (p1, p2) with
      | (exist _ n1 pf1, exist _ n2 pf2) =>
        (exist (fun n => n > 0) (n1 * n2) (mult_gt_0 pf1 pf2))
    end.

Lemma posnatMult_comm : forall p1 p2,
  (posnatEq (posnatMult p1 p2) (posnatMult p2 p1)).

  intuition.
  unfold posnatMult.
  destruct p1; destruct p2.
  econstructor.
  apply Nat.mul_comm.
Qed.  

Coercion posnatToNat : posnat >-> nat.

Lemma posnat_pos : forall (p : posnat),
  p > 0.
  
  intuition.
  destruct p.
  unfold posnatToNat.
  trivial.
Qed.

#[export] Instance nz_posnat : forall (p : posnat),
  nz p.

intuition.
econstructor.
eapply posnat_pos.

Qed.

Definition natToPosnat(n : nat)(pf : nz n) :=
  (exist (fun x => x > 0) n agz).

Notation "'pos' x" := (@natToPosnat x _) (at level 40).

Fixpoint expnat n1 n2 :=
  match n2 with
    | 0 => 1
    | S n2' =>
      n1 * (expnat n1 n2')
  end.

Theorem expnat_pos : forall x n,
  x > 0 ->
  expnat x n > 0.
  
  induction n; intuition; simpl in *.
  apply mult_gt_0; assumption.
Qed.

Lemma div2_le : forall n,
  le (Nat.div2 n) n.
  
  intuition.

  eapply PeanoNat.Nat.div2_decr.
  lia.
  
Qed.

Lemma div2_ge_double : forall n, 
  n >= (Nat.div2 n) + (Nat.div2 n).
  
  intuition.
  destruct (Nat.Even_Odd_dec n).
  
  rewrite (Nat.Even_double n) at 1.
  unfold Nat.double.
  lia.
  trivial.
  rewrite (Nat.Odd_double n) at 1.
  unfold Nat.double.
  lia.
  trivial.
Qed.

Local Open Scope N_scope.
Definition modNat (n : nat)(p : posnat) : nat :=
  N.to_nat ((N.of_nat n) mod (N.of_nat p)).

Lemma Npos_nz : forall p, 
  Npos p <> N0.
  intros []; discriminate.
Qed.

Lemma modNat_plus : forall n1 n2 p,
    (modNat (n1 + n2) p = modNat ((modNat n1 p) + n2) p)%nat.
  
  unfold modNat.

  intuition.
  rewrite Nnat.Nat2N.inj_add.

  rewrite <- N.add_mod_idemp_l.
  f_equal.
  rewrite <- (Nnat.Nat2N.id n2) at 2.
  rewrite Nnat.Nat2N.inj_add.
  repeat rewrite Nnat.N2Nat.id.
  trivial.

  destruct p.
  simpl.
  
  destruct x;
  simpl.
  lia.
  

  apply Npos_nz.

Qed.


Lemma modNat_arg_eq : forall (p : posnat),
  modNat p p = O.

  intuition.
  unfold modNat.
  rewrite N.mod_same.
  trivial.
  unfold N.of_nat, posnatToNat.
  destruct p.
  destruct x.
  lia.
  apply Npos_nz.

Qed.

Lemma of_nat_ge_0 : forall n,
  0 <= N.of_nat n.

  intuition.
  unfold N.of_nat.
  destruct n.
  intuition.

  lia.
Qed.

Lemma of_posnat_gt_0 : forall (p : posnat),
  0 < N.of_nat p.

  intuition.
  unfold N.of_nat, posnatToNat.
  destruct p.
  destruct x.
  lia.
  destruct x; intuition; simpl in *.
  lia.
  lia.
Qed.

Lemma modNat_lt : forall x p, (modNat x p < p)%nat.

  intuition.
  unfold modNat.
  assert (N.of_nat x mod N.of_nat p < N.of_nat p)%N.
  apply N.mod_bound_pos.
  apply of_nat_ge_0.
  apply of_posnat_gt_0.

  specialize (Nnat.N2Nat.inj_compare); intros H0.
  rewrite <- (Nnat.Nat2N.id p) at 2.
  apply nat_compare_lt.
  rewrite <- H0.
  apply N.compare_lt_iff.
  trivial.

Qed.

Lemma modNat_eq : forall (n : posnat) x, (x < n -> modNat x n = x)%nat.
  
  intuition.
  unfold modNat.
  rewrite N.mod_small.
  apply Nnat.Nat2N.id.
  specialize (Nnat.N2Nat.inj_compare); intuition.
  specialize (N.compare_lt_iff (N.of_nat x) (N.of_nat n)); intuition.
  apply H2.
  rewrite H0.
  repeat rewrite Nnat.Nat2N.id.
  apply nat_compare_lt.
  trivial.
Qed.

Definition modNatAddInverse (n : nat)(p : posnat) :=
  (p - (modNat n p))%nat.

Lemma modNatAddInverse_correct_gen : forall x y p,
  modNat x p = modNat y p ->
  modNat (x + modNatAddInverse y p) p = O.
  
  intuition.
  unfold modNatAddInverse.
  rewrite <- H.
  rewrite modNat_plus.
  rewrite minus_add_assoc.
  rewrite (Nat.add_comm).
  rewrite <- minus_add_assoc.
  rewrite Nat.sub_diag.
  rewrite Nat.add_0_r.
  apply modNat_arg_eq.
  
  trivial.
  
  assert (modNat x p < p)%nat.
  apply modNat_lt.
  lia.
  
Qed.

Lemma modNatAddInverse_correct : forall n p,
    modNat (n + modNatAddInverse n p) p = O.

  intuition.
  eapply modNatAddInverse_correct_gen.
  trivial.
  
Qed.

Lemma modNat_correct : forall x (p : posnat),
  exists k, (x = k * p + modNat x p)%nat.

  intuition.
  unfold modNat in *.
  assert (p > 0)%nat.
  eapply posnat_pos.
  assert (posnatToNat p <> 0)%nat.
  lia.
  assert (N.of_nat p <> 0%N).
  intro.
  eapply H0.
  
  rewrite <- Nnat.Nat2N.id.
  rewrite <- (Nnat.Nat2N.id p).
  f_equal.
  trivial.

  exists (N.to_nat (N.of_nat x / N.of_nat p)).
  rewrite N.mod_eq; trivial.

  rewrite <- (Nnat.Nat2N.id p) at 2.
  rewrite <- Nnat.N2Nat.inj_mul.
  rewrite <- Nnat.N2Nat.inj_add.
  rewrite N.mul_comm.
  remember (N.of_nat p * (N.of_nat x / N.of_nat p)) as z.
  rewrite N.add_sub_assoc.
  rewrite N.add_comm.
  rewrite N.add_sub.
  rewrite Nnat.Nat2N.id.
  trivial.

  subst.  
  eapply N.mul_div_le.
  trivial.
Qed.

Lemma modNat_divides : forall x p,
  modNat x p = O ->
  exists k, (x = k * p)%nat.

  intuition.
  destruct (modNat_correct x p).
  rewrite H in H0.
  econstructor.
  rewrite Nat.add_0_r in H0.
  eauto.
Qed.


Local Open Scope nat_scope.
Lemma modNatAddInverse_sum_0 : forall x y p,
  modNat (x + (modNatAddInverse y p)) p = O ->
  modNat x p = modNat y p.
  
  intuition.
  
  assert (modNat x p < p).
  eapply modNat_lt.
  assert (modNat y p < p).
  eapply modNat_lt.
  
  rewrite modNat_plus in H.
  unfold modNatAddInverse in *.
  rewrite minus_add_assoc in H; intuition.
  rewrite Nat.add_comm in H.
  
  apply modNat_divides in H.
  destruct H.
  
  remember (modNat x p) as a.
  remember (modNat y p) as b.
  assert (p + a >= p).
  lia.
  assert (p + a < 2 * p)%nat.
  lia.
  assert (p + a - b < 2 * p).
  lia.
  assert (p + a - b > 0).
  lia.
  
  assert (x0 * p > 0).
  lia.
  assert (x0 * p < 2 * p).
  lia.
  
  destruct x0.
  lia.
  destruct x0.
  
  simpl in H.
  rewrite Nat.add_0_r in H.
  lia.
  
  assert (p > 0).
  eapply posnat_pos.
  simpl in H7.
  remember (x0 * p)%nat as c.
  lia.
Qed.

Lemma modNat_correct_if : forall x y z (p : posnat),
  x * p + y = z ->
  modNat z p = modNat y p.
  
  induction x; intuition; simpl in *.
  subst.
  trivial.
  
  assert (x * p + (y + p) = z).
  lia.
  apply IHx in H0.
  
  rewrite H0.
  rewrite Nat.add_comm.
  rewrite modNat_plus.
  rewrite modNat_arg_eq.
  rewrite Nat.add_0_l.
  trivial.
Qed.

Lemma modNat_mult : forall x (p : posnat),
  modNat (x * p) p = 0.
  
  induction x; intuition; simpl in *.
  rewrite modNat_plus.
  rewrite modNat_arg_eq.
  rewrite Nat.add_0_l.
  eauto.
  
Qed.

Lemma modNat_add_same_l : forall x y z p,
  modNat (x + y) p = modNat (x + z) p ->
  modNat y p = modNat z p.
  
  induction x; intuition; simpl in *.
  assert (S (x + y) = x + S y).
  lia.
  rewrite H0 in H.
  clear H0.
  assert (S (x + z) = x + S z).
  lia.
  rewrite H0 in H.
  clear H0.
  apply IHx in H.
  
  destruct (modNat_correct (S y) p).
  destruct (modNat_correct (S z) p).
  rewrite H in H0.
  
  assert (S y - x0 * p = modNat (S z) p).
  lia.
  assert (S z - x1 * p = modNat (S z) p).
  lia.
  rewrite <- H2 in H3.
  
  assert (z - x1 * p = y - x0 * p).
  lia.
  
  assert (x1 * p + y = x0 * p + z).
  lia.
  
  apply modNat_correct_if in H5.
  rewrite modNat_plus in H5.
  
  rewrite modNat_mult in H5.
  rewrite Nat.add_0_l in H5.
  auto.
  
Qed.

Lemma modNat_add_same_r : forall x y z p,
  modNat (y + x) p = modNat (z + x) p ->
  modNat y p = modNat z p.
  
  intuition.
  eapply (modNat_add_same_l x y z).
  rewrite Nat.add_comm.
  rewrite H.
  rewrite Nat.add_comm.
  trivial.
Qed.

Lemma expnat_base_S : forall n k,
  ((expnat k n) + n * (expnat k (pred n)) <= expnat (S k) n)%nat.

  induction n; intuition.
  simpl in *.
  eapply Nat.le_trans.
  
  2:{
    eapply Nat.add_le_mono.
    eapply IHn.
    eapply Nat.mul_le_mono.
    eapply Nat.le_refl.
    eapply IHn.
  }

  rewrite Nat.mul_add_distr_l.
  repeat rewrite Nat.mul_assoc.
  repeat rewrite Nat.add_assoc.
  eapply Nat.add_le_mono.
  rewrite Nat.add_comm.
  eapply Nat.add_le_mono.
  rewrite <- (Nat.add_0_r (expnat k n)) at 1.
  eapply Nat.add_le_mono. 
  lia.
  intuition.
  intuition.

  rewrite (Nat.mul_comm k n).
  rewrite <- (Nat.mul_assoc n).
  destruct n; simpl; intuition.
Qed.

Lemma expnat_base_S_same : forall n,
  n > 0 ->
  (2 * (expnat n n) <= expnat (S n) n)%nat.

  intuition.
  simpl in *.
  rewrite Nat.add_0_r.
  eapply Nat.le_trans.
  2:{
    eapply expnat_base_S.
  }
  destruct n; simpl.
  lia.
  intuition.
Qed.

Lemma sqrt_le_lin_gen : forall a b,
  (a <= b ->
    Nat.sqrt a <= b)%nat.
  
  intuition.
  eapply Nat.le_trans.
  eapply Nat.sqrt_le_lin.
  trivial.
Qed.

Lemma div2_le_mono : forall n1 n2,
  (n1 <= n2 -> 
    Nat.div2 n1 <= Nat.div2 n2)%nat.
  
  assert (I : 0 < 2) by now apply Nat.lt_0_succ.
  intros n1 n2;
  destruct (Nat.Even_Odd_dec n1) as [[k1 ->] | [k1 ->]];
  destruct (Nat.Even_Odd_dec n2) as [[k2 ->] | [k2 ->]]; intros H.
  - now rewrite 2!Nat.div2_double; apply Nat.mul_le_mono_pos_l with (1 := I).
  - rewrite Nat.div2_double, Nat.add_1_r, Nat.div2_succ_double.
    apply Nat.mul_le_mono_pos_l with (1 := I). lia.
  - rewrite Nat.div2_double, Nat.add_1_r, Nat.div2_succ_double.
    apply Nat.mul_le_mono_pos_l with (1 := I). lia.
  - rewrite 2!Nat.add_1_r, 2!Nat.div2_succ_double. lia.
Qed.

Lemma div2_ge : forall n n',
  n >= n' ->
  forall x,
    (n' = 2 * x)%nat ->
    Nat.div2 n >= x.
  
  induction 1; intuition; subst; simpl in *.
  specialize (Nat.div2_double x); intuition; simpl in *.
  rewrite H.
  lia.
  
  destruct m.
  lia.
  destruct (Nat.Even_Odd_dec m).
  rewrite Nat.Even_div2.
  assert (Nat.div2 (S m) >= x).
  eapply IHle.
  trivial.
  lia.
  trivial.
  
  rewrite Nat.Odd_div2.
  
  eapply IHle.
  trivial.
  trivial.
Qed.

#[export] Instance expnat_nz : forall k n (p : nz n),
  nz (expnat n k).

intuition.

induction k; intuition; simpl in *.
econstructor.
lia.
econstructor.
edestruct IHk; eauto.
destruct p.
eapply mult_gt_0; intuition.

Qed.
  
Lemma expnat_2_ge_1 : forall n,
  (1 <= expnat 2 n)%nat.

  induction n; intuition; simpl in *.
  lia.
Qed.

Lemma le_expnat_2 : forall n,
  (n <= expnat 2 n)%nat.

  induction n; intuition; simpl in *.
  rewrite Nat.add_0_r.
  assert (S n = 1 + n)%nat.
  lia.
  rewrite H.
  eapply Nat.add_le_mono.
  eapply expnat_2_ge_1.
  trivial.
  
Qed.

Lemma expnat_1 : forall k,
  expnat 1%nat k = 1%nat.

  induction k; intuition; simpl in *.
  rewrite Nat.add_0_r.
  trivial.

Qed.

Theorem expnat_base_le : 
  forall k n1 n2,
    n1 <= n2 ->
    expnat n1 k <=
    expnat n2 k.
  
  induction k; intuition; simpl in *.
  eapply Nat.mul_le_mono; intuition.
Qed.

Theorem expnat_double_le : 
  forall k n,
    n >= 2 ->
    expnat n (S k) >= 2 * expnat n k.

  induction k; intuition; simpl in *.
  lia.
  rewrite Nat.add_0_r.
  rewrite <- Nat.mul_add_distr_l.
  eapply Nat.mul_le_mono.
  trivial.
  rewrite <- Nat.add_0_r at 1.
  rewrite <- Nat.add_assoc.
  eapply IHk.
  trivial.
Qed.

Theorem nat_half_plus : 
  forall x, 
    x > 1 ->
    exists a b,
      a > 0 /\ b <= 1 /\ x = 2 * a + b.
  
  induction x; intuition; simpl in *.
  lia.
  
  destruct (eq_nat_dec x 1); subst.
  exists 1.
  exists 0.
  intuition; lia.
  
  edestruct (IHx).
  lia.
  destruct H0.
  intuition.
  destruct x1.
  rewrite Nat.add_0_r in H3.
  exists x0.
  exists 1.
  subst.
  intuition; lia.
  
  exists (S x0).
  exists 0.
  subst.
  intuition.
  lia.
            
Qed.

Theorem log2_div2 : 
  forall x y,
    S y = Nat.log2 x ->
    Nat.log2 (Nat.div2 x) = y.
  
  intuition.
  specialize (Nat.log2_double); intuition.
  
  destruct (@nat_half_plus x).
  eapply Nat.log2_lt_cancel.
  rewrite Nat.log2_1.
  lia.
  destruct H1.
  intuition.
  subst.
  destruct x1.
  rewrite Nat.add_0_r in *.
  rewrite Nat.div2_double.
  rewrite H0 in H.
  lia.
  lia.
  
  destruct x1.
  
  rewrite Nat.add_comm.
  rewrite Nat.add_1_l, Nat.div2_succ_double.
  
  rewrite Nat.log2_succ_double in H.
  lia.
  lia.
  
  lia.
  
Qed.

Lemma log2_0 : 
  Nat.log2 0 = 0.
  trivial.
Qed.

Theorem expnat_0 : 
  forall k,
    k > 0 ->
    expnat 0 k = 0.
  
  induction k; intuition; simpl in *.
  
Qed.

Theorem expnat_plus : 
  forall k1 k2 n,
    expnat n (k1 + k2) = expnat n k1 * expnat n k2.
  
  induction k1; simpl in *; intuition.
  rewrite IHk1.
  rewrite Nat.mul_assoc.
  trivial.
  
Qed.

Theorem expnat_ge_1 :
  forall k n,
    n > 0 ->
    1 <= expnat n k.
  
  induction k; intuition; simpl in *.
  rewrite <- Nat.mul_1_r at 1.
  eapply Nat.mul_le_mono.
  lia.
  eauto.
Qed.


Theorem expnat_exp_le : 
  forall n2 n4 n,
    (n2 > 0 \/ n > 0) ->
    n2 <= n4 ->
    expnat n n2 <= expnat n n4.
  
  induction n2; destruct n4; simpl in *; intuition; try lia.
  rewrite <- Nat.mul_1_l at 1.
  eapply Nat.mul_le_mono.
  lia.
  eapply expnat_ge_1; trivial.
  
  destruct (eq_nat_dec n 0); subst.
  simpl; intuition.
  eapply Nat.mul_le_mono; intuition.
  eapply IHn2.
  lia.
  lia.
  
Qed.

Lemma mult_lt_compat : 
  forall a b c d,
    a < b ->
    c < d ->
    a * c < b * d.
  
  intuition.
  eapply Nat.le_lt_trans.
  eapply Nat.mul_le_mono.
  assert (a <= b).
  lia.
  eapply H1.
  eapply Nat.le_refl.
  apply Nat.mul_lt_mono_pos_l; lia.
Qed.

Theorem orb_same_eq_if : 
  forall a b c,
    (a = false -> b = c) ->
    orb a b = orb a c.
  
  intuition.
  destruct a; trivial; intuition.
     
Qed.
