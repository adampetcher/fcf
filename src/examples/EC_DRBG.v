
(* An exercise to prove the security of the (academic version of) Dual_EC_DRBG.  Taken from http://eprint.iacr.org/2007/048. *)

Set Implicit Arguments.

Require Import FCF.
Require Import DiffieHellman.
Require Import RndNat.

Local Open Scope list_scope.
Local Open Scope group_scope.

(*
Section DLP.

  Context`{FCG : FiniteCyclicGroup}.
  Hypothesis group_eqd : EqDec GroupElement.

  Variable A : GroupElement -> Comp nat.

  Definition DLP_G :=
    x <-$ RndNat order;
    x' <-$ A (g ^ x);
    ret (eqb x x').

  Definition DLP_Advantage := Pr[DLP_G].

End DLP.
*)

(*
Section PRG.

  Variable D B : Set.
  Variable RndD : Comp D.
  Variable RndB : Comp B.
  Variable f : D -> (D * B).

  Variable A : (D * B) -> Comp bool.

  Definition PRG_G1 :=
    r <-$ RndD;
    g <-$ (A (f r));
    ret g.

  Definition PRG_G2 :=
    r <-$ RndD;
    b <-$ RndB;
    g <-$ (A (r, b));
    ret g.

  Definition PRG_Advantage := | (Pr[PRG_G1]) - (Pr[PRG_G2]) |.
End PRG.
*)

Section Dual_EC_DRBG.
  
  Context`{FCG : FiniteCyclicGroup}.
  Hypothesis eqd_GroupElement : EqDec GroupElement.
  
  Definition P := g.
  Variable x : GroupElement -> nat.
  Variable from_x : nat -> GroupElement.
  
  Definition DRBG(P Q : GroupElement)(t : nat) : (GroupElement * GroupElement ) :=
    let s :=  x (P ^ t) in
        (P ^ s, Q ^ t).

  Variable A : (GroupElement * GroupElement * GroupElement) -> Comp bool.

  Definition DRBG_GA Q :=
    seed <-$ RndNat order;
    [s1, v1] <-2 DRBG P Q seed;
    b <-$ A (Q, s1, v1);
    ret b.

  Definition DRBG_GB Q :=
    x2 <-$ RndNat order;
    x3 <-$ RndNat order;
    b <-$ A (Q, (P^x2), (P^x3));
    ret b.

  Definition DRBG_P (f : GroupElement -> Comp bool) :=
    x <-$ RndNat order;
    Q <- P ^ x;
    f Q.

  Definition G2 Q :=
    seed <-$ RndNat order;
    [s1, v1] <-2 (seed, Q ^ seed);
    b <-$ A (Q, (P ^ s1), v1);
    ret b.

  Definition xLogAdvantage := | Pr[DRBG_P DRBG_GA] - Pr[DRBG_P G2] |.

  Definition DRBG_Advantage := | Pr[DRBG_P DRBG_GA] - Pr[DRBG_P DRBG_GB] |.

  Theorem DRBG_P_DH : | Pr[DRBG_P G2] - Pr[DRBG_P DRBG_GB] | == @DDH_Advantage _ groupOp ident inverse _ g order A.
    
    unfold DDH_Advantage.
    unfold DRBG_P, DRBG_GB, G2, DDH0, DDH1.
    unfold P.
    eapply ratDistance_eqRat_compat.
    comp_skip.
    comp_skip.
    rewrite groupExp_mult.
    reflexivity.

    reflexivity.

  Qed.

  Theorem DRBG_P_secure :  | Pr[DRBG_P DRBG_GA] - Pr[DRBG_P DRBG_GB] | <= xLogAdvantage + @DDH_Advantage _ groupOp ident inverse _ g order A.

    eapply leRat_trans.
    eapply ratTriangleInequality.
    eapply ratAdd_leRat_compat.
    eapply eqRat_impl_leRat.
    eapply eqRat_refl.
    eapply eqRat_impl_leRat.
    eapply DRBG_P_DH.
    
  Qed.

  Section DRBG_S.

    Variable Q : GroupElement.

    Definition DRBG_S (f : GroupElement -> Comp bool) :=
      f Q.

    Theorem DRBG_S_DH : | Pr[DRBG_S G2] - Pr[DRBG_S DRBG_GB] | == @DDH_Advantage _ groupOp ident inverse _ g order A.
      
      unfold DDH_Advantage.
      unfold DRBG_S, DRBG_GB, G2, DDH0, DDH1.
      unfold P.
      eapply ratDistance_eqRat_compat.
      comp_irr_r.
      comp_skip.
      rewrite <- groupExp_mult.
      
    (* Now we are stuck: nothing leads to Q = G^x *)
      
    Abort.

  End DRBG_S.

End Dual_EC_DRBG.


Section Dual_EC_DRBG_V.

  Context`{FCG : FiniteCyclicGroup}.
  Hypothesis eqd_GroupElement : EqDec GroupElement.
  
  Variable x : GroupElement -> nat.
  Variable from_x : nat -> GroupElement.

  Variable Q : GroupElement.
  Variable z : nat.
  Hypothesis Q_eq_g_z : Q = g ^ z.

  Definition B (e: (GroupElement * GroupElement * GroupElement)) := 
    [a, b, c] <-3 e;
    g_seed <- c ^ modNatAddInverse z order;
    ret (eqb b (g ^ (x g_seed))).

  Theorem GA_always_true :
    Pr[(@DRBG_GA _ groupOp ident inverse _ g order x B Q)] == 1.

    unfold DRBG_GA, DRBG, P.
    subst.
    comp_irr_l.

    Not quite right.  We need to assume something about what the x function leaks about the point.
    In ECC, x leaks the x coordinate of the point.  

    comp_simp.
    comp_irr_l.
    subst.
    unfold P.
    rewrite evalDist_ret_1.
    intuition.
    eapply eqb_leibniz.
    f_equal.
    f_equal.
    repeat rewrite groupExp_mult.
    rewrite mult_comm.
    rewrite <- mult_assoc.
    rewrite <- groupExp_mult.

    SearchAbout modNatAddInverse.

    SearchAbout groupExp modNat.
    SearchAbout eqb true.
    SearchAbout evalDist Ret.
    eapply evalDist_ret_1.

  Qed.

  Theorem foo : 
    | Pr[(@DRBG_GA _ groupOp ident inverse _ g order x B Q)] - 
      Pr[(@DRBG_GB _ groupOp ident inverse _ g order B Q)] | == 1.

    unfold DRBG_GA, DRBG_GB, DRBG.
    subst.
    unfold P.

    unfold B.
    comp_simp.

    SearchAbout ratDistance Bind.

    assert (((g ^ z) ^ seed) ^ modNatAddInverse z order = g^seed).
    rewrite <- groupExp_mult.

    SearchAbout modNatAddInverse.

    SearchAbout FiniteCyclicGroup.

    SearchAbout ratDistance eqRat.
    

  Qed.
  

End Dual_EC_DRBG_V.