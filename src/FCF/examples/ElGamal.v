(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
(* The El Gamal encryption scheme and a proof that it is IND-CPA-secure. *)

Set Implicit Arguments.

(* Import the core FCF definitions and theory. *)
Require Import FCF.
(* We will use a construction that produces a random group element.  This functionality is provided in the RndGrpElem module. *)
Require Import RndGrpElem.
(* Import the security definitions for public key encryption. *)
Require Import Encryption_PK.
(* Import the security definitions for Diffie-Hellman problems.  *)
Require Import DiffieHellman.
(* The proof uses a one-time pad argument provided by the OTP module. *)
Require Import OTP.

(* Arithmetic operators ("*" and "^") should be interpreted as group operations. *)
Local Open Scope group_scope.

Section ElGamal.

  (* Assume a finite cyclic group.   This command brings several names into the environment, including 'order' which describes the order of the group. *)
  Context`{FCG : FiniteCyclicGroup}.

  (* FiniteCyclicGroup is from a generic group theory library.  To use any type in FCF, equality must be decidable for that type.  Assume that equality is decidable for group elements. This fact will be located automatically when needed. *)
  Hypothesis GroupElement_EqDec : EqDec GroupElement.

  (* The ElGamal key generation procedure.  The notation [ .. order) is from the RndNat library, and it produces a uniformly-random natural number in the specified interval.  *)
  Definition ElGamalKeygen :=
    m <-$ [0 .. order);
    ret (m, g^m).

  (* The ElGamal encryption procedure. *)
  Definition ElGamalEncrypt(msg key : GroupElement) := 
    m <-$ [0 .. order);
    ret (g^m, key^m * msg).

  (* The ElGamal decryption procedure. *)
  Definition ElGamalDecrypt(key : nat)(ct : GroupElement * GroupElement) :=
    [c1, c2] <-2 ct;
    s <- c1^key;
    (inverse s) * c2.

  (* We can prove that decryption is correct.  This procedure is deterministic, so this is just a typical Coq proof.  *)
  Theorem ElGamalDecrypt_correct : 
    forall (pubkey msg : GroupElement)(prikey : nat)(ct : GroupElement * GroupElement),
      In (prikey, pubkey) (getSupport ElGamalKeygen) ->
      In ct (getSupport (ElGamalEncrypt msg pubkey)) ->
      ElGamalDecrypt prikey ct = msg.

    unfold ElGamalKeygen, ElGamalEncrypt, ElGamalDecrypt.
    intuition. 
    (* simp_in_support is an automated tactic that breaks down hypotheses that state that some value is in the support of some distribution.  The resulting hypotheses will be more atomic and more directly useful.  *)
    repeat simp_in_support.
    rewrite <- associativity.
    repeat rewrite groupExp_mult.
    rewrite Nat.mul_comm.
    rewrite left_inverse.
    apply left_identity.
  Qed.
    
  (* Assume an adversary composed of two procedures that share state.  We also need to assume that equality is decidable for the type of this state. *)
  Variable A_State : Set.
  Hypothesis A_State_EqDec : EqDec A_State.

  Variable A1 : GroupElement -> Comp (GroupElement * GroupElement * A_State).
  Variable A2 : (GroupElement * GroupElement * A_State) -> Comp bool.

  (* It is necessary to assume that the adversary procedures are "well-formed."  That is, they terminate with probability 1. *)
  Hypothesis wfA1 : forall x, well_formed_comp (A1 x).
  Hypothesis wfA2 : forall x, well_formed_comp (A2 x).  

  (* Build an adversary from A1 and A2 that can win DDH *)
  Definition B(g_xyz : (GroupElement * GroupElement * GroupElement)) : Comp bool :=
    [gx, gy, gz] <-3 g_xyz;
    [p0, p1, s] <-$3 A1(gx);
    b <-$ {0,1};
    pb <- if b then p0 else p1;
      c <- (gy, gz * pb);
      b' <-$ (A2 (c, s));
      ret (b ?= b').

  (* Specialize the DDH games to our group.  Note that definitions can also used modules or classes to make these explicit specializations unnecessary. *)
  Definition DDH0 := (@DDH0 _ _ _ _ _ g order).
  Definition DDH1 := (@DDH1 _ _ _ _ _ g order).
  Definition DDH_Advantage := (@DDH_Advantage _ _ _ _ _ g order).

  (* This is what we want to (eventually) prove. *)
  Theorem ElGamal_IND_CPA_Advantage :
    (IND_CPA_Advantage ElGamalKeygen ElGamalEncrypt A1 A2) ==
    (DDH_Advantage B).

    unfold IND_CPA_Advantage, DDH_Advantage, DiffieHellman.DDH_Advantage.
    (* The goal is an equality on distances.  We will prove the equality of each pair of terms, which implies equality of the distances. *)

  Abort.

  (* We can directly prove the equivalence of the IND_CPA game with DDH0. *)
  Theorem ElGamal_IND_CPA0 :
    Pr[IND_CPA_G ElGamalKeygen ElGamalEncrypt A1 A2] == 
    Pr[DDH0 B].
    
    unfold IND_CPA_G, DDH0, DiffieHellman.DDH0, ElGamalKeygen, ElGamalEncrypt, B.

    (* Inline the first computation in the game on the left hand side. *)
    inline_first.
    (* Remove the first pair of terms, and assign the result of both to a single (new) variable.  *)
    comp_skip.

    (* apply the "dist_inline" tactic to the program on the right at location 1 (where 0 is the first statement).  We have to use %nat here because FCF is in rat_scope by default, and we want this 1 to be interpreted as a nat. *)
    comp_at dist_inline rightc 1%nat.
    (* Swap the first two statement of the program on the right. *)
    comp_swap rightc.
    comp_skip.

    destruct x0.
    destruct p.

    comp_at dist_inline rightc 1%nat.
    comp_swap rightc.
    comp_skip.

    comp_inline leftc.
    comp_skip.

    comp_inline rightc.
    comp_skip.
    rewrite groupExp_mult; intuition auto with *.

    (* Simplify using left identity. *)
    comp_simp.

    (* The goal is an equality on two (obviously equal) rational numbers.  This equality is registered as a setoid in Coq, so it can be proved automatically using the intuition tactic. *)
    intuition auto with *.
  Qed.

  (* The next equality is proved using a short sequence involving two intermediate games.  RndG produces a random group element as described in the RndGrpElem module.  *)
  Definition G1 :=
    gx <-$ RndG;
    gy <-$ RndG;
    [p0, p1, s] <-$3 (A1 gx);
    b <-$ {0, 1};
    gz' <-$ (
    pb <- if b then p0 else p1;
    gz <-$ RndG ; ret (gz * pb));
    b' <-$ (A2 (gy, gz', s));
    ret (b ?= b').

  Definition G2 :=
    gx <-$ RndG;
    gy <-$ RndG;
    [p0, p1, s] <-$3 (A1 gx);
    gz <-$ RndG ;
    b' <-$ (A2 (gy, gz, s));
    b <-$ {0, 1};
    ret (b ?= b').

  Theorem ElGamal_G1_DDH1 :
    Pr [G1] == Pr [DDH1 B].

    unfold G1, DDH1, DiffieHellman.DDH1, B, RndGrpElem.

    inline_first.
    comp_skip.
    inline_first.
    comp_skip.

    comp_at comp_inline rightc 1%nat.
    comp_swap rightc.
    comp_skip.

    destruct x1.
    destruct p.

    comp_at dist_inline leftc 1%nat.
    comp_at dist_inline leftc 1%nat.
    comp_swap leftc.
    comp_skip.
    
    comp_inline rightc.
    comp_skip.
    
    inline_first.
    comp_skip.

    comp_simp.
    intuition auto with *.
    
  Qed.   

  Theorem ElGamal_G1_G2 :
    Pr[G1] == Pr[G2].
    
    unfold G1, G2, B.

    (* We do this step in the program logic.  The following theorem produces a goal in the program logic from a probabilistic goal. *)
    eapply comp_spec_eq_impl_eq.

    (* Many of the comp_* tactics still work in the program logic, and they will apply the equivalent argument.  There are also prog_* tactics that work only in the program logic, and dist_* tactics that work only on probability claims.  *)

    (* We can use Coq tacticals to apply FCF tactics. *)
    do 3 comp_skip.
 
    (* In the program logic, use the prog_at tactical instead of comp_at. *)
    prog_at comp_swap rightc 1%nat.
    comp_swap_r.
    comp_skip.

    eapply comp_spec_symm.
    comp_skip.
    (* Apply a one-time pad argument in the program logic. *)
    eapply group_OTP_r.
    subst.
    eapply comp_spec_consequence.
    (* Equality in the program logic is not a registered setoid, so we have to manually apply reflexivity. *)
    eapply comp_spec_eq_refl.
    intuition.
  Qed.

  Theorem ElGamal_G2_OneHalf :
    Pr [G2] == 1 / 2.
   
    unfold G2.

    (* ignore the first 5 commands *)
    do 3 comp_irr_l.
    comp_simp.
    do 2 comp_irr_l.
    (* compute the probability *)
    dist_compute.
  Qed.
  
  Theorem ElGamal_IND_CPA_Advantage :
    (IND_CPA_Advantage ElGamalKeygen ElGamalEncrypt A1 A2) ==
    (DDH_Advantage B).

    unfold IND_CPA_Advantage, DDH_Advantage, DiffieHellman.DDH_Advantage.
    eapply ratDistance_eqRat_compat.    
    eapply ElGamal_IND_CPA0.
    (* Rational number equality is a setoid, so we can rewrite with it. *)
    rewrite <- ElGamal_G1_DDH1.
    rewrite ElGamal_G1_G2.
    symmetry.
    eapply ElGamal_G2_OneHalf.
  Qed.

End ElGamal.
