
Require Import FCF.
Require Import FCF.PRF.
Require Import Permutation.

Set Implicit Arguments.

(* Sorted random functions are useful, because they ensure the function state is eq
when queries happen in different orders. *)

Section SortedRandomFunc.

  Variable A B : Set.
  Hypothesis A_EqDec : EqDec A.
  Hypothesis B_EqDec : EqDec B.
  Variable leA : A -> A -> bool.
  Hypothesis leA_trans : forall a1 a2 a3, leA a1 a2 = true -> leA a2 a3 = true -> leA a1 a3 = true.
  Hypothesis leA_refl : forall a, leA a a = true.
  Hypothesis leA_antisymm : forall a1 a2, leA a1 a2 = true -> leA a2 a1 = true -> a1 = a2.
  Hypothesis leA_total : forall a1 a2, (leA a1 a2) || (leA a2 a1) = true.
  Variable rndB : Comp B.

  Fixpoint insertInOrder (ls : list (A * B))(a : A)(b : B) :=
    match ls with
    | nil => (a, b)::ls
    | (a', b')::ls' => if (leA a a') 
      then ((a, b)::ls) 
      else (a', b')::(insertInOrder ls' a b)
    end.

  Theorem insertInOrder_twice_eq : forall (ls : list (A * B)) a1 b1 a2 b2,
    a1 <> a2 ->
    insertInOrder (insertInOrder ls a1 b1) a2 b2 =
    insertInOrder (insertInOrder ls a2 b2) a1 b1.

    induction ls; intuition idtac; simpl in *.
    case_eq (leA a2 a1); intros.
    case_eq (leA a1 a2); intros.
    exfalso.
    eapply H.
    eapply leA_antisymm; eauto.
    trivial.
    case_eq (leA a1 a2); intros.
    trivial.
    specialize (leA_total a1 a2).
    rewrite H0 in leA_total.
    rewrite H1 in leA_total.
    discriminate.
    
    case_eq (leA a1 a0); intros; 
    case_eq (leA a2 a0); intros.
    simpl.
    case_eq (leA a2 a1); intros;
    case_eq (leA a1 a2); intros.
    exfalso.
    eapply H.
    eapply leA_antisymm; eauto.
    rewrite H0.
    trivial.
    rewrite H1.
    trivial.
    specialize (leA_total a1 a2).
    rewrite H2 in leA_total.
    rewrite H3 in leA_total.
    discriminate.
    simpl.
    rewrite H0.
    case_eq (leA a2 a1); intros.
    erewrite leA_trans in H1; eauto. discriminate.
    rewrite H1.
    trivial.

    simpl.
    rewrite H1.
    rewrite H0.
    case_eq (leA a1 a2); intros.
    erewrite leA_trans in H0; eauto. discriminate.
    trivial.

    simpl.
    rewrite H1.
    rewrite H0.
    f_equal.
    eauto.

  Qed.

  Theorem arrayLookup_insertInOrder_same : 
    forall (ls : list (A * B)) a b,
    arrayLookup _ (insertInOrder ls a b) a = Some b.

    induction ls; intuition idtac; simpl in *.
    rewrite eqb_refl.
    trivial.
    case_eq (leA a a0); intuition idtac.
    simpl.
    rewrite eqb_refl.
    trivial.
    simpl.
    case_eq (eqb a a0); intuition idtac.
    rewrite eqb_leibniz in H0.
    subst.
    rewrite leA_refl in H.
    discriminate.
    eauto.

  Qed.

  Theorem arrayLookup_insertInOrder_ne : 
    forall (ls : list (A * B)) a1 a2 b,
    a1 <> a2 ->
    arrayLookup _ (insertInOrder ls a1 b) a2 = arrayLookup _ ls a2.

    induction ls; intuition idtac; simpl in *.
    case_eq (eqb a2 a1); intuition idtac.
    rewrite eqb_leibniz in H0.
    subst.
    intuition idtac.
    case_eq (leA a1 a0); intuition idtac.
    simpl.
    case_eq (eqb a2 a1); intuition idtac.
    rewrite eqb_leibniz in H1.
    subst.
    intuition idtac.
    simpl.
    case_eq (eqb a2 a0); intuition idtac.
    eauto.
  Qed.

  Theorem insertInOrder_NoDup :
    forall (s : list (A * B)) a b,
    NoDup (fst (split s)) ->
    arrayLookup _ s a = None ->
    NoDup (fst (split (insertInOrder s a b))).

    induction s; intuition idtac; simpl in *.
    econstructor.
    intuition idtac.
    econstructor.

    case_eq (eqb a a0); intros.
    rewrite H1 in H0.
    discriminate.
    rewrite H1 in H0.
    remember (split s) as z. destruct z.
    simpl in *.
    case_eq (leA a a0); intros.
    simpl.
    remember (split s) as z. destruct z.
    simpl.
    inversion H; clear H; subst.
    econstructor.
    simpl; intuition idtac.
    subst.
    rewrite eqb_refl in *.
    discriminate.
    eapply arrayLookup_None_not_In in H0.
    intuition idtac.
    rewrite <- Heqz0.
    intuition idtac.
    econstructor; intuition idtac.
    pairInv.
    intuition idtac.
    pairInv.
    intuition idtac.

    simpl.
    remember (split (insertInOrder s a b0)) as z. destruct z.
    simpl.
    inversion H; clear H; subst.
    econstructor. 
    assert (arrayLookup _ (insertInOrder s a b0) a0 = None).
    rewrite arrayLookup_insertInOrder_ne.
    eapply notInArrayLookupNone.
    rewrite <- Heqz.
    intuition idtac.
    intuition idtac; subst.
    rewrite eqb_refl in *. discriminate.
    intuition idtac.
    eapply arrayLookup_None_not_In in H.
    intuition idtac.
    rewrite <- Heqz0.
    trivial.
    specialize (IHs a b0).
    intuition idtac.
    rewrite <- Heqz0 in H3.
    trivial.

  Qed.

  Definition sortedRandomFunc (ls : list (A * B))(a : A) :=
    match (arrayLookup _ ls a) with
    | None => b <-$ rndB; ret (b, (insertInOrder ls a b))
    | Some b => ret (b, ls)
  end.

  Ltac matchOpt :=
    match goal with
    | [|- context[match ?a with | Some _ => _ | None => _ end] ] =>
      case_eq a; intros
    end.

  Theorem sortedRandomFunc_swap : forall s d1 d2,
    comp_spec eq
    ([x2, s2] <-$2 sortedRandomFunc s d1; [x3, s3] <-$2 sortedRandomFunc s2 d2; ret ((x2, x3), s3))
    ([x3, s2] <-$2 sortedRandomFunc s d2; [x2, s3] <-$2 sortedRandomFunc s2 d1; ret ((x2, x3), s3)).

    intuition idtac.
    assert B.
    eapply comp_base_exists; eauto.
    unfold sortedRandomFunc.
    
    case_eq (eqb d1 d2); intros.
    rewrite eqb_leibniz in H0.
    subst.
    matchOpt.
    fcf_simp.
    rewrite H0.
    fcf_simp.
    eapply comp_spec_eq_refl.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    rewrite arrayLookup_insertInOrder_same.
    fcf_simp.
    eapply comp_spec_eq_refl.

    matchOpt.
    fcf_simp.
    matchOpt.
    fcf_simp.
    rewrite H1.
    fcf_simp.
    eapply comp_spec_ret; intuition idtac.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    rewrite arrayLookup_insertInOrder_ne.
    rewrite H1.
    fcf_simp.
    apply comp_spec_eq_refl.
    intuition idtac; subst.
    rewrite eqb_refl in *.
    discriminate.
    matchOpt.
    fcf_simp.
    rewrite H1.
    fcf_inline_first.
    fcf_skip.
    rewrite arrayLookup_insertInOrder_ne.
    rewrite H2.
    fcf_simp.
    eapply comp_spec_eq_refl.
    intuition idtac; subst.
    rewrite eqb_refl in *. discriminate.
    
    fcf_inline_first.
    eapply (@comp_spec_eq_trans _ _ _ 
      (a <-$ rndB; b1 <-$ rndB;
   z <-$ ret (a, insertInOrder s d1 a);
   [x2, s2]<-2 z;
   z0 <-$ (
       ret (b1, insertInOrder s2 d2 b1)); 
      [x3, s3]<-2 z0; ret (x2, x3, s3))
    ).
    fcf_skip.
    rewrite arrayLookup_insertInOrder_ne.
    rewrite H2.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    eapply comp_spec_eq_refl.
    intuition idtac; subst.
    rewrite eqb_refl in *. discriminate.
    fcf_swap leftc.
    fcf_skip.
    fcf_simp.
    rewrite arrayLookup_insertInOrder_ne.
    rewrite H1.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    eapply comp_spec_ret; intuition idtac.
    f_equal.
    eapply insertInOrder_twice_eq.
    intuition idtac; subst.
    rewrite eqb_refl in *; discriminate.
    intuition idtac; subst.
    rewrite eqb_refl in *; discriminate.

  Qed.

  Theorem insertInOrder_perm : forall s a b,
    Permutation ((a, b)::s) (insertInOrder s a b).

    induction s; intuition idtac; simpl in *.
    eapply Permutation_refl.
    case_eq (leA a a0); intros.
    eapply Permutation_refl.
    eapply Permutation_trans.
    2:{
    econstructor.
    eapply IHs.
    }
    econstructor.

  Qed.

  Fixpoint sortDom (ls : list (A * B)) :=
    match ls with
    | nil => nil
    | (d, r) :: ls' => insertInOrder (sortDom ls') d r
    end.

  Theorem sortDom_perm : forall ls,
    Permutation ls (sortDom ls).

    induction ls; intuition idtac; simpl in *.
    econstructor.
    eapply Permutation_trans.
    econstructor.
    eauto.
    eapply insertInOrder_perm.

  Qed.

  Theorem arrayLookup_sortDom_eq : forall (ls : list (A * B)) a,
    arrayLookup _ ls a = arrayLookup _ (sortDom ls) a.

    induction ls; intuition idtac; simpl in *.
    case_eq (eqb a a0); intros.
    rewrite eqb_leibniz in H.
    subst.
    rewrite arrayLookup_insertInOrder_same.
    trivial.
    rewrite arrayLookup_insertInOrder_ne.
    eauto.
    intuition idtac; subst.
    rewrite eqb_refl in *. discriminate.

  Qed.

  Theorem sortedRandomFunc_sorted_equiv : forall s a,
    comp_spec (fun s1 s2 => fst s1 = fst s2 /\ (snd s2) = sortDom (snd s1))
    (@randomFunc A B rndB _ s a) (sortedRandomFunc (sortDom s) a).

    intuition idtac.
    unfold randomFunc, sortedRandomFunc.
    rewrite <- arrayLookup_sortDom_eq.
    case_eq (arrayLookup A_EqDec s a); intuition idtac.
    eapply comp_spec_ret; intuition idtac.
    fcf_skip.
    eapply comp_base_exists; eauto.
    eapply comp_base_exists; eauto.
    eapply comp_spec_ret; intuition idtac.

  Qed.

End SortedRandomFunc.

Theorem ExpROM_swap_spec_h : forall 
  (D1 R1 : Set)
  (A1 : Set)
  (c1 : OracleComp D1 R1 A1) 
  (D2 R2 : Set)
  (A2 : Set)
  (c2 : OracleComp D2 R2 A2) 
  (eqdr1 : EqDec R1)(eqdr2 : EqDec R2)
  (eqda1 : EqDec A1)(eqda2 : EqDec A2)
  (S : Set)(eqds : EqDec S)
  (o1 : S -> D1 -> Comp (R1 * S))
  (o2 : S -> D2 -> Comp (R2 * S))
  s,
  (forall s d1, 
    comp_spec eq
    ([x2, s2] <-$2 o1 s d1; [x3, s3] <-$2 c2 _ _ o2 s2; ret ((x2, x3), s3))
    ([x3, s2] <-$2 c2 _ _  o2 s; [x2, s3] <-$2 o1 s2 d1; ret ((x2, x3), s3))
  ) ->
  comp_spec eq 
  ([x2, s2] <-$2 c1 _ _ o1 s; [x3, s3] <-$2 c2 _ _ o2 s2; ret ((x2, x3), s3))
  ([x3, s2] <-$2 c2 _ _ o2 s; [x2, s3] <-$2 c1 _ _ o1 s2; ret ((x2, x3), s3)).

  induction c1; intuition idtac; simpl in *.

  (* query case *)
  specialize (@H s a).
  despec.
  intuition idtac.
  exists x.
  intuition idtac.

  eapply eqRat_trans.
  2:{
  eapply eqRat_trans.
  eapply H0. 
  unfold marginal_l.
  fcf_skip.
  eapply evalDist_ret_eq.
  simpl.
  case_eq (eqbPair (pair_EqDec eqda1 eqda2) eqds
  (fst x0) (a1, b0, b)); intros.
  case_eq (eqbPair (pair_EqDec eqdr1 eqda2) eqds
  (fst x0) (a1, b0, b));
  intros.
  eauto.
  apply eqbPair_prop in H3.
  destruct x0; simpl in *; subst.
  rewrite eqbPair_refl in H4.
  discriminate.
  case_eq (eqbPair (pair_EqDec eqdr1 eqda2) eqds
  (fst x0) (a1, b0, b));
  intros.
  apply eqbPair_prop in H4.
  destruct x0; simpl in *; subst.
  rewrite eqbPair_refl in H3.
  discriminate.
  trivial.
  }
  fcf_skip.
  fcf_simp.
  fcf_skip.
  fcf_simp.
  fcf_compute.

  eapply eqRat_trans.
  2:{
  eapply eqRat_trans.
  eapply H. 
  unfold marginal_r.
  fcf_skip.
  eapply evalDist_ret_eq.
  simpl.
  case_eq (eqbPair (pair_EqDec eqda1 eqda2) eqds
  (snd x0) (a1, b0, b)); intros.
  case_eq (eqbPair (pair_EqDec eqdr1 eqda2) eqds
  (snd x0) (a1, b0, b));
  intros.
  eauto.
  apply eqbPair_prop in H3.
  destruct x0; simpl in *; subst.
  rewrite eqbPair_refl in H4.
  discriminate.
  case_eq (eqbPair (pair_EqDec eqdr1 eqda2) eqds
  (snd x0) (a1, b0, b));
  intros.
  apply eqbPair_prop in H4.
  destruct x0; simpl in *; subst.
  rewrite eqbPair_refl in H3.
  discriminate.
  trivial.
  }
  fcf_skip.
  fcf_simp.
  fcf_skip.
  fcf_simp.
  fcf_compute.

  (* run case *)
  assert (A -> B * S) as bs.
  intros.
  eapply oc_base_exists; eauto.
  intuition idtac.
  assert (B' * S0).
  eapply comp_base_exists; eauto.
  intuition idtac.

  assert C as c.
  eapply oc_base_exists; eauto.
  intuition idtac.

  assert (D2 -> R2) as r2.
  intuition idtac.
  assert (R2 * S0).
  eapply comp_base_exists; eauto.
  intuition idtac.

  assert A2 as a2.
  eapply oc_base_exists; eauto.

  fcf_inline_first.
  assert (EqDec C).
  eapply EqDec_pair_l; eauto.

  eapply (@comp_spec_eq_trans_l _ _ _ _ _
    (y <-$ (a <-$
   c1 (S * S0)%type (pair_EqDec e eqds)
     (fun (x : S * S0) (y : A) =>
      p <-$ (o (fst x) y) S0 eqds o1 (snd x);
      ret (fst (fst p), (snd (fst p), snd p))) 
     (s, s0);
   [x2, s3]<-2 a;
   z0 <-$ c2 (S * S0)%type _ 
    (fun p d => r <-$ o2 (snd p) d; ret (fst r, (fst p, snd r))) s3; 
  [x3, s4]<-2 z0; ret (x2, x3, s4));
  ret (((fst (fst y), fst (snd y)), (snd (fst y))), (snd (snd y))))
  ).
  fcf_inline_first.
  fcf_skip.

  fcf_inline_first.
  fcf_skip.
  simpl.
  eapply (@fcf_oracle_eq _ _ (fun p1 p2 => p1 = (snd p2) /\ fst p2 = a));
  intuition idtac.
  subst.
  eapply comp_spec_eq_trans_l.
  eapply comp_spec_symm.
  eapply comp_spec_consequence.
  eapply comp_spec_right_ident.
  intros; subst; trivial.
  fcf_skip.
  simpl.
  eapply comp_spec_ret; intuition idtac.
  simpl.
  fcf_simp.
  simpl in *; intuition idtac; subst.
  eapply comp_spec_ret; intuition idtac.
  
  specialize (@IHc1 _ _ _ c2 _ _ _ _ (S * S0)%type _ 
    (fun (x : S * S0) (y : A) =>
      p <-$ (o (fst x) y) S0 eqds o1 (snd x);
      ret (fst (fst p), (snd (fst p), snd p)))
    (fun (p : S * S0) (d : D2) =>
      r <-$ o2 (snd p) d; ret (fst r, (fst p, snd r)))).
  eapply (@ comp_spec_eq_trans_r _ _ _ _ _ 
      (y <-$ (z <-$
          c2 _ _ 
            (fun (p : S * S0) (d : D2) =>
             r <-$ o2 (snd p) d; ret (fst r, (fst p, snd r))) (s, s0);
          [x3, s3]<-2 z;
          z0 <-$
          c1 _ _
            (fun (x : S * S0) (y : A) =>
             p <-$ (o (fst x) y) S0 eqds o1 (snd x);
             ret (fst (fst p), (snd (fst p), snd p))) s3;
          [x2, s4]<-2 z0; ret (x2, x3, s4));
      ret (((fst (fst y), fst (snd y)), (snd (fst y))), (snd (snd y))))
  ).
  eapply comp_spec_seq_eq.
  intuition idtac.
  intuition idtac. 
  eapply IHc1.
  intuition idtac.
  simpl in *. subst.
  eapply (@ comp_spec_eq_trans_l _ _ _ _ _ 
    (y <-$(z <-$ (o a d1) S0 eqds o1 b;
     [x2, s3]<-2 z;
     z0 <-$ c2 _ _ o2 s3;
     [x3, s4]<-2 z0; ret (x2, x3, s4));
      ret ((fst (fst (fst y)), (snd (fst y))), (snd (fst (fst y)), (snd y)))
    )
  ).
  fcf_inline_first.
  fcf_skip.
  simpl.
  fcf_inline_first.
  fcf_skip.
  eapply (@fcf_oracle_eq _ _ (fun p1 p2 => (snd p1) = p2 /\ fst p1 = b2)); intuition idtac.
  subst.
  eapply comp_spec_eq_trans_r.
  2:{
  eapply comp_spec_right_ident.
  }
  fcf_skip.
  eapply comp_spec_ret; intuition idtac.
  fcf_simp.
  simpl in *; intuition idtac.
  subst.  
  eapply comp_spec_ret; intuition idtac.

  eapply (@ comp_spec_eq_trans_r _ _ _ _ _ 
    (y <-$
      (z <-$ c2 _ _ o2 b;
      [x2, s3] <-2 z;
      z0 <-$ (o a d1) _ _ o1 s3;
      [x3, s4] <-2 z0; ret (x3, x2, s4));
      ret ((fst (fst (fst y)), (snd (fst y))), (snd (fst (fst y)), (snd y)))
    )
  ).
  eapply comp_spec_seq.
  intuition idtac.
  intuition idtac.
  eapply H;
  eauto.
  intuition idtac.
  subst.
  eapply comp_spec_ret; intuition idtac.

  fcf_inline_first.
  fcf_skip.
  eapply (@fcf_oracle_eq _ _ (fun p1 p2 => p1 = (snd p2) /\ fst p2 = a)); intuition idtac.
  subst.
  eapply comp_spec_eq_trans_l.
  eapply comp_spec_symm.
  eapply comp_spec_consequence.
  eapply comp_spec_right_ident.
  intros; subst; trivial.
  fcf_skip.
  eapply comp_spec_ret; intuition idtac.

  simpl in *; intuition idtac; subst.
  fcf_inline_first.
  fcf_simp.
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  eapply comp_spec_eq_refl.

  intros.
  eapply comp_spec_eq_refl.

  fcf_inline_first.
  fcf_skip.
  eapply (@fcf_oracle_eq _ _ (fun p1 p2 => snd p1 = p2 /\ fst p1 = s));
  intuition idtac.
  subst.
  simpl.
  eapply comp_spec_eq_trans_r.
  2:{
  eapply comp_spec_right_ident.
  }
  fcf_skip.
  eapply comp_spec_ret; simpl in *; intuition idtac.
  simpl in *; intuition idtac; subst.
  fcf_simp.
  fcf_inline_first.
  fcf_skip.
  simpl.
  fcf_simp.
  eapply comp_spec_ret; intuition idtac.

  (* ret case *)
  assert C as c_ex.
  eapply comp_base_exists; eauto.

  assert A2 as a2_ex.
  eapply oc_base_exists; eauto.
  intuition idtac.
  assert (R2 * S).
  eapply comp_base_exists; eauto.
  intuition idtac.

  fcf_inline_first.
  eapply (@comp_spec_eq_trans_l _ _ _ _ _
    (a <-$ c;
      z0 <-$ c2 S eqds o2 s; [x3, s4]<-2 z0; ret (a, x3, s4))
  ).
  fcf_skip.
  fcf_swap leftc.
  fcf_skip.
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  eapply comp_spec_ret; intuition idtac.

  (* bind case *)
  assert C as c_ex.
  eapply oc_base_exists; eauto.
  intuition idtac.
  assert (B * S).
  eapply comp_base_exists; eauto.
  intuition idtac.

  assert C' as c'_ex.
  eapply oc_base_exists.
  eapply o.
  intuition idtac.
  intuition idtac.
  assert (B * S).
  eapply comp_base_exists; eauto.
  intuition idtac.

  assert A2 as a2_ex.
  eapply oc_base_exists; eauto.
  intuition idtac.
  assert (R2 * S).
  eapply comp_base_exists; eauto.
  intuition idtac.

  fcf_inline_first. 
  eapply (@comp_spec_eq_trans_l _ _ _ _ _ 
    (a <-$ c1 S eqds o1 s;
     [z, s']<-2 a;
     z <-$ ((o z) S eqds o1 s');
     [x2, s3]<-2 z;
     z0 <-$ c2 S eqds o2 s3;
     [x3, s4]<-2 z0; ret (x2, x3, s4))
  ).
  fcf_skip.

  eapply (@comp_spec_eq_trans _ _ _
    (a <-$ c1 S eqds o1 s;
     [z, s']<-2 a;
     z1 <-$ c2 S eqds o2 s';
     [x2, s3]<-2 z1;
     z0 <-$ ((o z) S eqds o1 s3);
     [x3, s4]<-2 z0; ret (x3, x2, s4))
  ).
  fcf_skip.
  eapply H; intuition idtac.

  eapply (@comp_spec_eq_trans_l _ _ _ _ _ 
    (y <-$ (a <-$ c1 S eqds o1 s;
     [z, s']<-2 a;
     z1 <-$ c2 S eqds o2 s';
     [x2, s3]<-2 z1;
      ret (z, x2, s3)
    );
    z0 <-$ (o (fst (fst y))) S eqds o1 (snd y);
     [x3, s4]<-2 z0; ret (x3, (snd (fst y)), s4))
  ).
  fcf_inline_first.
  fcf_skip.
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  simpl. 
  fcf_inline_first.
  eapply comp_spec_eq_refl.

  eapply (@comp_spec_eq_trans_r _ _ _ _ _
    (y <-$ 
     (a <-$ c2 S eqds o2 s;
     [z, s']<-2 a;
     z1 <-$ c1 S eqds o1 s';
     [x2, s3]<-2 z1;
      ret (x2, z, s3)
    );
    z0 <-$ (o (fst (fst y))) S eqds o1 (snd y);
     [x3, s4]<-2 z0; ret (x3, (snd (fst y)), s4))
  ).
  eapply comp_spec_seq.
  intuition idtac.
  intuition idtac.
  eapply IHc1; intuition idtac.
  intuition idtac.
  subst.
  fcf_skip.

  fcf_inline_first.
  fcf_skip.
  fcf_inline_first.
  fcf_skip.
  simpl.
  fcf_skip.

  Unshelve.

  eapply pair_EqDec; intuition idtac.
  eapply oc_EqDec.
  eauto.
  intuition idtac.
  assert (B * S).
  eapply comp_base_exists; eauto.
  intuition idtac.
  intuition idtac.
  
  eapply pair_EqDec; intuition idtac.
  eapply oc_EqDec.
  eauto.
  intuition idtac.
  assert (B * S).
  eapply comp_base_exists; eauto.
  intuition idtac.
  intuition idtac.

  eapply pair_EqDec; intuition idtac.
  eapply oc_EqDec.
  eauto.
  intuition idtac.
  assert (B * S).
  eapply comp_base_exists; eauto.
  intuition idtac.
  intuition idtac.

  eapply oc_EqDec.
  eauto.
  intuition idtac.
  assert (B * S).
  eapply comp_base_exists; eauto.
  intuition idtac.
  intuition idtac.

  eapply pair_EqDec; intuition idtac.
  eapply oc_EqDec.
  eauto.
  intuition idtac.
  assert (B * S).
  eapply comp_base_exists; eauto.
  intuition idtac.
  intuition idtac.

Qed.

Theorem ExpROM_query_swap_spec : forall 
  (D2 R2 : Set)
  (A2 : Set)
  (c2 : OracleComp D2 R2 A2) 
  (D1 R1 : Set)
  (A1 : Set)
  (eqdr1 : EqDec R1)(eqdr2 : EqDec R2)
  (eqda1 : EqDec A1)(eqda2 : EqDec A2)
  (S : Set)(eqds : EqDec S)
  (o1 : S -> D1 -> Comp (R1 * S))
  (o2 : S -> D2 -> Comp (R2 * S))
  s d,
  (forall s d1 d2, 
    comp_spec eq
    ([x2, s2] <-$2 o1 s d1; [x3, s3] <-$2 o2 s2 d2; ret ((x2, x3), s3))
    ([x3, s2] <-$2 o2 s d2; [x2, s3] <-$2 o1 s2 d1; ret ((x2, x3), s3))
  ) ->
  comp_spec eq 
  ([x2, s2] <-$2 o1 s d; [x3, s3] <-$2 c2 _ _ o2 s2; ret ((x2, x3), s3))
  ([x3, s2] <-$2 c2 _ _ o2 s; [x2, s3] <-$2 o1 s2 d; ret ((x2, x3), s3)).

  induction c2; intuition idtac; simpl in *.

  (* query case *)
  specialize (@H s d a).
  despec.
  intuition idtac.
  exists x.
  intuition idtac.

  eapply eqRat_trans.
  2:{
  eapply eqRat_trans.
  eapply H0. 
  unfold marginal_l.
  fcf_skip.
  eapply evalDist_ret_eq.
  simpl.
  case_eq (eqbPair (pair_EqDec eqdr1 eqda2) eqds
  (fst x0) (a1, b0, b)); intros.
  case_eq (eqbPair (pair_EqDec eqdr1 eqdr2) eqds
  (fst x0) (a1, b0, b));
  intros.
  eauto.
  apply eqbPair_prop in H3.
  destruct x0; simpl in *; subst.
  rewrite eqbPair_refl in H4.
  discriminate.
  case_eq (eqbPair (pair_EqDec eqdr1 eqdr2) eqds
  (fst x0) (a1, b0, b));
  intros.
  apply eqbPair_prop in H4.
  destruct x0; simpl in *; subst.
  rewrite eqbPair_refl in H3.
  discriminate.
  trivial.
  }
  fcf_skip.
  fcf_simp.
  fcf_skip.
  fcf_simp.
  fcf_compute.

  eapply eqRat_trans.
  2:{
  eapply eqRat_trans.
  eapply H. 
  unfold marginal_r.
  fcf_skip.
  eapply evalDist_ret_eq.
  simpl.
  case_eq (eqbPair (pair_EqDec eqdr1 eqda2) eqds
  (snd x0) (a1, b0, b)); intros.
  case_eq (eqbPair (pair_EqDec eqdr1 eqdr2) eqds
  (snd x0) (a1, b0, b));
  intros.
  eauto.
  apply eqbPair_prop in H3.
  destruct x0; simpl in *; subst.
  rewrite eqbPair_refl in H4.
  discriminate.
  case_eq (eqbPair (pair_EqDec eqdr1 eqdr2) eqds
  (snd x0) (a1, b0, b));
  intros.
  apply eqbPair_prop in H4.
  destruct x0; simpl in *; subst.
  rewrite eqbPair_refl in H3.
  discriminate.
  trivial.
  }
  fcf_skip.
  fcf_simp.
  fcf_skip.
  fcf_simp.
  fcf_compute.

  (* run case *)

  assert R1 as r1_ex.
  assert (R1 * S0).
  eapply comp_base_exists.
  eauto.
  intuition idtac.

  assert (A' -> B') as b'_ex.
  intros.
  assert (B' * S0).
  eapply comp_base_exists; eauto.
  intuition idtac.

  assert (A -> B) as b_ex.
  intros.
  assert (B * S).
  eapply oc_base_exists.
  eapply o.
  trivial.
  trivial.
  trivial.
  intuition idtac.
  
  assert C as c_ex.
  eapply oc_base_exists.
  eauto.
  intuition idtac.

  fcf_inline_first.
  assert (EqDec C).
  eapply EqDec_pair_l; eauto.

  eapply (@comp_spec_eq_trans_l _ _ _ _ _
    (y <-$ (z <-$ (fun p d => r <-$ o1 (snd p) d; ret (fst r, (fst p, snd r))) (s, s0) d;
     [x2, s2]<-2 z;
      z0 <-$
        c2 (S * S0)%type (pair_EqDec e eqds)
          (fun (x : S * S0) (y : A) =>
           p <-$
           (o (fst x) y) S0 eqds o2 (snd x);
           ret (fst (fst p),
               (snd (fst p), snd p))) 
          s2;
      [x3, s3]<-2 z0;
      ret (x2, x3, s3));
     ret ((fst (fst y)), (snd (fst y), fst (snd y)), snd (snd y)))
  ).
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  eapply comp_spec_ret; intuition idtac.
  
  specialize (@IHc2 _ _ _ _ _ _ _ (S * S0)%type _ 
    (fun p d => r <-$ o1 (snd p) d; ret (fst r, (fst p, snd r)))
    (fun (x : S * S0) (y : A) =>
       p <-$
       (o (fst x) y) S0 eqds o2 (snd x);
       ret (fst (fst p),
           (snd (fst p), snd p)))
  ).
  eapply (@comp_spec_eq_trans_r _ _ _ _ _
    (y <-$
   (z <-$
          c2 (S * S0)%type
            (pair_EqDec e eqds)
            (fun (x : S * S0) (y : A) =>
             p <-$
             (o (fst x) y) S0 eqds o2
               (snd x);
             ret (fst (fst p),
                 (snd (fst p), snd p))) (s, s0);
          [x3, s2]<-2 z;
          z0 <-$
          (fun (p : S * S0) (d0 : D1) =>
           r <-$ o1 (snd p) d0;
           ret (fst r, (fst p, snd r))) s2 d;
          [x2, s3]<-2 z0; ret (x2, x3, s3));
   ret (fst (fst y),
       (snd (fst y), fst (snd y)),
       snd (snd y)))
  ).
  eapply comp_spec_seq.
  intuition idtac.
  intuition idtac.
  eapply IHc2.
  
  intuition idtac.
  
  simpl.
  eapply (@comp_spec_eq_trans_l _ _ _ _ _
      ([a, b, c] <-$3 (r <-$ o1 b d1; 
      [x2, s2] <-2 r;
      z0 <-$ (o a d2) S0 eqds o2 s2;
      [x3, s3]<-2 z0; 
      ret (x2, x3, s3));
      ret (a, (fst b), (snd b, c)))
  ).
  fcf_inline_first.
  fcf_skip.
  fcf_inline_first.
  simpl.
  fcf_skip.
  fcf_simp.
  eapply comp_spec_ret; intuition idtac.

  eapply (@comp_spec_eq_trans_r _ _ _ _ _
    ([a, b, c] <-$3 
      (z <-$ (o a d2) S0 eqds o2 b;
       [x3, s2]<-2 z;
       z0 <-$ o1 s2 d1;
       [x2, s3]<-2 z0; ret (x2, x3, s3));
    ret (a, (fst b), (snd b, c)))
  ).
  eapply comp_spec_seq_eq.
  intuition idtac.
  intuition idtac.
  eapply H; intuition idtac.
  eauto.
  intuition idtac.
  eapply comp_spec_eq_refl.
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  simpl.
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  apply comp_spec_ret; intuition idtac.

  intuition idtac.
  subst. simpl in *.  
  eapply comp_spec_ret; intuition idtac.

  fcf_inline_first.
  fcf_skip.
  fcf_inline_first.
  fcf_simp.
  fcf_skip.
  simpl.
  eapply comp_spec_ret; intuition idtac.

  (* ret case *)
  assert R1 as r1_ex.
  assert (R1 * S).
  eapply comp_base_exists; eauto.
  intuition idtac.

  assert C as c_ex.
  apply comp_base_exists; eauto.

  fcf_inline_first.
  eapply comp_spec_eq_symm.
  eapply (@comp_spec_eq_trans _ _ _ 
    (a <-$ c;
     z0 <-$ o1 s d;
     [x2, s3]<-2 z0; ret (x2, a, s3))
  ).
  fcf_skip.
  fcf_swap leftc.
  fcf_skip.
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  eapply comp_spec_ret; intuition idtac.

  (* bind case *)
  assert R1 as r1_ex.
  assert (R1 * S).
  eapply comp_base_exists; eauto.
  intuition idtac.

  assert (A -> B).
  intros.
  assert (B * S).
  eapply comp_base_exists; eauto.
  intuition idtac.

  assert C as c_ex.
  eapply oc_base_exists; eauto.

  assert C' as c'_ex.
  eapply oc_base_exists.
  eapply o. 
  trivial.
  intuition idtac.

  fcf_inline_first. 
  eapply (@comp_spec_eq_trans_l _ _ _ _ _ 
    ([a, b, c] <-$3 (z <-$ o1 s d;
      [x2, s2]<-2 z;
      z0 <-$ c2 S eqds o2 s2;
      [z1, s']<-2 z0; 
      ret (x2, z1, s'));
     z1 <-$
     ((o b) S eqds o2 c);
     [x3, s3]<-2 z1; ret (a, x3, s3))
  ).
  fcf_inline_first.
  fcf_skip.
  fcf_inline_first.
  fcf_skip.
  fcf_simp.
  eapply comp_spec_eq_refl.

  eapply (@comp_spec_eq_trans _ _ _ 
    ([a, b, c] <-$3 
      (z <-$ c2 S eqds o2 s;
          [x3, s2]<-2 z;
          z0 <-$ o1 s2 d;
          [x2, s3]<-2 z0; ret (x2, x3, s3));
     z1 <-$
     ((o b) S eqds o2 c);
     [x3, s3]<-2 z1; ret (a, x3, s3))
  ).
  eapply comp_spec_seq_eq.
  intuition idtac.
  intuition idtac.
  eapply IHc2; intuition idtac.
  eauto.
  intuition idtac.
  eapply comp_spec_eq_refl.
  fcf_inline_first.
  fcf_skip.
  eapply comp_spec_eq_trans.
  2:{
  eapply H; intuition idtac.
  eauto.
  }
  fcf_inline_first.
  fcf_skip.
  
  Unshelve.

  eapply pair_EqDec; intuition idtac.
  eapply oc_EqDec.
  eauto.
  intuition idtac.
  intuition idtac.

  eapply oc_EqDec.
  eauto.
  intuition idtac.
  intuition idtac.

  eapply pair_EqDec; intuition idtac.
  eapply oc_EqDec.
  eauto.
  intuition idtac.
  intuition idtac.

Qed.

Theorem ExpROM_swap_spec : forall 
  (D1 R1 : Set)
  (A1 : Set)
  (c1 : OracleComp D1 R1 A1) 
  (D2 R2 : Set)
  (A2 : Set)
  (c2 : OracleComp D2 R2 A2) 
  (eqdr1 : EqDec R1)(eqdr2 : EqDec R2)
  (eqda1 : EqDec A1)(eqda2 : EqDec A2)
  (S : Set)(eqds : EqDec S)
  (o1 : S -> D1 -> Comp (R1 * S))
  (o2 : S -> D2 -> Comp (R2 * S))
  s,
  (forall s d1 d2, 
    comp_spec eq
    ([x2, s2] <-$2 o1 s d1; [x3, s3] <-$2 o2 s2 d2; ret ((x2, x3), s3))
    ([x3, s2] <-$2 o2 s d2; [x2, s3] <-$2 o1 s2 d1; ret ((x2, x3), s3))
  ) ->
  comp_spec eq 
  ([x2, s2] <-$2 c1 _ _ o1 s; [x3, s3] <-$2 c2 _ _ o2 s2; ret ((x2, x3), s3))
  ([x3, s2] <-$2 c2 _ _ o2 s; [x2, s3] <-$2 c1 _ _ o1 s2; ret ((x2, x3), s3)).

  intuition idtac.
  eapply ExpROM_swap_spec_h.
  intuition idtac.
  intuition idtac.
  eapply ExpROM_query_swap_spec; intuition idtac.
  
  eauto.

Qed.

(* Experiments in the random oracle model and related theory. *)
Section ExperimentROM.

  Variable DomainRO RangeRO : Set.
  Hypothesis DomainRO_EqDec : EqDec DomainRO.
  Hypothesis RangeRO_EqDec : EqDec RangeRO.
  Variable rndRange : Comp RangeRO.

  Section WithProcs.
    Variable T : Set.
    Hypothesis T_EqDec : EqDec T.
    Variable A : OracleComp DomainRO RangeRO T.
    (* The experiment takes a function that calculates the result from the RO state *)
    Variable X : Set.
    Hypothesis X_EqDec : EqDec X.
    Variable f : T -> list (DomainRO * RangeRO) -> X.

    Definition ExpROM_gen_s s := 
      [t, s] <-$2 A _ _ (@randomFunc DomainRO RangeRO rndRange _) s;
      ret f t s.

    Definition ExpROM_gen := ExpROM_gen_s nil.

    Definition ExpROM := 
      [t, _] <-$2 A _ _ (@randomFunc DomainRO RangeRO rndRange _) nil;
      ret t.
  End WithProcs.

  Theorem ExpROM_gen_seq_eq : forall (A B C : Set) 
    (eqdb : EqDec B)(eqdc : EqDec C)
    (c1a c1b : OracleComp DomainRO RangeRO A) 
    (c2a c2b : A -> OracleComp DomainRO RangeRO B) 
    (f : B -> (list (DomainRO*RangeRO)) -> C)
    v s,
    (forall x, 
      evalDist (c1a _ _ (randomFunc rndRange DomainRO_EqDec) s) x ==
      evalDist (c1b _ _ (randomFunc rndRange DomainRO_EqDec) s) x) ->
    (forall x1 s v,
      evalDist (z <-$
     (c2a x1)
       (list (DomainRO * RangeRO))
       (list_EqDec
          (pair_EqDec DomainRO_EqDec RangeRO_EqDec))
       (randomFunc rndRange DomainRO_EqDec) s;
     [a, s]<-2 z; ret (f a s)) v ==
     evalDist
    (z <-$
     (c2b x1)
       (list (DomainRO * RangeRO))
       (list_EqDec
          (pair_EqDec DomainRO_EqDec RangeRO_EqDec))
       (randomFunc rndRange DomainRO_EqDec) s;
     [a, s]<-2 z; ret (f a s)) v
    ) ->
    evalDist (z <-$
   (x1 <--$ c1a; c2a x1)
     (list (DomainRO * RangeRO))
     (list_EqDec
        (pair_EqDec DomainRO_EqDec RangeRO_EqDec))
     (randomFunc rndRange DomainRO_EqDec) s;
   [a, s]<-2 z; ret (f a s)) v ==
   evalDist
  (z <-$
   (x1 <--$ c1b; c2b x1)
     (list (DomainRO * RangeRO))
     (list_EqDec
        (pair_EqDec DomainRO_EqDec RangeRO_EqDec))
     (randomFunc rndRange DomainRO_EqDec) s;
   [a, s]<-2 z; ret (f a s)) v.

    intuition idtac.
    Local Opaque evalDist.
    simpl.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    eauto.

    Local Transparent evalDist.

  Qed.

  Theorem ExpROM_seq_eq : forall (A B : Set) 
    (eqdb : EqDec B)
    (c1a c1b : OracleComp DomainRO RangeRO A) 
    (c2a c2b : A -> OracleComp DomainRO RangeRO B) 
    v s,
    (forall x, 
      evalDist (c1a _ _ (randomFunc rndRange DomainRO_EqDec) s) x ==
      evalDist (c1b _ _ (randomFunc rndRange DomainRO_EqDec) s) x) ->
    (forall x1 s v,
      evalDist (z <-$
     (c2a x1)
       (list (DomainRO * RangeRO))
       (list_EqDec
          (pair_EqDec DomainRO_EqDec RangeRO_EqDec))
       (randomFunc rndRange DomainRO_EqDec) s;
     [a, _]<-2 z; ret a) v ==
     evalDist
    (z <-$
     (c2b x1)
       (list (DomainRO * RangeRO))
       (list_EqDec
          (pair_EqDec DomainRO_EqDec RangeRO_EqDec))
       (randomFunc rndRange DomainRO_EqDec) s;
     [a, _]<-2 z; ret a) v
    ) ->
    evalDist (z <-$
   (x1 <--$ c1a; c2a x1)
     (list (DomainRO * RangeRO))
     (list_EqDec
        (pair_EqDec DomainRO_EqDec RangeRO_EqDec))
     (randomFunc rndRange DomainRO_EqDec) s;
   [a, _]<-2 z; ret a) v ==
   evalDist
  (z <-$
   (x1 <--$ c1b; c2b x1)
     (list (DomainRO * RangeRO))
     (list_EqDec
        (pair_EqDec DomainRO_EqDec RangeRO_EqDec))
     (randomFunc rndRange DomainRO_EqDec) s;
   [a, _]<-2 z; ret a) v.

    intuition idtac.
    Local Opaque evalDist.
    simpl.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    eauto.

    Local Transparent evalDist.

  Qed.

  Theorem randomFunc_lookup_Some_inv : forall (D R : Set)(eqdd : EqDec D)(rndR : Comp R) s1 s2 v x b a,
    In (v, s2) (getSupport (@randomFunc D R rndR _ s1 a)) ->
    arrayLookup _ s1 x = Some b ->
    arrayLookup _ s2 x = Some b.

    intuition idtac.
    unfold randomFunc in *.
    case_eq (arrayLookup eqdd s1 a); intuition idtac;
    rewrite H1 in H;
    repeat simp_in_support.
    trivial.
    simpl.
    case_eq (eqb x a); intuition idtac.
    rewrite eqb_leibniz in H.
    subst.
    rewrite H0 in H1.
    discriminate.

  Qed.

  (* If the function is a fold with a commutative accumulator, then independent statements
  can be swapped. *)

  Theorem sumList_permutation_body_eq:
    forall (A : Set) (f1 f2 : A -> Rat) (ls1 ls2 : list A),
    Permutation ls1 ls2 -> 
    (forall a, In a ls2 -> (f1 a == f2 a)) ->
    sumList ls1 f1 == sumList ls2 f2.

    intros.
    eapply eqRat_trans.
    eapply sumList_permutation; eauto.
    eapply sumList_body_eq; intuition idtac.

  Qed.

  Variable leDom : DomainRO -> DomainRO -> bool.
  Hypothesis leDom_trans : forall a1 a2 a3, leDom a1 a2 = true -> leDom a2 a3 = true -> leDom a1 a3 = true.
  Hypothesis leDom_refl : forall a, leDom a a = true.
  Hypothesis leDom_antisymm : forall a1 a2, leDom a1 a2 = true -> leDom a2 a1 = true -> a1 = a2.
  Hypothesis leDOm_total : forall a1 a2, (leDom a1 a2) || (leDom a2 a1) = true.

  Theorem ExpROM_swap : forall (A B C : Set) 
    (c1 : OracleComp DomainRO RangeRO A) 
    (c2 : OracleComp DomainRO RangeRO B) 
    (c3 : A -> B -> OracleComp DomainRO RangeRO C)
    (E : Set)(eqde : EqDec E)(f2 : C -> E -> (DomainRO * RangeRO) -> E)
    (init : E) s x,
    (forall c e d1 d2, f2 c (f2 c e d1) d2 = f2 c (f2 c e d2) d1) ->
    evalDist (ExpROM_gen_s (x1 <--$ c1; x2 <--$ c2; c3 x1 x2) _ (fun c ls => fold_left (fun e d => (f2 c e d)) ls init) s ) x ==
    evalDist (ExpROM_gen_s (x2 <--$ c2; x1 <--$ c1; c3 x1 x2) _ (fun c ls => fold_left (fun e d => (f2 c e d)) ls init) s ) x.

    intuition idtac.

    assert RangeRO as RangeRO_ex.
    eapply comp_base_exists; eauto.

    assert A as a_ex.
    eapply oc_base_exists; eauto.
    
    assert B as b_ex.
    eapply oc_base_exists; eauto.

    assert C as c_ex.
    eapply oc_base_exists.
    eapply c3; intuition idtac.
    intuition idtac.

    unfold ExpROM_gen_s.
    
    eapply (@eqRat_trans  _
      (evalDist (z <-$
     (x1 <--$ c1; x2 <--$ c2; c3 x1 x2)
       (list (DomainRO * RangeRO))
       (list_EqDec (pair_EqDec DomainRO_EqDec RangeRO_EqDec))
       (sortedRandomFunc _ _ leDom rndRange) (sortDom leDom s);
     [t, s0]<-2 z;
     ret fold_left
           (fun (e : E) (d : DomainRO * RangeRO) => f2 t e d)
           s0 init) x)
    ).

    eapply comp_spec_eq_impl_eq.
    fcf_skip.
    eapply fcf_oracle_eq.
    2:{
    intros.
    assert ((fun x1 x2 => x2 = sortDom leDom x1) x1 x2).
    eapply H0.
    simpl in *.
    subst.
    eapply sortedRandomFunc_sorted_equiv; intuition idtac.
    }
    simpl in *.
    trivial.
    simpl in *; intuition idtac.
    destruct b0; simpl in *; subst.
    eapply comp_spec_ret; intuition idtac.
    eapply fold_left_comm_perm_eq; intuition idtac.
    eapply sortDom_perm.
    eauto.
    symmetry.
    eapply (@eqRat_trans  _
      (evalDist (z <-$
     (x1 <--$ c2; x2 <--$ c1; c3 x2 x1)
       (list (DomainRO * RangeRO))
       (list_EqDec (pair_EqDec DomainRO_EqDec RangeRO_EqDec))
       (sortedRandomFunc _ _ leDom rndRange) (sortDom leDom s);
     [t, s0]<-2 z;
     ret fold_left
           (fun (e : E) (d : DomainRO * RangeRO) => f2 t e d)
           s0 init) x)
    ).

    eapply comp_spec_eq_impl_eq.
    fcf_skip.
    eapply fcf_oracle_eq.
    2:{
    intros.
    assert ((fun x1 x2 => x2 = sortDom leDom x1) x1 x2).
    eapply H0.
    simpl in *.
    subst.
    eapply sortedRandomFunc_sorted_equiv; intuition idtac.
    }
    simpl in *.
    trivial.
    simpl in *; intuition idtac.
    destruct b0; simpl in *; subst.
    eapply comp_spec_ret; intuition idtac.
    eapply fold_left_comm_perm_eq; intuition idtac.
    eapply sortDom_perm.
    eauto.

    eapply comp_spec_eq_impl_eq.
    simpl.
    eapply (@comp_spec_eq_trans _ _ _
      (z <-$
     ([z, z2, s'0] <-$3 (z0 <-$
      c2 (list (DomainRO * RangeRO))
        (list_EqDec
           (pair_EqDec DomainRO_EqDec
              RangeRO_EqDec))
        (sortedRandomFunc DomainRO_EqDec
           RangeRO_EqDec leDom rndRange)
        (sortDom leDom s);
      [z, s']<-2 z0;
      z1 <-$
      c1 (list (DomainRO * RangeRO))
        (list_EqDec
           (pair_EqDec DomainRO_EqDec
              RangeRO_EqDec))
        (sortedRandomFunc DomainRO_EqDec
           RangeRO_EqDec leDom rndRange) s';
      [z2, s'0]<-2 z1;
      ret (z, z2, s'0));

      (c3 z2 z) (list (DomainRO * RangeRO))
        (list_EqDec
           (pair_EqDec DomainRO_EqDec
              RangeRO_EqDec))
        (sortedRandomFunc DomainRO_EqDec
           RangeRO_EqDec leDom rndRange) s'0);
     [t, s0]<-2 z;
     ret fold_left
           (fun (e : E) (d : DomainRO * RangeRO)
            => f2 t e d) s0 init)
    ).
    fcf_inline_first.
    fcf_skip.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    eapply comp_spec_eq_refl.

    eapply comp_spec_eq_symm.
    eapply (@comp_spec_eq_trans _ _ _
      (z <-$
     ([z, z2, s'0] <-$3 (z0 <-$
      c1 (list (DomainRO * RangeRO))
        (list_EqDec
           (pair_EqDec DomainRO_EqDec
              RangeRO_EqDec))
        (sortedRandomFunc DomainRO_EqDec
           RangeRO_EqDec leDom rndRange)
        (sortDom leDom s);
      [z, s']<-2 z0;
      z1 <-$
      c2 (list (DomainRO * RangeRO))
        (list_EqDec
           (pair_EqDec DomainRO_EqDec
              RangeRO_EqDec))
        (sortedRandomFunc DomainRO_EqDec
           RangeRO_EqDec leDom rndRange) s';
      [z2, s'0]<-2 z1;
      ret (z2, z, s'0));

      (c3 z2 z) (list (DomainRO * RangeRO))
        (list_EqDec
           (pair_EqDec DomainRO_EqDec
              RangeRO_EqDec))
        (sortedRandomFunc DomainRO_EqDec
           RangeRO_EqDec leDom rndRange) s'0);
     [t, s0]<-2 z;
     ret fold_left
           (fun (e : E) (d : DomainRO * RangeRO)
            => f2 t e d) s0 init)
    ).
    fcf_inline_first.
    fcf_skip.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    eapply comp_spec_eq_refl.

    eapply comp_spec_seq_eq; trivial.
    eapply comp_spec_seq_eq; trivial.
    
    intuition idtac.
    intuition idtac.

    eapply comp_spec_eq_symm.
    eapply ExpROM_swap_spec; intuition idtac.
    eapply sortedRandomFunc_swap; intuition idtac.
    intuition idtac.
    eapply comp_spec_eq_refl.
    intuition idtac.
    eapply comp_spec_eq_refl.

    Unshelve.

    eapply oc_EqDec.
    eapply c3; intuition idtac.
    intuition idtac.
    intuition idtac.
    
    eapply oc_EqDec.
    eapply c3; intuition idtac.
    intuition idtac.
    intuition idtac.

    eapply pair_EqDec.
    eapply oc_EqDec; eauto.
    eapply list_EqDec.
    eapply pair_EqDec; intuition idtac.

    eapply pair_EqDec.
    eapply oc_EqDec; eauto.
    eapply list_EqDec.
    eapply pair_EqDec; eauto.
    
    eapply pair_EqDec.
    eapply oc_EqDec; eauto.
    eapply list_EqDec.
    eapply pair_EqDec; eauto.
    
    eapply pair_EqDec.
    eapply oc_EqDec; eauto.
    eapply list_EqDec.
    eapply pair_EqDec; eauto.

    eapply pair_EqDec.
    eapply oc_EqDec; eauto.
    eapply list_EqDec.
    eapply pair_EqDec; eauto.
    eapply oc_EqDec; eauto.
    eapply oc_EqDec; eauto.
  Qed.  
    
End ExperimentROM.