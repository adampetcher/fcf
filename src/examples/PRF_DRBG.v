
Set Implicit Arguments.

Require Import FCF.
Require Import HasDups.
Require Import RndInList.
Require Import CompFold.

Section DRBG.

  (* The type of random seeds. *)
  Variable S : Set.
  Hypothesis S_EqDec : EqDec S.
  Variable RndS : Comp S.
  
  (* The type of DRBG outputs. *)
  Variable R : Set.
  Hypothesis R_EqDec : EqDec R.
  Variable RndR : Comp R.

  (* The DRBG *)
  Variable f : S -> R.

  Variable A : R -> Comp bool.

  Definition DRBG_G0 :=
    s <-$ RndS ;
    A (f s).

  Definition DRBG_G1 :=
    r <-$ RndR;
    A r.

  Definition DRBG_Advantage := | Pr[DRBG_G0] - Pr[DRBG_G1] |.

End DRBG.

(* For example, a DRBG on uniform bit vectors. *)
Section DRBG_bits.

  Variable k : nat.
  Variable l : nat.

  Definition DRBG_bits_Advantage := DRBG_Advantage ({0, 1}^k) ({0, 1}^l).

End DRBG_bits.

Require Import PRF.

(* To avoid all the bit vector complexities, we will use the generic definition and use lists of PRF outputs as the output of the DRBG. *)

(* We need an adaptively-secure PRF because we use the PRF output to produce the next input, and therefore this input is unpredictable. *)

Local Open Scope list_scope.
Local Opaque evalDist.

Section PRF_DRBG.

  Variable Key D : Set.
  (* The range of the PRF is a bit vector of length eta. *)
  Variable eta : nat.
  Hypothesis D_EqDec : EqDec D.

  Variable RndKey : Comp Key.

  (* f is an adaptively-secure PRF. *)
  Variable f : Key -> D -> Bvector eta.

  (* For this construction, we need an injection from the range of the PRF to the domain.  This allows us to use the previous PRF output to compute the next one. *)
  Variable injD : Bvector eta -> D.
  Hypothesis injD_correct : 
    forall r1 r2, (injD r1) = (injD r2) -> r1 = r2.

  Variable l : nat.
  Hypothesis l_pos : l  > 0.
  Variable r_init : Bvector eta.
  Definition v_init := injD r_init.
  
  Definition RndOut := compMap _ (fun _ => {0, 1}^eta) (forNats l).
  
  Fixpoint PRF_DRBG_f (v : D)(n : nat)(k : Key) :=
    match n with
        | O => nil
        | S n' => 
          r <- (f k v);
            r :: (PRF_DRBG_f (injD r) n' k)
    end.

  Definition PRF_DRBG (k : Key) :=
    PRF_DRBG_f v_init l k.
  
  Variable A : list (Bvector eta) -> Comp bool.
  Hypothesis A_wf : forall c, well_formed_comp (A c).

  (* Step 1: inline definitions and simplify. *)
  Definition PRF_DRBG_G1 :=
    s <-$ RndKey ;
    A (PRF_DRBG_f v_init l s).

  (* This game is equivalent to the first game in the security definition. *)
  Theorem PRF_DRBG_G1_equiv : 
    Pr[DRBG_G0 RndKey PRF_DRBG A] == Pr[PRF_DRBG_G1].

    reflexivity.

  Qed.

  (* Step 2: use the PRF as an oracle. *)
  Fixpoint PRF_DRBG_f_G2 (v : D)(n : nat) :=
    match n with
        | O => $ ret nil
        | S n' => 
          r <--$ (OC_Query _ v);
            ls' <--$ (PRF_DRBG_f_G2 (injD r) n');
                $ ret (r :: ls')
    end.


  Definition PRF_A := (ls <--$ PRF_DRBG_f_G2 v_init l; $ A ls).

  Theorem PRF_DRBG_f_G2_wf : 
    forall n v,
      well_formed_oc (PRF_DRBG_f_G2 v n).

    induction n; intuition; simpl in *.
    econstructor.
    wftac.
    econstructor.
    econstructor.
    intuition.
    econstructor.
    eauto.
    intuition.
    econstructor.
    wftac.
  Qed.

  Theorem PRF_A_wf : well_formed_oc PRF_A.

    unfold PRF_A.
    econstructor.
    apply PRF_DRBG_f_G2_wf.
    intuition.
    econstructor.
    apply A_wf.

  Qed.

  Definition PRF_DRBG_G2 :=
    s <-$ RndKey ;
    [b, _] <-$2 PRF_A unit _ (f_oracle f _ s) tt;
    ret b.

  (* In an intermediate step, put the construction in the form of a (deterministic) computation.  Then we can more easily change it to an oracle interaction in the following step. *)
  Fixpoint PRF_DRBG_f_G1_1 (v : D)(n : nat)(k : Key) :=
    match n with
        | O => ret nil
        | S n' => 
          r <-$ ret (f k v);
          ls <-$ (PRF_DRBG_f_G1_1 (injD r) n' k);
            ret (r :: ls)
    end.

   Definition PRF_DRBG_G1_1 :=
    s <-$ RndKey ;
    ls <-$ PRF_DRBG_f_G1_1 v_init l s;
    A ls.

   Theorem  PRF_DRBG_f_G1_1_eq_ret : 
     forall k n v,
       comp_spec eq (PRF_DRBG_f_G1_1 v n k) (ret (PRF_DRBG_f v n k)).

     induction n; intuition; simpl in *.

     eapply comp_spec_eq_refl.

     comp_simp.
     eapply comp_spec_eq_trans.
     eapply comp_spec_seq_eq; eauto with inhabited.
     intuition.
     eapply comp_spec_eq_refl.
     comp_simp.
     eapply comp_spec_eq_refl.
   Qed.

   Theorem PRF_DRBG_G1_1_equiv :
     Pr[PRF_DRBG_G1] == Pr[PRF_DRBG_G1_1].

     unfold PRF_DRBG_G1, PRF_DRBG_G1_1.
     comp_skip.
     eapply comp_spec_eq_impl_eq.
     eapply comp_spec_eq_symm.
     eapply comp_spec_eq_trans.
     eapply comp_spec_seq_eq; eauto with inhabited.
     eapply  PRF_DRBG_f_G1_1_eq_ret.
     intuition.
     eapply comp_spec_eq_refl.
     comp_simp.
     eapply comp_spec_eq_refl.

   Qed.


   Theorem PRF_DRBG_f_G1_1_G2_equiv :
     forall k n v,
     comp_spec (fun x1 x2 => x1 = fst x2) (PRF_DRBG_f_G1_1 v n k)
     ((PRF_DRBG_f_G2 v n) unit unit_EqDec
        (f_oracle f (Bvector_EqDec eta) k) tt).

     induction n; intuition; simpl in *.

     comp_simp.
     eapply comp_spec_ret.
     trivial.

     comp_skip.
     unfold f_oracle.
     eapply (comp_spec_ret _ _ (fun x1 x2 => x1 = fst x2)).
     trivial.
     simpl in *.
     intuition; subst.
     comp_skip.
     comp_simp.
     eapply comp_spec_ret; intuition.

   Qed.

  Theorem PRF_DRBG_G1_G2_equiv : 
    Pr[ PRF_DRBG_G1 ] == Pr[ PRF_DRBG_G2 ].

    rewrite PRF_DRBG_G1_1_equiv.
    unfold  PRF_DRBG_G1_1,  PRF_DRBG_G2.
    unfold PRF_A.
    simpl.
    comp_skip.
    inline_first.

    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply PRF_DRBG_f_G1_1_G2_equiv.
    simpl in *.
    subst.
    comp_simp.
    simpl.
    inline_first.
    eapply eq_impl_comp_spec_eq.
    intuition.
    rewrite <- evalDist_right_ident.
    comp_skip.
    comp_simp.
    reflexivity.
  Qed.

  (* Step 3: replace the PRF with a random function *)

  Definition PRF_DRBG_G3 :=
    [b, _] <-$2 PRF_A _ _ (randomFunc ({0,1}^eta) _) nil;
    ret b.

  Theorem PRF_DRBG_G2_G3_close : 
    | Pr[PRF_DRBG_G2] - Pr[PRF_DRBG_G3] | <= PRF_Advantage RndKey ({0,1}^eta) f _ _ PRF_A.

    reflexivity.
  Qed.

  
  (* Step 4 : replace the random function with random values.  This is the same as long as there are no duplicates in the list of random function inputs. *)
  Definition PRF_DRBG_G4 :=
    [b, _] <-$2 PRF_A _ _ (fun _ _ => x <-$ {0, 1}^eta; ret (x, tt)) tt;
    ret b.

  Definition randomFunc_withDups ls x :=
    y <-$ 
      (match (arrayLookup _ ls x) with 
        | Some y => ret y 
        | None => {0,1}^eta 
       end); 
    ret (y, (x, y) :: ls).

  (* Step 3.1: preserve duplicate calls *)
  Definition PRF_DRBG_G3_1 :=
    [b, _] <-$2 PRF_A _ _ (randomFunc_withDups) nil;
    ret b.
  
  Theorem randomFunc_withDups_spec : 
    forall x1 x2 a, 
      (forall x, arrayLookup _ x1 x = arrayLookup _ x2 x) ->
    comp_spec
     (fun y1 y2 : Bvector eta * list (D * Bvector eta) =>
      fst y1 = fst y2 /\
      (forall a0 : D,
       arrayLookup D_EqDec (snd y1) a0 = arrayLookup D_EqDec (snd y2) a0))
     (randomFunc ({ 0 , 1 }^eta) D_EqDec x1 a) (randomFunc_withDups x2 a).

    intuition.
    unfold randomFunc, randomFunc_withDups.
    rewrite H.
    case_eq (arrayLookup D_EqDec x2 a); intuition.
    comp_simp.
    eapply comp_spec_ret; intuition.
    simpl.
    case_eq (eqb a0 a); intuition.
    rewrite eqb_leibniz in H1.
    subst.
    rewrite H.
    trivial.

    comp_skip.
    eapply comp_spec_ret; intuition.
    simpl.
    rewrite H.
    trivial.

  Qed.

  Theorem PRF_DRBG_G3_1_eq : 
    Pr[PRF_DRBG_G3] == Pr[PRF_DRBG_G3_1].
    
    unfold PRF_DRBG_G3, PRF_DRBG_G3_1.
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply (oc_comp_spec_eq _ _ _ _ _ _ (fun x1 x2 => forall a, arrayLookup _ x1 a = arrayLookup _ x2 a)); intuition.
    apply randomFunc_withDups_spec; intuition.

    comp_simp.
    simpl in H1; intuition; subst.
    eapply comp_spec_eq_refl.

  Qed.

  Definition PRF_DRBG_G3_2 :=
    [b, ls] <-$2 PRF_A _ _ (randomFunc_withDups) nil;
    ret (b, hasDups _ (fst (split ls))).

  Theorem PRF_DRBG_G3_1_2_eq : 
    Pr[PRF_DRBG_G3_1] == Pr[x <-$ PRF_DRBG_G3_2; ret (fst x)].

    unfold PRF_DRBG_G3_1, PRF_DRBG_G3_2.
    simpl.
    inline_first.
    comp_skip.
    comp_simp.
    inline_first.
    comp_skip.
    comp_simp.
    simpl.
    reflexivity.
  Qed.

  Definition PRF_DRBG_G3_3 :=
    [b, ls] <-$2 PRF_A _ _  (fun ls a => x <-$ {0, 1}^eta; ret (x, (a, x)::ls)) nil;
    ret (b, hasDups _ (fst (split ls))).
 

  Theorem PRF_A_randomFunc_eq_until_bad : 
    comp_spec 
      (fun y1 y2 =>
         hasDups _ (fst (split (snd y1))) =
         hasDups _ (fst (split (snd y2))) /\
         (hasDups _ (fst (split (snd y1))) = false ->
          snd y1 = snd y2 /\ fst y1 = fst y2))
      (PRF_A _ _ randomFunc_withDups nil)
      (PRF_A _ _ 
             (fun (ls : list (D * Bvector eta)) (x : D) =>
         r <-$ { 0 , 1 }^eta; ret (r, (x, r) :: ls)) nil).
    
    
    eapply (oc_comp_spec_eq_until_bad _ _ _ _ (fun x => hasDups _ (fst (split x))) (fun x => hasDups _ (fst (split x))) eq); intuition.
    
    unfold randomFunc_withDups.
    destruct ( arrayLookup D_EqDec a b);
    wftac.

    wftac.

    subst.

    unfold randomFunc_withDups.

    case_eq (arrayLookup _ x2 a); intuition. 
    eapply comp_spec_irr_r; intuition.
    wftac.
    comp_simp.
    eapply comp_spec_ret.
    intuition.
    simpl.   
    remember (split x2) as z.
    destruct z.
    simpl in *.
    trivial.
    simpl in *.
    remember (split x2) as z.
    destruct z.
    simpl in *.
    destruct (in_dec (EqDec_dec D_EqDec) a l0); intuition.
    discriminate.
    rewrite notInArrayLookupNone in H.
    discriminate.
    intuition.
    rewrite unzip_eq_split in H3.
    remember (split x2) as z.
    destruct z.
    pairInv.
    simpl in *.
    intuition.
    
    simpl in *.
    remember (split x2) as z.
    destruct z.
    simpl in *.
    destruct (in_dec (EqDec_dec D_EqDec) a l0).
    discriminate.
    rewrite notInArrayLookupNone in H.
    discriminate.
    intuition.
    rewrite unzip_eq_split in H3.
    remember (split x2) as z.
    destruct z.
    pairInv.
    simpl in *.
    intuition.
    
    comp_skip.
    eapply comp_spec_ret.
    intuition.

    unfold randomFunc_withDups in *.
    repeat simp_in_support.
    simpl.
    remember (split c) as z.
    destruct z.
    simpl in *.
    destruct (in_dec (EqDec_dec D_EqDec) d l0); intuition.

    repeat simp_in_support.
    simpl in *.
    remember (split c) as z.
    destruct z.
    simpl in *.
    destruct (in_dec (EqDec_dec D_EqDec) d l0); intuition.

    Grab Existential Variables.
    apply PRF_A_wf.

  Qed.


   Theorem PRF_DRBG_G3_2_3_badness_same : 
      Pr  [x <-$ PRF_DRBG_G3_2; ret snd x ] ==
      Pr  [x <-$ PRF_DRBG_G3_3; ret snd x ].

     unfold PRF_DRBG_G3_2, PRF_DRBG_G3_3.
     comp_inline_l.
     comp_inline_r.
     eapply comp_spec_eq_impl_eq.
     comp_skip.
     eapply PRF_A_randomFunc_eq_until_bad.

     comp_simp.
     intuition.
     simpl in *.
     eapply comp_spec_ret; intuition.
   Qed.


   Theorem PRF_DRBG_G3_2_3_close : 
     | Pr[x <-$ PRF_DRBG_G3_2; ret (fst x)] - Pr[x <-$ PRF_DRBG_G3_3; ret (fst x)] | <= Pr[x <-$ PRF_DRBG_G3_3; ret (snd x)].

     rewrite ratDistance_comm.
     eapply fundamental_lemma_h.
     symmetry.
     eapply PRF_DRBG_G3_2_3_badness_same.

     intuition.
     symmetry.
     unfold PRF_DRBG_G3_2, PRF_DRBG_G3_3.
     eapply comp_spec_impl_eq.
     comp_skip.
     eapply PRF_A_randomFunc_eq_until_bad.
     comp_simp.
     eapply comp_spec_ret; intuition.
     simpl in *; pairInv; intuition; subst;
     trivial.

     simpl in *.
     pairInv.
     rewrite H2.
     rewrite <- H2 in H6.
     edestruct H3; intuition; subst.
     trivial.
  
   Qed.

   Theorem PRF_DRBG_G3_3_G4_eq :
     Pr[ x <-$ PRF_DRBG_G3_3; ret (fst x) ] == Pr[ PRF_DRBG_G4 ].
     
     unfold PRF_DRBG_G3_3, PRF_DRBG_G4.
     simpl.
     inline_first.
     eapply comp_spec_eq_impl_eq.
     comp_skip.
     eapply (oc_comp_spec_eq _ _ _ _ _ _ (fun x1 x2 => True)); intuition.    
     comp_skip.
     eapply comp_spec_ret; intuition.
     simpl in H1.
     intuition; subst.
     comp_simp.
     inline_first.
     simpl.
     comp_skip.
     simpl; comp_simp.
     eapply comp_spec_eq_refl.

   Qed.


   Fixpoint PRF_DRBG_f_bad (v : D)(n : nat) :=
    match n with
        | O =>  ret nil
        | S n' => 
          r <-$ {0,1}^eta;
            ls' <-$ (PRF_DRBG_f_bad (injD r) n');
            ret (v :: ls')
    end.

   Definition PRF_DRBG_G3_bad_1 :=
     ls <-$ PRF_DRBG_f_bad v_init l;
     ret (hasDups _ ls).

   Require Import Permutation.

   Theorem PRF_DRBG_f_bad_spec : 
     forall n v ls,
     comp_spec (fun x1 x2 => Permutation (fst (split (snd x1))) ((fst (split ls)) ++ x2))
     ((PRF_DRBG_f_G2 v n) _ _
        (fun (ls : list (D * Bvector eta)) (a : D) =>
         x <-$ { 0 , 1 }^eta; ret (x, (a, x) :: ls)) ls)
     (PRF_DRBG_f_bad v n).

     induction n; intuition; simpl in *.
     comp_simp.
     eapply comp_spec_ret; intuition.
     simpl.
     rewrite app_nil_r.
     eapply Permutation_refl.

     inline_first.
     comp_skip.
     comp_skip.
     eapply comp_spec_ret; intuition.
     simpl in H3.
     simpl.
     destruct (split ls).
     simpl in H3. simpl.
     eapply Permutation_trans.
     eapply H3.
     eapply Permutation_cons_app.
     eapply Permutation_refl.
   Qed.

   Theorem PRF_DRBG_G3_bad_equiv : 
     Pr[x <-$ PRF_DRBG_G3_3; ret (snd x)] == Pr[PRF_DRBG_G3_bad_1].

     unfold PRF_DRBG_G3_3, PRF_DRBG_G3_bad_1.
     simpl.
     inline_first.
     
     eapply comp_spec_eq_impl_eq.
     comp_skip.
     eapply PRF_DRBG_f_bad_spec.
     simpl in H1.
     inline_first.
     comp_irr_l.
     comp_simp.
     simpl.
     eapply comp_spec_ret; intuition.

     Theorem Permutation_hasDups : 
       forall (A : Set)(eqd : EqDec A)(ls1 ls2 : list A),
         Permutation ls1 ls2 ->
         hasDups eqd ls1 = hasDups eqd ls2.

       intuition.
       case_eq ( hasDups eqd ls1); intuition.
       apply hasDups_true_not_NoDup in H0.
       intuition.
       case_eq (hasDups eqd ls2); intuition.
       apply hasDups_false_NoDup in H1; intuition.
       
       exfalso.
       eapply H0.
       eapply permutation_NoDup.
       eapply Permutation_sym.
       eauto.
       trivial.

       eapply hasDups_false_NoDup in H0; intuition.
       case_eq (hasDups eqd ls2); intuition.
       apply hasDups_true_not_NoDup in H1.
       exfalso.
       apply H1.
       eapply permutation_NoDup;
       eauto.

     Qed.

     eapply Permutation_hasDups.
     trivial.

   Qed.

   Fixpoint PRF_DRBG_f_bad_2 (n : nat) :=
    match n with
        | O =>  ret nil
        | S n' => 
          r <-$ {0,1}^eta;
            ls' <-$ (PRF_DRBG_f_bad_2 n');
            ret (r :: ls')
    end.

   Definition PRF_DRBG_G3_bad_2 :=
     ls <-$ PRF_DRBG_f_bad_2 (pred l);
     ret (hasDups _ (v_init :: (map injD ls))).

   Theorem PRF_DRBG_f_bad_2_equiv : 
     forall n v, 
     comp_spec (fun x1 x2 => x1 = v :: (map injD x2))
               (PRF_DRBG_f_bad v (S n)) 
               (PRF_DRBG_f_bad_2 n).

     induction n; intuition; simpl in *.
     comp_irr_l.
     comp_simp.
     eapply comp_spec_ret; intuition.

     comp_skip.
     comp_skip.
     eapply comp_spec_ret; intuition.

   Qed.

   Theorem PRF_DRBG_G3_bad_1_2_equiv : 
     Pr[PRF_DRBG_G3_bad_1] == Pr[PRF_DRBG_G3_bad_2].

     unfold PRF_DRBG_G3_bad_1, PRF_DRBG_G3_bad_2.
     eapply comp_spec_eq_impl_eq.
     destruct l; simpl; intuition.
     comp_simp.
     simpl.
     eapply comp_spec_eq_refl.

     comp_skip.
     eapply PRF_DRBG_f_bad_2_equiv.
     simpl in H1.
     subst.
     eapply comp_spec_ret; intuition.
  
   Qed.

   Definition PRF_DRBG_G3_bad_3 :=
     ls <-$ compMap _ (fun _ => {0, 1}^eta) (forNats (pred l));
     ret (hasDups _ (v_init :: (map injD ls))).

   Theorem PRF_DRBG_f_bad_2_compMap_equiv :
     forall n, 
     comp_spec eq
     (PRF_DRBG_f_bad_2 n)
     (compMap (Bvector_EqDec eta) (fun _ : nat => { 0 , 1 }^eta)
        (forNats n)).

     induction n; intuition; simpl in *.
     eapply comp_spec_eq_refl.
     comp_skip.
     comp_skip.
     eapply IHn.
     subst.
     eapply comp_spec_eq_refl.

   Qed.

   Theorem PRF_DRBG_G3_bad_2_3_equiv : 
     Pr[PRF_DRBG_G3_bad_2] == Pr[PRF_DRBG_G3_bad_3].

     unfold PRF_DRBG_G3_bad_2, PRF_DRBG_G3_bad_3.
     eapply comp_spec_eq_impl_eq.
     comp_skip.
     eapply PRF_DRBG_f_bad_2_compMap_equiv.
     subst.
     eapply comp_spec_eq_refl.

   Qed.

   Definition PRF_DRBG_G3_bad_4 :=
     ls <-$ compMap _ (fun _ => {0, 1}^eta) (forNats (pred l));
     ret (hasDups _ (r_init :: ls)).

    Theorem PRF_DRBG_G3_bad_3_4_equiv : 
     Pr[PRF_DRBG_G3_bad_3] == Pr[PRF_DRBG_G3_bad_4].

     unfold PRF_DRBG_G3_bad_3, PRF_DRBG_G3_bad_4.
     eapply comp_spec_eq_impl_eq.
     comp_skip.
     eapply comp_spec_ret; intuition.
     unfold v_init.

     Theorem hasDups_inj_equiv : 
       forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(lsa : list A)(inj : A -> B),
         (forall a1 a2, inj a1 = inj a2 -> a1 = a2) ->
         hasDups _ lsa = hasDups _ (map inj lsa).

       induction lsa; intuition; simpl in *.
       destruct (in_dec (EqDec_dec eqda) a lsa);
       destruct (in_dec (EqDec_dec eqdb) (inj a) (map inj lsa));
       intuition.
       exfalso.
       eapply n.
       eapply in_map_iff.
       econstructor.
       intuition.
       eapply in_map_iff in i.
       destruct i.
       intuition.
       apply H in H1.
       subst.
       intuition.
     Qed.

     symmetry.
     erewrite (hasDups_inj_equiv _ _ (r_init :: b)).
     simpl. eauto.
     trivial.
   Qed.

   

   (* We need a form of the dupProb theorem that allows the first item in the list to be fixed. *)
   Theorem dupProb_const : 
    forall (X : Set)(ls : list X)(v : Bvector eta),
      Pr[x <-$ compMap _ (fun _ => {0, 1}^eta) ls; ret (hasDups _ (v :: x))] <= 
      ((S (length ls)) ^ 2 / 2 ^ eta).


     intuition.
     assert (Pr[x <-$ compMap (Bvector_EqDec eta) (fun _ : X => { 0 , 1 }^eta) ls;
    ret hasDups (Bvector_EqDec eta) (v :: x) ] 
               ==
               Pr[x <-$ compMap (Bvector_EqDec eta) (fun _ : X => { 0 , 1 }^eta) ls;
    ret ((if (in_dec (EqDec_dec _) v x) then true else false) || (hasDups (Bvector_EqDec eta) x)) ] 
                 ).
     comp_skip.
     simpl.
     destruct ( in_dec (EqDec_dec (Bvector_EqDec eta)) v x).
     simpl.
     intuition.
     rewrite orb_false_l.
     intuition.

     rewrite H.
     clear H.

     eapply leRat_trans.
     apply evalDist_orb_le.
     rewrite FixedInRndList_prob.
     rewrite dupProb.
     
     simpl.
     rewrite mult_1_r.
     cutrewrite ( S (length ls + length ls * S (length ls)) =  (S (length ls) + length ls * S (length ls)))%nat.
     eapply leRat_trans.
     Focus 2.
     eapply eqRat_impl_leRat.
     symmetry.
     eapply ratAdd_num.
     eapply ratAdd_leRat_compat.
     eapply leRat_terms;
     omega.
     eapply leRat_terms.
     eapply mult_le_compat; omega.
     trivial.
     omega.
  Qed.

   Theorem PRF_DRBG_G3_bad_4_small :
      Pr[PRF_DRBG_G3_bad_4] <= (l ^ 2 / 2 ^ eta).

     unfold PRF_DRBG_G3_bad_4.
     rewrite dupProb_const.
     destruct l.
     omega.
     
     simpl.
     rewrite forNats_length.
     rewrite mult_1_r.
     reflexivity.
 
   Qed.

   Theorem PRF_DRBG_G3_G4_close : 
     | Pr[ PRF_DRBG_G3 ] - Pr[  PRF_DRBG_G4 ] | <= (l^2 / 2^eta).

     rewrite PRF_DRBG_G3_1_eq.
     rewrite PRF_DRBG_G3_1_2_eq.
     rewrite <- PRF_DRBG_G3_3_G4_eq.
     rewrite  PRF_DRBG_G3_2_3_close.
     rewrite PRF_DRBG_G3_bad_equiv.
     rewrite PRF_DRBG_G3_bad_1_2_equiv.
     rewrite PRF_DRBG_G3_bad_2_3_equiv.
     rewrite PRF_DRBG_G3_bad_3_4_equiv.
     apply PRF_DRBG_G3_bad_4_small.

   Qed.

   Theorem PRF_DRBG_f_G2_compMap_spec :
     forall n v, 
     comp_spec (fun x1 x2 => fst x1 = x2)
     ((PRF_DRBG_f_G2 v n) unit unit_EqDec
        (fun (_ : unit) (_ : D) => x <-$ { 0 , 1 }^eta; ret (x, tt)) tt)
     (compMap (Bvector_EqDec eta) (fun _ : nat => { 0 , 1 }^eta) (forNats n)).

     induction n; intuition; simpl in *.
     comp_simp.
     eapply comp_spec_ret; intuition.
     
     inline_first.
     comp_skip.
     comp_skip.
     eapply comp_spec_ret; intuition.
   Qed.


  Theorem PRF_DRBG_G4_DRBG_equiv : 
    Pr[PRF_DRBG_G4] == Pr[DRBG_G1 RndOut A].

    unfold PRF_DRBG_G4, DRBG_G1, RndOut, PRF_A.
    simpl.
    inline_first.
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply PRF_DRBG_f_G2_compMap_spec.
    simpl in H1; subst.
    inline_first.
    eapply eq_impl_comp_spec_eq; intuition.
    symmetry.
    rewrite <- evalDist_right_ident.
    comp_skip.
    comp_simp.
    reflexivity.
  Qed.


  Theorem PRF_DRBG_Adv_small : 
    DRBG_Advantage RndKey RndOut PRF_DRBG A <=  
    PRF_Advantage RndKey ({ 0 , 1 }^eta) f D_EqDec (Bvector_EqDec eta) PRF_A
    + l ^ 2 / 2 ^ eta.

    intuition.
    unfold DRBG_Advantage.
    rewrite PRF_DRBG_G1_equiv.
    rewrite PRF_DRBG_G1_G2_equiv.
    rewrite <- PRF_DRBG_G4_DRBG_equiv.
    eapply ratDistance_le_trans.
    apply PRF_DRBG_G2_G3_close.
    apply PRF_DRBG_G3_G4_close.

  Qed.

  Print Assumptions PRF_DRBG_Adv_small.

End PRF_DRBG.
