(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
Set Implicit Arguments.

Require Import Coq.ZArith.Zdigits.

Require Import FCF.
Require Import CompFold.
Require Import GroupTheory.
Require Import RndPerm.
Require Import PRF.

Require Import SSE.
Require Import TSet.

Local Open Scope list_scope.
Local Open Scope type_scope.

Section ESPADA_SSE_OXT.

  Variable lambda : posnat.
  Definition DB := DB lambda.

  Variable p : posnat.
  Definition multModP (a b : nat) :=
    modNat (a * b) p.

  Context `{FCG : FiniteCyclicGroup nat}.

  Hypothesis op_multModP : 
    groupOp = multModP.

  (* PRFs *)
  Variable F : Bvector lambda -> Keyword -> Bvector lambda.
  Variable F_P : Bvector lambda -> Blist -> nat.

  (* Encryption scheme *)
  Variable Enc : Bvector lambda -> Bvector lambda -> Comp (Bvector lambda).
  Variable Dec : Bvector lambda -> Bvector lambda -> Bvector lambda.
  Hypothesis Enc_correct : 
    forall k p c,
      In c (getSupport (Enc k p)) ->
      Dec k c = p.
  

  Instance nz_posnat_plus : 
    forall (x y : posnat),
      nz (x + y).

  intuition.
  unfold posnatToNat, natToPosnat.
  destruct x.
  destruct y.
  econstructor.
  omega.

  Qed.

  (* TSet *)
  Variable TSet : Set.
  Hypothesis TSet_EqDec : EqDec TSet.
  Variable TSetKey : Set.
  Hypothesis TSetKey_EqDec : EqDec TSetKey.
  Variable Tag : Set.
  Hypothesis Tag_EqDec : EqDec Tag.
  Variable TSetSetup : T (pos (lambda + lambda)) -> Comp (TSet * TSetKey).
  Variable TSetGetTag : TSetKey -> Keyword -> Comp Tag. 
  Variable TSetRetrieve : TSet -> Tag -> (list (Bvector (lambda + lambda))).
  Variable Leakage_T : Set.
  Hypothesis Leakage_T_EqDec : EqDec Leakage_T.
  Variable L_T : T (pos (lambda + lambda)) -> list Keyword -> Leakage_T.

  Definition XSet := list nat.
  Definition EDB := TSet * XSet.
  Definition Key := Bvector lambda * Bvector lambda * Bvector lambda * Bvector lambda * TSetKey.
  Definition Query := Keyword * Keyword.

  Definition natToBvector(n : nat) : Bvector lambda :=
    Z_to_binary lambda (Z.of_nat n).

  Definition natToBlist (n : nat) :=
    Vector.to_list (natToBvector n).

   Definition bvectorToNat(v : Bvector lambda) : nat :=
    Z.to_nat (binary_value _ v).

  Coercion natToBlist : nat >-> list.

  Definition lookupInds(db : DB)(w : Keyword) :=
    fold_left (fun ls p => if (in_dec (EqDec_dec _) w (snd p)) then (fst p :: ls) else ls) db nil.
        
  Local Open Scope group_scope.

  Definition OXT_EDBSetup_indLoop k_I k_Z k_E k_X w (e : Identifier lambda * nat) :=
    [ind, c] <-2 e;
    xind <- F_P k_I (Vector.to_list ind);
    z <- F_P k_Z (w ++ c);
    y <- xind * (inverse z);
    e <-$ Enc k_E ind;
    xtag <- g^((F_P k_X w) * xind);
    ret (Vector.append e (natToBvector y), xtag).

  Definition OXT_EDBSetup_wLoop db k_S k_I k_Z k_X w :=
    k_E <- F k_S w;
    inds <- lookupInds db w;
    inds <-$ shuffle _ inds; 
    indLoopRes <-$ compMap _ (OXT_EDBSetup_indLoop k_I k_Z k_E k_X w) (combine inds (allNatsLt (length inds)));
    ret (split indLoopRes).
    
  Definition toW (db : DB) :=
    removeDups _ (flatten (snd (split db))).

  Definition OXT_EDBSetup (db : DB) : Comp (Key * (TSet * XSet)) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (OXT_EDBSetup_wLoop db k_S k_I k_Z k_X) (toW db);
    [t_entries, xSet_raw] <-2 split wLoopRes;
    t <- combine (toW db) t_entries;
    xSet <- flatten xSet_raw;
    [tSet, k_T] <-$2 TSetSetup t;
    ret ((k_S, k_X, k_I, k_Z, k_T), (tSet, xSet)).

  Definition OXT_Search_ClientInit(k : Key)(q : Query) :=
    [k_S, k_X, k_I, k_Z, k_T] <-5 k;
    [w1, _] <-2 q;
    TSetGetTag k_T w1.

  Definition OXT_Search_ServerInit(edb : EDB) stag :=
    [tSet, _] <-2 edb;
    TSetRetrieve tSet stag.

  Definition computeXToken c k_Z k_X s x :=
    g^((F_P k_Z (s ++ c)) * (F_P k_X x)).

  Definition OXT_Search_Loop_Client (k : Key)(q : Query) c :=
    [k_S, k_X, k_I, k_Z, k_T] <-5 k;
    [s, x] <-2 q;
    computeXToken c k_Z k_X s x.

  Fixpoint splitVector(A : Set)(n m : nat) : Vector.t A (n + m) -> (Vector.t A n * Vector.t A m) :=
    match n with
        | 0 => 
          fun (v : Vector.t A (O + m)) => (@Vector.nil A, v)
        | S n' => 
          fun (v : Vector.t A (S n' + m)) => 
            let (v1, v2) := splitVector _ _ (Vector.tl v) in
            (Vector.cons _ (Vector.hd v) _ v1, v2)
    end.

  Definition OXT_Search_Loop_Server (edb : EDB) xtoken t_c :=
    [_, xSet] <-2 edb;
    [e, y] <-2 splitVector lambda _ t_c;
    if (in_dec (EqDec_dec _) (xtoken^(bvectorToNat y)) xSet) then (Some e) else None.

  Definition OXT_Search_Loop edb k q (e : nat * Bvector (lambda + lambda)) :=
    [c, t_c] <-2 e;
    xtoken <- OXT_Search_Loop_Client k q c ;
    answer <- OXT_Search_Loop_Server edb xtoken t_c;
    (xtoken, answer).

  Definition OXT_Search_ClientFinalize (k : Key) (q : Query) es :=
    [k_S, k_X, k_I, k_Z, k_T] <-5 k;
    [w1, ws] <-2 q;
    k_E <- F k_S w1;
    map (Dec k_E) es.
    
  Fixpoint getSomes(A : Type)(ls : list (option A)) :=
    match ls with
      | nil => nil 
      | o :: ls' =>
        match o with
            | None => (getSomes ls')
            | Some a => a :: (getSomes ls')
        end
    end.

  
  Definition SearchTranscript := (Tag * list (nat * option (Bvector lambda)))%type.

  Definition OXT_Search (edb : EDB) (k : Key) (q : Query) : Comp (list (Identifier lambda) * SearchTranscript) :=
    stag <-$ OXT_Search_ClientInit k q;
    t <- OXT_Search_ServerInit edb stag;
    xscript <- map (OXT_Search_Loop edb k q) (combine (allNatsLt (length t)) t);
    es <- getSomes (snd (split xscript));
    inds <- OXT_Search_ClientFinalize k q es;
    ret (inds, (stag, xscript)).

  Definition dbSize(db : DB) :=
    fold_left (fun n e => n + length (snd e))%nat db 0%nat.

  Require Import RndListElem.
  Check firstIndexOf.

  Definition equalityPattern(ls : list Keyword) :=
    map (fun x => firstIndexOf (EqDec_dec _) ls x 0) ls.

  Definition sizePattern(db : DB)(ls : list Keyword) :=
    map (fun x => length (lookupInds db x)) ls.

  Definition lookupIndsConj(db : DB)(w : Query) :=
    [s, x] <-2 w;
    inds <- lookupInds db s;
    intersect (EqDec_dec _) inds (lookupInds db x).

  Definition resultsPattern(db : DB)(q: list Query) :=
    map (lookupIndsConj db) q.

  Definition condIntPattern(db : DB) (i j : nat) (qi qj : Query):=
    r <- intersect (EqDec_dec _) (lookupInds db (fst qi)) (lookupInds db (fst qj));
    if (eq_nat_dec i j) then nil else
      if (eqb (snd qi) (snd (qj))) then r else nil.      

  Definition condIntPatternTable(db : DB)(q : list Query) :=
    map (fun e => [i,qi] <-2 e; 
         map 
           (fun e => [j,qj] <-2 e; condIntPattern db i j qi qj)
           (combine (allNatsLt (length q)) q))
        (combine (allNatsLt (length q)) q).

  Definition L_OXT(db : DB)(q : list Query) :=
    n <- dbSize db;
    s_bar <- equalityPattern (fst (split q));
    sP <- sizePattern db (fst (split q));
    rP <- resultsPattern db q;
    iP <- condIntPatternTable db q;
    (n, s_bar, sP, rP, iP).

  Require Import RndGrpElem.

  Definition L_cLoop (k : Bvector lambda)(c : nat) :=
    y <-$ RndG;
    e <-$ Enc k (Vector.const false lambda);
    ret (Vector.append (natToBvector y) e).

  Definition L_wLoop (db : DB)(w : Keyword) :=
    k <-$ {0, 1}^lambda;
    t_entries <-$ compMap _ (L_cLoop k) (allNatsLt (length (lookupInds db w)));
    ret (w, t_entries).
    
  Definition L (db : DB)(q : list Query) :=
    bigT <-$ compMap _ (L_wLoop db) (toW db);
    s <- fst (unzip q);
    tSetAnswers <- map (lookupAnswers (pos (lambda + lambda))%nat bigT) s;
    ret (L_OXT db q, L_T bigT s, tSetAnswers ).

  Variable A_State : Set.
  Hypothesis A_State_EqDec : EqDec A_State.
  Variable A1 : Comp (DB * list Query * A_State).
  Variable A2 : A_State -> EDB -> list SearchTranscript -> Comp bool.

  Hypothesis A1_wf : well_formed_comp A1.
  Hypothesis A2_wf : forall x y z, well_formed_comp (A2 x y z).

  (* Step 1: simplify and put the game into the "Initialize" form of the paper. *)
   Definition Initialize_1 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (OXT_EDBSetup_wLoop db k_S k_I k_Z k_X) (toW db);
    [t_entries, xSet_raw] <-2 split wLoopRes;
    t <- combine (toW db) t_entries;
    xSet <- flatten xSet_raw;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    key <- (k_S, k_X, k_I, k_Z, k_T);
    searchRes <-$ compMap _ (OXT_Search edb key) q;
    ret (edb, searchRes).

   Definition G_gen (init : DB -> list Query -> Comp (EDB * (list (list (Bvector lambda) * SearchTranscript)))) :=
    [db, q, s_A] <-$3 A1;
    [edb, ls] <-$2 init db q;
    A2 s_A edb (snd (split ls)).

   Theorem G1_equiv :     
     Pr[SSE_Sec_NA_Real OXT_EDBSetup _ OXT_Search A1 A2 ] == Pr[G_gen Initialize_1].
   
     intuition.
     unfold SSE_Sec_NA_Real, G_gen.
     comp_skip.
     comp_simp.
     unfold Initialize_1, OXT_EDBSetup.
     do 7 (inline_first; comp_skip; comp_simp);
     reflexivity.

   Qed.

   
   (* Step 2: simplify and split some loops.  This gets us close to game G0 in the paper, except we still
look up answers in the real way. *)

  Definition Initialize_indLoop_2 k_I k_Z k_E w (e : Identifier lambda * nat) :=
    [ind, c] <-2 e;
    e <-$ Enc k_E ind;
    xind <- F_P k_I (Vector.to_list ind);
    z <- F_P k_Z (w ++ c);
    y <- xind * (inverse z);
    ret (Vector.append e (natToBvector y)).

  Definition Initialize_wLoop_2 db k_S k_I k_Z w :=
    inds <- lookupInds db w;
    sigma <-$ RndPerm (length inds);
    k_E <- F k_S w;
    indLoopRes <-$ compMap _ (Initialize_indLoop_2 k_I k_Z k_E w) (combine (permute inds sigma) (allNatsLt (length inds)));
    ret (indLoopRes, sigma).

  Definition XSetSetup_indLoop_2 k_X k_I w (ind : Bvector lambda) :=
    e <- F_P k_X w;
    xind <- F_P k_I (Vector.to_list ind);
    g^(e * xind).

  Definition XSetSetup_wLoop_2 k_X k_I db e :=
    [w, sigma] <-2 e;
    map (XSetSetup_indLoop_2 k_X k_I w) (permute (lookupInds db w) sigma).
    
  Definition XSetSetup_2 k_X k_I db sigmas :=
    flatten (map (XSetSetup_wLoop_2 k_X k_I db) (combine (toW db) sigmas)).

  Definition ServerSearchLoop_2 xSet e :=
    [xtoken, t_c] <-2 e;
    [e, y] <-2 splitVector lambda _ t_c;
    if (in_dec (EqDec_dec _) (xtoken^(bvectorToNat y)) xSet) then (Some e) else None.

  Definition ServerSearch_2 xSet (xtokens : list nat) t :=
    map (ServerSearchLoop_2 xSet) (combine xtokens t).

  Definition GenTrans_2 (edb : EDB) k_X k_Z k_S (e : Query * Tag) : (list (Identifier lambda) * SearchTranscript) :=
    [q, stag] <-2 e;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    t <- TSetRetrieve tSet stag;
    e <- F_P k_X x;
    xtokens <- map (fun (c : nat) => g^(e * (F_P k_Z (s ++ c)))) (allNatsLt (length t));
    res <- ServerSearch_2 xSet xtokens t;
    es <- getSomes res;
    k_E <- F k_S s;
    inds <- map (Dec k_E) es;
    (inds, (stag, (combine xtokens res))).

  Definition Initialize_2 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    stags <-$ compMap _ (TSetGetTag k_T) (fst (split q));
    searchRes <- map (GenTrans_2 edb k_X k_Z k_S) (combine q stags);
    ret (edb, searchRes).

  Definition G2 := G_gen Initialize_2.


(* Step 1.1: start splitting off the XSet computation. This will take a few steps and we'll start with the innermost loop. *)
   
  Definition Initialize_wLoop_1_1 db k_S k_I k_Z k_X w :=
    k_E <- F k_S w;
    inds <- lookupInds db w;
    sigma <-$ RndPerm (length inds);
    inds <- permute inds sigma; 
    indLoopRes <-$ compMap _ (Initialize_indLoop_2 k_I k_Z k_E w) (combine inds (allNatsLt (length inds)));
    xSet <- map (XSetSetup_indLoop_2 k_X k_I w) inds;
    ret (indLoopRes, xSet).

  Definition Initialize_1_1 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_1_1 db k_S k_I k_Z k_X) (toW db);
    [t_entries, xSet_raw] <-2 split wLoopRes;
    t <- combine (toW db) t_entries;
    xSet <- flatten xSet_raw;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    key <- (k_S, k_X, k_I, k_Z, k_T);
    searchRes <-$ compMap _ (OXT_Search edb key) q;
    ret (edb, searchRes).

  Theorem fst_split_eq_list_pred : 
    forall (A B : Set)(ls1 : list (A * B))(ls2 : list A),
      list_pred (fun a b => fst a = b) ls1 ls2 ->
      fst (split ls1) = ls2.
    
    induction 1; intuition; simpl in *.
    subst.
    destruct a1.
    remember (split ls1) as x.
    destruct x.
    simpl in *.
    f_equal.
  Qed.

  Theorem G1_1_equiv :
    Pr[G_gen Initialize_1] == Pr[G_gen Initialize_1_1].

    unfold G_gen, Initialize_1, Initialize_1_1.
    do 6 (comp_skip; comp_simp).
    eapply comp_spec_eq_impl_eq.
    eapply comp_spec_seq; eauto with inhabited.
    eapply compMap_spec.
    eapply list_pred_eq.
    intuition; subst.
    
    Theorem Init_wLoop_1_1_spec : 
      forall d x x1 x2 x0 b0,
      comp_spec eq 
                (OXT_EDBSetup_wLoop d x x1 x2 x0 b0)
                (Initialize_wLoop_1_1 d x x1 x2 x0 b0).

      intuition.
      unfold OXT_EDBSetup_wLoop, Initialize_wLoop_1_1.
      comp_simp.
      
      assert (comp_spec eq
     (inds <-$ shuffle (Bvector_EqDec lambda) (lookupInds d b0);
      indLoopRes <-$
      (foreach  (x3 in combine inds (allNatsLt (length inds)))
       OXT_EDBSetup_indLoop x1 x2 (F x b0) x0 b0 x3); 
      ret split indLoopRes)
     (inds <-$ (
       x <-$ RndPerm (length (lookupInds d b0)); ret permute (lookupInds d b0) x
     );
      indLoopRes <-$
      (foreach  (x3 in combine inds (allNatsLt (length inds)))
       OXT_EDBSetup_indLoop x1 x2 (F x b0) x0 b0 x3); 
      ret split indLoopRes)
     ).

      comp_skip.
      eapply shuffle_RndPerm_spec_eq.
      subst.
      eapply comp_spec_eq_refl.
      eapply comp_spec_eq_trans.
      eapply H.
      clear H.

      inline_first.
      comp_skip.
      
      comp_skip.
      eapply compMap_spec.
      eapply list_pred_eq.
      intuition; subst.

      Theorem Init_indLoop_2_spec : 
        forall x1 x2 x3 x0 b0 e,
          comp_spec (fun p1 p2 => fst p1 = p2)
                    (OXT_EDBSetup_indLoop x1 x2 x3 x0 b0 e)
                    (Initialize_indLoop_2 x1 x2 x3 b0 e).

        intuition.
        unfold OXT_EDBSetup_indLoop, Initialize_indLoop_2.
        comp_simp.
        comp_skip; try eapply (oneVector (lambda + lambda)).
        eapply comp_spec_ret; intuition.
      Qed.

      eapply Init_indLoop_2_spec.
      eapply comp_spec_ret; intuition.
     
      remember (split a) as z.
      destruct z.
      f_equal.
      assert (fst (split a) = b1).
      eapply fst_split_eq_list_pred .
      eauto.
      rewrite <- Heqz in H4.
      simpl in H4.
      trivial.
    
      eapply  (@compMap_support _ _ (fun z1 z2 => @snd (Bvector (lambda + lambda)) nat z2 = XSetSetup_indLoop_2 x0 x1 b0 (fst z1))) in H1.

      Theorem list_pred_fst_split_irr_gen : 
        forall (A B C : Set) (P : A -> C -> Prop) ls1 ls2 ,
          list_pred (fun (x : A * B)(y : C) => P (fst x) y) ls1 ls2 ->
          forall ls3, ls3 = fst (split ls1) -> 
          list_pred (fun (x : A)(y : C) => P x y) ls3 ls2.
        
        induction 1; intuition; simpl in *; subst.
        econstructor.
        destruct a1.
        remember (split ls1) as z.
        destruct z.
        simpl in *.
        econstructor.
        eauto.
        eapply IHlist_pred.
        intuition.
      Qed.

      Theorem list_pred_fst_split_irr : 
        forall (A B C : Set) (P : A -> C -> Prop) ls1 ls2 ,
          list_pred (fun (x : A * B)(y : C) => P (fst x) y) ls1 ls2 ->
          list_pred (fun (x : A)(y : C) => P x y) (fst (split ls1)) ls2.

        intuition.
        eapply list_pred_fst_split_irr_gen; eauto.

      Qed.

      Theorem list_pred_snd_split_irr_gen : 
        forall (A B C : Set) (P : B -> C -> Prop) ls1 ls2 ,
          list_pred (fun (x : A * B)(y : C) => P (snd x) y) ls1 ls2 ->
          forall ls3, ls3 = snd (split ls1) ->
          list_pred (fun (x : B)(y : C) => P x y) ls3 ls2.
        
        induction 1; intuition; simpl in *; subst.
        econstructor.
        destruct a1.
        remember (split ls1) as z.
        destruct z.
        simpl in *.
        econstructor.
        eauto.
        eapply IHlist_pred.
        intuition.
      Qed.


      Theorem list_pred_snd_split_irr : 
        forall (A B C : Set) (P : B -> C -> Prop) ls1 ls2 ,
          list_pred (fun (x : A * B)(y : C) => P (snd x) y) ls1 ls2 ->
          list_pred (fun (x : B)(y : C) => P x y) (snd (split ls1)) ls2.

        intuition.
        eapply list_pred_snd_split_irr_gen; eauto.
      Qed.

      Theorem snd_split_eq_map_list_pred : 
        forall (A B C : Set)(ls1 : list (A * C))(ls2 : list B)(f : B -> C),
          list_pred (fun a b => snd a = (f b)) ls1 ls2 ->
          snd (split ls1) = (map f ls2).
        
        induction 1; intuition; simpl in *.
        destruct a1.
        remember (split ls1) as x.
        destruct x.
        simpl in *.
        subst.
        f_equal.
      Qed.

      Show.
      assert (snd (split a) = (foreach  (x in permute (lookupInds d b0) b)
    XSetSetup_indLoop_2 x0 x1 b0 x)).
      eapply snd_split_eq_map_list_pred.
      eapply list_pred_symm.
      eapply list_pred_fst_split_irr_gen.
      eapply list_pred_impl.
      eapply H1.
      intuition.
      rewrite combine_split.
      simpl.
      trivial.
      rewrite allNatsLt_length.
      trivial.
      rewrite <- Heqz in H4.
      simpl in *.
      intuition.
      
      intuition.
      unfold OXT_EDBSetup_indLoop, XSetSetup_indLoop_2 in *.
      repeat simp_in_support.
      simpl.
      trivial.
    Qed.

    eapply Init_wLoop_1_1_spec.
    intuition.
    apply list_pred_eq_impl_eq in H6.
    subst.
    eapply comp_spec_eq_refl.
  Qed.

  (* Step 1.2: pull the XSet computation outside of the setup loop.  Start by putting it in the form where we can use loop fission. *)
  Definition Initialize_wLoop_1_2 db k_S k_I k_Z w :=
    k_E <- F k_S w;
    inds <- lookupInds db w;
    sigma <-$ RndPerm (length inds);
    inds <- permute inds sigma; 
    indLoopRes <-$ compMap _ (Initialize_indLoop_2 k_I k_Z k_E w) (combine inds (allNatsLt (length inds)));
    ret (w, indLoopRes, inds).

  Definition XSetSetup_wLoop_1_2 k_X k_I (e : Blist * list (Bvector (lambda + lambda)) * list (Bvector lambda)) :=
    [w, x, inds] <-3 e;
    r <- map (XSetSetup_indLoop_2 k_X k_I w) inds; 
    (x, r).

  Definition Initialize_1_2 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ (x <-$ compMap _ (Initialize_wLoop_1_2 db k_S k_I k_Z) (toW db);
                  ret (map (XSetSetup_wLoop_1_2 k_X k_I) x));
    [t_entries, xSet_raw] <-2 split wLoopRes;
    t <- combine (toW db) t_entries;
    xSet <- flatten xSet_raw;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    key <- (k_S, k_X, k_I, k_Z, k_T);
    searchRes <-$ compMap _ (OXT_Search edb key) q;
    ret (edb, searchRes).

  Theorem compMap_map_fission
     : forall (A B C : Set) (eqdb : EqDec B) 
         (eqdc : EqDec C) (ls : list A) (f1 : A -> Comp B) 
         (f2 : A -> Comp C) (f3 : B -> C),
       (forall a : A,
        comp_spec (fun (b : B) (c : C) => f3 b = c) (f1 a) (f2 a)) ->
       comp_spec eq
         (lsb <-$ compMap _ f1 ls; ret (map f3 lsb))
         (compMap _ f2 ls).
    
    induction ls; intuition; simpl in *.
    comp_simp.
    simpl.
    eapply comp_spec_eq_refl.

    inline_first.
    
    eapply comp_spec_seq; try eapply nil.
    eauto.
    intuition.
    subst.
    inline_first.

    assert ( comp_spec eq
     (a1 <-$ (foreach  (x in ls)f1 x);
      lsb <-$ ret a0 :: a1; ret (foreach  (x in lsb)f3 x))
     (a1 <-$ (foreach  (x in ls)f1 x);
      ret (foreach  (x in (a0 :: a1))f3 x))
     ).
    comp_skip.
    eapply comp_spec_eq_trans.
    eapply H2.
    clear H2.
    simpl.
    
    assert ( comp_spec eq
     (ls <-$ (a1 <-$ (foreach  (x in ls)f1 x); ret (map f3 a1)); ret f3 a0 :: ls)
     (lsb' <-$ (foreach  (x in ls)f2 x); ret f3 a0 :: lsb')).

    eapply comp_spec_seq_eq; try eapply nil.
    eapply IHls.
    intuition.
    intuition.
    eapply comp_spec_eq_trans_r.
    Focus 2.
    eapply H2.
    clear H2.
    inline_first.
    comp_skip.
    comp_simp.
    eapply comp_spec_eq_refl.
  Qed.


  Theorem G_1_2_equiv : 
    Pr[G_gen Initialize_1_1] == Pr[G_gen Initialize_1_2].

    unfold G_gen, Initialize_1_1, Initialize_1_2.
    do 6 (comp_skip; comp_simp).
    eapply comp_spec_eq_impl_eq.
    eapply comp_spec_seq_eq; eauto with inhabited.

    eapply comp_spec_eq_symm.
    eapply compMap_map_fission.
    intuition.
    unfold Initialize_wLoop_1_1, Initialize_wLoop_1_2,  XSetSetup_wLoop_1_2.
    comp_simp.
    comp_skip.
    comp_skip.
    eapply comp_spec_ret; intuition.

    intuition.
    eapply comp_spec_eq_refl.
  Qed.

  (* Step 1.3: Now simplify and take the game out of the form of the loop fission argument*)
  Definition Initialize_wLoop_1_3 db k_S k_I k_Z w :=
    k_E <- F k_S w;
    inds <- lookupInds db w;
    sigma <-$ RndPerm (length inds);
    inds <- permute inds sigma; 
    indLoopRes <-$ compMap _ (Initialize_indLoop_2 k_I k_Z k_E w) (combine inds (allNatsLt (length inds)));
    ret (indLoopRes, inds).

  Definition XSetSetup_wLoop_1_3 k_X k_I e :=
    [w, inds] <-2 e;
    map (XSetSetup_indLoop_2 k_X k_I w) inds.

  Definition Initialize_1_3 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_1_3 db k_S k_I k_Z) (toW db);
    [t_entries, inds] <-2 split wLoopRes;
    xSet_raw <- map (XSetSetup_wLoop_1_3 k_X k_I) (combine (toW db) inds);
    t <- combine (toW db) t_entries;
    xSet <- flatten xSet_raw;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    key <- (k_S, k_X, k_I, k_Z, k_T);
    searchRes <-$ compMap _ (OXT_Search edb key) q;
    ret (edb, searchRes).

  Theorem G_1_3_equiv : 
    Pr[G_gen Initialize_1_2] == Pr[G_gen Initialize_1_3].
    
    unfold G_gen, Initialize_1_2, Initialize_1_3.
    do 6 (comp_skip; comp_simp).
    inline_first.
    eapply comp_spec_eq_impl_eq.
    eapply comp_spec_seq; eauto with inhabited.
    eapply compMap_spec.
    eapply list_pred_eq.
    intuition; subst.
    
    Theorem Init_wLoop_equiv_1_3 : 
      forall d x x1 x2 b0,
      comp_spec (fun a1 a2 => snd (fst a1) = fst a2 /\ snd a1 = snd a2)
                (Initialize_wLoop_1_2 d x x1 x2 b0)
                (Initialize_wLoop_1_3 d x x1 x2 b0).

      intuition.

      unfold Initialize_wLoop_1_2, Initialize_wLoop_1_3.
      comp_simp.
      comp_skip.
      comp_skip.
      eapply comp_spec_ret; intuition.

    Qed.

    eapply Init_wLoop_equiv_1_3.
    intuition.
    comp_ret_l.
    remember (split (map (XSetSetup_wLoop_1_2 x0 x1) a1)) as z.
    destruct z.
    remember (split b0) as z.
    destruct z.

    
    Theorem XSetSetup_wLoop_1_2_fst_eq : 
      forall a1 x0 x1,
        fst (split (map (XSetSetup_wLoop_1_2 x0 x1) a1)) = snd (split (fst (split a1))).

      induction a1; intuition; simpl in *.
      remember (split (foreach  (x in a1)XSetSetup_wLoop_1_2 x0 x1 x))as z.
      destruct z.
      remember (split a1) as z.
      destruct z.
      simpl.
      remember (split l1) as z.
      destruct z.
      simpl.
      f_equal.
      assert (l = (fst (split (foreach  (x in a1)XSetSetup_wLoop_1_2 x0 x1 x)))).
      rewrite <- Heqz.
      trivial.
      subst.
      rewrite IHa1.
      simpl.
      rewrite <- Heqz1.
      trivial.
    Qed.

    Show.
    assert (l0 = l2).
    assert (l0 = fst (split (map (XSetSetup_wLoop_1_2 x0 x1) a1))).
    rewrite <- Heqz.
    trivial.
    subst.
    rewrite XSetSetup_wLoop_1_2_fst_eq.

    assert (fst (split b0) = l2).
    rewrite <- Heqz0.
    trivial.
    subst.

   
     Ltac split_eq_one  := 
       match goal with
      | [|- _ = _] =>  eapply list_pred_eq_impl_eq
      | [|- list_pred _ (fst (split _)) _ ] => eapply list_pred_fst_split_irr
      | [|- list_pred _ (snd (split _)) _ ] => eapply list_pred_snd_split_irr
      | [|- list_pred _ _ (fst (split _)) ] => eapply list_pred_symm; split_eq_one; eapply list_pred_symm
      | [|- list_pred _ _ (snd (split _)) ] => eapply list_pred_symm; split_eq_one; eapply list_pred_symm
     end.

     Ltac split_eq := repeat split_eq_one.

     split_eq.
     eapply list_pred_impl.
     eauto.
     intuition.

     subst.
     comp_skip.
     comp_skip.
     eapply compMap_spec.
     eapply list_pred_eq.
     intuition; subst.

     Theorem comp_spec_eq_refl_gen : 
       forall (A : Set)(eqd : EqDec A)(c1 c2 : Comp A),
         c1 = c2 ->
         comp_spec eq c1 c2.

       intuition; subst.
       eapply comp_spec_eq_refl.

     Qed.

     eapply comp_spec_eq_refl_gen.
     f_equal.
     f_equal.
     f_equal.

     Ltac split_subst :=
       match goal with
       | [H : (_, ?b) = split ?ls |- context[?b] ] => assert (b = (snd (split ls))); [rewrite <- H; trivial | idtac]; subst
       | [H : (?a, _) = split ?ls |- context[?a] ] => assert (a = (fst (split ls))); [rewrite <- H; trivial | idtac]; subst
     end.

     split_subst.
     split_eq.

     eapply (@list_pred_impl _ _ _ _ (fun a b => snd a = b)).

     Theorem list_pred_map_both':
       forall (A B C D: Set) (lsa : list A) (lsb : list B) 
              (P : C -> D -> Prop) (f1 : A -> C)(f2 : B -> D),
         list_pred (fun (a : A) (b : B) => P (f1 a) (f2 b)) lsa lsb ->
         list_pred P (map f1 lsa) (map f2 lsb).

       induction 1; intuition; simpl in *.
       econstructor.
       econstructor; eauto.

     Qed.
            
     eapply (list_pred_map_both').
     
     Theorem list_pred_combine_l_h : 
       forall (A C : Set)(lsa : list A)(lsc : list C) P1,
         list_pred P1 lsa lsc ->
         forall (B : Set)(lsb : list B) P2, 
         list_pred P2 lsb lsc ->
         list_pred (fun p c => P1 (fst p) c /\ P2 (snd p) c) (combine lsa lsb) lsc.

       induction 1; intuition; simpl in *.
       econstructor.
       inversion H1; clear H1; subst.
       econstructor.
       intuition.

       eauto.

     Qed.

     Theorem list_pred_combine_l : 
       forall (A B C : Set)P1 P2 (lsa : list A)(lsb : list B)(lsc : list C),
         list_pred P1 lsa lsc -> 
         list_pred P2 lsb lsc ->
         list_pred (fun p c => P1 (fst p) c /\ P2 (snd p) c) (combine lsa lsb) lsc.
       
       intuition.
       eapply list_pred_combine_l_h; eauto.
       
     Qed.


     eapply list_pred_symm.
     eapply (@list_pred_impl).

     eapply (@list_pred_combine_l _ _ _ _ (fun a b => a = snd b)). 
    
     eapply (compMap_support (fun a b => fst (fst b) = a)).
     eapply H4.
     intuition.
     unfold Initialize_wLoop_1_2 in *.
     repeat simp_in_support.
     trivial.     

     split_subst.
     eapply (@list_pred_impl _ _ _ _ (fun a b => a = snd b)).
     split_eq.
     eapply list_pred_symm.
     eapply (@list_pred_impl).
     eapply H6.
     intuition.
     intuition.

     intuition.
     simpl in *; subst.
     unfold XSetSetup_wLoop_1_2.
     comp_simp.
     simpl.
     trivial.

     intuition.
     eapply comp_spec_ret; intuition.
     f_equal.
     f_equal.
     f_equal.
     split_subst.
     split_eq.
     eapply list_pred_map_both'.
     eapply list_pred_symm.
     eapply list_pred_impl.
     eapply (@list_pred_combine_l _ _ _ _ (fun a b => a = snd b)). 
     eapply (compMap_support (fun a b => fst (fst b) = a)).
     eapply H4.
     intuition.
     unfold Initialize_wLoop_1_2 in *.
     repeat simp_in_support.
     trivial.     

     split_subst.
     eapply (@list_pred_impl _ _ _ _ (fun a b => a = snd b)).
     split_eq.
     eapply list_pred_symm.
     eapply (@list_pred_impl).
     eapply H6.
     intuition.
     intuition.
     intuition.
     simpl in *; subst.
     unfold XSetSetup_wLoop_1_2.
     comp_simp.
     trivial.
     
     eapply list_pred_eq_impl_eq.
     trivial.

  Qed.

  (* Step 1.4: have the setup routine return permutations instead of indices.  Start by returning both. *)
  Definition Initialize_wLoop_1_4 db k_S k_I k_Z w :=
    k_E <- F k_S w;
    inds <- lookupInds db w;
    sigma <-$ RndPerm (length inds);
    inds <- permute inds sigma; 
    indLoopRes <-$ compMap _ (Initialize_indLoop_2 k_I k_Z k_E w) (combine inds (allNatsLt (length inds)));
    ret (indLoopRes, inds, sigma).

  Definition Initialize_1_4 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_1_4 db k_S k_I k_Z) (toW db);
    [t_inds, sigmas] <-2 split wLoopRes;
    [t_entries, inds] <-2 split t_inds;
    xSet_raw <- map (XSetSetup_wLoop_1_3 k_X k_I) (combine (toW db) inds);
    t <- combine (toW db) t_entries;
    xSet <- flatten xSet_raw;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    key <- (k_S, k_X, k_I, k_Z, k_T);
    searchRes <-$ compMap _ (OXT_Search edb key) q;
    ret (edb, searchRes).

  Theorem G_1_4_equiv : 
    Pr[G_gen Initialize_1_3] == Pr[G_gen Initialize_1_4].

    unfold G_gen, Initialize_1_3, Initialize_1_4.
    do 6 (comp_skip; comp_simp).
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply compMap_spec.
    eapply list_pred_eq.
    intuition; subst.
    
     Theorem Init_wLoop_1_4_spec : 
      forall d x x1 x2 b0,
      comp_spec (fun a b => fst a = fst (fst b) /\ snd a = snd (fst b))
                (Initialize_wLoop_1_3 d x x1 x2 b0)
                (Initialize_wLoop_1_4 d x x1 x2 b0).

       intuition.
       unfold Initialize_wLoop_1_3, Initialize_wLoop_1_4.
       comp_simp.
       comp_skip.
       comp_skip.
       eapply comp_spec_ret; intuition.

     Qed.

     eapply Init_wLoop_1_4_spec.
     remember (split a1) as z.
     destruct z.
     remember ( split b0)as z.
     destruct z.
     remember ( split l2) as z.
     destruct z.
     assert (l0 = l4).
     do 3 (split_subst; split_eq).
     eapply list_pred_impl.
     eauto.
     intuition.
     subst.
     comp_skip.
     assert (l1 = l5).
     do 3 (split_subst; split_eq).
     eapply list_pred_impl.
     eauto.
     intuition.
     subst.
     
     intuition.

  Qed.

  (* Step 1.5: Now remove the indices and just use the permutations *)
  Definition Initialize_1_5 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet_raw <- map (XSetSetup_wLoop_2 k_X k_I db) (combine (toW db) sigmas);
    t <- combine (toW db) t_entries;
    xSet <- flatten xSet_raw;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    key <- (k_S, k_X, k_I, k_Z, k_T);
    searchRes <-$ compMap _ (OXT_Search edb key) q;
    ret (edb, searchRes).

  Theorem G_1_5_equiv : 
    Pr[G_gen Initialize_1_4] == Pr[G_gen Initialize_1_5].

    unfold G_gen, Initialize_1_4, Initialize_1_5.
    do 6 (comp_skip; comp_simp).
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply compMap_spec.
    eapply list_pred_eq.
    intuition; subst.
    
    Theorem Init_wLoop_2_spec : 
      forall d x x1 x2 b0,
      comp_spec (fun a b => fst (fst a) = fst b /\ snd a = snd b)
                (Initialize_wLoop_1_4 d x x1 x2 b0)
                (Initialize_wLoop_2 d x x1 x2 b0).

      intuition.
      unfold Initialize_wLoop_1_4, Initialize_wLoop_2.
      comp_simp.
      comp_skip.
      comp_skip.
      rewrite permute_length_eq.
      apply RndPerm_In_support_length in H0.
      rewrite H0.
      eapply comp_spec_eq_refl.
      intuition.
      eapply allNatsLt_lt.

      Require Import Permutation.

      eapply Permutation_in.
      eapply Permutation_sym.
      eapply RndPerm_In_support.
      eauto.
      trivial.
      subst.

      eapply comp_spec_ret; intuition.
      
    Qed.

    eapply Init_wLoop_2_spec.
    remember (split a1) as z.
    destruct z.
    remember (split l0) as z.
    destruct z.
    remember (split b0) as z.
    destruct z.

    assert (l2 = l4).
    do 3 (split_subst; split_eq).
    eapply list_pred_impl.
    eauto.
    intuition.
    subst.
    comp_skip.

    assert (l1 = l5).
    do 2 (split_subst; split_eq).
    eapply list_pred_impl.
    eauto.
    intuition.
    subst.

    assert (map (XSetSetup_wLoop_1_3 x0 x1) (combine (toW d) l3) = 
            (map (XSetSetup_wLoop_2 x0 x1 d) (combine (toW d) l5))).
   
    eapply (compMap_support (fun a b => snd (fst b) = permute (lookupInds d a) (snd b))) in H4.
    
    Theorem map_ext_pred : 
      forall (A B C : Set)(P : A -> B -> Prop)(lsa : list A)(lsb : list B)(f1 : A -> C)(f2 : B -> C),
        list_pred P lsa lsb ->
        (forall a b, P a b -> (f1 a) = (f2 b)) ->
        map f1 lsa = map f2 lsb.

      induction 1; intuition; simpl in *.
      f_equal; intuition.
      
    Qed.

    eapply (@map_ext_pred _ _ _ (fun a b => fst a = fst b /\ snd a = permute (lookupInds d (fst a)) (snd b))).
    

    Theorem list_pred_combine_same : 
      forall (A B C : Set)(P : A -> (B * C) -> Prop)(lsa : list A)(lsb : list B)(lsc : list C),
        list_pred P lsa (combine lsb lsc) ->
        length lsb = length lsc ->
        list_pred (fun p1 p2 => fst p1 = fst p2 /\ P (fst p1) (snd p1, snd p2))
                  (combine lsa lsb)
                  (combine lsa lsc).

      induction lsa; intuition; simpl in *.
      econstructor.

      inversion H; subst; clear H.

      destruct lsb; destruct lsc; simpl in *; try congruence.
      inversion H3; clear H3; subst.
      econstructor.

      simpl; intuition.
      eauto.

    Qed.


    eapply list_pred_impl.
    eapply (@list_pred_combine_same _ _ _ (fun a2 b2 => (fst b2) = permute (lookupInds d a2) (snd b2))).
    assert (combine l3 l5 = map (fun z => (snd (fst z), snd z)) a1).

    Theorem combine_eq_map_1_3 : 
      forall (A B C : Set)(a : list (A * B * C))(l1 : list B)(l2 : list C),
        l1 = snd (split (fst (split a))) ->
        l2 = snd (split a) ->
        combine l1 l2 = map (fun p => (snd (fst p), snd p)) a.

      induction a; intuition; subst; simpl in *.
      trivial.

      remember (split a0 )as z.
      destruct z.
      simpl.
      remember (split l) as z.
      destruct z.
      simpl.
      f_equal.
      eapply IHa.

      simpl.
      rewrite <- Heqz0.
      trivial.
      trivial.
    Qed.

    eapply combine_eq_map_1_3.
    do 2 (split_subst; split_eq).
    eapply list_pred_impl.
    eapply list_pred_eq.
    intuition.
    subst; trivial.

    (split_subst; split_eq).
    eapply list_pred_impl.
    eapply list_pred_eq.
    intuition.
    subst; trivial.

    rewrite H9.
    eapply list_pred_map_r'.
    eapply list_pred_impl.
    eapply H4.
    intuition.

    repeat (split_subst; try rewrite split_length_l; try rewrite split_length_r); trivial.

    intuition.
    intuition.
    simpl in *; subst.
    intuition.

    intuition.
    unfold Initialize_wLoop_1_4 in *.
    repeat simp_in_support.
    trivial.

    rewrite H9.
    eapply comp_spec_eq_refl.
  Qed.


  (* Step 1.6: Now we factor out the tag computation. I did this without using the loop fission argument for some reason. *)

  Definition Initialize_1_6 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet_raw <- map (XSetSetup_wLoop_2 k_X k_I db) (combine (toW db) sigmas);
    t <- combine (toW db) t_entries;
    xSet <- flatten xSet_raw;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    key <- (k_S, k_X, k_I, k_Z, k_T);
    searchRes <-$ 
              (ls <-$ compMap _ (fun p => z <-$ TSetGetTag k_T (fst p); ret (p, z)) q;
               ret (map (GenTrans_2 edb k_X k_Z k_S) ls));
    ret (edb, searchRes).

  Theorem G_1_6_equiv : 
    Pr[G_gen Initialize_1_5] == Pr[G_gen Initialize_1_6].

    unfold G_gen, Initialize_1_5, Initialize_1_6.
    do 9 (comp_skip; comp_simp).
    eapply comp_spec_eq_impl_eq.
    eapply comp_spec_eq_symm.
    eapply compMap_map_fission.
    intuition.

    unfold OXT_Search.
    unfold OXT_Search_ClientInit.
    comp_simp.
    simpl.

    comp_skip.
    eapply comp_base_exists; eauto.
    eapply comp_base_exists; eauto.

    eapply comp_spec_ret; intuition.
    unfold GenTrans_2.
    comp_simp.
    unfold ServerSearch_2.
    f_equal.
    f_equal.
    f_equal.
    
    split_eq.
    eapply list_pred_map_both'.
    
    Theorem list_pred_combine_simple : 
      forall (A B C D : Set)(P1 : A -> C -> Prop)(P2 : B -> D -> Prop) lsa lsb lsc lsd,
        list_pred P1 lsa lsc ->
        list_pred P2 lsb lsd ->
        length lsa = length lsb ->
        list_pred (fun x1 x2 => P1 (fst x1) (fst x2) /\ P2 (snd x1) (snd x2))
                  (combine lsa lsb)
                  (combine lsc lsd).

      induction lsa; intuition; simpl in *.
      inversion H; clear H; subst.
      simpl.
      econstructor.

      destruct lsb; simpl in *; try discriminate.
      
      inversion H; clear H; subst.
      inversion H0; clear H0; subst.
      simpl.
      econstructor; simpl in *; eauto.

    Qed.

    Show.
    eapply list_pred_impl.
    eapply (@list_pred_combine_simple _ _ _ _ (fun (a c : nat) => a = g ^ (F_P x0 k0 * F_P x2 (k ++ c))) eq).
    eapply list_pred_map_l'.
    eapply list_pred_impl.
    eapply list_pred_eq.
    intuition; subst; intuition.
    eapply list_pred_eq.
    rewrite map_length.
    eapply allNatsLt_length.

    intuition.
    unfold ServerSearchLoop_2, OXT_Search_Loop.
    unfold OXT_Search_Loop_Client, OXT_Search_Loop_Server, computeXToken.
    simpl in *; subst.
    destruct b2.
    simpl.
    comp_simp.
    rewrite mult_comm.
    trivial.

    f_equal.

    Theorem combine_map_eq : 
      forall (A B C D : Type)(f1 : A -> B)(f2 : C -> D) ls1 ls2,
        (length ls1 = length ls2) ->
      combine (map f1 ls1) (map f2 ls2) = map (fun p => (f1 (fst p),  f2 (snd p))) (combine ls1 ls2).

      induction ls1; destruct ls2; intuition; simpl in *.
      f_equal; eauto.

    Qed.

    rewrite combine_map_eq.
    
    eapply (@map_ext_pred _ _ _ (fun (a : nat * (nat * Bvector (lambda + lambda))) b => fst a = fst b /\ snd (snd a) = snd b 
                                            /\ fst (snd a) = (g ^ (F_P x2 (k ++ (fst b)) * F_P x0 k0))  )).

    Theorem list_pred_combine_same'
    : forall (A B C : Set) (P : A * B -> A * C -> Prop) 
             (lsa : list A) (lsb : list B) (lsc : list C),
        list_pred (fun a p => P (a, fst p) (a, snd p)) lsa (combine lsb lsc) ->
        length lsb = length lsc ->
        list_pred
          P
          (combine lsa lsb) (combine lsa lsc).
      
      induction lsa; intuition; simpl in *.
      econstructor.

      destruct lsb; destruct lsc; simpl in *; try discriminate.
      econstructor.

      inversion H; clear H; subst.
      econstructor; eauto.

    Qed.
    
    intuition.
    eapply list_pred_combine_same'.
    eapply list_pred_symm.
    

    Theorem list_pred_combine_assoc_l : 
      forall (A B C D : Set)(P : (A * B) * C -> D -> Prop) lsa lsb lsc lsd, 
      list_pred (fun p d => P ((fst p, fst (snd p)), snd (snd p)) d)
                (combine lsa (combine lsb lsc)) 
                lsd ->
      list_pred P
                (combine (combine lsa lsb) lsc) 
                lsd.

      induction lsa; intuition; simpl in *.
      inversion H; clear H; subst.
      econstructor.

      destruct lsb; simpl in *.
      inversion H; clear H; subst.
      econstructor.

      destruct lsc; simpl in *.
      inversion H; clear H; subst.
      econstructor.

      inversion H; clear H; subst.
      econstructor.
      simpl in *; trivial.
      
      eauto.

    Qed.

    eapply list_pred_combine_assoc_l.

    assert (list_pred (fun (b : (nat * (Bvector (lambda + lambda) * (Bvector (lambda + lambda))))) (a : nat)  => fst b = (g ^ (F_P x0 k0 * F_P x2 (k ++ a))) /\ fst (snd b) = snd (snd b))                    
     (combine
        (for  (c '< length (TSetRetrieve t b0))
              g ^ (F_P x0 k0 * F_P x2 (k ++ (natToBlist c)))) 
        (combine (TSetRetrieve t b0) (TSetRetrieve t b0)))
     (allNatsLt (length (TSetRetrieve t b0)))
           ).

    eapply list_pred_impl.

    eapply (@list_pred_combine_l _ _ _ (fun (a : nat) (b : nat) => a = g ^ (F_P x0 k0 * F_P x2 (k ++ b))) (fun a b => fst a = snd a)); intuition.
    eapply list_pred_map_l'.
    eapply list_pred_impl.
    eapply list_pred_eq.
    intuition; subst; intuition.

    Theorem list_pred_combine_same_l : 
      forall (A B : Set)(P : A -> B -> Prop) lsa lsb,
        list_pred P lsa lsb ->
        list_pred (fun p b => fst p = snd p /\ (P (fst p) b)) (combine lsa lsa) lsb.

      induction lsa; intuition; simpl in *.
      inversion H; clear H; subst.
      econstructor.

      inversion H; clear H; subst.
      econstructor; eauto.

    Qed.

    eapply list_pred_impl.
    eapply list_pred_combine_same_l.
    eapply list_pred_I.
    symmetry.
    eapply allNatsLt_length.
    intuition.
    intuition.
    
    eapply list_pred_impl.
    eapply H8.
    intuition.
    simpl in *.
    subst.
    rewrite mult_comm.
    trivial.

    rewrite combine_length.
    rewrite Min.min_l.
    rewrite map_length.
    eapply allNatsLt_length.
    rewrite map_length.
    rewrite allNatsLt_length.
    intuition.

    intuition.
    simpl in *; subst; intuition.
    intuition.
    unfold ServerSearchLoop_2, OXT_Search_Loop,  OXT_Search_Loop_Client, computeXToken.
    simpl.
    comp_simp.
    f_equal.
    rewrite mult_comm.
    trivial.

    rewrite combine_length.
    rewrite Min.min_l.
    rewrite map_length.
    trivial.
    rewrite map_length.
    rewrite allNatsLt_length.
    intuition.
  Qed.

  (* We get G2 by simplification *)
  Theorem G2_equiv : 
    Pr[G_gen Initialize_1_6] == Pr[G2].

    unfold G2, G_gen, Initialize_1_6, Initialize_2.
    do 8 (comp_skip; comp_simp).
    inline_first.
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply (@compMap_spec _ _ _ _ _ _ (fun a b => fst a = b) (fun a b => snd a = b)).
    split_eq.
    eapply list_pred_impl.
    eapply list_pred_eq.
    intuition.
    subst.
    trivial.
    intuition.
    subst.
    eapply comp_spec_symm.
    eapply comp_spec_eq_trans_l.
    eapply comp_spec_symm.
    eapply comp_spec_consequence.
    eapply comp_spec_right_ident.
    intuition.
    eapply comp_spec_seq_eq.
    eapply comp_base_exists; eauto.
    intuition.
    eapply comp_base_exists; eauto.
    eapply comp_spec_eq_refl.
    intuition.
    eapply comp_spec_ret; intuition.

    eapply comp_spec_ret; intuition.
    f_equal.

    eapply (@compMap_support _ _ (fun a b => (fst b) = a)) in H6.
    
    eapply (@map_ext_pred _ _ _ eq).
    eapply list_pred_symm.
    eapply list_pred_impl.
    eapply list_pred_combine_l.
    eapply H6.
    eapply list_pred_symm.
    eapply H8.
    intuition.
    simpl in *; subst.
    destruct b2; trivial.
    
    intuition; subst.
    trivial.
    
    intuition.
    repeat simp_in_support.
    trivial.

  Qed.

  (* Step 3 : replace the TSetRetrieve and use the actual values instead.  We make this transformation by applying the TSet correctness definition. *)
  Definition GenTrans_3 (edb : EDB) k_X k_Z k_S (e : Query * (Tag * list (Bvector (lambda + lambda)))) : (list (Identifier lambda) * SearchTranscript) :=
    [q, stag_t] <-2 e;
    [stag, t] <-2 stag_t;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    e <- F_P k_X x;
    xtokens <- map (fun (c : nat) => g^(e * (F_P k_Z (s ++ c)))) (allNatsLt (length t));
    res <- ServerSearch_2 xSet xtokens t;
    es <- getSomes res;
    k_E <- F k_S s;
    inds <- map (Dec k_E) es;
    (inds, (stag, (combine xtokens res))).

  Definition Initialize_3 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    stags_ts <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_3 edb k_X k_Z k_S) (combine q stags_ts);
    ret (edb, searchRes).

  Definition G3 := G_gen Initialize_3.

  (*Step 2.1: factor the TSetRetrieve out into the main loop. *)
  Definition Initialize_2_1 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    stags <-$ compMap _ (TSetGetTag k_T) (fst (split q));
    ts <- map (TSetRetrieve tSet) stags;
    stags_ts <- combine stags ts;
    searchRes <- map (GenTrans_3 edb k_X k_Z k_S) (combine q stags_ts);
    ret (edb, searchRes).


  Theorem G2_1_equiv : 
    Pr[G2] == Pr[G_gen Initialize_2_1].

    unfold G2, G_gen, Initialize_2, Initialize_2_1.
    do 9 (comp_skip; comp_simp).
    eapply evalDist_ret_eq.
    f_equal.
    eapply (@map_ext_pred).

    eapply (@list_pred_combine_simple _ _  _ _ eq (fun b a => fst a = b /\ snd a = TSetRetrieve t b)).
    eapply list_pred_eq.
    eapply list_pred_symm.
    eapply (@list_pred_impl _ _ _ _ (fun a b => fst a = b /\ snd a = TSetRetrieve t b)).
    eapply (@list_pred_combine_l _ _ _ eq (fun a b => a = TSetRetrieve t b)).
    eapply list_pred_eq.
    eapply list_pred_map_l'.
    eapply list_pred_impl.
    eapply list_pred_eq.
    intuition.
    subst; trivial.

    intuition.
    apply compMap_length in H6.
    rewrite H6.
    symmetry.
    eapply split_length_l.

    intuition.
    simpl in *; subst.
    unfold GenTrans_3.
    destruct b1.
    destruct p0.
    simpl in *.
    subst.
    trivial.

  Qed.
  

  (*Step 2.2: We will use an identical until bad argument.  Make the badness from the top-level game. *)
  Definition G2_2 :=
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    stags <-$ compMap _ (TSetGetTag k_T) (fst (split q));
    ts <- map (TSetRetrieve tSet) stags;
    correct_ts <- map (arrayLookupList _ t) (fst (split q));
    stags_ts <- combine stags ts;
    searchRes <- map (GenTrans_3 edb k_X k_Z k_S) (combine q stags_ts);
    b <-$ A2 s_A edb (snd (split searchRes));
    ret (b, negb (eqb ts correct_ts)).

  Theorem G2_2_equiv : 
    Pr[G_gen Initialize_2_1] == Pr[p <-$ G2_2; ret fst p].

    unfold G_gen, Initialize_2_1, G2_2.
    repeat (inline_first; comp_skip; comp_simp).
    inline_first.
    rewrite <- evalDist_right_ident.
    comp_skip.
    reflexivity.
    comp_simp.
    simpl.
    intuition.
  Qed.


    (*Step 2.3: switch over to the actual values*)
  Definition G2_3 :=
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    stags <-$ compMap _ (TSetGetTag k_T) (fst (split q));
    ts <- map (TSetRetrieve tSet) stags;
    correct_ts <- map (arrayLookupList _ t) (fst (split q));
    stags_ts <- combine stags correct_ts;
    searchRes <- map (GenTrans_3 edb k_X k_Z k_S) (combine q stags_ts);
    b <-$ A2 s_A edb (snd (split searchRes));
    ret (b, negb (eqb ts correct_ts)).

  Theorem G2_2_3_badness_eq : 
     Pr  [a <-$ G2_2; ret snd a ] == Pr  [a <-$ G2_3; ret snd a ].

    unfold G2_2, G2_3.
    do 8 (inline_first ; comp_skip; comp_simp).
    inline_first.
    comp_irr_l.
    comp_irr_r.

    comp_simp.
    simpl.
    intuition.
 
  Qed.

  Theorem G2_2_3_eq_until_bad : forall x,
    evalDist (a <-$ G2_2; ret (fst a, snd a)) (x, false) ==
   evalDist (a <-$ G2_3; ret (fst a, snd a)) (x, false).

    intuition.
    unfold G2_2, G2_3.
    
    do 8 (inline_first ; comp_skip; comp_simp).
    case_eq ((eqb (map (TSetRetrieve t) x5)
                (map
                   (arrayLookupList (list_EqDec bool_EqDec)
                      (combine (toW d) l0)) (fst (split l))))); intuition.

    rewrite eqb_leibniz in H7.
    repeat rewrite H7.
    reflexivity.

    inline_first.
    comp_irr_l.
    comp_irr_r.
    comp_simp.
    repeat rewrite evalDist_ret_0; intuition.

    pairInv.
    apply negb_false_iff in H13.
    rewrite eqb_leibniz in H13.
    rewrite H13 in H7.
    rewrite eqb_refl in H7.
    discriminate.
    
    pairInv.
    apply negb_false_iff in H13.
    rewrite eqb_leibniz in H13.
    rewrite H13 in H7.
    rewrite eqb_refl in H7.
    discriminate.
  Qed.
   
  Theorem G2_3_equiv : 
    | Pr[x <-$ G2_2; ret fst x] - Pr[x <-$ G2_3; ret fst x] | 
    <= Pr[x <-$ G2_2; ret snd x].

    eapply fundamental_lemma; intuition.
    eapply G2_2_3_badness_eq.
    eapply  G2_2_3_eq_until_bad.

  Qed.


  (* Now we need to show that the bad event is related to TSet correctness.  Put the game in the correct form.   *)
  Definition TSetCorA := 
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    t <- combine (toW db) t_entries;
    ret (t, (fst (split q))).

  Definition G2_2_bad1 :=
    [t, q] <-$2 TSetCorA;
    [tSet, k_T] <-$2 TSetSetup t;
    stags <-$ compMap _ (TSetGetTag k_T) q;
    ts <- map (TSetRetrieve tSet) stags;
    correct_ts <- map (arrayLookupList _ t) q;
    ret (negb (eqb ts correct_ts)).

  Theorem G2_2_bad1_equiv : 
    Pr[x <-$ G2_2; ret snd x] ==
    Pr[G2_2_bad1].

    unfold G2_2_bad1, TSetCorA, G2_2.
    do 2 (inline_first; comp_skip; comp_simp).
    comp_inline_l.
    comp_irr_l; wftac.
    do 5 (inline_first; comp_skip; comp_simp).

    comp_inline_l.
    comp_irr_l.
    eapply evalDist_ret_eq; simpl; intuition.
  Qed.

  Theorem G2_2_bad1_TSetCor : 
    Pr[G2_2_bad1] == Pr[AdvCor _ TSetSetup TSetGetTag TSetRetrieve TSetCorA].

    unfold G2_2_bad1, TSetCorA, AdvCor.

    repeat (inline_first; comp_skip; comp_simp).
    (* doesn't quite work because the definition only allows the adversary
to provide a set. *)
    (* I need to do more work on this, but I may change the definition anyway when I 
use the TSet later.  *)

  Admitted.

  (* remove the badness and move some things around to get G3 *)
  Theorem G3_equiv : 
    Pr[x <-$ G2_3; ret fst x] == Pr[G3].

    unfold G2_3, G3, G_gen, Initialize_3.
    (* There is some loop fission in here, but otherwise they are identical *)

  Admitted.


  Theorem G2_G3_close : 
    | Pr[G2] - Pr[G3] | <=  Pr[AdvCor _ TSetSetup TSetGetTag TSetRetrieve TSetCorA].

    rewrite G2_1_equiv.
    rewrite G2_2_equiv.
    rewrite <- G3_equiv.
    rewrite G2_3_equiv.
    rewrite G2_2_bad1_equiv.
    rewrite G2_2_bad1_TSetCor.
    intuition.
  Qed.

  (* Step 4: Give the plaintexts to GenTrans and remove the decryption.*)
    Definition Initialize_indLoop_4 k_I k_Z k_E w (e : Identifier lambda * nat) :=
    [ind, c] <-2 e;
    e <-$ Enc k_E ind;
    xind <- F_P k_I (Vector.to_list ind);
    z <- F_P k_Z (w ++ c);
    y <- xind * (inverse z);
    ret (Vector.append e (natToBvector y), ind).

  Definition Initialize_wLoop_4 db k_S k_I k_Z w :=
    inds <- lookupInds db w;
    sigma <-$ RndPerm (length inds);
    k_E <- F k_S w;
    indLoopRes <-$ compMap _ (Initialize_indLoop_4 k_I k_Z k_E w) (combine (permute inds sigma) (allNatsLt (length inds)));
    ret (indLoopRes, sigma).

   Definition ServerSearchLoop_4 xSet (e : nat * (Bvector (lambda + lambda) * Bvector lambda)) :=
    [xtoken, t_c_ind] <-2 e;
     [t_c, ind] <-2 t_c_ind;
    [e, y] <-2 splitVector lambda _ t_c;
    if (in_dec (EqDec_dec _) (xtoken^(bvectorToNat y)) xSet) then (Some (e, ind)) else None.

  Definition ServerSearch_4 xSet (xtokens : list nat) (t : list (Bvector (lambda + lambda) * Bvector lambda)) :=
    map (ServerSearchLoop_4 xSet) (combine xtokens t).

  Definition GenTrans_4 (edb : EDB) k_X k_Z (e : Query * (Tag * list (Bvector (lambda + lambda) * (Bvector lambda)))) : (list (Identifier lambda) * SearchTranscript) :=
    [q, stag_t] <-2 e;
    [stag, t] <-2 stag_t;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    e <- F_P k_X x;
    xtokens <- map (fun (c : nat) => g^(e * (F_P k_Z (s ++ c)))) (allNatsLt (length t));
    res <- ServerSearch_4 xSet xtokens t;
    es <- getSomes res;
    res <- map (fun z => match z with
                           | Some y => Some (fst y)
                           | None => None
                         end) res;
    inds <- map (fun x => snd x) es;
    (inds, (stag, (combine xtokens res))).

  Definition Initialize_4 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_4 db k_S k_I k_Z) (toW db);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts);
    ret (edb, searchRes).

  Definition G4 := G_gen Initialize_4.
  
  
  Theorem splitVector_append : 
    forall (A : Set)(n1 : nat)(v1 : Vector.t A n1)(n2 : nat)(v2 : Vector.t A n2),
      splitVector n1 n2 (Vector.append v1 v2) = (v1, v2).
    
    induction v1; intuition; simpl in *.
    
    rewrite IHv1.
    trivial.
  Qed.
  
  Theorem Init_indLoop_4_spec : 
    forall k1 k2 k3 w id n z1 z2,
      In (z1, z2) (getSupport (Initialize_indLoop_4 k1 k2 k3 w (id, n))) ->
      Dec k3 (fst (splitVector lambda lambda z1)) = z2.

    intuition.
    unfold Initialize_indLoop_4 in *.
    repeat simp_in_support.
    rewrite splitVector_append.
    simpl.
    eapply Enc_correct; eauto.

  Qed.

  
  Theorem list_pred_impl_1_r : 
    forall (A B : Set)(P' : A -> B -> Prop)(P : B -> B -> Prop) ls ls',
      list_pred P' ls' ls ->
      (forall a b, P' a b -> P b b) ->
      list_pred P ls ls.
    
    induction ls; intuition; simpl in *.
    econstructor.
    inversion H; clear H; subst.
    econstructor; eauto.
    
  Qed.

  Theorem Init_wLoop_4_spec : 
    forall db k1 k2 k3 w z1 z2,
      In (z1, z2) (getSupport (Initialize_wLoop_4 db k1 k2 k3 w)) ->
      list_pred (fun a b => Dec (F k1 w) (fst (splitVector lambda lambda a)) = b) (fst (split z1)) (snd (split z1)).

    intuition.
    unfold Initialize_wLoop_4 in *.
    repeat simp_in_support.
    simpl.
    split_eq.
    eapply list_pred_impl_1_r.
    eapply (@compMap_support _ _ (fun a b => Dec (F k1 w) (fst (splitVector lambda lambda (fst b))) = (snd b))) in H1.
    eauto.
    intuition.
    destruct b0.
    simpl.
    eapply Init_indLoop_4_spec.
    eauto.
    intuition.
  Qed.


  Definition GenTrans_3_1 (edb : EDB) k_X k_Z k_S (e : Query * (Tag * list (Bvector (lambda + lambda) * Bvector lambda))) : (list (Identifier lambda) * SearchTranscript) :=
    [q, stag_t] <-2 e;
    [stag, t] <-2 stag_t;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    e <- F_P k_X x;
    xtokens <- map (fun (c : nat) => g^(e * (F_P k_Z (s ++ c)))) (allNatsLt (length t));
    res <- ServerSearch_4 xSet xtokens t;
    res <- map (fun x => match x with
                             | Some v => Some (fst v)
                             | None => None
                         end) res;
    es <- getSomes res;
    k_E <- F k_S s;
    inds <- map (Dec k_E) es;
    (inds, (stag, (combine xtokens res))).

  Definition Initialize_3_1 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_4 db k_S k_I k_Z) (toW db);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_3_1 edb k_X k_Z k_S) (combine q stags_ts);
    ret (edb, searchRes).

  Theorem list_pred_fst_split_irr_if:
    forall (A B C : Set) (P : A -> C -> Prop) (ls1 : list (A * B))
           (ls2 : list C),
      list_pred (fun (x : A) (y : C) => P x y) (fst (split ls1)) ls2 ->
      list_pred (fun (x : A * B) (y : C) => P (fst x) y) ls1 ls2.

    induction ls1; intuition; simpl in *.
    inversion H; clear H; subst.
    econstructor.
    remember (split ls1) as z.
    destruct z.
    simpl in *.
    inversion H; clear H; subst.
    econstructor;
      simpl;
      intuition.
    
  Qed.
  
  Theorem G4_equiv : 
    Pr[G_gen Initialize_3_1] == Pr[G4].

    unfold G4, G_gen, Initialize_3_1, Initialize_4.
    do 6 (comp_skip; comp_simp).
    comp_skip.
    remember (split x3) as z.
    comp_simp.
    comp_skip; comp_simp.
    comp_skip.

    eapply (@compMap_support _ _ 
                             (fun (a : Keyword) (b :  (list (Vector.t bool (lambda + lambda) * Identifier lambda) *
          list nat)) => 
           map (fun v => Dec (F x a) (fst (splitVector lambda lambda v))) (fst (split (fst b))) = (snd (split (fst b))))) in H4.

    eapply evalDist_ret_eq.
    f_equal.

    eapply (@compMap_support _ _ 
                             (fun (a : Blist) (b : Tag * (list (Vector.t bool (lambda + lambda) * Identifier lambda))) => snd b = arrayLookupList _ (combine (toW d) l0) a)) 
           in H7.
    
    eapply (@map_ext_pred _ _ _ (fun a b => a = b /\ (map (fun v => Dec (F x (fst (fst b))) (fst (splitVector lambda lambda v))) (fst (split (snd (snd b))))) = (snd (split (snd (snd b)))))).   

    eapply list_pred_combine_same'.
    simpl.
    eapply list_pred_symm.
    eapply list_pred_impl.
    eapply list_pred_combine_same_l.
    eapply list_pred_symm.
    eapply list_pred_impl.
    eapply list_pred_fst_split_irr_if.
    eapply H7.
    intuition.
    eapply H9.
    intuition.
    simpl in *.
    subst.
    pairInv.
    trivial.
    simpl in *.
    subst.
    pairInv.

    assert (l0 = fst (split x3)).
    rewrite <- Heqz.
    trivial.
    subst.

    Theorem list_pred_arrayLookupList : 
      forall (A B : Set){eqda : EqDec A}(P : A -> list B -> Prop) lsa lsb,
        list_pred P lsa lsb ->
        forall a, 
        (P a nil) ->
        P a (arrayLookupList _ (combine lsa lsb) a).

      induction 1; intuition; simpl in *.
      unfold arrayLookupList.
      simpl.
      case_eq (eqb a a1); intuition.
      rewrite eqb_leibniz in H2; subst.
      trivial.
      specialize (IHlist_pred a).
      intuition.
      
    Qed.

    Show.
    specialize (@list_pred_arrayLookupList _ _ _ 
                                           (fun a b => 
                                              (foreach  (v in fst (split b))
           Dec (F x a) (fst (splitVector lambda lambda v))) =
          snd (split b)) (toW d) (fst (split x3))); intuition.
    eapply H6.
    split_eq.
    eapply H4.
    simpl.
    trivial.
    trivial.

    (* proof of equality of GenTrans given list predicate*)

    intuition.
    unfold GenTrans_3_1, GenTrans_4.
    destruct b0.
    destruct p1.
    simpl in *.
    pairInv.
    comp_simp.
    f_equal.
    simpl in *.
    eapply (@map_ext_pred _ _ _ (fun a b => a = fst b /\ (snd b = Dec (F x a1) (fst b)))).
    Theorem list_pred_getSomes : 
      forall (A B : Set) (P : A -> B -> Prop) lsa lsb,
        list_pred (fun a b => 
                     match a with
                         | Some x => 
                           match b with
                             | Some y => P x y
                             | None => False
                           end 
                         | None => 
                           match b with
                             | Some y => False
                             | None => True
                           end 
                     end) lsa lsb ->
        list_pred P
                  (getSomes lsa) (getSomes lsb).

      induction lsa; inversion 1; intuition; subst; simpl in *.
      econstructor.
      destruct a.
      destruct a2.
      inversion H.
      subst; clear H.
      econstructor; intuition.

      inversion H; clear H; subst.
      intuition.
      
      destruct a2.
      inversion H; clear H; subst.
      intuition.
      eapply IHlsa.
      intuition.

    Qed.
    eapply list_pred_getSomes.
    eapply list_pred_map_l'.
    

    Theorem list_pred_unary : 
      forall (A : Set)(P : A -> Prop)(ls : list A),
        (forall a, In a ls -> P a) ->
        list_pred (fun a b => P a /\ a = b) ls ls.

      induction ls; intuition; simpl in *.
      econstructor.
      econstructor; intuition.

    Qed.

    Theorem ServerSearch_4_spec : 
      forall a b ls z,
        In z (ServerSearch_4 a b ls) ->
        match z with
            | None => True
            | Some p => 
              exists e,
                In e ls /\ snd e = snd p
                /\ (fst (splitVector lambda lambda (fst e))) = fst p
        end.

      intuition.
      unfold ServerSearch_4 in *.
      eapply in_map_iff in H.
      destruct H.
      intuition.
      unfold ServerSearchLoop_4 in *.
      destruct x.
      destruct p0.
      remember (splitVector lambda lambda b0) as y.
      destruct y.
      destruct (in_dec (EqDec_dec nat_EqDec) (n ^ bvectorToNat t0) a).
      rewrite <- H0.
      exists (b0, b1).
      intuition.
      eapply in_combine_r.
      eauto.
      simpl.
      rewrite <- Heqy.
      trivial.

      rewrite <- H0.
      trivial.

    Qed.

    Show.
    eapply list_pred_impl.
    eapply list_pred_unary.
    eapply ServerSearch_4_spec.
    intuition.
    destruct a2.
    intuition.
    subst.
    intuition.
    destruct H11.
    intuition.
    
    Theorem map_split_eq : 
      forall (A B : Type)(f : A -> B)(ls : list (A * B)),
        map f (fst (split ls)) = snd (split ls) ->
        (forall p, In p ls -> f (fst p) = snd p).

      induction ls; intuition; simpl in *;
      intuition.

      subst.
      remember (split ls) as z.
      destruct z.
      destruct p0.
      simpl in *.
      inversion H; clear H; subst.
      intuition.

      remember (split ls) as z.
      destruct z.
      destruct a.
      simpl in *.
      inversion H; clear H; subst.
      intuition.

    Qed.

    symmetry.
    destruct p0; simpl in *.
    subst.
    
    specialize (@map_split_eq _ _ (fun (a : Bvector (lambda + lambda)) => Dec (F x a1) (fst (splitVector lambda lambda a)))); intuition.
    eapply H6.
    eauto.
    trivial.
    intuition; subst.
    intuition.
    intuition.
    subst.
    intuition.
    intuition.
    repeat simp_in_support.
    trivial.
    intuition.
    

    (* correct proof of second goal begins*)
    intuition.
    unfold Initialize_wLoop_4 in *.
    repeat simp_in_support.
    
    eapply (@compMap_support _ _ (fun a b => Dec (F x a1) (fst (splitVector lambda lambda (fst b))) = snd b)) in H11.

    simpl.
    eapply list_pred_eq_impl_eq.
    eapply list_pred_map_l'.
    split_eq.

    Theorem list_pred_impl_unary : 
      forall (A B: Set)(P1 : A -> B -> Prop)(P2 : A -> A -> Prop)(lsa : list A)(lsb : list B),
        list_pred P1 lsa lsb ->
        (forall a b, P1 a b -> P2 a a) ->
        list_pred P2 lsa lsa.

      induction 1; intuition; simpl in *.
      econstructor.
      econstructor; intuition; eauto.

    Qed.

    eapply list_pred_impl_unary .
    eapply list_pred_symm.
    eapply H11.
    intuition.
    intuition.
    unfold Initialize_indLoop_4 in *.
    repeat simp_in_support.
    simpl.
    rewrite splitVector_append.
    simpl.
    eapply Enc_correct; intuition.
    (* correct proof of second goal ends*)

  Qed.
  

  Theorem G3_1_equiv : 
    Pr[G3] == Pr[G_gen Initialize_3_1].

    unfold G3, G_gen, Initialize_3, Initialize_3_1.
    do 6 (comp_skip; comp_simp).
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply compMap_spec.
    eapply list_pred_eq.
    intuition; subst.

    Theorem Init_indLoop_4_eq_spec : 
      forall d x x1 x2 b0,
        comp_spec 
          (fun a b => fst b = a)
          (Initialize_indLoop_2 x1 x2 x b0 d)
          (Initialize_indLoop_4 x1 x2 x b0 d).

      intuition.
      unfold Initialize_indLoop_2.
      unfold Initialize_indLoop_4.
      comp_skip; try
      eapply (oneVector (lambda + lambda)).
      eapply comp_spec_ret; intuition.
    Qed.

    Theorem Init_wLoop_4_eq_spec : 
      forall d x x1 x2 b0,
      comp_spec 
        (fun a b => (fst (split (fst b)) = fst a) /\  (snd a = snd b))
        (Initialize_wLoop_2 d x x1 x2 b0)
        (Initialize_wLoop_4 d x x1 x2 b0).

      intuition.
      unfold Initialize_wLoop_2, Initialize_wLoop_4.
      comp_simp.
      comp_skip.
      comp_skip.
      eapply compMap_spec.
      eapply list_pred_eq.
      intuition; subst.
      eapply Init_indLoop_4_eq_spec.
      eapply comp_spec_ret; intuition.
      simpl.
      split_eq.
      eapply list_pred_symm.
      eauto.

    Qed.

    eapply Init_wLoop_4_eq_spec.
    remember (split a1) as z.
    destruct z.
    remember (split b0) as z.
    destruct z.

    assert (map
              (fun
                 v : list
                       (Vector.t bool (lambda + lambda) * Identifier lambda) =>
               fst (split v)) l2 = l0).
    split_eq.
    eapply list_pred_map_l'.
    assert (l0 = fst (split a1)).
    rewrite <- Heqz.
    trivial.
    subst.
    assert (l2 = (fst (split b0))).
    rewrite <- Heqz0.
    trivial.
    subst.
    split_eq.
    eapply list_pred_symm.
    eapply list_pred_impl.
    eapply H6.
    intuition.

    rewrite H7.
    eapply comp_spec_seq_eq; eauto with inhabited.
    eapply comp_spec_eq_refl.
    intros.
    comp_simp.
    
    comp_skip.
    eapply (@compMap_spec _ _ _ _ _ _ eq 
                          (fun a b => fst a = fst b /\
                          snd a = fst (split (snd b)))
           ).
    eapply list_pred_eq.
    intuition; subst.
    comp_skip.
    eapply comp_base_exists; intuition.
    eapply comp_base_exists; intuition.

    eapply comp_spec_ret; intuition.
    simpl.

    unfold arrayLookupList.

     Theorem arrayLookup_Some_list_pred : 
      forall (A B C : Set){eqda : EqDec A}(P : B -> C -> Prop)(lsa : list A) lsb lsc a b,
        list_pred P lsb lsc ->
        arrayLookup _ (combine lsa lsb) a = Some b->
        (exists c,
          arrayLookup _ (combine lsa lsc) a = Some c /\
          P b c).

      induction lsa; intuition; simpl in *.
      discriminate.
      destruct lsb.
      inversion H; clear H; subst.
      simpl in *.
      discriminate.
      
      inversion H; clear H; subst.
      simpl in *.
      case_eq (eqb a0 a); intuition.
      rewrite eqb_leibniz in H.
      subst.
      rewrite eqb_refl in *.
      inversion H0; clear H0; subst.
      econstructor; eauto.
      
      rewrite H in H0.
      eapply IHlsa; eauto.

    Qed.

    Theorem arrayLookup_None_combine : 
      forall (A B C : Set){eqd : EqDec A}(lsa : list A)(lsb : list B)(lsc : list C) a,
        arrayLookup _ (combine lsa lsb) a = None ->
        length lsb = length lsc ->
        arrayLookup _ (combine lsa lsc) a = None.

      induction lsa; intuition; simpl in *.
      destruct lsc; simpl in *.
      trivial.
      destruct lsb; simpl in *.
      omega.
      destruct ( eqb a0 a).
      discriminate.
      eauto.

    Qed.

    case_eq (@arrayLookup Keyword
               (list
                  (prod
                     (Vector.t bool
                        (plus (posnatToNat lambda) (posnatToNat lambda)))
                     (Identifier (posnatToNat lambda))))
               (@list_EqDec bool bool_EqDec)
               (@combine Keyword
                  (list
                     (prod
                        (Vector.t bool
                           (plus (posnatToNat lambda) (posnatToNat lambda)))
                        (Identifier (posnatToNat lambda)))) 
                  (toW d) l2) b1); intuition.
    eapply (@arrayLookup_Some_list_pred _ _ _ _ (fun a b => fst (split a) = b)) in H12.
    destruct H12.
    intuition.
    rewrite H13.
    intuition.
    eapply list_pred_map_r'.
    eapply list_pred_impl.
    eapply list_pred_eq.
    intuition.
    subst.
    trivial.
    
    eapply arrayLookup_None_combine in H12.
    rewrite H12.
    trivial.
    rewrite map_length.
    trivial.

    assert (l1 = l3).
    assert (l3 = snd (split b0)).
    rewrite <- Heqz0.
    trivial.
    assert (l1 = snd (split a1)).
    rewrite <- Heqz.
    trivial.
    subst.
    split_eq.
    eapply list_pred_impl.
    eauto.
    intuition.
    subst.
    
    eapply comp_spec_ret; intuition.
    f_equal.


    eapply map_ext_pred.
    eapply list_pred_combine_simple.
    eapply list_pred_eq.
    eauto.
    eapply compMap_length in H9.
    rewrite H9.
    symmetry.
    eapply split_length_l.

    intuition.
    simpl in *.
    subst.
    unfold GenTrans_3_1.
    destruct b2.
    simpl.
    destruct p0.
    destruct q.
    comp_simp.
    simpl.

    assert (
        (ServerSearch_2 (XSetSetup_2 x0 x1 d l3)
              (map
                 (fun c : nat =>
                  groupExp g (mult (F_P x0 k0) (F_P x2 (app k c))))
                 (allNatsLt (length (fst (split l0))))) 
              (fst (split l0))) = 
(map
              (fun x3 : option (prod (Vector.t bool lambda) (Bvector lambda)) =>
               match x3 with
               | Some v => Some (fst v)
               | None => None
               end)
              (ServerSearch_4 (XSetSetup_2 x0 x1 d l3)
                 (map
                    (fun c : nat =>
                     groupExp g (mult (F_P x0 k0) (F_P x2 (app k c))))
                    (allNatsLt (length l0))) l0))

            ).

    eapply list_pred_eq_impl_eq.
    eapply list_pred_map_r'.
    
    unfold ServerSearch_2, ServerSearch_4.
    eapply list_pred_map_both'.
    eapply list_pred_impl.
    eapply (@list_pred_combine_simple _ _ _ _ eq (fun a b => fst b = a)).
    assert (length (fst (split l0)) = length l0).
    eapply split_length_l.
    rewrite H8.
    eapply list_pred_eq.
    split_eq.
    eapply list_pred_impl.
    eapply list_pred_eq.
    intuition.
    subst; trivial.
    rewrite map_length.
    rewrite allNatsLt_length.
    trivial.
    
    intuition.
    simpl in *; subst.
    unfold ServerSearchLoop_4.
    destruct b3.
    destruct p0.
    simpl.
    remember (splitVector lambda lambda b2) as z.
    destruct z.
    destruct (in_dec (EqDec_dec nat_EqDec) (n ^ bvectorToNat t3)
         (XSetSetup_2 x0 x1 d l3)); trivial.

    f_equal.
    eapply map_ext_pred.
    eapply (@list_pred_getSomes _ _ eq).
    eapply list_pred_impl.
    eapply list_pred_eq_gen.
    eapply H8.
    intuition; subst.
    destruct b2; intuition.
    intuition.
    subst.
    trivial.
    
    f_equal.
    f_equal.
    rewrite split_length_l.
    trivial.
    eapply H8.
  Qed.

  (* Step 5: prepare to the replace the first PRF with a random function. *)
  Fixpoint oc_compMap(A B C D : Set)(eqdb : EqDec B)(c : A -> OracleComp C D B)(ls : list A) : OracleComp C D (list B) :=
    match ls with
      | nil => $ (ret nil)
      | a :: ls' =>
        b <--$ c a;
          lsb' <--$ oc_compMap _ c ls';
          $ (ret (b :: lsb'))
    end. 
  
  Notation "'query' v" := (OC_Query  _ v) (at level 79) : comp_scope. 
  
  Definition Initialize_wLoop_5 db k_I k_Z w :=
    inds <- lookupInds db w;
    sigma <--$$ RndPerm (length inds);
    k_E <--$ query w;
    indLoopRes <--$$ compMap _ (Initialize_indLoop_4 k_I k_Z k_E w) (combine (permute inds sigma) (allNatsLt (length inds)));
    $ ret (indLoopRes, sigma).

  Definition Initialize_5 (db : DB)(q : list Query) :=
    
    k_X <--$$ {0,1}^lambda;
    k_I <--$$ {0,1}^lambda;
    k_Z <--$$ {0,1}^lambda;
    wLoopRes <--$ oc_compMap _ (Initialize_wLoop_5 db k_I k_Z) (toW db);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <--$2$ TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <--$$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts);
    $ ret (edb, searchRes).

  Definition G5_A :=
    [db, q, s_A] <--$3$ A1;
    z0 <--$ Initialize_5 db q; 
    [edb, ls]<-2 z0; 
    $ A2 s_A edb (snd (split ls)).

  Definition G5 :=
    k_S <-$ {0,1}^lambda;
    [b, _] <-$2 G5_A _ _ (f_oracle F _ k_S) tt;
    ret b.


  (* Step 4.1: move the key sampling to the beginning of the game. *)
  Definition Initialize_4_1 k_S (db : DB)(q : list Query) :=
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_4 db k_S k_I k_Z) (toW db);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts);
    ret (edb, searchRes).

  Definition G4_1 :=
    k_S <-$ {0,1}^lambda;
    z <-$ A1;
    [db, q, s_A]<-3 z;
    z0 <-$ Initialize_4_1 k_S db q; 
    [edb, ls]<-2 z0; 
    A2 s_A edb (snd (split ls)).

  Theorem G4_1_equiv : 
    Pr[G4] == Pr[G4_1].

    unfold G4_1, G4, G_gen.
    comp_swap_r.
    comp_skip.
    comp_simp.
    unfold  Initialize_4,  Initialize_4_1.
    repeat (inline_first; comp_skip; try reflexivity).
  Qed.

  Theorem compMap_oc_spec : 
    forall (C D : Set)(P2 : C -> D -> Prop)(A B : Set)(P1 : A -> B -> Prop)(eqdc : EqDec C)(eqdd : EqDec D)(E F S: Set)(eqds : EqDec S)(ls1 : list A)(ls2 : list B)(c1 : A -> Comp C)(c2 : B -> OracleComp E F D)o (s : S),
      list_pred P1 ls1 ls2 ->
      (forall a b z, P1 a b -> comp_spec (fun x y => P2 x (fst y)) (c1 a) (c2 b _ _ o z)) -> 
      comp_spec (fun a b => list_pred P2 a (fst b))
                (compMap _ c1 ls1)
                ((oc_compMap _ c2 ls2) _ _ o s).
    
    induction ls1; inversion 1; subst; intuition; simpl in *.
    comp_simp.
    eapply comp_spec_ret; simpl; econstructor.
    
    simpl.
    comp_skip.
    comp_simp.
    comp_skip.
    comp_simp.
    eapply comp_spec_ret; intuition.
    simpl.
    econstructor; eauto.
    
  Qed.

  Theorem G5_equiv : 
    Pr[G4_1] == Pr[G5].

    unfold G4_1, G5, G5_A, Initialize_4, Initialize_5.
    comp_skip.
    
    eapply comp_spec_eq_impl_eq.
    simpl.
    inline_first.
    comp_skip.
    comp_simp.
    unfold Initialize_4_1.
    do 3 (simpl; inline_first; eapply comp_spec_seq_eq; eauto with inhabited; try reflexivity; intuition; comp_simp).
    inline_first.
    comp_skip.
    eapply (@compMap_oc_spec _ _ eq).
    eapply list_pred_eq.
    intuition; subst.

    unfold Initialize_wLoop_4, Initialize_wLoop_5.
    simpl; inline_first.

    do 2 (simpl; inline_first; eapply comp_spec_seq_eq; eauto with inhabited; try reflexivity; intuition; comp_simp).
    eapply comp_spec_ret; intuition.
    
    destruct b1.
    simpl in *.
    assert (a3 = l).
    eapply list_pred_eq_impl_eq.
    trivial.
    subst.
    remember (split l) as z.
    destruct z.
    do 2 (simpl; inline_first; comp_skip; comp_simp).
    simpl.
    comp_simp.
    inline_first.
    comp_simp.
    eapply comp_spec_eq_trans_l.
    eapply comp_spec_eq_symm.
    eapply comp_spec_right_ident.
    simpl; inline_first.
    comp_skip.
    comp_simp.
    eapply comp_spec_eq_refl.
  Qed.

  (* Step 6: replace the PRF with a random function. *)
   Definition G6 :=
    [b, _] <-$2 G5_A _ _ (@randomFunc Blist (Bvector lambda) (Rnd lambda) _) nil;
    ret b.
  
   Theorem G6_close : 
     | Pr[G5] - Pr[G6] | == PRF_Advantage (Rnd lambda) (Rnd lambda) F _ _ G5_A.

     reflexivity.

   Qed.

   (* Step 7: replace random function outputs with random values. *)
   Definition Initialize_wLoop_7 db k_I k_Z w :=
    inds <- lookupInds db w;
    sigma <-$ RndPerm (length inds);
    k_E <-$ {0, 1}^lambda;
    indLoopRes <-$ compMap _ (Initialize_indLoop_4 k_I k_Z k_E w) (combine (permute inds sigma) (allNatsLt (length inds)));
    ret (indLoopRes, sigma).

  Definition Initialize_7 (db : DB)(q : list Query) :=
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_7 db k_I k_Z) (toW db);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts);
    ret (edb, searchRes).

  Definition G7 := G_gen Initialize_7.

  (* Step 6.1: We'll use a standard argument about mapping a randomf function over a list with 
no duplicates.  Start by changing the structure to match that argument. *)
  Definition Initialize_wLoop_6_1 db k_E k_I k_Z w :=
    inds <- lookupInds db w;
    sigma <-$ RndPerm (length inds);
    indLoopRes <-$ compMap _ (Initialize_indLoop_4 k_I k_Z k_E w) (combine (permute inds sigma) (allNatsLt (length inds)));
     ret (indLoopRes, sigma).

  Definition Initialize_6_1 (db : DB)(q : list Query) :=
    
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    [wLoopRes, _] <-$2 
             (oc_compMap _ (fun w => k_E <--$ query w; $ Initialize_wLoop_6_1 db k_E k_I k_Z w) (toW db))
    _ _ (@randomFunc Blist (Bvector lambda) (Rnd lambda) _) nil;
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts);
    ret (edb, searchRes).

  Definition G6_1 :=
    [db, q, s_A] <-$3 A1;
    z0 <-$ Initialize_6_1 db q; 
    [edb, ls]<-2 z0; 
    A2 s_A edb (snd (split ls)).

  Theorem G6_1_equiv : 
    Pr[G6] == Pr[G6_1].

    unfold G6, G6_1, Initialize_6_1, G5_A.
    eapply comp_spec_eq_impl_eq.
    simpl; inline_first; comp_skip; comp_simp.
    unfold Initialize_5.
    do 3 (simpl; inline_first; comp_skip; comp_simp).
    
    simpl; inline_first.
    comp_skip.

    Theorem oc_compMap_eq : 
      forall (A B C D : Set){eqd : EqDec D}(f1 f2 : A -> OracleComp B C D)(ls : list A) (S : Set){eqds : EqDec S} o (s : S),
        (forall s a, comp_spec 
                       eq
                       ((f1 a) _ _ o s)
                       ((f2 a) _ _ o s)) ->
        comp_spec 
          eq
          ((oc_compMap _ f1 ls) _ _ o s)
          ((oc_compMap _ f2 ls) _ _ o s).

      induction ls; intuition; simpl in *.
      comp_simp.
      eapply comp_spec_eq_refl.
      comp_skip.
      comp_skip.
      comp_simp.
      eapply comp_spec_eq_refl.

    Qed.

    eapply  oc_compMap_eq; intuition.
    unfold Initialize_wLoop_5, Initialize_wLoop_6_1.
    simpl; inline_first.

    assert (comp_spec eq

                      (Bind (RndPerm (length (lookupInds a a0)))
        (fun a1 : list nat =>
         Bind
           (Ret
              (EqDec_dec
                 (pair_EqDec
                    (comp_EqDec (RndPerm (length (lookupInds a a0))))
                    (list_EqDec
                       (pair_EqDec (list_EqDec bool_EqDec)
                          (Bvector_EqDec lambda))))) 
              (pair a1 s))
           (fun z0 : prod (list nat) (list (prod Blist (Bvector lambda))) =>
            let 'pair z s' := z0 in
                 Bind (randomFunc (Rnd lambda) (list_EqDec bool_EqDec) s' a0)
                   (fun
                      z1 : prod (Bvector lambda)
                             (list (prod Blist (Bvector lambda))) =>
                    let 'pair z2 s'0 := z1 in
                         Bind
                           (Bind
                              (compMap
                                 (pair_EqDec
                                    (Bvector_EqDec (plus lambda lambda))
                                    (Bvector_EqDec lambda))
                                 (Initialize_indLoop_4 b2 b3 z2 a0)
                                 (combine
                                    (permute
                                       (lookupInds a a0) z)
                                    (allNatsLt (length (lookupInds a a0)))))
                              (fun
                                 x : list
                                       (prod
                                          (Vector.t bool (plus lambda lambda))
                                          (Identifier lambda)) =>
                               Ret
                                 (EqDec_dec
                                    (pair_EqDec
                                       (comp_EqDec
                                          (compMap
                                             (pair_EqDec
                                                (Bvector_EqDec
                                                  (plus lambda lambda))
                                                (Bvector_EqDec lambda))
                                             (Initialize_indLoop_4 b2 b3 z2
                                                a0)
                                             (combine
                                                (permute 
                                                  
                                                  (lookupInds a a0) z)
                                                (allNatsLt
                                                  (length (lookupInds a a0))))))
                                       (list_EqDec
                                          (pair_EqDec 
                                             (list_EqDec bool_EqDec)
                                             (Bvector_EqDec lambda)))))
                                 (pair x s'0)))
                           (fun
                              z3 : prod
                                     (list
                                        (prod
                                           (Vector.t bool
                                              (plus lambda lambda))
                                           (Identifier lambda)))
                                     (list (prod Blist (Bvector lambda))) =>
                            let 'pair z4 s'1 := z3 in
                                 Bind
                                   (Ret
                                      (EqDec_dec
                                         (pair_EqDec
                                            (list_EqDec
                                               (pair_EqDec
                                                  (Bvector_EqDec
                                                  (plus lambda lambda))
                                                  (Bvector_EqDec lambda)))
                                            (list_EqDec nat_EqDec)))
                                      (pair z4 z))
                                   (fun
                                      x : prod
                                            (list
                                               (prod
                                                  (Vector.t bool
                                                  (plus lambda lambda))
                                                  (Identifier lambda)))
                                            (list nat) =>
                                    Ret
                                      (EqDec_dec
                                         (pair_EqDec
                                            (comp_EqDec
                                               (Ret
                                                  (EqDec_dec
                                                  (pair_EqDec
                                                  (list_EqDec
                                                  (pair_EqDec
                                                  (Bvector_EqDec
                                                  (plus lambda lambda))
                                                  (Bvector_EqDec lambda)))
                                                  (list_EqDec nat_EqDec)))
                                                  (pair z4 z)))
                                            (list_EqDec
                                               (pair_EqDec
                                                  (list_EqDec bool_EqDec)
                                                  (Bvector_EqDec lambda)))))
                                      (pair x s'1)))))))

     (a1 <-$ RndPerm (length (lookupInds a a0));
      z1 <-$ randomFunc ({ 0 , 1 }^lambda) (list_EqDec bool_EqDec) s a0;
      [z2, s'0]<-2 z1;
      z3 <-$
      (x <-$
       (foreach  (x
        in combine (permute (lookupInds a a0) a1)
             (allNatsLt (length (lookupInds a a0))))
        Initialize_indLoop_4 b2 b3 z2 a0 x); ret (x, s'0));
      [z4, s'1]<-2 z3; x <-$ ret (z4, a1); ret (x, s'1))).


    eapply eq_impl_comp_spec_eq.
    intuition.
    comp_skip.
    comp_skip.
    comp_simp.
    inline_first.
    comp_skip.
    reflexivity.
    comp_simp.
    eapply evalDist_ret_eq.
    trivial.
    rewrite H1.
    clear H1.

    eapply eq_impl_comp_spec_eq.
    intros.
    comp_swap_l.
    comp_skip.
    reflexivity.
    comp_simp.
    eapply comp_spec_eq_impl_eq.
    simpl; inline_first.
    comp_skip.
    simpl; inline_first.
    comp_skip.
    comp_simp.
    eapply comp_spec_ret; intuition.

    subst.
    remember (split a1) as z.
    destruct z.
    
    do 2 (simpl; inline_first; comp_skip; comp_simp).
    inline_first; comp_simp.
    simpl.
    inline_first.
    eapply comp_spec_eq_trans_l.
    Focus 2.
    eapply comp_spec_right_ident.
    comp_skip.
 
  Qed.

  Definition Initialize_6_2 (db : DB)(q : list Query) :=
    
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    [wLoopRes, _] <-$2 
             (oc_compMap _ (fun w => k_E <--$ query w; $ Initialize_wLoop_6_1 db k_E k_I k_Z w) (toW db))
    _ _ (fun (s: unit)(a : Blist) => b <-$ {0, 1}^lambda; ret (b, s)) tt;
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts);
    ret (edb, searchRes).

  Definition G6_2 :=
    [db, q, s_A] <-$3 A1;
    z0 <-$ Initialize_6_2 db q; 
    [edb, ls]<-2 z0; 
    A2 s_A edb (snd (split ls)).

  Theorem G6_2_equiv : 
    Pr[G6_1] == Pr[G6_2].

    unfold G6_1, G6_2.
    comp_skip.
    comp_simp.
    unfold Initialize_6_1, Initialize_6_2.
    do 3 (inline_first; comp_skip; comp_simp).
    inline_first.
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    
    Theorem compMap_randomFunc_NoDup : 
      forall (A B C: Set){eqda : EqDec A}{eqdb : EqDec B}{eqdc : EqDec C}(ls : list A)(f : A -> B -> Comp C)(rndB : Comp B)(lsf : list (A * B)),
        NoDup ls ->
        (forall a, In a ls -> arrayLookup _ lsf a = None) ->
        comp_spec (fun a b => fst a = fst b)
                  ((oc_compMap _ (fun x => y <--$ query x; $ f x y) ls) _ _ (@randomFunc A B rndB _) lsf)
                  ((oc_compMap _ (fun x => y <--$ query x; $ f x y) ls) _ _ (fun s a => b <-$ rndB; ret (b, s)) tt).

      induction ls; intuition; simpl in *.
      comp_simp.
      eapply comp_spec_ret; intuition.
      inversion H; clear H; subst.

      simpl; inline_first.
      unfold randomFunc.
      rewrite H0.
      inline_first.
      comp_skip.
      comp_simp.
      inline_first.
      comp_skip.
      comp_simp.
      comp_skip.
      eapply IHls; intuition.
      simpl.
      case_eq (eqb a0 a); intuition.
      rewrite eqb_leibniz in H7.
      subst.
      intuition.
      comp_simp.
      simpl in *; subst.
      eapply comp_spec_ret; intuition.
      intuition.

    Qed.

    eapply compMap_randomFunc_NoDup.
    eapply removeDups_NoDup.
    intuition.

    destruct b0.
    simpl in *; subst.
    remember (split l0) as z.
    destruct z.
    inline_first.
    reflexivity.
    
  Qed.

  Theorem G7_equiv_h : 
    Pr[G6_2] == Pr[G7].

    unfold G6_2, G7, G_gen, Initialize_6_2, Initialize_7.

    do 4 (comp_skip; comp_simp; inline_first).
    eapply comp_spec_eq_impl_eq.

    comp_skip.
    eapply comp_spec_symm.
    eapply (@compMap_oc_spec _ _ (fun a b => a = b)).
    eapply list_pred_eq.
    intuition; subst.
    unfold Initialize_wLoop_7,  Initialize_wLoop_6_1.
    simpl; comp_simp.
    inline_first.
    comp_swap_l.
    do 2 (comp_skip; comp_simp; inline_first).
    comp_skip.
    comp_simp.
    eapply comp_spec_ret; intuition.

    simpl in *.
    remember (split a1) as z.
    destruct z.
    remember (split b0) as z.
    destruct z.
    assert (l0 = l2).
    assert (l0 = fst (split a1)).
    rewrite <- Heqz.
    trivial.
    assert (l2 = fst (split b0)).
    rewrite <- Heqz0.
    trivial.
    subst.
    split_eq.
    eapply list_pred_symm.
    eapply list_pred_impl.
    eapply H6.
    intuition.
    subst; trivial.
    subst.
    
    inline_first; comp_skip.
    inline_first; comp_skip.
    comp_simp.
    assert (l1 = l3).
    assert (l1 = snd (split a1)).
    rewrite <- Heqz.
    trivial.
    assert (l3 = snd (split b0)).
    rewrite <- Heqz0.
    trivial.
    subst.
    split_eq.
    eapply list_pred_symm.
    eapply list_pred_impl.
    eapply H6.
    intuition.
    subst; trivial.
    subst.
    reflexivity.
  Qed.
    

  (* Step 8: Apply the semantic security definition to replace the ciphertexts with encryptions of 0^lambda *)
  Definition zeroVector n := Vector.const false n.
  
  Definition Initialize_indLoop_8 k_I k_Z k_E w (e : Identifier lambda * nat) :=
    [ind, c] <-2 e;
    e <-$ Enc k_E (zeroVector lambda);
    xind <- F_P k_I (Vector.to_list ind);
    z <- F_P k_Z (w ++ c);
    y <- xind * (inverse z);
    ret (Vector.append e (natToBvector y), ind).

    Definition Initialize_wLoop_8 db k_I k_Z w :=
    inds <- lookupInds db w;
    sigma <-$ RndPerm (length inds);
    k_E <-$ {0, 1}^lambda;
    indLoopRes <-$ compMap _ (Initialize_indLoop_8 k_I k_Z k_E w) (combine (permute inds sigma) (allNatsLt (length inds)));
    ret (indLoopRes, sigma).

  Definition Initialize_8 (db : DB)(q : list Query) :=
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_8 db k_I k_Z) (toW db);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts);
    ret (edb, searchRes).

  Definition G8 := G_gen Initialize_8.

  Require Import Encryption.

  (* Step 7.1: We will use an iterated semantic security definition, and we need to get the game in the correct form. Start by moving some things around. *)

  Definition Initialize_indLoop_7_1 (enc : Bvector lambda -> Bvector lambda -> Comp (Bvector lambda)) k_I k_Z k_E w (e : Identifier lambda * nat) :=
    [ind, c] <-2 e;
    e <-$ enc k_E ind;
    xind <- F_P k_I (Vector.to_list ind);
    z <- F_P k_Z (w ++ c);
    y <- xind * (inverse z);
    ret (Vector.append e (natToBvector y), ind).

  Definition Initialize_wLoop_7_1 (enc : Bvector lambda -> Bvector lambda -> Comp (Bvector lambda)) db k_I k_Z w :=
    k_E <-$ {0, 1}^lambda;
    inds <- lookupInds db w;
    sigma <-$ RndPerm (length inds);
    indLoopRes <-$ compMap _ (Initialize_indLoop_7_1 enc k_I k_Z k_E w) (combine (permute inds sigma) (allNatsLt (length inds)));
    ret (indLoopRes, sigma).

  Definition Initialize_7_1 (enc : Bvector lambda -> Bvector lambda -> Comp (Bvector lambda)) (db : DB)(q : list Query) :=
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_7_1 enc db k_I k_Z) (toW db);
    k_X <-$ {0,1}^lambda;
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts);
    ret (edb, searchRes).


  Definition G7_1 (enc : Bvector lambda -> Bvector lambda -> Comp (Bvector lambda)) :=
    [db, q, s_A] <-$3 A1;
    z0 <-$ Initialize_7_1 enc db q; 
    [edb, ls]<-2 z0; 
    A2 s_A edb (snd (split ls)).
    
  
  Theorem G7_1_equiv : 
    Pr[G7] == Pr[G7_1 Enc].

    unfold G7, G7_1, Initialize_7, Initialize_7_1.
    comp_skip.
    comp_simp.
    do 3 (inline_first; comp_at comp_inline leftc 1%nat; comp_swap_l; comp_skip).

    eapply compMap_eq.
    eapply list_pred_eq.
    intuition; subst.
    unfold Initialize_wLoop_7, Initialize_wLoop_7_1.
    comp_simp.
    comp_swap_r.
    reflexivity.

    inline_first.
    comp_skip.

    reflexivity.
    
  Qed.

  (* Step 7.2: Put the game in the form of the encryption definition. *)
  Definition Initialize_indLoop_7_2 k_I k_Z  w (e : Identifier lambda * nat) :=
    [ind, c] <-2 e;
    e <--$ query ind;
    xind <- F_P k_I (Vector.to_list ind);
    z <- F_P k_Z (w ++ c);
    y <- xind * (inverse z);
    $ ret (@Vector.append bool lambda lambda e (natToBvector y), ind).


  Definition Initialize_wLoop_7_2 db k_I k_Z w :=
    inds <- lookupInds db w;
    sigma <--$$ RndPerm (length inds);
    indLoopRes <--$ oc_compMap _ (Initialize_indLoop_7_2 k_I k_Z w) (combine (permute inds sigma) (allNatsLt (length inds)));
    $ ret (indLoopRes, sigma).

  Definition EncI_A1 :=
    [db, q, s_A] <-$3 A1;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    ret (toW db, (k_I, k_Z, db, q, s_A)).

  Definition EncI_A2 (s : Bvector lambda * Bvector lambda * DB * list Query * A_State) w :=
    let '(k_I, k_Z, db, q, s_A) := s in
    Initialize_wLoop_7_2 db k_I k_Z w.

  Definition EncI_A3 (s : Bvector lambda * Bvector lambda * DB * list Query * A_State) wLoopRes :=
    let '(k_I, k_Z, db, q, s_A) := s in
     k_X <-$ {0,1}^lambda;
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts);
    A2 s_A edb (snd (split searchRes)).

  Definition G7_2  (enc : Bvector lambda -> Bvector lambda -> Comp (Bvector lambda)) :=
    [ws, s] <-$2 EncI_A1;
    wLoopRes <-$ compMap _ (fun x => 
                              key <-$ {0,1}^lambda;
                            [b, _] <-$2 (EncI_A2 s x) _ _ (EncryptOracle enc _ key) tt;
                           ret b) ws;
    EncI_A3 s wLoopRes.

  Theorem G7_2_equiv : forall enc, 
    Pr[G7_1 enc] == Pr[G7_2 enc].

    intuition.
    unfold G7_2, G_gen, EncI_A1.
    inline_first.
    comp_skip.
    comp_simp.
    unfold Initialize_7_1.
    inline_first.
    comp_skip.
    inline_first.
    comp_skip.
    comp_simp.
    inline_first.
    comp_skip.
    eapply compMap_eq.
    eapply list_pred_eq.
    intuition; subst.
    unfold Initialize_wLoop_7_1.
    inline_first.
    comp_skip.
    unfold EncI_A2.
    unfold Initialize_wLoop_7_2.
    comp_simp.
    eapply comp_spec_eq_impl_eq.
    simpl.
    inline_first.
    comp_skip.
    comp_simp.
    inline_first.
    comp_skip.
    eapply (@compMap_oc_spec _ _ (fun a b => a = b)).
    eapply list_pred_eq.
    intuition.
    pairInv.
    unfold Initialize_indLoop_4, Initialize_indLoop_7_2.
    simpl.
    unfold EncryptOracle.
    inline_first.
    comp_skip; try
    eapply (oneVector (lambda + lambda)).
    comp_simp.
    eapply comp_spec_ret; intuition.

    comp_simp.
    inline_first.
    comp_simp.
    eapply comp_spec_ret; intuition.
    f_equal.
    simpl in *.
    eapply list_pred_eq_impl_eq; intuition.
    
    unfold EncI_A3.
    inline_first.
    comp_skip.
    remember (split x1) as z.
    destruct z.
    
    remember (
        @split
            (list
               (prod
                  (Bvector
                     (posnatToNat
                        (@natToPosnat
                           (plus (posnatToNat lambda) (posnatToNat lambda))
                           (nz_posnat_plus lambda lambda))))
                  (Bvector (posnatToNat lambda)))) 
            (list nat) x1
            ) as z.
    destruct z.
    inline_first.
    assert (l0 = l2).
    assert (l0 = (fst (split x1))).
    rewrite <- Heqz.
    trivial.
    assert (l2 = (fst (@split
            (list
               (prod
                  (Bvector
                     (posnatToNat
                        (@natToPosnat
                           (plus (posnatToNat lambda) (posnatToNat lambda))
                           (nz_posnat_plus lambda lambda))))
                  (Bvector (posnatToNat lambda)))) 
            (list nat) x1))).
    rewrite <- Heqz0.
    trivial.
    subst.
    trivial.

    subst.
    comp_skip.
    reflexivity.
    comp_simp.
    inline_first.
    comp_skip.
    reflexivity.
    
    assert (l1 = l3).
    assert (l1 = (snd (split x1))).
    rewrite <- Heqz.
    trivial.
    assert (l3 = (snd ((@split
            (list
               (prod
                  (Bvector
                     (posnatToNat
                        (@natToPosnat
                           (plus (posnatToNat lambda) (posnatToNat lambda))
                           (nz_posnat_plus lambda lambda))))
                  (Bvector (posnatToNat lambda)))) 
            (list nat) x1)))).
    rewrite <- Heqz0.
    trivial.
    subst.
    trivial.
    subst.
    reflexivity.

  Qed.

  
  (* Step 7.3 : Apply the encryption security definition. *)
  Definition G7_3 :=
    [ws, s] <-$2 EncI_A1;
    wLoopRes <-$ compMap _ (fun x => 
                              key <-$ {0,1}^lambda;
                            [b, _] <-$2 (EncI_A2 s x) _ _ (EncryptNothingOracle Enc _ (zeroVector lambda) key) tt;
                           ret b) ws;
    EncI_A3 s wLoopRes.

  Theorem G7_3_close : 
    | Pr[G7_2 Enc] - Pr[G7_3] | <= IND_CPA_SecretKey_OI_Advantage (Rnd lambda) Enc EncI_A1 EncI_A2 EncI_A3 _ _ (zeroVector lambda).

    eapply leRat_refl.

  Qed.
  
  (* Now put everything back.  Start by showing that the last game is the same as G7_2 with a different encrypt function. *)
  Theorem G7_3_back_equiv : 
    Pr[G7_3] == Pr[G7_2 (fun k p => Enc k (zeroVector lambda))].


    reflexivity.
    
  Qed.
  

  (* use G7_2_equiv to do the next step *)

  Theorem G8_equiv_h : 
    Pr[G7_1 (fun k p => Enc k (zeroVector lambda))] == Pr[G8].

    unfold G8, G_gen, G7_1, Initialize_7_1, Initialize_8.
    comp_skip; comp_simp.
    do 3 (inline_first; comp_at comp_inline rightc 1%nat; comp_swap_r; comp_skip).

    eapply compMap_eq.
    eapply list_pred_eq.
    intuition; subst.
    unfold Initialize_wLoop_7_1, Initialize_wLoop_8.
    comp_simp.
    comp_swap_l.
    reflexivity.

    inline_first; comp_skip.
    reflexivity.

  Qed.


  (* Step 9: Next we will replace the "Z" PRF with a random function.  Start by putting the game in the oracle form. *)
  Definition Initialize_indLoop_9 k_I k_E w (e : Identifier lambda * nat) :=
    [ind, c] <-2 e;
    e <--$$ Enc k_E (zeroVector lambda);
    xind <- F_P k_I (Vector.to_list ind);
    z <--$ query (w ++ c);
    y <- xind * (inverse z);
    $ ret (Vector.append e (natToBvector y), ind).

    Definition Initialize_wLoop_9 db k_I w :=
    inds <- lookupInds db w;
    sigma <--$$ RndPerm (length inds);
    k_E <--$$ {0, 1}^lambda;
    indLoopRes <--$ oc_compMap _ (Initialize_indLoop_9 k_I k_E w) (combine (permute inds sigma) (allNatsLt (length inds)));
    $ ret (indLoopRes, sigma).

    Definition GenTrans_9 (edb : EDB) k_X (e : Query * (Tag * list (Bvector (lambda + lambda) * (Bvector lambda)))) :=
    [q, stag_t] <-2 e;
    [stag, t] <-2 stag_t;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    e <- F_P k_X x;
    xtokens <--$ oc_compMap _ (fun (c : nat) => z <--$ query s ++ c; $ ret g^(e * z)) (allNatsLt (length t));
    res <- ServerSearch_4 xSet xtokens t;
    es <- getSomes res;
    res <- map (fun z => match z with
                           | Some y => Some (fst y)
                           | None => None
                         end) res;
    inds <- map (fun x => snd x) es;
    $ ret (inds, (stag, (combine xtokens res))).

  Definition Initialize_9 (db : DB)(q : list Query) :=
    k_X <--$$ {0,1}^lambda;
    k_I <--$$ {0,1}^lambda;
    wLoopRes <--$ oc_compMap _ (Initialize_wLoop_9 db k_I) (toW db);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <--$2$ TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <--$$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <--$ oc_compMap _ (GenTrans_9 edb k_X) (combine q stags_ts);
    $ ret (edb, searchRes).

  Definition G9_A :=
    [db, q, s_A] <--$3$ A1;
    z0 <--$ Initialize_9 db q; 
    [edb, ls]<-2 z0; 
    $ A2 s_A edb (snd (split ls)).
  
  Definition G9 :=
    k <-$ {0, 1}^lambda;
    [b, _] <-$2 G9_A _ _ (f_oracle F_P _ k) tt;
    ret b.


  (* Step 8.1: Start by sampling the key at the beginning. *)
  Definition G8_1  :=
    
    k_Z <-$ {0,1}^lambda;
    [db, q, s_A] <-$3 A1;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_8 db k_I k_Z) (toW db);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts);
    A2 s_A edb (snd (split searchRes)).
  
  
  Theorem G8_1_equiv : 
    Pr[G8] == Pr[G8_1].
    
    unfold G8, G8_1, G_gen, Initialize_8.
    comp_swap_r.
    comp_skip.
    comp_simp.
    inline_first.
    comp_swap_r.
    comp_skip.
    inline_first.
    comp_swap_r.
    comp_skip.
    
    repeat (inline_first; comp_skip; comp_simp).
    reflexivity.

  Qed.
  
  
    (* Step 8.2: put some functions in the form of computations. *)
  
  Definition GenTrans_8_2 (edb : EDB) k_X k_Z (e : Query * (Tag * list (Bvector (lambda + lambda) * (Bvector lambda)))) :=
    [q, stag_t] <-2 e;
    [stag, t] <-2 stag_t;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    e <- F_P k_X x;
    xtokens <-$ compMap _ (fun (c : nat) => ret g^(e * (F_P k_Z (s ++ c)))) (allNatsLt (length t));
    res <- ServerSearch_4 xSet xtokens t;
    es <- getSomes res;
    res <- map (fun z => match z with
                           | Some y => Some (fst y)
                           | None => None
                         end) res;
    inds <- map (fun x => snd x) es;
    ret (inds, (stag, (combine xtokens res))).

  Definition G8_2  :=
    
    k_Z <-$ {0,1}^lambda;
    [db, q, s_A] <-$3 A1;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_8 db k_I k_Z) (toW db);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <-$ compMap _ (GenTrans_8_2 edb k_X k_Z) (combine q stags_ts);
    A2 s_A edb (snd (split searchRes)).
  
  
  Theorem G8_2_equiv : 
    Pr[G8_1] == Pr[G8_2].
    
    unfold G8_1, G8_2, G_gen, Initialize_8.
    do 6 (comp_skip; comp_simp).
    comp_skip.
    comp_irr_r.
    eapply compMap_wf; intuition.
    unfold GenTrans_8_2.
    comp_simp.
    wftac.
    eapply compMap_wf; intuition.
    wftac.
    eapply (@compMap_support _ _ (fun a b => b = GenTrans_4 (t, XSetSetup_2 x0 x1 d l1) x0 x a)) in H8.
    assert (map ( GenTrans_4 (t, XSetSetup_2 x0 x1 d l1) x0 x) (combine l x3) = x4).
    eapply list_pred_eq_impl_eq.
    eapply list_pred_map_l'.
    eapply list_pred_impl.
    eauto.
    intuition.
    subst.
    reflexivity.
    
    intuition.
    unfold GenTrans_8_2, GenTrans_4 in *.
    comp_simp.
    repeat simp_in_support.
    assert (x5 = map (fun (c : nat) =>  g ^ (F_P x0 k0 * F_P x (k ++ c))) (allNatsLt (length b0))).
    eapply list_pred_eq_impl_eq.
    
    eapply (@compMap_support _ _ (fun (a : nat) b => b = g ^ (F_P x0 k0 * F_P x (k ++ a)))) in H11.
    eapply list_pred_symm.
    eapply list_pred_map_l'.
    eapply H11.
    
    intuition.
    repeat simp_in_support.
    trivial.
    
    subst.
    reflexivity.

  Qed.
  

  Theorem G9_equiv :
    Pr[G8_2] == Pr[G9].
    
    unfold G8_2, G9, G9_A, Initialize_9.
    comp_skip.
    
    eapply comp_spec_eq_impl_eq.
    do 3 (simpl; inline_first; comp_skip; comp_simp).
    
    simpl; inline_first; comp_skip.

    eapply (@compMap_oc_spec _ _ eq).
    eapply list_pred_eq.
    intuition; subst.
    unfold Initialize_wLoop_8, Initialize_wLoop_9.
    comp_simp.
    repeat (simpl; inline_first; comp_skip; comp_simp).
    
    eapply (@compMap_oc_spec _ _ eq).
    eapply list_pred_eq.
    intuition; subst.
    pairInv.
    unfold Initialize_indLoop_8, Initialize_indLoop_9.
    
    repeat (simpl; inline_first; comp_skip; comp_simp); 
      try
        eapply (oneVector (lambda + lambda)).
    eapply comp_spec_ret; intuition.
    eapply comp_spec_ret; intuition.
    simpl in *.
    f_equal.
    eapply list_pred_eq_impl_eq; intuition.
    
    destruct b3.
    simpl in *.
    assert (a0 = l).
    eapply list_pred_eq_impl_eq; intuition.
    subst.
    remember (split l) as z.
    destruct z.
      
    repeat (simpl; inline_first; comp_skip; comp_simp).
    eapply (@compMap_oc_spec _ _ eq).
    eapply list_pred_eq.
    intuition; subst.
    pairInv.
    unfold GenTrans_8_2, GenTrans_9.
    
    comp_simp.
    simpl.
    comp_skip.
    eapply (@compMap_oc_spec _ _ eq).
    eapply list_pred_eq.
    intuition; subst.
    simpl.
    unfold f_oracle.
    comp_simp.
    eapply comp_spec_ret; intuition.
    comp_simp.
    simpl in *.
    eapply comp_spec_ret; intuition.
    simpl.
    assert (a0 = l2).
    eapply list_pred_eq_impl_eq.
    intuition.
    subst.
    reflexivity.

    inline_first; 
      comp_simp.
    simpl.
    inline_first.
    eapply comp_spec_eq_trans_l.
    eapply comp_spec_eq_symm.
    eapply comp_spec_right_ident.
    comp_skip.
    simpl in *.
    assert (a0 = l2).
    eapply list_pred_eq_impl_eq.
    intuition.
    subst.
    eapply comp_spec_eq_refl.
    subst.
    comp_simp.
    eapply comp_spec_eq_refl.
  Qed.

  (* Step 10: Replace the PRF with a random function. *)
  Definition G10 :=
    [b, _] <-$2 G9_A _ _ (@randomFunc Blist nat (RndNat (2^lambda)) _ ) nil;
    ret b.
  
  Theorem G10_close : 
  | Pr[G9] - Pr[G10] | <= PRF_Advantage (Rnd lambda) (RndNat (2^lambda)) F_P _ _ G9_A.
    
    reflexivity.
    
  Qed.

  (* DON'T USE PERMUTATIONS!!! Use a blinding construction that returns "None" when it is unblinded with an incompatible value. *)

  (*
  (* Step 10.1: change the codomain of the random function to an "option" type, but keep all values the same. *)
  Definition randomFuncOpt s d :=
    [r, s'] <-$2 (@randomFunc Blist _ (RndNat (2^lambda)) _ s d);
    ret (Some r, s').
  
  Definition Initialize_indLoop_10_1 k_I k_E w (e : Identifier lambda * nat) :=
    [ind, c] <-2 e;
    e <--$$ Enc k_E (zeroVector lambda);
    xind <- F_P k_I (Vector.to_list ind);
    opt_z <--$ query (w ++ c);
    $ ret
      match opt_z with
        | Some z => 
          y <- xind * (inverse z);
            Some (Vector.append e (natToBvector y), ind)
      | None => 
        None
      end.
  
  Fixpoint hasNone(A : Type)(ls : list (option A)) :=
    match ls with
      | nil => false
      | o :: ls' =>
        match o with
          | None => true
          | Some _ => hasNone ls'
        end
    end.
  
  Definition Initialize_wLoop_10_1 db k_I e :=
    [w, sigma] <-2 e;
    inds <- lookupInds db w;
    k_E <--$$ {0, 1}^lambda;
    indLoopRes <--$ oc_compMap _ (Initialize_indLoop_10_1 k_I k_E w) (combine (permute (oneVector lambda) inds sigma) (allNatsLt (length inds)));
    $ ret 
      if(hasNone indLoopRes) then None else Some (getSomes indLoopRes, sigma).
  
  Definition computeToken_10_1 e s (c : nat) :=
    opt_z <--$ query (s ++ c);
    $ ret 
      match opt_z with
        | None => None
        | Some z => 
          Some (g ^ (e * z))
      end.
  
  Definition GenTrans_10_1 (edb : EDB) k_X (e : Query * (Tag * list (Bvector (lambda + lambda) * (Bvector lambda)))) :=
    [q, stag_t] <-2 e;
    [stag, t] <-2 stag_t;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    e <- F_P k_X x;
    xtokens_raw <--$ oc_compMap _ (computeToken_10_1 e s) (allNatsLt (length t));
    if (hasNone xtokens_raw) then $ ret None else
      xtokens <- getSomes xtokens_raw;
    res <- ServerSearch_4 xSet xtokens t;
    es <- getSomes res;
    res <- map (fun z => match z with
                           | Some y => Some (fst y)
                           | None => None
                         end) res;
    inds <- map (fun x => snd x) es;
    $ ret (Some (inds, (stag, (combine xtokens res)))).

          
  Definition sampleSigmas_11 db w :=
    inds <- lookupInds db w;
    RndPerm (length inds).
    

  Definition Initialize_10_1 k_X k_I (db : DB)(q : list Query) sigmas :=    
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    wLoopRes_raw <--$ oc_compMap _ (Initialize_wLoop_10_1 db k_I) (combine (toW db) sigmas);
    if (hasNone wLoopRes_raw) then (OC_Ret _ _ (ret None)) else
    wLoopRes <- getSomes wLoopRes_raw;
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <--$2$ TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <--$$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes_raw <--$ oc_compMap _ (GenTrans_10_1 edb k_X) (combine q stags_ts);
    $ ret 
      if (hasNone searchRes_raw) then None else
        searchRes <- getSomes searchRes_raw;
        (Some (edb, searchRes)).

  Definition G10_1_A k_X k_I db q s_A sigmas :=
    z0_raw <--$ Initialize_10_1 k_X k_I db q sigmas; 
    match z0_raw with
      | None => $ ret false
      | Some z0 => 
        [edb, ls]<-2 z0; 
          $ A2 s_A edb (snd (split ls))
      end.

  Definition G10_1 :=
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    [db, q, s_A] <-$3 A1;
    sigmas <-$ compMap _ (sampleSigmas_11 db) (toW db);
    [b, _] <-$2 (G10_1_A k_X k_I db q s_A sigmas) _ _ (@randomFuncOpt) nil;
    ret b.
 
  *)

  (* Step 11:  Keep track of the blinding values and make sure nothing matches when we use the wrong value to unblind. *)
    Definition Initialize_indLoop_11 k_I k_E w (e : Identifier lambda * nat) :=
    [ind, c] <-2 e;
    e <--$$ Enc k_E (zeroVector lambda);
    xind <- F_P k_I (Vector.to_list ind);
    z <--$ query (w ++ c);
    y <- xind * (inverse z);
    $ ret (Vector.append e (natToBvector y), (ind, z)).

    Definition Initialize_wLoop_11 db k_I e :=
      [w, sigma] <-2 e;
    inds <- lookupInds db w;
    k_E <--$$ {0, 1}^lambda;
    indLoopRes <--$ oc_compMap _ (Initialize_indLoop_11 k_I k_E w) (combine (permute inds sigma) (allNatsLt (length inds)));
    $ ret (indLoopRes, sigma).

    Definition ServerSearchLoop_11 xSet (e : (nat * nat) * (Bvector (lambda + lambda) * (Bvector lambda * nat))) :=
    [xtoken_z1, t_c_ind_z2] <-2 e;
      [xtoken, z1] <-2 xtoken_z1;
     [t_c, ind_z2] <-2 t_c_ind_z2;
     [ind, z2] <-2 ind_z2;
     if (eq_nat_dec z1 z2) then 
       (
         [e, y] <-2 splitVector lambda _ t_c;
         if (in_dec (EqDec_dec _) (xtoken^(bvectorToNat y)) xSet) then (Some (e, ind)) else None
       )
     else None.

  Definition ServerSearch_11 xSet (xtokens : list (nat * nat)) (t : list (Bvector (lambda + lambda) * (Bvector lambda * nat))) :=
    map (ServerSearchLoop_11 xSet) (combine xtokens t).

    Definition GenTrans_11 (edb : EDB) k_X (e : Query * (Tag * list (Bvector (lambda + lambda) * (Bvector lambda * nat)))) :=
    [q, stag_t] <-2 e;
    [stag, t] <-2 stag_t;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    e <- F_P k_X x;
    xtokens <--$ oc_compMap _ (fun (c : nat) => z <--$ query s ++ c; $ ret (g^(e * z), z)) (allNatsLt (length t));
    res <- ServerSearch_11 xSet xtokens t;
    es <- getSomes res;
    res <- map (fun z => match z with
                           | Some y => Some (fst y)
                           | None => None
                         end) res;
    inds <- map (fun x => snd x) es;
    $ ret (inds, (stag, (combine (fst (split xtokens)) res))).



  Definition Initialize_11 k_X k_I (db : DB)(q : list Query) sigmas xSet :=
    wLoopRes <--$ oc_compMap _ (Initialize_wLoop_11 db k_I) (combine (toW db) sigmas);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <--$2$ TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <--$$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <--$ oc_compMap _ (GenTrans_11 edb k_X) (combine q stags_ts);
    $ ret (edb, searchRes).


  Definition sampleSigmas_11 db w :=
    inds <- lookupInds db w;
    RndPerm (length inds).
  
  Definition G11 :=
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    [db, q, s_A] <-$3 A1;
    sigmas <-$ compMap _ (sampleSigmas_11 db) (toW db);
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    [z, _] <-$2 (Initialize_11 k_X k_I db q sigmas xSet) _ _ (@randomFunc Blist nat (RndNat (2^lambda)) _ ) nil;
    [edb, ls] <-2 z;
     A2 s_A edb (snd (split ls)).


  (* Step 10.1 : move some things around and add some bookkeeping to get closer to game 11. *)
 
  Definition Initialize_indLoop_10_1 k_I k_E w (e : Identifier lambda * nat) :=
    [ind, c] <-2 e;
    e <--$$ Enc k_E (zeroVector lambda);
    xind <- F_P k_I (Vector.to_list ind);
    z <--$ query (w ++ c);
    y <- xind * (inverse z);
    $ ret (Vector.append e (natToBvector y), (ind, z)).

    Definition Initialize_wLoop_10_1 db k_I w :=
    inds <- lookupInds db w;
      sigma <--$$ RndPerm (length inds);
    k_E <--$$ {0, 1}^lambda;
    indLoopRes <--$ oc_compMap _ (Initialize_indLoop_11 k_I k_E w) (combine (permute inds sigma) (allNatsLt (length inds)));
    $ ret (indLoopRes, sigma).

  Definition ServerSearchLoop_10_1 xSet (e : (nat * nat) * (Bvector (lambda + lambda) * (Bvector lambda * nat))) :=
    [xtoken_z1, t_c_ind_z2] <-2 e;
      [xtoken, z1] <-2 xtoken_z1;
     [t_c, ind_z2] <-2 t_c_ind_z2;
     [ind, z2] <-2 ind_z2;
     [e, y] <-2 splitVector lambda _ t_c;
     if (in_dec (EqDec_dec _) (xtoken^(bvectorToNat y)) xSet) then (Some (e, ind)) else None.

  Definition ServerSearch_10_1 xSet (xtokens : list (nat * nat)) (t : list (Bvector (lambda + lambda) * (Bvector lambda * nat))) :=
    map (ServerSearchLoop_10_1 xSet) (combine xtokens t).

    Definition GenTrans_10_1 (edb : EDB) k_X (e : Query * (Tag * list (Bvector (lambda + lambda) * (Bvector lambda * nat)))) :=
    [q, stag_t] <-2 e;
    [stag, t] <-2 stag_t;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    e <- F_P k_X x;
    xtokens <--$ oc_compMap _ (fun (c : nat) => z <--$ query s ++ c; $ ret (g^(e * z), z)) (allNatsLt (length t));
    res <- ServerSearch_10_1 xSet xtokens t;
    es <- getSomes res;
    res <- map (fun z => match z with
                           | Some y => Some (fst y)
                           | None => None
                         end) res;
    inds <- map (fun x => snd x) es;
    $ ret (inds, (stag, (combine (fst (split xtokens)) res))).

   Definition Initialize_10_1 k_X k_I (db : DB)(q : list Query) :=
    wLoopRes <--$ oc_compMap _ (Initialize_wLoop_10_1 db k_I) (toW db);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <--$2$ TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <--$$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <--$ oc_compMap _ (GenTrans_10_1 edb k_X) (combine q stags_ts);
    $ ret (edb, searchRes).

    Definition G10_1 :=
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    [db, q, s_A] <-$3 A1;
    [z, _] <-$2 (Initialize_10_1 k_X k_I db q) _ _ (@randomFunc Blist nat (RndNat (2^lambda)) _ ) nil;
    [edb, ls] <-2 z;
     A2 s_A edb (snd (split ls)).

    Theorem G10_1_equiv : 
      Pr[G10] == Pr[G10_1].

      unfold G10, G10_1, G9_A.
      Local Opaque evalDist.
      simpl.
      inline_first.
      comp_at comp_swap rightc 1%nat.
      comp_swap_r.
      comp_skip.
      comp_simp.
      simpl.
      inline_first.
      do 2 (comp_skip; comp_simp; inline_first).
      eapply comp_spec_eq_impl_eq.
      comp_skip.

      Theorem oc_compMap_spec:
        forall (D E S A1 A2 : Set) P1 P2 (inv : S -> Prop) (B C : Set) (eqdd : EqDec D)(eqde : EqDec E) (f1 : A1 -> OracleComp B C D)(f2 : A2 -> OracleComp B C E)
               (ls1 : list A1)(ls2 : list A2)(eqds : EqDec S) (o : S -> B -> Comp (C * S))
               (s : S) ,
          list_pred P1 ls1 ls2 ->
          inv s ->
          (forall (s0 : S) (a1 : A1)(a2 : A2),
             inv s0 ->
             P1 a1 a2 ->
             In a1 ls1 ->
             In a2 ls2 ->
             comp_spec (fun a b => (P2) (fst a) (fst b) /\ snd a = snd b /\ inv (snd a)) ((f1 a1) S eqds o s0) ((f2 a2) S eqds o s0)) ->
          comp_spec (fun a b => list_pred (P2) (fst a) (fst b) /\ snd a = snd b /\ inv (snd a)) ((oc_compMap _ f1 ls1) S eqds o s)
                    ((oc_compMap _ f2 ls2) S eqds o s).

        induction ls1; inversion 1; intuition; simpl in *; subst.
        comp_simp.
        eapply comp_spec_ret; intuition.
        simpl.
        econstructor.

        comp_skip.
        comp_simp.
        simpl in *.
        subst.
        
        comp_skip.
        comp_simp.
        simpl in *.
        eapply comp_spec_ret; intuition.
        subst.
        simpl.
        econstructor; intuition.

      Qed.

      eapply (@oc_compMap_spec _ _ _ _ _ _
                               (fun a b => 
                                  (fst (split (fst a))) = (fst (split (fst b))) /\
                                  (snd (split (fst a))) = (fst (split (snd (split (fst b))))) /\ 
                                  snd a = snd b
             )
             (fun s => True)
             ).

      eapply list_pred_eq.
      intuition.
      intuition; subst.
      unfold Initialize_wLoop_9, Initialize_wLoop_10_1.
      comp_simp.
      simpl.
      inline_first.
      comp_skip.
      comp_simp.
      inline_first.
      comp_skip.
      comp_simp.
      comp_skip.
      eapply (@oc_compMap_spec _ _ _ _ _ _ (fun a b => fst a = fst b /\ snd a = fst (snd b)) (fun s => True)).
      eapply list_pred_eq; intuition.
      intuition.
      intuition.
      subst.
      
      unfold Initialize_indLoop_9, Initialize_indLoop_11.
      comp_simp; simpl.
      inline_first.
      comp_skip.
      eapply (oneVector (lambda + lambda)).
      eapply (oneVector (lambda + lambda)).
      comp_simp.
      comp_skip.
      eapply (oneVector (lambda + lambda)).
      eapply (oneVector (lambda + lambda)).
      comp_simp.
      eapply comp_spec_ret; intuition.
      comp_simp.
      simpl in *.
      eapply comp_spec_ret; intuition.
      simpl.
      subst.
      split_eq.
      eapply list_pred_impl; eauto.
      intuition.
      subst.
      simpl.
      split_eq.
      eapply list_pred_impl; eauto.
      intuition.
      
      destruct b0.
      remember (split a1) as z.
      destruct z.
      remember (split l0) as z.
      destruct z.
      simpl.
      inline_first.
      simpl in *; intuition.
      subst.
      assert ((foreach  (v in l2)fst (split v)) = 
              (foreach  (v in l4)fst (split v))).

      eapply (@map_ext_pred _ _ _
                             (fun
            (a0 : list (Vector.t bool (lambda + lambda) * Identifier lambda))
            (b : list
                   (Vector.t bool (lambda + lambda) *
                    (Identifier lambda * nat))) =>
          fst (split a0) = fst (split b) /\
          snd (split a0) = fst (split (snd (split b)))
                       )
                             ).

      assert (l2 = (fst (split a1))).
      rewrite <- Heqz.
      trivial.
      assert (l4 = fst (split l0)).
      rewrite <- Heqz0.
      trivial.
      subst.
      split_eq.
      eapply list_pred_impl; eauto.
      intuition.
      intuition.
      
      rewrite H5.
      comp_skip.
      simpl; inline_first.
      comp_simp.
      simpl.
      inline_first.
      eapply (@comp_spec_seq _ _); eauto with inhabited.
      eapply (@compMap_spec _ _ _ _ _ _ _ (fun a b => fst a = fst b)).
      eapply list_pred_eq.
      
      intuition; subst.
      comp_skip.
      eapply comp_base_exists; eauto.
      eapply comp_base_exists; eauto.
      eapply comp_spec_ret; intuition.
      intuition.
      comp_simp.
      inline_first.

      (*

      eapply (@compMap_support _ _ (fun a b => (snd b) = arrayLookupList (list_EqDec bool_EqDec)
                    (combine (toW d) l2) a)) in H10.
      eapply (@compMap_support _ _ (fun a b => (snd b) = arrayLookupList (list_EqDec bool_EqDec)
                    (combine (toW d) l4) a)) in H11.

      comp_skip.
      eapply oc_compMap_spec.
      eapply list_pred_combine_l.
      eapply list_pred_symm.
      eapply list_pred_impl.
      eapply list_pred_combine_l.
      eapply list_pred_eq.
      eapply list_pred_symm.
      eapply list_pred_impl.
      eapply list_pred_fst_split_irr_if.
      eapply H11.
      intuition.
      eapply H13.
      intuition.
      simpl in *.
      subst.
      
      eapply list_pred_symm.
      eapply list_pred_impl.
      eapply list_pred_combine_l.
      eapply list_pred_symm.
      eapply list_pred_impl.
      eapply list_pred_fst_split_irr_if.
      eapply H10.
      intuition.
      eapply H13.
      
      intuition.
      eapply H13.
      intuition.
      simpl in *.
      subst.
*)
      
    Admitted.

    (* Step 10.2 : compute the permutations and the XSet at the beginning. *)
    Definition Initialize_10_2 k_X k_I (db : DB)(q : list Query) sigmas xSet :=
    wLoopRes <--$ oc_compMap _ (Initialize_wLoop_11 db k_I) (combine (toW db) sigmas);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <--$2$ TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <--$$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <--$ oc_compMap _ (GenTrans_10_1 edb k_X) (combine q stags_ts);
    $ ret (edb, searchRes).

    Definition G10_2 :=
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    [db, q, s_A] <-$3 A1;
    sigmas <-$ compMap _ (sampleSigmas_11 db) (toW db);
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    [z, _] <-$2 (Initialize_10_2 k_X k_I db q sigmas xSet) _ _ (@randomFunc Blist nat (RndNat (2^lambda)) _ ) nil;
    [edb, ls] <-2 z;
     A2 s_A edb (snd (split ls)).

    Theorem oc_compMap_fission_r : 
    forall (A B C D E : Set)(eqdd : EqDec D)(eqde : EqDec E)(ls : list A)(c1 : A -> OracleComp B C D)(c2 : D -> Comp E)
           (S : Set)(eqds : EqDec S)(o : S -> B -> Comp (C * S))(s : S) x,
      evalDist ((oc_compMap _ (fun a => d <--$ c1 a; $ (c2 d)) ls) _ _ o s) x ==
      evalDist ([lsD, s'] <-$2 (oc_compMap _ c1 ls) _ _ o s; v <-$ (compMap _ c2 lsD); ret (v, s')) x.
    
    Local Opaque evalDist.
    induction ls; intuition; simpl in *.
    inline_first; comp_simp.
    simpl.
    comp_simp.
    eapply evalDist_ret_eq; intuition.
    
    inline_first.
    comp_skip.
    comp_simp.
    
    inline_first.
    
    assert (
        (evalDist
           (Bind (c2 d)
                 (fun a1 : E =>
                    Bind
                      (Ret (EqDec_dec (pair_EqDec (comp_EqDec (c2 d)) eqds))
                           (pair a1 s0))
                      (fun z0 : prod E S =>
                         let 'pair z s' := z0 in
                         Bind
                           ((oc_compMap eqde
                                        (fun a2 : A =>
                                           OC_Bind (c1 a2) (fun d0 : D => OC_Ret B C (c2 d0)))
                                        ls) S eqds o s')
                           (fun z1 : prod (list E) S =>
                              let 'pair z2 s'0 := z1 in
                              Bind
                                (Ret (EqDec_dec (list_EqDec eqde)) (cons z z2))
                                (fun x : list E =>
                                   Ret
                                     (EqDec_dec
                                        (pair_EqDec
                                           (comp_EqDec
                                              (Ret (EqDec_dec (list_EqDec eqde))
                                                   (cons z z2))) eqds))
                                     (pair x s'0)))))) 
           (pair a0 b))
     ==
     evalDist
       (z1 <-$
           (oc_compMap eqde (fun a2 : A => d0 <--$ c1 a2; $ c2 d0) ls) S eqds o s0;
        a1 <-$ c2 d;
        
        [z2, s'0]<-2 z1; x <-$ ret a1 :: z2; ret (x, s'0)) 
       (a0, b) 
      ).
    
    comp_swap_r.
    comp_skip.
    comp_skip.
    comp_simp.
    eapply evalDist_ret_eq; intuition.
    rewrite H0.
    clear H0.
    eapply eqRat_trans.
    comp_skip.
    eapply eqRat_refl.
    inline_first.
    comp_skip.
    comp_simp.
    inline_first.
    comp_simp.
    simpl.
    inline_first.
    comp_at comp_inline rightc 1%nat.        
    comp_swap_r.
    comp_skip.
  Qed.

  Theorem oc_compMap_fission_l : 
    forall (A B C D E : Set)(eqdd : EqDec D)(eqde : EqDec E)(ls : list D)(c1 : E -> OracleComp B C D)(c2 : D -> Comp E)
           (S : Set)(eqds : EqDec S)(o : S -> B -> Comp (C * S))(s : S) x,
      evalDist ((oc_compMap _ (fun d => e <--$$ c2 d; (c1 e)) ls) _ _ o s) x ==
      evalDist ( lsE <-$ compMap _ c2 ls; (oc_compMap _ c1 lsE) _ _ o s) x.
    
    Local Opaque evalDist.
    induction ls; intuition; simpl in *.
    inline_first; comp_simp.
    simpl.
    comp_simp.
    eapply evalDist_ret_eq; intuition.
    
    inline_first.
    comp_skip.
    inline_first.

    assert (
        (evalDist
        (Bind (compMap eqde c2 ls)
           (fun a1 : list E =>
            Bind (Ret (EqDec_dec (list_EqDec eqde)) (cons x a1))
              (fun lsE : list E => (oc_compMap eqdd c1 lsE) S eqds o s)))
        (pair a0 b))
     ==
     evalDist
     (a1 <-$ (foreach  (x in ls)c2 x);
      [z, s'] <-$2 (c1 x) _ _ o s;
      [lsE, s''] <-$2 (oc_compMap eqdd c1 a1) S eqds o s';
        ret (z :: lsE, s''))
     (a0, b)
     ).

    comp_skip.
    reflexivity.
    simpl.
    comp_skip.
    comp_simp.
    comp_skip.
    comp_simp.
    eapply evalDist_ret_eq; intuition.
    rewrite H0.
    clear H0.
    comp_swap_r.
    comp_skip.
    comp_simp.
    eapply eqRat_trans.
    comp_skip.
    eapply eqRat_refl.
    inline_first.
    comp_skip.
    reflexivity.
    comp_skip.
    comp_simp.
    eapply evalDist_ret_eq.
    intuition.
  Qed.

  (* Step 10.3 : Check the random function for badness and expose it. *)

  Variable MaxMatchingIDs : nat.

  Print DB_Entry.

  Definition allPairs_1(A B : Type)(a : A)(lsb : list B) :=
    map (pair a) lsb.

  Definition allPairs_2(A B : Type)(lsa : list A)(lsb : list B) : list (A * B) :=
    flatten (map (fun a => allPairs_1 a lsb) lsa).

  Definition badBlinding_ezxz (xSet : list nat) (e z : nat)(p : nat * nat) :=
    [xind, y] <-2 p;
    if (eq_nat_dec y z) then false else
      if (in_dec (EqDec_dec _) (g^(e * z * xind * (inverse y))) xSet ) then true else false.

  Definition badBlinding_ez (xinds : list nat)(f : list (Blist * nat)) (xSet : list nat) (e z : nat) :=
    allXindsZs <- allPairs_2 xinds (snd (split f));
    fold_left (fun (b : bool) x => if b then true else badBlinding_ezxz xSet e z x) allXindsZs false.

  Definition badBlinding_c k_X (xinds : list nat)(f : list (Blist * nat)) xSet (q : Query)(c : nat) :=
    [s, x] <-2 q;
    e <- F_P k_X x;
    z_opt <- arrayLookup _ f (s ++ c);
    match z_opt with
        | None => false
        | Some z => badBlinding_ez xinds f xSet e z
    end.
    
  Definition badBlinding_q k_X (xinds : list nat)(f : list (Blist * nat)) xSet (q : Query) :=
    fold_left (fun (b : bool) z => if b then true else badBlinding_c k_X xinds f xSet q z) (allNatsLt MaxMatchingIDs) false.

  Definition badBlinding k_I k_X (db : DB)(f : list (Blist * nat)) xSet (q : list Query) :=
    xinds <- map (fun x => F_P k_I (Vector.to_list x)) (fst (split db));
    fold_left (fun (b : bool) x => if b then true else (badBlinding_q k_X  xinds f xSet x)) q false.

   Definition goodBlinding_ezxz_Prop (xSet : list nat) (e z : nat)(xind y : nat) :=
     In (g ^ (e * z * xind * (inverse y))) xSet -> 
     y = z.

  Definition goodBlinding_ez_Prop (xinds : list nat)(f : list (Blist * nat)) (xSet : list nat) (e z : nat) :=
    forall xind y, 
      In (xind, y) (allPairs_2 xinds (snd (split f))) ->
      goodBlinding_ezxz_Prop xSet e z xind y.

  Definition goodBlinding_c_Prop k_X (xinds : list nat)(f : list (Blist * nat)) xSet s x (c : nat) :=
    forall z, 
      arrayLookup _ f (s ++ c) = Some z ->
    goodBlinding_ez_Prop xinds f xSet (F_P k_X x) z.

    
  Definition goodBlinding_q_Prop k_X (xinds : list nat)(f : list (Blist * nat)) xSet s x :=
    forall z,
      In z (allNatsLt MaxMatchingIDs) ->
      goodBlinding_c_Prop k_X xinds f xSet s x z.
  
  Theorem fold_left_bad_true : 
    forall (A : Type)(f : A -> bool) ls,
      fold_left (fun (b : bool)(a : A) => if b then true else (f a)) ls true = true.
    
    induction ls; intuition.
    
  Qed.

  Theorem badBlinding_ez_Prop_correct_h : 
    forall ls xSet y z0 xind y0,
      fold_left
        (fun (b : bool) (x : nat * nat) =>
         if b then true else badBlinding_ezxz xSet y z0 x)
        ls false = false ->
        In (xind, y0) ls ->
        goodBlinding_ezxz_Prop xSet y z0 xind y0.

    induction ls; intuition; simpl in *.
    intuition.
    intuition.
    pairInv.

    destruct (eq_nat_dec y0 z0); subst.
    unfold goodBlinding_ezxz_Prop.
    intuition.

    destruct ( in_dec (EqDec_dec nat_EqDec) (g ^ (y * z0 * xind * inverse y0))
              xSet).
    rewrite fold_left_bad_true in H.
    discriminate.
    
    unfold goodBlinding_ezxz_Prop.
    intuition.

    destruct (eq_nat_dec b z0); subst.
    eapply IHls; intuition.
    destruct (in_dec (EqDec_dec nat_EqDec) (g ^ (y * z0 * a0 * inverse b)) xSet).
    rewrite fold_left_bad_true in H.
    discriminate.
    eapply IHls; intuition.
  Qed.
  
  Theorem badBlinding_ez_Prop_correct : 
    forall xinds f xSet y z0,
    badBlinding_ez xinds f xSet y z0 = false ->
    goodBlinding_ez_Prop xinds f xSet y z0.

    unfold goodBlinding_ez_Prop.
    intuition.
    eapply  badBlinding_ez_Prop_correct_h.
    eapply H.
    trivial.

  Qed.

  Theorem goodBlinding_q_Prop_correct_h : 
    forall ls k_X xinds f xSet s x z,
      fold_left
        (fun (b : bool) (z : nat) =>
         if b then true else badBlinding_c k_X xinds f xSet (s, x) z)
        ls false = false ->
        In z ls ->
        goodBlinding_c_Prop k_X xinds f xSet s x z.

    induction ls; intuition; simpl in *.

    unfold goodBlinding_q_Prop.
    intuition.

    intuition; subst.
    unfold setLet in *.
    unfold goodBlinding_c_Prop; intuition.
    rewrite H1 in H.
    
    case_eq (badBlinding_ez xinds f xSet (F_P k_X x) z0); intuition.
    rewrite H2 in H.
    rewrite fold_left_bad_true in H.
    discriminate.

    eapply badBlinding_ez_Prop_correct; intuition.

    unfold setLet in *.

    case_eq ( @arrayLookup Blist nat (@list_EqDec bool bool_EqDec) f
               (@app bool s (natToBlist a))); intuition;
    rewrite H1 in H.
    
    case_eq ((badBlinding_ez xinds f xSet (F_P k_X x) n)); intuition.
    rewrite H3 in H.
    rewrite fold_left_bad_true in H.
    discriminate.

    rewrite H3 in H.

    eapply IHls.
    eapply H.
    trivial.

    eapply IHls.
    eapply H.
    trivial.
  Qed.
    
  Theorem goodBlinding_q_Prop_correct : 
    forall k_X xinds f xSet s x,
      badBlinding_q k_X xinds f xSet (s, x) = false ->
      goodBlinding_q_Prop k_X xinds f xSet s x.

    unfold badBlinding_q, goodBlinding_q_Prop.
    intuition.
    eapply goodBlinding_q_Prop_correct_h; eauto.

  Qed.

  Definition natRandFunc := (@randomFunc Blist nat (RndNat (2^lambda)) _ ).
  
  Definition G10_3 :=
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    [db, q, s_A] <-$3 A1;
    sigmas <-$ compMap _ (sampleSigmas_11 db) (toW db);
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    [z, f] <-$2 (Initialize_10_2 k_X k_I db q sigmas xSet) _ _ natRandFunc nil;
    [edb, ls] <-2 z;
    b <-$ A2 s_A edb (snd (split ls));
    ret (b, badBlinding k_I k_X db f xSet q).

  (* Step 10.4 : use the bookkeeping and only unblind when the z values match *)
  Definition G10_4 :=
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    [db, q, s_A] <-$3 A1;
    sigmas <-$ compMap _ (sampleSigmas_11 db) (toW db);
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    [z, f] <-$2 (Initialize_11 k_X k_I db q sigmas xSet) _ _ natRandFunc nil;
    [edb, ls] <-2 z;
    b <-$ A2 s_A edb (snd (split ls));
    ret (b, badBlinding k_I k_X db f xSet q).

  
  Hypothesis natGroupOp_exp : 
    forall a b c,
      a ^ (b * c)%group = a ^ (b * c)%nat.

  Hypothesis MaxMatchingIDs_correct : 
    forall db q s_A,
      In (db, q, s_A) (getSupport A1) ->
      forall w,
        (length (lookupInds db w) <= MaxMatchingIDs)%nat.

  Theorem compMap_support_unary : 
    forall (A B : Set)(eqdb : EqDec B)(P : B -> Prop)(lsa : list A)(c : A -> Comp B)(lsb : list B),
      In lsb (getSupport (compMap _ c lsa)) ->
      (forall a b, In a lsa -> In b (getSupport (c a)) -> P b) ->
      forall b, In b lsb -> P b.
    
    Local Opaque getSupport.
    
    induction lsa; intuition; simpl in *;
    repeat simp_in_support.
    simpl in *.
    intuition.
    
    simpl in *.
    intuition; subst.
    eapply H0; intuition.
    eapply IHlsa; eauto.
    
  Qed.

  Theorem natRandFunc_badBlinding_persists : 
    (forall q f1 f2 xSet db k_X k_I a b,
       badBlinding k_I k_X db f1 xSet q = true ->
       In (b, f2) (getSupport (natRandFunc f1 a)) -> 
       badBlinding k_I k_X db f2 xSet q = true).
    
    intuition.
    unfold natRandFunc, randomFunc in *.
    case_eq (arrayLookup (list_EqDec bool_EqDec) f1 a); intuition;
    unfold Blist in *;
    rewrite H2 in H1; 
    repeat simp_in_support.
    trivial.
    
    
    Theorem badBlinding_ez_f_app : 
      forall xinds f1 xSet y n a x,
      badBlinding_ez xinds f1 xSet y n = true ->
      badBlinding_ez xinds ((a, x) :: f1) xSet y n = true.

      induction xinds;

      intuition.
      unfold badBlinding_ez in *.
      unfold setLet in *.
      unfold allPairs_2 in *.
      simpl in *.

      Theorem fold_left_bool_app_true : 
        forall (A : Set)(ls1 ls2 : list A) f,
          fold_left (fun (b : bool) a => if b then true else (f a)) (ls1 ++ ls2) false = true ->
          fold_left (fun (b : bool) a => if b then true else (f a)) ls1 false = true \/
          fold_left (fun (b : bool) a => if b then true else (f a)) ls2 false = true.

        induction ls1; intuition; simpl in *.
        destruct (f a).
        left.
        eapply fold_left_bad_true.

        eapply IHls1.
        trivial.

      Qed.

      Theorem fold_left_bool_app_true_l : 
        forall (A : Set)(ls1 ls2 : list A) f,
          fold_left (fun (b : bool) a => if b then true else (f a)) ls1 false = true  ->
          fold_left (fun (b : bool) a => if b then true else (f a)) (ls1 ++ ls2) false = true.

        induction ls1; intuition; simpl in *.
        destruct (f a).
        eapply fold_left_bad_true.
        eauto.
      
      Qed.

      Theorem fold_left_bool_app_true_r : 
        forall (A : Set)(ls1 ls2 : list A) f,
          fold_left (fun (b : bool) a => if b then true else (f a)) ls2 false = true  ->
          fold_left (fun (b : bool) a => if b then true else (f a)) (ls1 ++ ls2) false = true.

        induction ls1; intuition; simpl in *.
        destruct (f a).
        eapply fold_left_bad_true.
        eauto.
      
      Qed.

      specialize (IHxinds f1).
      remember (split f1) as z.
      destruct z.
      simpl in *.
      destruct (eq_nat_dec x n); subst.
      
      eapply fold_left_bool_app_true in H; intuition.
      eapply fold_left_bool_app_true_l .
      trivial.
      
      eapply fold_left_bool_app_true_r .
      eapply IHxinds; eauto.

      destruct (in_dec (EqDec_dec nat_EqDec) (g ^ (y * n * a * inverse x)) xSet).
      eapply fold_left_bad_true.
      
      eapply fold_left_bool_app_true in H; intuition.
      eapply fold_left_bool_app_true_l .
      trivial.
      eapply fold_left_bool_app_true_r .
      eapply IHxinds; eauto.

    Qed.

    Theorem badBlinding_c_f_app : 
      forall q f1 xSet k_X xinds a x c,
        arrayLookup _ f1 a = None ->
        badBlinding_c k_X xinds f1 xSet q c = true ->
        badBlinding_c k_X xinds ((a, x) :: f1) xSet q c = true.
      
      intuition.
      unfold badBlinding_c in *.
      destruct q.
      unfold setLet in *.

      simpl.
      case_eq (@eqb Blist (@list_EqDec bool bool_EqDec)
           (@app bool k (natToBlist c)) a); intuition.
      rewrite eqb_leibniz in H2.
      subst.
      rewrite H in H1.
      discriminate.

      case_eq (@arrayLookup Blist nat (@list_EqDec bool bool_EqDec) f1
             (@app bool k (natToBlist c)) ); intuition.
      rewrite H3 in H1.
      eapply badBlinding_ez_f_app ; intuition.

      rewrite H3 in H1.
      discriminate.

    Qed.

    Theorem badBlinding_q_f_app_h : 
      forall ls q f1 xSet k_X xinds a x ,
        arrayLookup _ f1 a = None ->
        fold_left
          (fun (b : bool) (z : nat) =>
             if b then true else badBlinding_c k_X xinds f1 xSet q z)
          ls false = true ->
        fold_left
          (fun (b : bool) (z : nat) =>
             if b then true else badBlinding_c k_X xinds ((a, x) :: f1) xSet q z)
          ls false = true.
      
      induction ls; intuition; simpl in *.
      
      case_eq ((badBlinding_c k_X xinds f1 xSet q a)); intuition.
      erewrite badBlinding_c_f_app.
      eapply fold_left_bad_true.
      trivial.
      eauto.
      
      rewrite H2 in H1.
      destruct ((badBlinding_c k_X xinds ((a0, x) :: f1) xSet q a)).
      eapply fold_left_bad_true.
      eapply IHls.
      trivial.
      trivial.
    Qed.
    
    Theorem badBlinding_q_f_app : 
      forall q f1 xSet k_X xinds a x ,
        arrayLookup _ f1 a = None ->
        badBlinding_q k_X xinds f1 xSet q = true ->
        badBlinding_q k_X xinds ((a, x) :: f1) xSet q = true.
      
      intuition.
      unfold badBlinding_q in *.
      eapply badBlinding_q_f_app_h.
      trivial.
      trivial.
    Qed.    
    
    Theorem badBlinding_f_app : 
      forall q f1 xSet db k_X k_I a x ,
        arrayLookup _ f1 a = None ->
        badBlinding k_I k_X db f1 xSet q = true ->
        badBlinding k_I k_X db ((a, x) :: f1) xSet q = true.
      
      induction q; intuition.
      unfold badBlinding.
      unfold badBlinding in H1.
      unfold setLet in *.
      simpl in *.
      
      case_eq ((badBlinding_q k_X
                              (foreach  (x0 in fst (split db))F_P k_I (Vector.to_list x0)) f1
                              xSet a)); intuition.
      erewrite badBlinding_q_f_app.
      eapply fold_left_bad_true.
      trivial.
      trivial.
      rewrite H2 in H1.

      case_eq (badBlinding_q k_X
                             (foreach  (x0 in fst (split db))F_P k_I (Vector.to_list x0))
                             ((a0, x) :: f1) xSet a); intuition.
      eapply fold_left_bad_true.
      unfold badBlinding in *.
      unfold setLet in *.
      eapply IHq.
      trivial.
      eauto.
    Qed.
    
    eapply badBlinding_f_app.
    trivial.
    trivial.
  Qed.
  
  Theorem natRandFunc_badBlinding_persists_oc : 
    (forall (X : Set) (c : OracleComp _ _ X) (a : X) f1 f2 q xSet db k_X k_I,
       badBlinding k_I k_X db f1 xSet q = true ->
       In (a, f2) (getSupport (c _ _ natRandFunc f1)) -> 
       badBlinding k_I k_X db f2 xSet q = true) .
    
    intuition.
    eapply (@oc_comp_invariant _ _ _ c _ (fun s => badBlinding k_I k_X db s xSet q = true) _ natRandFunc); intuition.
    
    eapply natRandFunc_badBlinding_persists;
      eauto.
    eauto.
    eauto.
    
  Qed.

  Definition goodBlinding_Prop k_I k_X (db : DB) f xSet qs :=
    xinds <- (foreach  (x in fst (split db))F_P k_I (Vector.to_list x));
    forall s x, In (s, x) qs ->
                goodBlinding_q_Prop k_X xinds f xSet s x.
  
  Theorem goodBlinding_Prop_correct : 
    forall qs k_I k_X db f xSet,
      badBlinding k_I k_X db f xSet qs = false ->
      goodBlinding_Prop k_I k_X db f xSet qs.
    
    induction qs; 
    intuition;
    unfold badBlinding, goodBlinding_Prop in *;
    unfold setLet in *;
    intuition.
          
    simpl in *.
    intuition.
    
    simpl in *.
    intuition.
    subst.
    
    case_eq (badBlinding_q k_X
                           (foreach  (x0 in fst (split db))F_P k_I (Vector.to_list x0)) f
                           xSet (s, x)); intuition;
    rewrite H in H0.
    rewrite fold_left_bad_true in H0.
    discriminate.
    
    eapply goodBlinding_q_Prop_correct; intuition.
    
    case_eq (badBlinding_q k_X
                           (foreach  (x in fst (split db))F_P k_I (Vector.to_list x)) f xSet
                           a); intuition;
    rewrite H in H0.
    rewrite fold_left_bad_true in H0.
    discriminate.
    
    eapply IHqs.
    eauto.
    trivial.
  Qed.


  Theorem oc_compMap_wf : 
    forall (A B C D : Set)(eqdd : EqDec D)(ls : list A)(c : A -> OracleComp B C D)(S : Set)(eqds : EqDec S)(inv : S -> Prop)(o : S -> B -> Comp (C * S))(s : S),
      (forall a, In a ls -> well_formed_oc (c a)) ->
      (forall s a, inv s -> well_formed_comp (o s a)) ->
      inv s -> 
      (forall s s' b c, inv s -> In (c, s') (getSupport (o s b)) -> inv s') ->
      well_formed_comp ((oc_compMap _ c ls) _ _ o s).

    induction ls; intuition; simpl in *;
    wftac.

    eapply oc_comp_wf_inv.
    eauto.
    intuition.
    eapply H0.
    eapply H3.
    intuition.
    eapply H2; intuition.
    eapply H3.
    eauto.
    trivial.
    
    eapply IHls;
    intuition.
    eapply H0.
    eapply H4.
    eapply oc_comp_invariant.
    intuition.
    eapply H2.
    eapply H5.
    eauto.
    eapply H1.
    eauto.
    eapply H2.
    eapply H4.
    eauto.
  Qed.


  Theorem oc_compMap_spec_bad:
    forall (D E S A1 A2 : Set) P1 P2 (inv : S -> Prop)(bad : S -> bool) (B C : Set) (eqdd : EqDec D)(eqde : EqDec E) (f1 : A1 -> OracleComp B C D)(f2 : A2 -> OracleComp B C E)
           (ls1 : list A1)(ls2 : list A2)(eqds : EqDec S) (o : S -> B -> Comp (C * S))
           (s : S) ,
      list_pred P1 ls1 ls2 ->
      bad s = false ->
      inv s ->
      (forall a, In a ls1 -> well_formed_oc (f1 a)) ->
      (forall a, In a ls2 -> well_formed_oc (f2 a)) ->
      (forall s a, inv s -> well_formed_comp (o s a)) ->
      (forall s s' a b ,
         inv s -> In (b, s') (getSupport (o s a)) -> inv s') ->
      (forall (s0 : S) (a1 : A1)(a2 : A2),
         bad s0 = false ->
         inv s0 ->
         P1 a1 a2 ->
         In a1 ls1 ->
         In a2 ls2 ->
         comp_spec (fun a b => bad (snd a) = bad (snd b) /\
                               (bad (snd a) = false -> ((P2) (fst a) (fst b) /\ snd a = snd b))) 
                   ((f1 a1) S eqds o s0) ((f2 a2) S eqds o s0)) ->
      (forall s1 s2 a b,
         bad s1 = true ->
         In (b, s2) (getSupport (o s1 a)) ->
         bad s2 = true) ->
      comp_spec (fun a b => bad (snd a) = bad (snd b) /\
                            (bad (snd a) = false -> (list_pred (P2) (fst a) (fst b) /\ snd a = snd b))) 
                ((oc_compMap _ f1 ls1) S eqds o s)
                ((oc_compMap _ f2 ls2) S eqds o s).
    
    induction ls1; inversion 1; intuition; simpl in *.
    
    comp_simp.
    eapply comp_spec_ret; intuition.
    simpl.
    econstructor.
    
    subst.
    comp_skip.
    comp_simp.
    simpl in *; subst.
    case_eq (bad b); intuition.
    comp_irr_l.

    eapply oc_compMap_wf; intuition.
    eapply H9; intuition.
    eauto.
    eapply oc_comp_invariant.
    eauto.
    eauto.
    eauto.
    eapply H10; eauto.

    comp_irr_r.
    eapply oc_compMap_wf; intuition.
    eapply H9; intuition.
    eauto.
    eapply oc_comp_invariant.
    eauto.
    eauto.
    eauto.
    eapply H10; eauto.

    comp_simp.

    assert (bad s1 = true).
    eapply oc_comp_invariant_f.
    intuition.
    eapply H12.
    eauto.
    eauto.
    eauto.    
    eapply H15.

    eapply comp_spec_ret; intros.
    simpl.
    split.
    
    rewrite H17.
    assert (bad s2 = true).
    eapply oc_comp_invariant_f.
    intuition.
    eapply H12.
    eapply H19.
    eauto.
    rewrite H13 in H3.
    eapply H3.
    eauto.
    rewrite H18.
    trivial.
    
    intros.
    exfalso.
    congruence.
    
    subst.
    comp_skip.
    eapply IHls1; intuition.
    eapply oc_comp_invariant;
    eauto.
    
    comp_simp.
    simpl in *.
    eapply comp_spec_ret; intuition.
    subst.
    simpl.
    econstructor; intuition.
  Qed.

      
  Theorem oc_compMap_support_inv : 
    forall (S : Set) (inv : S -> Prop)(A B C D : Set) (eqdd : EqDec D) (c : A -> OracleComp B C D) (ls : list A) (eqds : EqDec S)(o : S -> B -> Comp (C * S)) s x y,
      (forall x y a d, inv x -> In (d, y) (getSupport ((c a) _ _ o x)) -> inv y) ->
      inv s ->
      In (x, y) (getSupport ((oc_compMap _ c ls) _ _ o s)) ->
      inv y.
    
    induction ls; intuition. simpl in *.
    repeat simp_in_support.
    trivial.
    
    Local Opaque getSupport.
    simpl in *.
    repeat simp_in_support.
    destruct x0.
    repeat simp_in_support.
    destruct x0.
    repeat simp_in_support.
    eapply IHls.
    intuition.
    eapply H.
    eapply H1.
    eauto.
    eapply H.
    eapply H0.
    eauto.
    eauto.
  Qed.
  
  Theorem oc_compMap_support : 
    forall (S A D : Set)(R : S -> A -> D -> Prop)(B C : Set)(eqdd : EqDec D)(c : A -> OracleComp B C D)(ls : list A)(eqds : EqDec S)(o : S -> B -> Comp (C * S)) s x y ,
      (forall s s' a d, In a ls -> In (d, s') (getSupport ((c a) _ _ o s)) -> R s' a d) ->
      (forall s s' a d a' d', R s a d -> In (d', s') (getSupport ((c a') _ _ o s)) -> R s' a d) ->
      In (x, y) (getSupport ((oc_compMap _ c ls) _ _ o s)) ->
      list_pred (R y) ls x.
    
    induction ls; intuition.
    simpl in *.
    repeat simp_in_support.
    econstructor.
    
    simpl in *.
    repeat simp_in_support.
    destruct x0.
    repeat simp_in_support.
    destruct x0.
    repeat simp_in_support.
    econstructor.
    eapply (@oc_compMap_support_inv _ (fun s => R s a d) _ _ _ _ _ c).
    intros.          
    eapply H0.
    eapply H1.
    eapply H4.
    eapply H.
    eauto.
    eauto.
    eauto.
    
    eapply IHls.
    intuition.
    eapply H; eauto.
    intuition.
    eauto.
  Qed.

  Theorem list_pred_In_exists : 
    forall (A B : Set) (a : A) lsa (lsb : list B)(P : A -> B -> Prop),
      list_pred P lsa lsb ->
      In a lsa ->
      exists b,
        In b lsb /\ P a b.
    
    induction lsa; inversion 1; intuition; simpl in *; subst;
    intuition.
    subst.
    econstructor.
    intuition.
    inversion H; clear H; subst.
    edestruct IHlsa.
    eauto.
    trivial.
    intuition.
    econstructor.
    split.
    right.
    eapply H1.
    trivial.
    
  Qed.
  
  Theorem In_allPairs_2 : 
    forall (A B : Type)(lsa : list A)(lsb : list B) a b,
      In a lsa ->
      In b lsb ->
      In (a, b) (allPairs_2 lsa lsb).
    
    induction lsa; intuition; simpl in *.
    intuition.
    subst.
    unfold allPairs_2.
    simpl.
    eapply in_or_app.
    left.
    unfold allPairs_1.
    eapply in_map_iff.
    econstructor.
    intuition.
    
    unfold allPairs_2.
    simpl.
    eapply in_or_app.
    right.
    eapply IHlsa; trivial.
    
  Qed.

  Theorem randomFunc_In_inv : 
    forall (A B C : Set)(eqda : EqDec A)(eqdb : EqDec B)(c : OracleComp A B C) s s' x (b : B) r,
      In b (snd (split s)) ->
      In (x, s') (getSupport (c _ _ (randomFunc r _) s)) ->
      In b (snd (split s')).
    
    intuition.
    eapply (@oc_comp_invariant _ _ _ c _ (fun s => In b (snd (split s))) _ (randomFunc r _)); intuition.
    unfold randomFunc in *.
    case_eq (arrayLookup eqda c0 d); intuition;
    rewrite H3 in H1;
    repeat simp_in_support.
    trivial.
    simpl.
    remember (split c0) as z.
    destruct z.
    simpl in *.
    intuition.
    eauto.
    eauto.
  Qed.
  
  Theorem GenTrans_10_1_11_spec : 
    forall a1 xSet k_I k_X q qs a2 b3 s0 db,
      (length b3 <= MaxMatchingIDs)%nat ->
      (forall a b c, In (a, (b, c)) b3 -> In c (snd (split s0))  /\ In b (fst (split db)) /\
                                          bvectorToNat (snd (splitVector lambda lambda a)) = F_P k_I (Vector.to_list b) * inverse c )%group ->
      badBlinding k_I k_X db s0 xSet qs  = false -> 
      In q qs ->
      comp_spec (fun a b => (
                     badBlinding k_I k_X db (snd a) xSet qs = 
                     badBlinding k_I k_X db (snd b) xSet qs) /\
                            (badBlinding k_I k_X db (snd a) xSet qs = false ->
                             a = b))
                ((GenTrans_10_1 (a1, xSet) k_X (q, (a2, b3))) 
                   (list (Blist * nat))
                   (list_EqDec (pair_EqDec (list_EqDec bool_EqDec) nat_EqDec)) natRandFunc s0)
                ((GenTrans_11 (a1, xSet) k_X (q, (a2, b3))) (list (Blist * nat))
                                                            (list_EqDec (pair_EqDec (list_EqDec bool_EqDec) nat_EqDec)) natRandFunc s0).
    
    intuition.
    intros.
    unfold GenTrans_10_1, GenTrans_11.
    comp_simp.
    simpl.
    comp_skip.
    
    comp_simp.
    eapply comp_spec_ret; intuition.
    simpl in *.
    
    assert ((ServerSearch_10_1 xSet a0 b3) = 
            (ServerSearch_11 xSet a0 b3)).
    unfold ServerSearch_10_1, ServerSearch_11.
    
    eapply map_ext_in.
    intuition.
    unfold ServerSearchLoop_10_1, ServerSearchLoop_11.
    
    destruct a.
    destruct p0.
    destruct p1.
    destruct p0.
    remember (splitVector lambda lambda b0) as z.
    destruct z.
    
    destruct (eq_nat_dec n0 n1); trivial.
    destruct (in_dec (EqDec_dec nat_EqDec) (n ^ bvectorToNat t0) xSet); trivial.
    exfalso.

    eapply goodBlinding_Prop_correct in H7.
    eapply n2.   

    eapply (@oc_compMap_support _ _ _ (fun s (a : nat)(b : nat * nat) => arrayLookup _ s (k ++ a) = Some (snd b) /\ fst b = g ^ (F_P k_X k0 * (snd b)))) in H0.
       
    pose proof H8.
    eapply in_combine_l in H8.
    edestruct list_pred_In_exists.
    eapply list_pred_symm in H0.
    eapply H0.
    eapply H8.
    intuition.
    simpl in *; subst.
    
    symmetry.
    eapply H7.
    eauto.
    eapply allNatsLt_lt_if.
    eapply lt_le_trans.
    eapply allNatsLt_lt.
    eapply H11.
    trivial.
    trivial.
    
    eapply In_allPairs_2.
    eapply in_map_iff.
    exists b1.
    intuition.
    eapply H2.
    eapply in_combine_r.
    eauto.
    
    eapply (@ oc_compMap_support_inv (list (Blist * nat)) (fun s => In n1 (snd (split s))) 
              nat Blist nat (nat * nat) ); intros.
    
    eapply randomFunc_In_inv.
    eauto.
    eauto.
    eapply H2.
    eapply in_combine_r.
    eauto.
    eapply H6.
    
    simpl in *.
    subst.
    assert ( bvectorToNat t0 = F_P k_I (Vector.to_list b1) * inverse n1)%group.
    assert (t0 = snd (splitVector lambda lambda b0)).
    rewrite <- Heqz.
    trivial.
    subst.
    eapply H2.
    eapply in_combine_r.
    eauto.
    rewrite  H12 in i.
    
    rewrite natGroupOp_exp in i.
    rewrite groupExp_mult in i.
    rewrite mult_assoc in i.
    trivial.
    
    intuition.
    simpl in *.
    repeat simp_in_support.
    destruct x.
    repeat simp_in_support.
    simpl.
    unfold natRandFunc, randomFunc in *.
    case_eq ( @arrayLookup Blist nat (@list_EqDec bool bool_EqDec) s
                           (@app bool k (natToBlist a))); intuition;
    rewrite H10 in H11.
    repeat simp_in_support.
    trivial.
    repeat simp_in_support.
    simpl.
    case_eq (eqb (k ++ a) (k ++ a)); intuition.
    rewrite eqb_refl in H11.
    discriminate.
    
    simpl in *.
    repeat simp_in_support.
    destruct x.
    repeat simp_in_support.
    simpl.
    trivial.
    
    intuition.
    simpl in *.
    subst.
    repeat simp_in_support.
    destruct x.
    repeat simp_in_support.
    unfold natRandFunc, randomFunc in *.
    case_eq (@arrayLookup Blist nat (@list_EqDec bool bool_EqDec) s
                          (@app bool k (natToBlist a'))); intuition;
    rewrite H9 in H10;
    repeat simp_in_support.
    trivial.
    simpl.
    case_eq (eqb (k ++ a) (k ++ a')); intuition.
    rewrite eqb_leibniz in H10.
    
    apply app_inv_head in H10.
    rewrite H10 in H11.
    unfold Blist in H9.
    rewrite H9 in H11.
    discriminate.
    
    rewrite H8.
    trivial.
  Qed.
 
  Theorem list_pred_unary_in : 
    forall (A : Set) P (ls : list A),
      list_pred P ls ls ->
      (forall a, In a ls -> P a a).
    
    induction ls; intuition; simpl in *;
    intuition.
    subst.
    inversion H; clear H; subst.
    trivial.
    inversion H; clear H; subst.
    eapply IHls; eauto.
    
  Qed.

  
  Theorem list_pred_in_all : 
    forall (A B : Set)(P1 : A -> Prop)(P2 : B -> Prop)(lsa : list A)(lsb : list B),
      list_pred (fun a b => P1 a -> P2 b) lsa lsb ->
      (forall a, In a lsa -> P1 a) ->
          forall b, In b lsb -> P2 b.
    
    induction 1; intuition; simpl in *.
    intuition.
    intuition; subst.
    eauto.
    
  Qed.

  Theorem oc_compMap_length :
    forall (A B C D : Set)(eqdd : EqDec D)(ls : list A)(c : A -> OracleComp B C D)(S : Set)(eqds : EqDec S)(o : S -> B -> Comp (C * S))(s : S) x y,
      In (x, y) (getSupport ((oc_compMap _ c ls) _ _ o s)) ->
      length x = length ls.
    
    induction ls; intuition; simpl in *;
    repeat simp_in_support;
        simpl.
    trivial.
    destruct x0.
    repeat simp_in_support.
    destruct x0.
    repeat simp_in_support.
    simpl.
    f_equal.
    eauto.
    
  Qed.

  Theorem randomFunc_In_inv_once:
    forall (A B : Set)(eqda : EqDec A) (s s' : list (A * B)) a b b' r,
      In b (snd (split s)) ->
      In (b', s')
         (getSupport (randomFunc r _ s a)) -> In b (snd (split s')).
    
    
    intuition.
    unfold randomFunc in *.
    destruct (arrayLookup eqda s a);
      repeat simp_in_support.
    trivial.
    simpl.
    remember (split s) as z.
    destruct z.
    simpl in *.
    intuition.
    
  Qed.
  
  Hypothesis nat_Bvector_inverse : 
    forall n, n < 2 ^ lambda ->
      bvectorToNat
     (natToBvector n) = n.

  Hypothesis group_lt_lambda : 
    forall n1 n2,
      (n1 * n2)%group < 2 ^ lambda.

  Theorem Init_10_2_11_eq_until_bad : 
    forall k_X k_I db q sigmas xSet s,
      (forall z, length (lookupInds db z) <= MaxMatchingIDs)%nat ->
      (forall z, In z sigmas -> length z <=  MaxMatchingIDs)%nat ->
      length (toW db) = length sigmas ->
      (forall k l1, In (k, l1) (combine (toW db) sigmas) ->
                    forall x, In x l1 ->
                              x < length (lookupInds db k)) ->
      comp_spec
        (fun a b => (badBlinding k_I k_X db (snd a) xSet q = badBlinding k_I k_X db (snd b) xSet q) /\
                    (badBlinding k_I k_X db (snd a) xSet q = false -> fst a = fst b))
        ((Initialize_10_2 k_X k_I db q sigmas xSet) _ _ natRandFunc s)
        ((Initialize_11 k_X k_I db q sigmas xSet) _ _ natRandFunc s).
    
    intuition.
    
    unfold Initialize_10_2, Initialize_11.
    simpl.
    
    assert TSet.
    assert (TSet * TSetKey).
    eapply comp_base_exists.
    eapply TSetSetup.
    econstructor.
    intuition.

    comp_skip.
    
    remember (split a0) as z.
    destruct z.
    
    simpl.
    inline_first.
    comp_skip.
    
    simpl.
    comp_simp.
    simpl.
    inline_first.
    comp_skip.
    comp_simp.
    
    case_eq (badBlinding k_I k_X db b xSet q); intuition.
    comp_irr_l.
    eapply pair_EqDec; intuition.
    eapply list_EqDec; intuition.
    eapply pair_EqDec; intuition.
    eapply list_EqDec; intuition.
    eapply pair_EqDec; intuition.
    eapply list_EqDec; intuition.
    eapply oc_compMap_wf; intuition.

    Theorem oc_compMap_wfoc : 
      forall (A B C D : Set)(eqdd : EqDec D)(c : A -> OracleComp B C D)(ls : list A),
        (forall a, In a ls -> well_formed_oc (c a)) ->
                  well_formed_oc (oc_compMap _ c ls).

      induction ls; intuition; simpl in *.
      econstructor.
      wftac.

      econstructor.
      eapply H.
      intuition.
      
      intuition.
      econstructor.
      eapply IHls.
      intuition.
      intuition.
      econstructor.
      wftac.
    Qed.

    Theorem GenTrans_10_1_wf : 
      forall x y z,
      well_formed_oc (GenTrans_10_1 x y z).

      intuition.
      unfold GenTrans_10_1.
      comp_simp.
      econstructor.
      eapply oc_compMap_wfoc; intuition.
      econstructor.
      econstructor.
      intuition.
      econstructor.
      wftac.

      intuition.
      econstructor.
      wftac.
    Qed.

    eapply GenTrans_10_1_wf.
    eapply randomFunc_wf.
    eapply well_formed_RndNat.
    assert (nz (2 ^ lambda)).
    eapply expnat_nz; intuition.
    eapply H.
    assert ((fun x => True) b).
    intuition.
    eapply H13.
    intuition.

    comp_irr_r.
    eapply pair_EqDec; intuition.
    eapply list_EqDec; intuition.
    eapply pair_EqDec; intuition.
    eapply list_EqDec; intuition.
    eapply pair_EqDec; intuition.
    eapply list_EqDec; intuition.

    eapply oc_compMap_wf; intuition.
    Theorem GenTrans_11_wf : 
      forall x y z,
      well_formed_oc (GenTrans_11 x y z).

      intuition.
      unfold GenTrans_11.
      comp_simp.
      econstructor.
      eapply oc_compMap_wfoc; intuition.
      econstructor.
      econstructor.
      intuition.
      econstructor.
      wftac.

      intuition.
      econstructor.
      wftac.
    Qed.
    eapply GenTrans_11_wf.
    eapply randomFunc_wf.
    eapply well_formed_RndNat.
    assert (nz (2 ^ lambda)).
    eapply expnat_nz; intuition.
    eapply H.
    assert ((fun x => True) b).
    intuition.
    eapply H14.
    intuition.

    comp_simp.
    eapply comp_spec_ret; intuition.
    simpl.
    
    erewrite natRandFunc_badBlinding_persists_oc.
    symmetry.
    erewrite natRandFunc_badBlinding_persists_oc.
    trivial.
    eauto.
    eapply H14.
    eauto.
    eapply H13.
    simpl in *.
    assert (badBlinding k_I k_X db l2 xSet q = true).
    eapply natRandFunc_badBlinding_persists_oc.
    eauto.
    eauto.
    congruence.
    
    assert (forall p, In p b1 -> forall a x c, In (a, (x, c)) (snd p) -> In c (snd (split b))  /\ In x (fst (split db)) /\
                                          bvectorToNat (snd (splitVector lambda lambda a)) = F_P k_I (Vector.to_list x) * inverse c )%group.
    
    intros.

    eapply (@oc_compMap_support _ _ _ (fun s a b => forall a x c, In (a, (x, c)) (fst b) ->                                                  
           In c (snd (split s)) /\ In x (fst (split db)) /\ 
           bvectorToNat (snd (splitVector lambda lambda a)) = F_P k_I (Vector.to_list x) * inverse c)) in H6.

    eapply list_pred_symm in H6.

     assert (list_pred (fun
            (b0 : list
                    (Vector.t bool (lambda + lambda) *
                     (Identifier lambda * nat)))
                         (_ : _) =>
          forall (a1 : Vector.t bool (lambda + lambda))
            (x : Identifier lambda) (c : nat),
          In (a1, (x, c)) b0 ->
          In c (snd (split b)) /\
          In x (fst (split db)) /\
          bvectorToNat (snd (splitVector lambda lambda a1)) =
          F_P k_I (Vector.to_list x) * inverse c)
                      (fst (split a0)) (combine (toW db) sigmas)).
     eapply list_pred_fst_split_irr.
     eapply H6.
     clear H6.


    eapply (@list_pred_impl_unary _ _ _
             ((fun
            (b0 _ : list
                    (Vector.t bool (lambda + lambda) *
                     (Identifier lambda * nat))) =>
          forall (a1 : Vector.t bool (lambda + lambda))
            (x : Identifier lambda) (c : nat),
          In (a1, (x, c)) b0 ->
          In c (snd (split b)) /\
          In x (fst (split db)) /\
          bvectorToNat (snd (splitVector lambda lambda a1)) =
          F_P k_I (Vector.to_list x) * inverse c))
             )
       in H15.

    eapply list_pred_unary_in in H15.
    eapply H15.
    eapply H14.
    eapply (@compMap_support _ _ (fun a b => snd b = nil \/ In (snd b) l)) in H10.
    eapply list_pred_symm in H10.
    assert ( list_pred
         (fun
            (b2 : list
                    (Vector.t bool (lambda + lambda) *
                     (Identifier lambda * nat))) (_ : Keyword) =>
          b2 = nil \/ In b2 l) (snd (split b1)) (fst (split q))).
    eapply list_pred_snd_split_irr.
    eauto.
    clear H10.
    eapply (@list_pred_impl_unary _ _ _ (fun a _ => a = nil \/ In a l)) in H6.
    rewrite <- Heqz.
    simpl.
    eapply list_pred_unary_in in H6.
    intuition; eauto.
    rewrite H10 in H14.
    simpl in *.
    intuition.

    Theorem snd_split_in : 
      forall (A B : Type)(ls : list (A * B))(p : A * B),
        In p ls ->
        In (snd p) (snd (split ls)).

      induction ls; intuition; simpl in *.
      intuition; subst.
      simpl.
      remember (split ls) as z.
      destruct z.
      simpl.
      intuition.
      
      remember (split ls) as z.
      destruct z.
      simpl.
      right.
      eapply IHls.
      trivial.
    Qed.

    eapply  snd_split_in.
    trivial.

    intuition.
    intuition.
    repeat simp_in_support.
    simpl.
    unfold arrayLookupList.
    case_eq ( @arrayLookup Keyword
            (list
               (prod
                  (Vector.t bool
                     (plus (posnatToNat lambda) (posnatToNat lambda)))
                  (prod (Identifier (posnatToNat lambda)) nat)))
            (@list_EqDec bool bool_EqDec)
            (@combine Keyword
               (list
                  (prod
                     (Vector.t bool
                        (plus (posnatToNat lambda) (posnatToNat lambda)))
                     (prod (Identifier (posnatToNat lambda)) nat))) 
               (toW db) l) a2); intuition.

     Theorem arrayLookup_combine_Some_In : 
      forall (A B : Set)(eqd : EqDec A) (lsa : list A) (lsb : list B) a b,
        arrayLookup _ (combine lsa lsb) a = Some b ->
        In b lsb.
      
      induction lsa; intuition; simpl in *.
      discriminate.
      destruct lsb;
        simpl in *.
      discriminate.
      
      destruct (eqb a0 a ).
      inversion H; clear H; subst.
      intuition.
      right.
      eauto.
      
    Qed.

    eapply arrayLookup_combine_Some_In in H5.
    intuition.

    intuition.
    intros.
    unfold Initialize_wLoop_11 in *.
    destruct a2.

    Ltac simp_in_support' := 
      unfold setLet in *;
      match goal with
        | [H : In _ (getSupport (Bind _ _)) |- _ ] =>
          apply getSupport_Bind_In in H; destruct_exists
        | [H : In _ (getSupport (if ?t then _ else _)) |- _ ] => let x := fresh "x" in remember t as x; destruct x
        | [H : In _ (getSupport (ret _)) |- _ ] => apply getSupport_In_Ret in H; try pairInv; subst
        (*     | [H : false = inRange _ _ |- _] => symmetry in H *)
        | [H : true = negb ?t |- _ ] => let x := fresh "x" in remember t as x; destruct x; simpl in H; try discriminate
        | [H : _ /\ _ |- _ ] => destruct H
      end.

    unfold setLet in *.
    simpl in *.
    repeat simp_in_support'.
    destruct x1.
    repeat simp_in_support'.
    simpl in *.

    eapply (@oc_compMap_support _ _ _ (fun (l3 : list (Blist * nat)) (a : Identifier lambda * nat) (b : Vector.t bool (lambda + lambda) * (Identifier lambda * nat)) => 
                                         In (fst a) (fst (split db)) ->
                                         let a3 := fst b in let (x0, c0) := snd b in 
                                                            (In c0 (snd (split l3)) /\
                                                             In x0 (fst (split db)) /\
                                                             bvectorToNat (snd (splitVector lambda lambda a3)) =
                                                             F_P k_I (Vector.to_list x0) * inverse c0))
                                
           ) in H18.


    Theorem list_pred_impl_all : 
      forall (A B : Set) P1 (P2 : B -> Prop) (lsa : list A)(lsb : list B),
        list_pred (fun a b => P1 a -> P2 b) lsa lsb ->
        forall b, 
        (forall a, In a lsa -> P1 a) ->
         In b lsb -> P2 b.

      induction 1; intuition; simpl in *.
      intuition.

      intuition; subst.
      eapply H.
      eapply X.
      intuition.

    Qed.

    specialize (@list_pred_impl_all _ _ _ _ _ _ H18 (a3, (x0, c0))); intros.
    simpl in *.
    eapply H19.
    intuition.
    destruct a2.
    simpl.
    eapply in_combine_l in H.
    
    Theorem in_permute_if : 
      forall (A : Set)(sigma : list nat)(ls : list A)(a : A),
        In a (permute ls sigma) ->
        (forall n, In n sigma -> n < length ls) ->
        In a ls.

      induction sigma; intuition; simpl in *;
      intuition.

      case_eq (nth_error ls a); intuition;
      rewrite H1 in H.
      simpl in *; intuition.
      subst.

      Theorem nth_error_Some_In : 
        forall (A : Set)(ls : list A) n (a : A),
          nth_error ls n = Some a ->
          In a ls.

        induction ls; destruct n; intuition; simpl in *.
        discriminate.
        discriminate.
        inversion H; clear H; subst.
        intuition.

        right.
        eapply IHls.
        eauto.

      Qed.

      eapply nth_error_Some_In.
      eauto.
      simpl in *.
      intuition.

    Qed.

    Theorem In_lookupInds_if_h : 
      forall db w i z,
        In i
           (fold_left
              (fun (ls : list (Identifier lambda))
                   (p0 : Identifier lambda * list Keyword) =>
                 if in_dec (EqDec_dec (list_EqDec bool_EqDec)) w (snd p0)
                 then fst p0 :: ls
                 else ls) db z) ->
        In i ((fst (split db)) ++ z).

      induction db; intuition; simpl in *.
      
      remember (split db) as y.
      destruct y.
      simpl in *.
      
      specialize (@IHdb _ _ _ H0).
      eapply in_app_or in IHdb.
      intuition.
 
      destruct (@in_dec (list bool)
                (@EqDec_dec (list bool) (@list_EqDec bool bool_EqDec)) w b).
      simpl in *.
      intuition.
      right.
      eapply in_or_app.
      intuition.
      
    Qed.


    Theorem In_lookupInds_if : 
      forall db w i,
        In i (lookupInds db w) ->
        In i (fst (split db)).

      intuition.
      specialize (@In_lookupInds_if_h _ _ _ _ H); intuition.
      apply in_app_or in H0.
      intuition.
      simpl in *.
      intuition.

    Qed.

    eapply In_lookupInds_if.
    eapply in_permute_if.
    eapply H.
    intuition.
    eapply H3.
    eauto.
    trivial.

    trivial.
    
    intuition.
    intuition.
    unfold Initialize_indLoop_11 in *.
    simpl in *.
    repeat simp_in_support'.
    destruct x1.
    repeat simp_in_support'.
    simpl.
    intuition.

    Theorem arrayLookup_Some_In : 
      forall (A B : Set)(eqd : EqDec A) (lsb : list (A * B)) a b,
        arrayLookup _ lsb a = Some b ->
        In b (snd (split lsb)).
      
      induction lsb; intuition; simpl in *.
      discriminate.
      remember (split lsb) as z.
      destruct z.
      simpl.
      
      destruct (eqb a a0 ).
      inversion H; clear H; subst.
      intuition.
      right.
      eauto.
      
    Qed.
    
    Theorem valueInRandomFunc : 
      forall (A B : Set)(eqda : EqDec A)(a : A)(v : B) f f' r,
        In (v, f') (getSupport (randomFunc r _ f a)) ->
        In v (snd (split f')).

      intuition.
      unfold randomFunc in *.
      case_eq (arrayLookup eqda f a); intuition;
      rewrite H0 in H;
      repeat simp_in_support.
      eapply arrayLookup_Some_In.
      eauto.
      simpl.
      remember (split f) as z.
      destruct z.
      simpl.
      intuition.

    Qed.

    unfold natRandFunc in *.
    eapply valueInRandomFunc.
    eauto.

    rewrite splitVector_append.
    simpl.
    eapply nat_Bvector_inverse.
    eapply group_lt_lambda.

    intuition.
    simpl in *.
    repeat simp_in_support'.
    destruct x1.
    repeat simp_in_support'.
    intuition.
    eapply randomFunc_In_inv_once;
    eauto.
    
    intuition.

    eapply randomFunc_In_inv.
    eapply H.
    eapply H17.
    eapply H16.
    eapply H.
    eapply H17.
    eapply H.
    trivial.

    comp_skip.
    
    eapply (@oc_compMap_spec_bad _ _ _ _ _ _ _ (fun s => forall x, In x b1 -> forall y, In y (snd x) -> In (snd (snd y)) (snd (split s)))
                                 (fun b => badBlinding k_I k_X db b xSet q)).
    eapply list_pred_eq.
    trivial.
    intuition.
    destruct y.
    simpl.
    destruct p0.
    simpl.
    eapply H13.
    eauto.
    eauto.
    intuition; subst.
    
    eapply GenTrans_10_1_wf.
    
    intuition.
    eapply GenTrans_11_wf.

    intuition.
    unfold natRandFunc.
    eapply randomFunc_wf.
    eapply well_formed_RndNat.
    assert (nz (2 ^ lambda)).
    eapply expnat_nz.
    intuition.
    inversion H; intuition.

    intuition.

    eapply randomFunc_In_inv_once.
    eapply H.
    eauto.
    trivial.
    eauto.

    intuition.
    subst.
    eapply comp_spec_consequence.
    eapply GenTrans_10_1_11_spec.

    apply in_combine_r in H17.
    eapply (@compMap_support _ _ (fun a b => snd b = arrayLookupList _ (combine (toW db) l) a)) in H10.
    eapply list_pred_symm in H10.
    eapply (@list_pred_impl_unary _ _ _ (fun a a => (snd a) = nil \/ In (snd a) l)) in H10.
    
    eapply list_pred_unary_in in H10.
    intuition.
    assert (snd (a2, b3) = nil).
    eapply H16.
    simpl in *.
    subst.
    simpl.    
    omega.
    simpl in *.
    
    eapply (@oc_compMap_support _ _ _ (fun s a b => length (snd a) <= MaxMatchingIDs -> length (fst b) <= MaxMatchingIDs))%nat in H6.
    eapply list_pred_symm in H6.
    
    eapply (@list_pred_fst_split_irr _ _ _  (fun
                                                (b0 : list
                                                        (Vector.t bool (lambda + lambda) *
                                                         (Identifier lambda * nat)))
                                                (a : Keyword * list nat) =>
                                                (length (snd a) <= MaxMatchingIDs -> length b0 <= MaxMatchingIDs)%nat)) in H6.
    
    
    
    eapply list_pred_symm in H6.
    eapply (@list_pred_snd_split_irr _ _ _  (fun
                                                (a : list nat)
                                                (b0 : list
                                                        (Vector.t bool (lambda + lambda) *
                                                         (Identifier lambda * nat)))
                                              =>
                                                (length a <= MaxMatchingIDs -> length b0 <= MaxMatchingIDs)%nat)) in H6.
    
    eapply (@list_pred_in_all _ _) in H6.
    eapply H6.
    intuition.
    eapply H1.
    assert (split (combine (toW db) sigmas) = ((toW db), sigmas)).
    eapply combine_split.
    trivial.
    rewrite H19 in H10.
    trivial.
    rewrite <- Heqz.
    trivial.
      
    intuition.
    simpl in *.
    repeat simp_in_support.
    destruct x.
    repeat simp_in_support.
    simpl.

    eapply oc_compMap_length in H22.
    rewrite H22.
    rewrite combine_length.
    eapply Nat.min_le_iff.
    right.
    rewrite allNatsLt_length.
    eapply H0.
    
    intuition.
    trivial.
    intuition.
    
    simpl in *; subst.
    unfold arrayLookupList.
    case_eq (@arrayLookup Keyword
            (list
               (prod
                  (Vector.t bool
                     (plus (posnatToNat lambda) (posnatToNat lambda)))
                  (prod (Identifier (posnatToNat lambda)) nat)))
            (@list_EqDec bool bool_EqDec)
            (@combine Keyword
               (list
                  (prod
                     (Vector.t bool
                        (plus (posnatToNat lambda) (posnatToNat lambda)))
                     (prod (Identifier (posnatToNat lambda)) nat))) 
               (toW db) l) b4); intuition.

   
    
    apply arrayLookup_combine_Some_In in H.
    intuition.
    
    intuition.
    repeat simp_in_support.
    trivial.

    intuition.
    assert (c = (snd (snd (a3, (b2, c))))).
    trivial.
    rewrite H19.
    clear H19.
    eapply H15.
    eapply in_combine_r.
    eauto.
    trivial.
    eapply H13.
    eapply in_combine_r.
    eauto.
    eauto.
    eapply H13.
    eapply in_combine_r.
    eauto.
    trivial.

    eauto.
    eapply in_combine_l.
    eauto.
    
    intuition.
    simpl.
    assert ((a3, (a4, b5)) = (fst b4)).
    subst.
    trivial.
    eapply H20.
    subst.
    trivial.

    intuition.
    eapply natRandFunc_badBlinding_persists;
    eauto.

    comp_simp.
    eapply comp_spec_ret; intuition.
    simpl in *.
    apply list_pred_eq_impl_eq in H18.
    subst.
    trivial.

  Qed.
  
  Theorem G10_4_eq_until_bad : 
    forall x, 
      evalDist G10_3 (x, false) == evalDist G10_4 (x, false).

    intuition.
    unfold G10_3, G10_4.
    do 4 (comp_skip; comp_simp).
    
    eapply comp_spec_impl_eq.
    comp_skip.

    eapply Init_10_2_11_eq_until_bad.
    eapply MaxMatchingIDs_correct; eauto.
    unfold sampleSigmas_11 in *.
    intuition.
   
    unfold setLet in *.
    eapply (@compMap_support_unary _ _ _ (fun z => length z <= MaxMatchingIDs)%nat _ (fun w => RndPerm (length (lookupInds d w)))).
    eapply H3.
    intuition.
    erewrite RndPerm_In_support_length.
    eapply MaxMatchingIDs_correct.
    eauto.
    eauto.
    trivial.
   
    symmetry.
    erewrite compMap_length; eauto.

    intuition.
    unfold sampleSigmas_11 in *.
    unfold setLet in *.
    eapply (@compMap_support _ _ (fun a b => forall x, In x b -> x < length (lookupInds d a))) in H3.
    
    Theorem list_pred_combine_equiv : 
      forall (A B : Set) P (lsa : list A)(lsb : list B),
        list_pred P lsa lsb ->
        forall x y, In (x, y) (combine lsa lsb) -> P x y.

      induction 1; intuition; simpl in *.
      intuition.

      intuition.
      pairInv.
      trivial.

    Qed.

    eapply list_pred_combine_equiv in H3.
    eapply H3; eauto.
    trivial.
   
    intuition.

    Require Import Permutation.

    Theorem RndPerm_In_support_lt:
      forall (n : nat) (ls : list nat),
        In ls (getSupport (RndPerm n)) -> 
        forall x, In x ls -> x < n.

      intuition.
     
      eapply allNatsLt_lt.
      eapply Permutation_in.
      eapply Permutation_sym.
      eapply RndPerm_In_support.
      eauto.
      trivial.

    Qed.

    eapply RndPerm_In_support_lt;
    eauto.

    comp_simp.
    intuition.
    simpl in H9.
    case_eq (badBlinding x1 x0 d b (XSetSetup_2 x0 x1 d x2) l); intuition.
    comp_irr_l.
    comp_irr_r.
    simpl in H8.
    rewrite <- H8.
    rewrite H7.
    eapply comp_spec_ret; intuition.
    pairInv.
    pairInv.
    pairInv.
    comp_skip.
    simpl in H8.
    rewrite <- H8.
    rewrite H7.
    eapply comp_spec_ret; intuition.
  Qed.


  Definition G10_3_bad :=
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    [db, q, s_A] <-$3 A1;
    sigmas <-$ compMap _ (sampleSigmas_11 db) (toW db);
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    z <-$ (Initialize_10_2 k_X k_I db q sigmas xSet) _ _ natRandFunc nil;
    ret (badBlinding k_I k_X db (snd z) xSet q).

  SearchAbout OracleComp.

  Theorem G10_3_bad_equiv : 
    Pr[x <-$ G10_3; ret snd x] == Pr[G10_3_bad].

    unfold G10_3, G10_3_bad.
    do 5 (comp_inline_l; comp_skip; comp_simp).
    comp_inline_l.
    comp_irr_l; wftac.
    simpl.
    intuition.
  Qed.

  Require Import RndInList.

  Variable MaxKeywords : nat.
  Hypothesis MaxKeywords_correct : 
    forall db q s, In (db, q, s) (getSupport A1) ->
      (length (toW db) <= MaxKeywords)%nat.
  Variable MaxQueries : nat.
  Hypothesis MaxQueries_correct : 
    forall db q s, In (db, q, s) (getSupport A1) ->
      (length q <= MaxQueries)%nat.

  Variable MaxIDs : nat.
  Hypothesis MaxIDs_correct : 
    forall db q s, In (db, q, s) (getSupport A1) ->
      (length db <= MaxIDs)%nat.
      
  Print XSetSetup_2.

  Theorem XSet_length_2 : 
    forall k_X k_I db sigmas q s, 
      In (db, q, s) (getSupport A1) ->
      (length (XSetSetup_2 k_X k_I db sigmas) <= MaxKeywords * MaxMatchingIDs)%nat.
    intuition.
    unfold XSetSetup_2.
  Admitted.

  Theorem G10_3_bad_small : 
    Pr[G10_3_bad] <= (((MaxKeywords + MaxQueries) * MaxMatchingIDs)^2) * 
    MaxQueries * MaxMatchingIDs * MaxIDs *
      MaxKeywords * MaxMatchingIDs / 2 ^ lambda.
  
    unfold G10_3_bad.
    
    do 3
      (inline_first;
    comp_irr_l; wftac).
    
    comp_simp.
    inline_first.
    comp_irr_l; wftac.
    eapply compMap_wf.
    intuition.
    unfold sampleSigmas_11.
    comp_simp.
    
    eapply RndPerm_wf.

    Theorem oc_compMap_qam : 
      forall (A B C D : Set)(eqdd : EqDec D)(c : A -> OracleComp B C D)(ls : list A) n,
        (forall a, In a ls -> queries_at_most (c a) n) ->
        queries_at_most (oc_compMap _ c ls) (length ls * n).

      induction ls; intuition; simpl in *.
      econstructor.

      econstructor.
      eapply H.
      intuition.
      
      intuition.
      econstructor.
      econstructor.
      eapply IHls.
      intuition.
      intuition.
      econstructor.
      omega.

    Qed.
    
    Theorem Initialize_indLoop_11_qam : 
      forall x0 c' a0 a,
      queries_at_most (Initialize_indLoop_11 x0 c' a0 a) 1.

      intuition.
      unfold Initialize_indLoop_11.
      econstructor.
      econstructor.
      econstructor.
      intuition.
      comp_simp.
      econstructor.
      econstructor.
      intuition.
      econstructor.
      omega.
      
    Qed.

    Theorem Initialize_wLoop_11_qam : 
      forall d x0 a,
        (exists y z, In (d, y, z) (getSupport A1)) ->
      queries_at_most (Initialize_wLoop_11 d x0 a)  MaxMatchingIDs.

      intuition.
      unfold Initialize_wLoop_11.
      comp_simp.
      econstructor.
      econstructor.
      econstructor.
      intuition.
      econstructor.
      eapply oc_compMap_qam.
      intuition.
      eapply Initialize_indLoop_11_qam.
      intuition.
      econstructor.
      rewrite combine_length.
      rewrite allNatsLt_length.
      rewrite plus_0_l.
      rewrite plus_0_r.
      rewrite mult_1_r.
      eapply le_trans.
      eapply Min.le_min_r.
      destruct H0.
      destruct H.
      eapply MaxMatchingIDs_correct.
      eauto.
    Qed.

    Theorem GenTrans_10_1_qam : 
      forall a x a1 a2 a3,
      queries_at_most (GenTrans_10_1 a x (a1, (a2, a3))) (length a3).

      intuition.
      unfold GenTrans_10_1.
      comp_simp.
      econstructor.
      econstructor.
      eapply oc_compMap_qam.
      intuition.
      econstructor.
      econstructor.
      intuition.
      econstructor.
      intuition.
      econstructor.
      rewrite allNatsLt_length.
      omega.
      
    Qed.

    Theorem Initialize_10_2_qam : 
      forall x x0 d l x1 xSet,
        (exists z, In (d, l, z) (getSupport A1)) -> 
      queries_at_most (Initialize_10_2 x x0 d l x1 xSet) 
      ((length (toW d) + length l) * MaxMatchingIDs)%nat.

      intuition.
      unfold Initialize_10_2.
      econstructor.
      econstructor.
      eapply oc_compMap_qam.
      intuition.
      eapply Initialize_wLoop_11_qam.
      destruct H0.
      econstructor.
      econstructor.
      eauto.

      intuition.
      remember (split c') as z.
      destruct z.
      comp_simp.
    
      econstructor.
      econstructor.
      intuition.
      comp_simp.
      econstructor.
      econstructor.
      intuition.
      econstructor.
      econstructor.
      eapply oc_compMap_qam.
      intuition.
      destruct a.
      destruct p0.
      econstructor.
      eapply GenTrans_10_1_qam.

      repeat (destruct H4).
      simpl in H4.
      repeat simp_in_support.
      eapply (@compMap_support _ _ (fun a b => length (snd b) <= MaxMatchingIDs))%nat in H6.
      eapply list_pred_fst_split_irr_if in H6.
      assert (l2 = snd (t1, l2)).
      trivial.
      rewrite H3.
      eapply (@list_pred_impl_all _ _ _ (fun x => length (snd x) <= MaxMatchingIDs)%nat).
      eapply list_pred_impl.
      eapply H6.
      intuition.
      intuition.
      eapply H7.
      eapply in_combine_r.
      eauto.

      intuition.
      repeat simp_in_support.
      simpl.

      Show.
      repeat (destruct H1).
      eapply (@oc_compMap_support _ _ _ (fun s a b => length (fst b) <= MaxMatchingIDs))%nat in H1.
      
      Theorem arrayLookupList_all : 
        forall (A B: Set)(eqda : EqDec A)(P : list B -> Prop)(arr : list (A * list B)) a,
          P nil ->
          (forall ls, In ls (snd (split arr)) -> P ls) ->
          P (arrayLookupList _ arr a).
        
        intuition.
        unfold arrayLookupList.
        case_eq (arrayLookup eqda arr a); intuition.
        eapply H0.
        eapply arrayLookup_Some_In.
        eauto.

      Qed.

      Show.
      eapply list_pred_symm in H1.
      SearchAbout list_pred split.
      eapply (@list_pred_fst_split_irr _ _ _ (fun x _ => length x <= MaxMatchingIDs)%nat) in H1.
      rewrite <- Heqz in H1.
      simpl in H1.
      eapply list_pred_symm in H1.
      eapply arrayLookupList_all.
      simpl.
      intuition.
      intuition.
      eapply (@list_pred_impl_all _ _ _ (fun x => length x <= MaxMatchingIDs)%nat).
      eapply list_pred_impl.
      eapply H1.
      intuition.
      intuition.
      eapply H10.

      Theorem In_snd_split_combine : 
        forall ( A B : Set)(lsa : list A)(lsb : list B) b,
          In b (snd (split (combine lsa lsb))) ->
          In b lsb.

        induction lsa; intuition; simpl in *.
        intuition.

        destruct lsb; simpl in *.
        intuition.
        remember (split (combine lsa lsb)) as z.
        destruct z.
        simpl in *.
        intuition.
        right.
        eapply IHlsa; eauto.
        rewrite <- Heqz.
        trivial.
      Qed.

      eapply In_snd_split_combine.
      eauto.
      
      intuition.
      unfold Initialize_wLoop_11 in *.
      simpl in H9.
      repeat simp_in_support.
      destruct x12.
      repeat simp_in_support.
      simpl.
      eapply oc_compMap_length in H11.
      rewrite H11.
      rewrite combine_length.
      rewrite Nat.le_min_r.
      rewrite allNatsLt_length.
      destruct H0.
      eapply MaxMatchingIDs_correct.
      eauto.

      intuition.
      rewrite combine_length.
      
      assert (length l = length c'0).
      repeat (destruct H4).
      simpl in H4.
      repeat simp_in_support.
      eapply compMap_length in H5.
      rewrite H5.
      rewrite split_length_l.
      trivial.
      rewrite <- H5.
      rewrite Min.min_idempotent.
      intuition.

      intuition.
      econstructor.

      repeat rewrite plus_0_l.
      rewrite plus_0_r.
      rewrite Max.max_0_l.
      rewrite mult_plus_distr_r.
      eapply plus_le_compat; intuition.
      eapply mult_le_compat; intuition.
      rewrite combine_length.
      eapply Nat.le_min_l.
    Qed.

    Theorem Initialize_10_2_badBlinding_prob : 
      forall x x0 d l x1 xSet,
        (exists z, In (d, l, z) (getSupport A1)) ->
      Pr[z <-$ (Initialize_10_2 x x0 d l x1 xSet) _ _ natRandFunc nil;
       ret ( badBlinding x0 x d (snd z) xSet l)] <= 
       (((length (toW d) + length l) * MaxMatchingIDs)^2) * 
    length l * MaxMatchingIDs * length d *
     length xSet / 2 ^ lambda.

      intuition.
      
      eapply leRat_trans.
      eapply (@oc_eventProb_0_1 _ (fun f => length f) (fun f => badBlinding x0 x d f xSet l)
      (fun n =>  length l * MaxMatchingIDs * length d * n * length xSet / 2 ^ lambda)).

      eapply Initialize_10_2_qam.
      trivial.

      admit.

      Theorem badBlinding_c_nil_f_false : 
        forall x z xSet a0 a,
        badBlinding_c x z nil xSet a0 a = false.

        intuition.
        unfold badBlinding_c.
        comp_simp.
        simpl.
        trivial.

      Qed.

      Theorem badBlinding_q_nil_f_false_h : 
        forall ls x z xSet a,
          fold_left
          (fun (b : bool) (z0 : nat) =>
            if b then true else badBlinding_c x z nil xSet a z0)
          ls false = false.
        
        induction ls; intuition; simpl in *.
        rewrite badBlinding_c_nil_f_false.
        eapply IHls.
        
      Qed.

      Theorem badBlinding_q_nil_f_false : 
        forall x z xSet a,
        badBlinding_q x z nil xSet a = false.

        intuition.
        unfold badBlinding_q.
        eapply badBlinding_q_nil_f_false_h.

      Qed.

      Theorem badBlinding_nil_f_false : 
        forall x0 x d xSet l,
          badBlinding x0 x d nil xSet l = false.

        induction l; intuition.
        unfold badBlinding, setLet.

        simpl.
        rewrite  badBlinding_q_nil_f_false.
        eapply IHl.

      Qed.

      eapply badBlinding_nil_f_false .

      intuition.
      
      unfold natRandFunc, randomFunc.
      case_eq ( @arrayLookup Blist nat (@list_EqDec bool bool_EqDec) s a); intuition.
      comp_simp.
      simpl.
      rewrite H1.
      rewrite evalDist_ret_0; intuition.
      eapply rat0_le_all.
      comp_inline_l.
      comp_at comp_ret leftc 1%nat.
      simpl.


      Fixpoint removeAll (A : Set) (eqd : eq_dec A) (ls : list A) (a : A) :=
        match ls with
          | nil => nil
          | a' :: ls' => if eqd a a' then (removeAll eqd ls' a) else a' :: removeAll eqd ls' a
        end.

      Theorem removeAll_length_ls : 
        forall (A : Set)(eqd : eq_dec A)(ls : list A)(a : A),
          (length (removeAll eqd ls a) <= length ls)%nat.

        induction ls; intuition; simpl in *.
        destruct (eqd a0 a).
        subst.
        eapply le_S.
        eapply IHls; intuition.
        simpl.
        eapply le_n_S.
        eapply IHls; intuition.
      Qed.

      Theorem removeAll_In_length : 
        forall (A : Set)(eqd : eq_dec A)(ls : list A)(a : A),
          In a ls ->
          (S (length (removeAll eqd ls a)) <= length ls)%nat.

        induction ls; intuition; simpl in *.
        intuition.
        intuition; subst.
        destruct (eqd a0 a0); intuition.
        eapply le_n_S.
        eapply removeAll_length_ls.

        destruct (eqd a0 a); intuition.
        simpl.
        eapply le_n_S.
        eapply IHls; intuition.

      Qed.

      Theorem badBlinding_ezxz_count : 
        forall ys xSet e z xind,
          NoDup ys ->
          (sumList ys (fun y => if (badBlinding_ezxz xSet e z (xind, y)) then 1 else 0) <= (length xSet) / 1).

        induction ys; intuition.

        unfold sumList; simpl.
        eapply rat0_le_all.

        rewrite sumList_cons.
        inversion H; clear H; subst.
        case_eq (badBlinding_ezxz xSet e z (xind, a)); intuition.
        unfold badBlinding_ezxz in H.
        destruct (eq_nat_dec a z); intuition.
        discriminate.
        destruct (in_dec (EqDec_dec nat_EqDec) (g ^ (e * z * xind * inverse a)) xSet).
        remember ((removeAll (EqDec_dec _) xSet (g ^ (e * z * xind * inverse a)))) as xSet'.
        assert ((1 + length xSet') <= length xSet)%nat.
        simpl.
        subst.
        eapply removeAll_In_length; intuition.
        eapply leRat_trans.
        Focus 2.
        eapply (leRat_terms (pos 1) (pos 1) H0).
        intuition.
        clear H0.

        eapply leRat_trans.
        Focus 2.
        eapply eqRat_impl_leRat.
        eapply eqRat_symm.
        eapply ratAdd_num.
        eapply ratAdd_leRat_compat.
        intuition.
        
        Theorem In_removeAll_ne : 
          forall (A : Set)(eqd : eq_dec A)(ls : list A)(a b : A),
            In a ls ->
            a <> b ->
            In a (removeAll eqd ls b).

          induction ls; intuition; simpl in *.
          intuition; subst.
          destruct (eqd b a0).
          subst.
          intuition.

          simpl; intuition.

          destruct (eqd b a); subst.
          eapply IHls; intuition.
          simpl.
          right.
          eapply IHls; intuition.

        Qed.

        Theorem In_removeAll_if : 
          forall (A : Set)(eqd : eq_dec A)(ls : list A)(a b : A),   
            In a (removeAll eqd ls b) ->
            In a ls.

          induction ls; intuition; simpl in *.
          destruct (eqd b a); subst.
          right.
          eapply IHls; intuition.
          eauto.

          simpl in *.
          intuition.
          right.
          eapply IHls; eauto.

        Qed.
            
        Theorem badBlinding_ezxz_remove_equiv : 
          forall ys xSet e z xind a,
            In (g ^ (e * z * xind * inverse a)) xSet ->
            ~ In a ys ->
            sumList ys
            (fun y : nat => if badBlinding_ezxz xSet e z (xind, y) then 1 else 0) == 
            sumList ys
            (fun y : nat => if badBlinding_ezxz (removeAll (EqDec_dec nat_EqDec) xSet
               (g ^ (e * z * xind * inverse a))) e z (xind, y) then 1 else 0).


          intuition.
          eapply sumList_body_eq.
          intuition.

          unfold badBlinding_ezxz.
          destruct (eq_nat_dec a0 z); intuition.
          destruct (in_dec (EqDec_dec nat_EqDec) (g ^ (e * z * xind * inverse a0)) xSet).
          destruct (in_dec (EqDec_dec nat_EqDec) (g ^ (e * z * xind * inverse a0))
            (removeAll (EqDec_dec nat_EqDec) xSet
               (g ^ (e * z * xind * inverse a)))).
          intuition.
          exfalso.
          eapply n0.
          eapply In_removeAll_ne.
          trivial.
          
          (* need a bit of group theory to prove this*)
          admit.

          destruct (in_dec (EqDec_dec nat_EqDec) (g ^ (e * z * xind * inverse a0))
            (removeAll (EqDec_dec nat_EqDec) xSet
               (g ^ (e * z * xind * inverse a)))); intuition.
          exfalso.
          eapply n0.
          eapply In_removeAll_if.
          eauto.
        Qed.

        rewrite  badBlinding_ezxz_remove_equiv .
        subst.
        eapply IHys; intuition.
        trivial.
        intuition.
        
        discriminate.
        rewrite <- ratAdd_0_l.
        eapply IHys; intuition.
      Qed.
        
      Theorem badBlinding_ez_count : 
        forall ys a xSet e z xinds f,
          badBlinding_ez xinds f xSet e z = false ->
          NoDup ys ->
          (sumList ys (fun y => if (badBlinding_ez xinds ((a, y) :: f) xSet e z) then 1 else 0) <= (length xinds * length xSet) / 1).

        intuition.
        unfold badBlinding_ez.
        unfold setLet.

        assert (forall y,  
          fold_left
           (fun (b : bool) (x : nat * nat) =>
            if b then true else badBlinding_ezxz xSet e z x)
           (allPairs_2 xinds (snd (split ((a, y) :: f)))) false
           =
            fold_left
           (fun (b : bool) (x : nat * nat) =>
            if b then true else badBlinding_ezxz xSet e z x)
           (map (fun z => (z, y)) xinds) false
           ).

        Theorem badBlinding_ez_allPairs_simp : 
          forall xinds f xSet e z,
          badBlinding_ez xinds f xSet e z = false ->
          forall a y, 
            fold_left
            (fun (b : bool) (x : nat * nat) =>
              if b then true else badBlinding_ezxz xSet e z x)
            (allPairs_2 xinds (snd (split ((a, y) :: f)))) false =
            fold_left
            (fun (b : bool) (x : nat * nat) =>
              if b then true else badBlinding_ezxz xSet e z x)
            (foreach  (z0 in xinds)(z0, y)) false.

          intuition.
          unfold badBlinding_ez in *.
          unfold setLet in *.
          simpl.
          remember (split f) as w.
          destruct w.
          simpl in *.

          Theorem fold_left_one_bad : 
            forall (A : Set)(ls : list A)(f : A -> bool)(a : A),
              In a ls ->
              f a = true ->
              fold_left (fun (b : bool) z => if b then true else (f z)) ls false = true.

            induction ls; intuition; simpl in *.
            intuition; subst.
            rewrite H0.
            eapply fold_left_bad_true.

            case_eq (f a); intuition.
            eapply fold_left_bad_true.
            eapply IHls;
            eauto.
          Qed.

          Theorem fold_left_bad_perm_equiv : 
            forall (A : Set)(ls1 ls2 : list A)(f : A -> bool),
              (forall a, f a = true -> (In a ls1 <-> In a ls2)) ->
              fold_left (fun (b : bool) a => if b then true else (f a)) ls1 false = 
              fold_left (fun (b : bool) a => if b then true else (f a)) ls2 false.


            induction ls1. 
            induction ls2; intuition; simpl in *.

            case_eq (f a); intuition.
            specialize (H a); intuition.
            eapply IHls2; intuition.
            eapply H.
            eapply H1; intuition.
            intuition.

            intuition.
            simpl in *.
            case_eq (f a); intuition.
            rewrite fold_left_bad_true.
            erewrite fold_left_one_bad.
            trivial.
            eapply H.
            eauto.
            intuition.
            trivial.

            eapply IHls1.
            intuition.
            eapply H; intuition.
            specialize (H a0); intuition.
            subst.
            congruence.

          Qed.

          assert (fold_left
     (fun (b : bool) (x : nat * nat) =>
       if b then true else badBlinding_ezxz xSet e z x)
     (allPairs_2 xinds (y :: l0)) false
     = 
     fold_left
     (fun (b : bool) (x : nat * nat) =>
       if b then true else badBlinding_ezxz xSet e z x)
     (allPairs_2 xinds l0 ++ (foreach  (z0 in xinds)(z0, y)) ) false
          ).

          eapply (fold_left_bad_perm_equiv) .
          
          intuition.
          unfold allPairs_2, allPairs_1 in *.
          simpl in *.
          eapply in_flatten in H1.
          destruct H1.
          intuition.
          eapply in_map_iff in H2.
          destruct H2.
          intuition; subst.
          simpl in *.
          intuition.
          subst.
          eapply in_or_app.
          right.
          eapply in_map_iff.
          econstructor.
          intuition.
          
          eapply in_map_iff in H1.
          destruct H1.
          intuition.
          subst.

          eapply in_or_app.
          left.
          eapply in_flatten.
          econstructor.
          split.
          eapply in_map_iff.
          econstructor.
          intuition.
          eauto.
          eapply in_map_iff.
          econstructor.
          intuition.

          unfold allPairs_2, allPairs_1 in *.
          simpl in *.
          eapply in_app_or in H1.
          intuition.
          
          eapply in_flatten in H2.
          destruct H2.
          intuition.
          eapply in_map_iff in H2.
          destruct H2.
          intuition.
          subst.
          eapply in_map_iff in H3.
          destruct H3.
          intuition.
          subst.
          eapply in_flatten.
          econstructor.
          split.
          eapply in_map_iff.
          econstructor.
          split.
          eauto.
          eauto.
          simpl.
          right.
          eapply in_map_iff.
          econstructor.
          intuition.
          eapply in_map_iff in H2.
          destruct H2.
          intuition.
          subst.
          eapply in_flatten.
          econstructor.
          split.
          eapply in_map_iff.
          econstructor.
          split.
          eauto.
          eauto.
          simpl.
          intuition.

          rewrite H0.
          clear H0.
          rewrite fold_left_app.
          rewrite H.
          trivial.

        Qed.

        eapply badBlinding_ez_allPairs_simp.
        trivial.
            
        eapply leRat_trans.
        eapply eqRat_impl_leRat.
        eapply sumList_body_eq.
        intros.
        rewrite (H1).
        
        eapply eqRat_refl.

        
        Theorem badBlinding_ez_count_h : 
           forall xinds ys xSet e z,
             NoDup ys ->
             sumList ys
             (fun a0 : nat =>
      if fold_left
        (fun (b : bool) (x : nat * nat) =>
          if b then true else badBlinding_ezxz xSet e z x)
        (foreach  (z0 in xinds)(z0, a0)) false
        then 1
        else 0) <= (length xinds * length xSet) / 1.

          induction xinds; intuition.
          simpl in *.
          eapply eqRat_impl_leRat.
          eapply sumList_0.
          intuition.

          Local Opaque badBlinding_ezxz.
          simpl.
          
          eapply leRat_trans.
          eapply sumList_le.
          intros.
          
          assert (
            (if fold_left
         (fun (b : bool) (x : nat * nat) =>
          if b then true else badBlinding_ezxz xSet e z x)
         (foreach  (z0 in xinds)(z0, a0)) (badBlinding_ezxz xSet e z (a, a0))
    then 1
    else 0)
             <=
             (if (badBlinding_ezxz xSet e z (a, a0)) then 1 else 0) + 
             (if fold_left
         (fun (b : bool) (x : nat * nat) =>
          if b then true else badBlinding_ezxz xSet e z x)
         (foreach  (z0 in xinds)(z0, a0)) false
    then 1
    else 0)
             )%rat.

          case_eq (badBlinding_ezxz xSet e z (a, a0)); intuition.
          rewrite fold_left_bad_true.
         
          assert (1 <= 1 + 0)%rat.
          eapply eqRat_impl_leRat.
          eapply ratAdd_0_r.
          eapply leRat_trans.
          eapply H2.
          clear H2.

          eapply ratAdd_leRat_compat; intuition.
          eapply rat0_le_all.

          eapply eqRat_impl_leRat.
          eapply ratAdd_0_l.
          eapply H1.

          rewrite sumList_sum.
          eapply leRat_trans.
          Focus 2.
          eapply eqRat_impl_leRat.
          eapply eqRat_symm.
          eapply ratAdd_num.
          
          eapply ratAdd_leRat_compat.
          eapply badBlinding_ezxz_count.
          trivial.
          
          eapply IHxinds.
          trivial.

        Qed.

        eapply badBlinding_ez_count_h.
        trivial.
      Qed.
             

      Theorem  badBlinding_c_count : 
        forall ys k_X xinds f xSet q c a,
          badBlinding_c k_X xinds f xSet q c = false ->
          NoDup ys ->
          (sumList ys (fun y => if (badBlinding_c k_X xinds ((a, y) :: f) xSet q c) then 1 else 0) <= (length xinds * length f * length xSet) / 1).

        intuition.
        unfold badBlinding_c in *.
        unfold setLet in *.
        destruct q.

        case_eq (eqb (k ++ c) a); intuition.
        assert (
          sumList ys
          (fun y : nat =>
            if match
                 arrayLookup (list_EqDec bool_EqDec) ((a, y) :: f) (k ++ c)
                 with
                 | Some z => badBlinding_ez xinds ((a, y) :: f) xSet (F_P k_X k0) z
                 | None => false
               end
              then 1
              else 0)
          ==
          sumList ys
          (fun y : nat =>
            if (badBlinding_ez xinds ((a, y) :: f) xSet (F_P k_X k0) y)
              
              then 1
              else 0)
        ).
        
        eapply sumList_body_eq; intuition.
        unfold arrayLookup.
        rewrite H.
        intuition.

        rewrite H3.
        clear H3.
        
        Theorem badBlinding_ez_count_z : 
        forall ys xSet e xinds f,
          NoDup ys ->
          (sumList ys (fun y => if (badBlinding_ez xinds f xSet e y) then 1 else 0) <= (length xinds * length f * length xSet) / 1).

          intuition.
          unfold badBlinding_ez.
          unfold setLet.

          (*
          Theorem sumList_count_orb_le : 
            forall (A : Set)(ls : list A)(f1 f2 : A -> bool),
              sumList ls (fun a => if ((f1 a) || (f2 a)) then 1 else 0) <=
              sumList ls (fun a => (if (f1 a) then 1 else 0) + (if (f2 a) then 1 else 0))%rat.

            induction ls; intuition.
            unfold sumList; simpl.
            intuition.

            repeat rewrite sumList_cons.
            eapply leRat_trans.
            Focus 2.
            eapply eqRat_impl_leRat.
            eapply eqRat_symm.
            eapply sumList_cons.
            simpl.
            destruct (f1 a); simpl.
            eapply ratAdd_leRat_compat; intuition.
            eapply leRat_trans.
            eapply eqRat_impl_leRat.
            eapply ratAdd_0_r.
            eapply ratAdd_leRat_compat; intuition.
            eapply rat0_le_all.
            
            destruct (f2 a).
            eapply ratAdd_leRat_compat; intuition.
            eapply eqRat_impl_leRat.
            eapply ratAdd_0_l.

            eapply ratAdd_leRat_compat; intuition.
            eapply rat0_le_all.
            
          Qed.
          *)
          
          Theorem badBlinding_ezxz_count_z : 
            forall ys xSet e p,
              NoDup ys ->
              (sumList ys (fun y => if (badBlinding_ezxz xSet e y p) then 1 else 0) <= (length xSet) / 1).
            
          Admitted.
          
          Theorem badBlinding_ez_count_z_h : 
            forall ps ys xSet e,
              NoDup ys ->
            sumList ys
            (fun y : nat =>
              if fold_left
                (fun (b : bool) (x : nat * nat) =>
                  if b then true else badBlinding_ezxz xSet e y x)
                ps false
                then 1
                else 0) <= length ps * length xSet / 1.

            induction ps; intuition; simpl in *.
            eapply eqRat_impl_leRat.
            eapply sumList_0.
            intuition.

            assert ( sumList ys
     (fun y : nat =>
      if fold_left
           (fun (b0 : bool) (x : nat * nat) =>
            if b0 then true else badBlinding_ezxz xSet e y x) ps
           (badBlinding_ezxz xSet e y (a0, b))
      then 1
      else 0)
     <=
      sumList ys
     (fun y : nat =>
       (if (badBlinding_ezxz xSet e y (a0, b)) then 1 else 0)%rat + 
         if  fold_left
           (fun (b0 : bool) (x : nat * nat) =>
            if b0 then true else badBlinding_ezxz xSet e y x) ps
           false
      then 1
      else 0)%rat
     ).
            
            eapply sumList_le; intuition.
            destruct (badBlinding_ezxz xSet e a (a0, b)).
            rewrite fold_left_bad_true.
            
            assert (1 == 1 + 0)%rat.
            eapply ratAdd_0_r.
            eapply leRat_trans.
            eapply eqRat_impl_leRat.
            eapply H1.
            eapply ratAdd_leRat_compat; intuition.
            eapply rat0_le_all.

            eapply eqRat_impl_leRat.
            eapply ratAdd_0_l.
            rewrite H0.
            clear H0.
            rewrite sumList_sum.
            eapply leRat_trans.
            Focus 2.
            eapply eqRat_impl_leRat.
            symmetry.
            eapply ratAdd_num.
            eapply ratAdd_leRat_compat; intuition.

            eapply badBlinding_ezxz_count_z.
            trivial.
          Qed.
            
          eapply leRat_trans.
          eapply badBlinding_ez_count_z_h.
          trivial.

          Theorem allPairs_2_length : 
            forall (A B : Set)(lsa : list A)(lsb : list B),
              (length (allPairs_2 lsa lsb) = length lsa * length lsb)%nat.

            induction lsa; intuition.
            unfold allPairs_2, allPairs_1 in *; simpl.
            rewrite app_length.
            
            rewrite IHlsa.
            rewrite map_length.
            intuition.
          Qed.
          
          rewrite  allPairs_2_length.
          rewrite split_length_r.
          intuition.

        Qed.

                (* In order to apply the next theorem, we need to show that putting (a, y) in the function changes nothing (since y is also used as the unblinding values) *)
        assert 
          (sumList ys
     (fun y : nat =>
      if badBlinding_ez xinds ((a, y) :: f) xSet (F_P k_X k0) y then 1 else 0) 
     ==
     sumList ys
     (fun y : nat =>
      if badBlinding_ez xinds f xSet (F_P k_X k0) y then 1 else 0)
     ).
        admit.
        rewrite H3.
        clear H3.

        eapply badBlinding_ez_count_z; intuition.

        eapply leRat_trans.
        eapply eqRat_impl_leRat.
        eapply sumList_body_eq.
        intuition.
        simpl.

        case_eq (@eqb Blist (@list_EqDec bool bool_EqDec)
             (@app bool k (natToBlist c)) a); intuition.
        rewrite eqb_leibniz in H4.
        subst.
        rewrite eqb_refl in H.
        discriminate.
        eapply eqRat_refl.

        case_eq (@arrayLookup Blist nat (@list_EqDec bool bool_EqDec) f
               (@app bool k (natToBlist c))); intuition.
        rewrite H3 in H0.
        eapply leRat_trans.
        eapply badBlinding_ez_count; intuition.
        eapply leRat_terms.
        eapply mult_le_compat; intuition.
        rewrite <- mult_1_r at 1.
        eapply mult_le_compat; intuition.
        (* the size of the function is at least 1 *)
        admit.
        intuition.
        eapply leRat_trans.
        eapply eqRat_impl_leRat.
        eapply sumList_0.
        intuition.
        eapply rat0_le_all.
      Qed.

      Theorem badBlinding_q_count : 
      forall ys k_X xinds f xSet q a,
          badBlinding_q k_X xinds f xSet q = false ->
          NoDup ys ->
          (sumList ys (fun y => if (badBlinding_q k_X xinds ((a, y) :: f) xSet q) then 1 else 0) <= (MaxMatchingIDs * length xinds * length f * length xSet) / 1).
        Admitted.

        Theorem badBlinding_count : 
      forall ys k_I k_X db f xSet q a,
          badBlinding k_I k_X db f xSet q = false ->
          NoDup ys ->
          (sumList ys (fun y => if (badBlinding k_I k_X db ((a, y) :: f) xSet q) then 1 else 0) <= (length q * MaxMatchingIDs * length db * length f * length xSet) / 1).
        Admitted.

      Theorem badBlinding_prob : 
        forall k_I k_X db f xSet q a,
          badBlinding k_I k_X db f xSet q = false ->
          Pr [a0 <-$ [ 0  .. 2 ^ lambda); ret badBlinding k_I k_X db ((a, a0) :: f) xSet q ] <= (length q * MaxMatchingIDs * length db * length f * length xSet) / 2 ^ lambda.

        intuition.
        rewrite evalDist_seq_step.

        eapply leRat_trans.
        eapply sumList_le.
        intuition.
        eapply ratMult_leRat_compat.
        eapply eqRat_impl_leRat.
        eapply RndNat_prob.
        eapply RndNat_support_lt.
        trivial.
        eapply leRat_refl.
        rewrite sumList_factor_constant_l.
        
        assert (
          (@sumList nat
           (@getSupport nat (RndNat (pow (S (S O)) (posnatToNat lambda))))
           (fun a0 : nat =>
            @evalDist bool
              (@Ret bool (@EqDec_dec bool bool_EqDec)
                 (badBlinding k_I k_X db
                    (@cons (prod Blist nat) (@pair Blist nat a a0) f) xSet q))
              true))
        ==
        (sumList (allNatsLt (2^ lambda)))
      (fun a0 : nat => if (badBlinding k_I k_X db ((a, a0) :: f) xSet q) then 1 else 0)

        ).
        
        erewrite sumList_permutation.
        eapply sumList_body_eq.
        intuition.
        Local Transparent evalDist.
        simpl.
        destruct ( badBlinding k_I k_X db ((a, a0) :: f) xSet q).
        destruct (EqDec_dec bool_EqDec true true); intuition.
        destruct (EqDec_dec bool_EqDec false true); intuition.

        Theorem RndNat_support_perm : 
          forall (n : nat),
            Permutation (getSupport (RndNat n)) (allNatsLt n).

          intuition.
          eapply NoDup_Permutation.
          eapply getSupport_NoDup.
          eapply allNatsLt_NoDup.
          intuition.
          eapply allNatsLt_lt_if.
          eapply RndNat_support_lt.
          trivial.
          eapply in_getSupport_RndNat.
          eapply allNatsLt_lt.
          trivial.

        Qed.

        eapply  RndNat_support_perm .
        
        rewrite H.
        clear H.

        rewrite badBlinding_count.
        eapply eqRat_impl_leRat.
        rewrite <- ratMult_num_den.
        eapply eqRat_terms.
        omega.
        unfold posnatMult, natToPosnat, posnatToNat.
        eapply mult_1_r.
        trivial.
        eapply allNatsLt_NoDup.
      Qed.

      Show.
      rewrite badBlinding_prob.
      admit.

      trivial.
      admit.
      trivial.

      rewrite <- ratMult_num_den.
      eapply leRat_terms.
      simpl.
      eapply le_eq.
      ring.
      unfold posnatMult, natToPosnat, posnatToNat.
      rewrite mult_1_l.
      trivial.

    Qed.

    Show.
    rewrite Initialize_10_2_badBlinding_prob.
    eapply leRat_terms.
    (* need to clean up the expression a bit*)
    admit.

    intuition.

    econstructor.
    eauto.
  Qed.


  Print G11.
  Print Initialize_11.
  Print GenTrans_11.
  Print ServerSearch_11.
  Print ServerSear



  Theorem G10_3_equiv :
    | Pr[x <-$ G10_2] - Pr[G10_3] | <= 0.

    rewrite Initialize_10_2_bad_Prob.
    

      rewrite mult_assoc;
      eapply mult_le_compat; intuition.
      ea
      ring.
      omega.

      (* TODO: replace MaxMatchingIDs everywhere with (length db)---simplifies things and gets rind of an assumptions, but makes bounds worse.*)

      Print lookupInds.

        SearchAbout ratMult RatIntro.
        

        Local Transparent evalDist.
        simpl.
        unfold evalDist.

        assert (
          sumList (getSupport ([ 0  .. 2 ^ lambda)))
      (fun a0 : nat =>
       Pr  [ret badBlinding k_I k_X db ((a, a0) :: f) xSet q ]))%rat
        ==
        sumList (getSupport ([ 0  .. 2 ^ lambda)))
      (fun a0 : nat =>
       Pr  [ret badBlinding k_I k_X db ((a, a0) :: f) xSet q ]))%rat
        ).

          (sumList ys (fun y => if (badBlinding k_I k_X db ((a, y) :: f) xSet q) then 1 else 0))
             ==
             (sumList ys (fun y => if (badBlinding k_I k_X db ((a, y) :: f) xSet q) then 1 else 0))
             ).
               
        
        eapply leRat_trans.
        eapply ratMult_leRat_compat.
        eapply leRat_refl.
        Focus 2.
        rewrite badBlinding_count.
        

      Qed.
        
      Set Printing All.
      Show.
      case_eq (arrayLookup (list_EqDec bool_EqDec) s a ); intuition.
      
      

      SearchAbout badBlinding nil
      

      unfold Initialize_10_2.


    Qed.

    Show.
    eapply Initialize_10_2_badBlinding_prob.

    Show.
    comp_inline_l.
    inline_first.
    

  Qed.


Here!!!
  

      intuition.
      
      unfold Initialize_10_2, Initialize_11.
      simpl.

      assert TSet.
      assert (TSet * TSetKey).
      eapply comp_base_exists.
      eapply TSetSetup.
      econstructor.
      intuition.

      comp_skip.

      remember (split a0) as z.
      destruct z.

      simpl.
      inline_first.
      comp_skip.

      simpl.
      comp_simp.
      simpl.
      inline_first.
      comp_skip.
      comp_simp.

      case_eq (badBlinding k_I k_X db b xSet q); intuition.
      comp_irr_l.
      admit.
      admit.
      comp_irr_r.
      admit.
      admit.
      comp_simp.
      eapply comp_spec_ret; intuition.
      simpl.

      

      erewrite natRandFunc_badBlinding_persists_oc.
      symmetry.
      erewrite natRandFunc_badBlinding_persists_oc.
      trivial.
      eauto.
      eapply H13.
      eauto.
      eapply H12.
      simpl in *.
      assert (badBlinding k_I k_X db l2 xSet q = true).
      eapply natRandFunc_badBlinding_persists_oc.
      eauto.
      eauto.
      congruence.
     
      comp_skip.
      (* This can go bad during the course of execution. *)
     


     

      
      Show.

      admit.

      intuition.
      subst.
      eapply comp_spec_consequence.
      eapply GenTrans_10_1_11_spec.
      apply in_combine_r in H15.
      eapply (@compMap_support _ _ (fun a b => snd b = arrayLookupList _ (combine (toW db) l) a)) in H9.
      eapply list_pred_symm in H9.
      eapply (@list_pred_impl_unary _ _ _ (fun a a => (snd a) = nil \/ In (snd a) l)) in H9.
      


      eapply list_pred_unary_in in H9.
      intuition.
      assert (snd (a2, b3) = nil).
      eapply H14.
      simpl in *.
      subst.
      simpl.    
      omega.
      simpl in *.

      eapply (@oc_compMap_support _ _ _ (fun s a b => length (snd a) <= MaxMatchingIDs -> length (fst b) <= MaxMatchingIDs))%nat in H5.
      eapply list_pred_symm in H5.

      eapply (@list_pred_fst_split_irr _ _ _  (fun
            (b0 : list
                    (Vector.t bool (lambda + lambda) *
                     (Identifier lambda * nat)))
            (a : Keyword * list nat) =>
          (length (snd a) <= MaxMatchingIDs -> length b0 <= MaxMatchingIDs)%nat)) in H5.



      eapply list_pred_symm in H5.
      eapply (@list_pred_snd_split_irr _ _ _  (fun
                                                  (a : list nat)
            (b0 : list
                    (Vector.t bool (lambda + lambda) *
                     (Identifier lambda * nat)))
            =>
          (length a <= MaxMatchingIDs -> length b0 <= MaxMatchingIDs)%nat)) in H5.

      eapply (@list_pred_in_all _ _) in H5.
      eapply H5.
      intuition.
      eapply H1.
      assert (split (combine (toW db) sigmas) = ((toW db), sigmas)).
      eapply combine_split.
      trivial.
      rewrite H17 in H9.
      trivial.
      rewrite <- Heqz.
      trivial.
      
      intuition.
      simpl in *.
      repeat simp_in_support.
      destruct x.
      repeat simp_in_support.
      simpl.
      
 

      erewrite (@oc_compMap_length _ _ _ _ _ _ _ (list (Blist * nat))).
      Focus 2.
      eapply H19.
      rewrite combine_length.
      eapply Nat.min_le_iff.
      right.
      rewrite allNatsLt_length.
      eauto.

      intuition.
      trivial.
      intuition.
      simpl in *.
      unfold arrayLookupList in *.
      case_eq 
        ( @arrayLookup Keyword
             (list
                (prod
                   (Vector.t bool
                      (plus (posnatToNat lambda) (posnatToNat lambda)))
                   (prod (Identifier (posnatToNat lambda)) nat)))
             (@list_EqDec bool bool_EqDec)
             (@combine Keyword
                (list
                   (prod
                      (Vector.t bool
                         (plus (posnatToNat lambda) (posnatToNat lambda)))
                      (prod (Identifier (posnatToNat lambda)) nat))) 
                (toW db) l) b4); intuition.
      rewrite H in H14.
      subst.



      right.
      eapply (@arrayLookup_combine_Some_In Blist).
      eauto.
      rewrite H in H14.
      subst.
      intuition.

      intuition.
      repeat simp_in_support.
      trivial.
      
      intuition.
      assert (c = (snd (snd (a3, (b2, c))))).
      trivial.
      rewrite H17.
      clear H17.
      eapply H13.
      eapply in_combine_r.
      eauto.
      trivial.

      assert (In b2 (fst (split db))).
      admit.
      eauto.

      assert (bvectorToNat (snd (splitVector lambda lambda a3)) =
              F_P k_I (Vector.to_list b2) * inverse c).
      (* I can derive this from the existing support information *)
      admit.
      eapply H17.

      eauto.
      eapply in_combine_l.
      eauto.
      
      intuition.
      simpl.
      assert ((a3, (a4, b5)) = fst b4).
      destruct b4; simpl in *; pairInv; trivial.
      eapply H18.
      destruct b4; simpl in *; pairInv; trivial.
      simpl.
      subst.
      
      eapply H13.

      eapply H19.


      Theorem badBlinding_all_false : 
        forall q k_I k_X db s0 xSet,
          badBlinding k_I k_X db s0 xSet q = false ->
          forall a, In a q -> 
                    badBlinding_q k_X (map (fun x => F_P k_I (Vector.to_list x)) (fst (split db))) s0 xSet a = false.

        induction q; unfold badBlinding; intuition; simpl in *;
        intuition.
        subst.
        unfold setLet in *.
        case_eq ((badBlinding_q k_X
            (foreach  (x in fst (split db))F_P k_I (Vector.to_list x)) s0
            xSet a0))
                 ; intuition.
        rewrite H1 in H0.
        rewrite fold_left_bad_true in H0.
        discriminate.
        
        unfold setLet in *.
        case_eq (badBlinding_q k_X
            (foreach  (x in fst (split db))F_P k_I (Vector.to_list x)) s0
            xSet a); intuition;
        rewrite H1 in H0.
        rewrite fold_left_bad_true in H0.
        discriminate.
        eapply IHq; eauto.
      Qed.

      Show.

      Theorem badBlinding_q_xind_subset : 
        forall x1 x2 k_X s xSet q,
          badBlinding_q k_X x1 s xSet q = false ->
          (forall a, In a x1 -> In a x2) ->
          badBlinding_q k_X x2 s xSet q = false.

      Admitted.

      eapply badBlinding_q_xind_subset.
      eapply badBlinding_all_false .
      eapply H4.
      eapply in_combine_l.
      eauto.
      
      intuition.
      (* Combine this with the support fact from before *)
      admit.

      intuition.
      simpl in *.
      
      intros.
      simpl in *.
      destruct H14.
      intuition.
      simpl in *.
      

      SearchAbout badBlinding_q.
      eapply goodBlinding_Prop_correct in H4.
      unfold badBlinding in *.
      unfold setLet in *.
      

      SearchAbout arrayLookup Some In.
      Set Printing All.
      Show.
      case_eq (arrayLookup (list_EqDec bool_EqDec) (combine (toW db) l) b4); intuition.
      unfold Blist in *.
      rewrite H in H4.

      eapply MaxMatchingIDs_correct.
      
      SearchAbout min le.
      SearchAbout combine length.

      eapply (@oc_compMap_support _ _ _ (fun s a b => length b <= MaxMatchingIDs))%nat.

      assert (length (fst (split a0)) <= MaxMatchingIDs)%nat.
      eapply H3.

      assert (forall x, In x l -> length x <= MaxMatchingIDs)%nat.
      admit.      
      apply in_combine_r in H10.
      

      assert (forall x, In x b1 -> length (snd x) <= MaxMatchingIDs)%nat.
      intuition.
      

      assert (b3 = snd (a2, b3)).
      trivial.
      rewrite H13.
      clear H13.
      eapply H12.
      eapply in_combine_r.
      eauto.
      

      eapply H12.
      eapply in_combine_r in H10.
      

      Show.
      
        
        simpl.
        
        eapply H11.
        
        rewrite H11 in H9.
        

        Set Printing All.
        Show.
        case_eq (arrayLookup (list_EqDec bool_EqDec) s (k ++ a) ); intuition.
        rewrite H9 in H10.
        

        SearchAbout groupExp mult.

        erewrite <- H2.

        intros.
        

        eapply H2.
        
        
       SearchAbout In split.
        
        eapply H.
        
        SearchAbout In allNatsLt.
        unfold goodBlinding_q_Prop in *.
        


        Theorem badBlinding_q_Prop : 
          forall 
          k_X (xinds : list nat)(f : list (Blist * nat)) xSet (q : Query),
          badBlinding_q k_X xinds f xSet q = false ->
          forall z, In z (allNatsLt MaxMatchingIDs) ->
                    badBlinding_c k_X xinds f xSet q z = false.


          fold_left (fun (b : bool) z => if b then true else badBlinding_c k_X xinds f xSet q z) (allNatsLt MaxMatchingIDs) false.

          
        
        unfold badBlinding_q in H6.
        
        
        subst.
        
        
        comp_simp.

        (forall n0 n1, 
        
        SearchAbout map eq.
        eapply map_ext'.

        f_equal.
        f_equal.
        


      Qed.

    Qed.

    
    eapply Init_10_2_11_eq_until_bad.
    comp_simp.
    intuition; simpl in *.
    destruct( badBlinding x1 x0 d b (XSetSetup_2 x0 x1 d x2) l); intuition.
    rewrite <- H8.
    comp_irr_l; wftac.
    comp_irr_r; wftac.
    eapply comp_spec_ret; intuition.
    pairInv.
    pairInv.
    pairInv.
    comp_skip.
    eapply comp_spec_ret; intuition.
    pairInv.
    rewrite <- H8.
    trivial.
    pairInv.
    trivial.
   

  Qed.

  Theorem G10_4_equiv : 
    | Pr[x <-$ G10_3; ret fst x] - Pr[x <-$ G10_4; ret fst x] | <= 0.

    eapply leRat_trans.
    eapply fundamental_lemma_h.
    
    

  Qed.
  

  (* Now remove the badness computation to get to game 11 *)


  (* Step 10.2 : Test for badness at the end of the game the result *)

  (* Step 10.3 : Like 11 with badness exposed.  Close to 10.2 by identical until bad *)

  (* These are the same unless there is a collision during unblinding.  The random function ensures that the probability of this event is small. *)
  (* Use identical until bad with oc_eventProb and other similar theorems. *)

  

  (* Step 12: Replace the random function calls in GenTrans with array lookups.  This is equivalent because unblidinding collisions are now impossible.  *)


  (* Step 13: replace random function calls in initialization with random values, since they are all unique*)

  

  

  (* Step 11 : We want to replace the random function with a random permutation that ensures that there are no unbliding collisions in the XSet.  First we move some things around to get the game in the form of the "generalized random permutation" argument. *)
  Require Import RandPermSwitching.

  Definition Initialize_wLoop_11 db k_I e :=
    [w, sigma ] <-2 e;
    inds <- lookupInds db w;
    k_E <--$$ {0, 1}^lambda;
    oc_compMap _ (Initialize_indLoop_9 k_I k_E w) (combine (permute (oneVector lambda) inds sigma) (allNatsLt (length inds))).

  Definition G11_A db q s_A k_X k_I sigmas xSet :=
    t_entries_pts <--$ oc_compMap _ (Initialize_wLoop_11 db k_I) (combine (toW db) sigmas);
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <--$2$ TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <--$$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <--$ oc_compMap _ (GenTrans_9 edb k_X) (combine q stags_ts);
    $ A2 s_A edb (snd (split searchRes)).

  
  Definition sampleSigmas_11 db w :=
    inds <- lookupInds db w;
    RndPerm (length inds).

  Definition G11 :=
    [db, q, s_A] <-$3 A1;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    sigmas <-$ compMap _ (sampleSigmas_11 db) (toW db);
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    [b, _] <-$2 (G11_A db q s_A k_X k_I sigmas xSet) _ _ (@randomFunc Blist nat (RndNat (2^lambda)) _ ) nil; 
    ret b.


  (* Step 12 : now apply the argument *)

  (* first we need the predicate that tells us when the PRP goes bad *)

  Definition allPairs_1(A B : Type)(a : A)(lsb : list B) :=
    map (pair a) lsb.

  Definition allPairs_2(A B : Type)(lsa : list A)(lsb : list B) : list (A * B) :=
    flatten (map (fun a => allPairs_1 a lsb) lsa).

  Definition rpBad1 (xSet : list nat)(r1 : nat)(p : nat * nat * nat) :=
    [xind, e, r2] <-3 p;
    if (in_dec (EqDec_dec _) (g ^ r1 * xind * e * r2) xSet) 
      then true else false.

  Definition rpBad k_X (xSet : list nat)(xinds : list nat)(f : list (Blist * nat))(d : Blist)(r : nat) :=
    keywords <- d :: (fst (split f));
    (* these aren't keywords, they are keywords appended with numbers, and they don't include query keywords *)
    es <- map (F_P k_X) keywords;
    xinds_es <- allPairs_2 xinds es;
    rs <- snd (split f);
    xinds_es_rs <- allPairs_2 xinds_es rs;
    bad1 <- fold_left (fun (b : bool) x => if b then true else (rpBad1 xSet r x)) xinds_es_rs false;
    rsInverse <- map inverse rs;
    xinds_es_rsInverse <- allPairs_2 xinds_es rsInverse;
    bad2 <- fold_left (fun (b : bool) x => if b then true else (rpBad1 xSet (inverse r) x)) xinds_es_rsInverse false;
    bad1 || bad2.
    
  Variable maxDB_Keywords : nat.
  Variable maxQueries : nat.
  Variable maxIDsPerKeyword : nat.
  Variable maxDB_Size : nat.

  Hypothesis maxDB_Keywords_correct : 
    forall db qs s_A,
      In (db, qs, s_A) (getSupport A1) ->
        (length (toW db) <= maxDB_Keywords)%nat.

  Hypothesis maxIDsPerKeyword_correct : 
    forall db qs s_A,
      In (db, qs, s_A) (getSupport A1) ->
      forall w,
        (length (lookupInds db w) <= maxIDsPerKeyword)%nat.

  Theorem oc_compMap_qam :
    forall (A B C D : Set){eqdd : EqDec D}(ls : list A)(c : A -> OracleComp B C D) n,
      (forall a, In a ls -> queries_at_most (c a) n) ->
      queries_at_most (oc_compMap _ c ls) (length ls * n).

    induction ls; intuition; simpl in *.
    econstructor.
    econstructor; intuition.
    rewrite <- plus_0_r.
    econstructor.
    eapply IHls.
    intuition.
    intuition.
    econstructor.
  Qed.

  Theorem G11_A_qam : 
    forall a0 b b0 b1 b2 b3 x,
      In (a0, b, x) (getSupport A1) ->
      In b3 (getSupport (compMap _ (sampleSigmas_11 a0) (toW a0))) ->
     queries_at_most (G11_A a0 b b0 b1 b2 b3 (XSetSetup_2 b1 b2 a0 b3)) (maxDB_Keywords * maxIDsPerKeyword + maxQueries * 2).
  
    intuition.
    unfold G11_A.
    econstructor.
    econstructor.
    eapply oc_compMap_qam.
    intuition.
    unfold Initialize_wLoop_11.
    comp_simp.
    econstructor.
    econstructor.
    intuition.
    econstructor.
    eapply oc_compMap_qam .
    intuition.
    unfold Initialize_indLoop_9.
    comp_simp.
    econstructor.
    econstructor.
    intuition.
    econstructor.
    econstructor.
    intuition.
    econstructor.
    rewrite plus_0_l.
    rewrite plus_0_r.
    rewrite mult_1_r.

    rewrite combine_length.
    rewrite allNatsLt_length.
    unfold sampleSigmas_11 in *.
    apply (@compMap_support _ _  (fun a b => length b = length (lookupInds a0 a))) in H1.

    rewrite permute_length_eq.
    rewrite min_r.
    eapply maxIDsPerKeyword_correct.
    eauto.
    eapply le_refl_gen.


    Theorem list_pred_in_combine : 
      forall (A B : Set) P (lsa : list A)(lsb : list B),
        list_pred P lsa lsb ->
        forall a b,
          In (a, b) (combine lsa lsb) ->
          P a b.

      induction 1; intuition; simpl in *.
      intuition.
      intuition.
      pairInv.
      trivial.

    Qed.

    eapply list_pred_in_combine in H1.
    symmetry.
    eapply H1.
    trivial.
    intuition.
    
    unfold setLet in *.
    eapply RndPerm_In_support_length.
    trivial.
    
    rewrite plus_0_l.
    eapply mult_le_compat; intuition.
    rewrite combine_length.
    apply compMap_length in H1.
    rewrite H1.
    rewrite min_l.
    eapply maxDB_Keywords_correct.
    eauto.
    trivial.
    
    intuition.
    comp_simp.
    simpl.
    rewrite <- plus_0_l.
    econstructor.
    econstructor.
    intuition.
    rewrite <- plus_0_l.
    econstructor.
    econstructor.
    intuition.
    rewrite <- plus_0_r.
    econstructor.

    econstructor.
    eapply oc_compMap_qam.
    intuition.
    unfold GenTrans_9.
    comp_simp.
    
    destruct a1.
    destruct p0.
    destruct q.
    unfold setLet.
    
    comp_simp.
    econstructor.
    econstructor.
    eapply oc_compMap_qam.
    intuition.
    econstructor.
    econstructor.
    intuition.
    econstructor.
    
    
  Qed.

  Definition G12 :=
    [db, q, s_A] <-$3 A1;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    sigmas <-$ compMap _ (sampleSigmas_11 db) (toW db);
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    allXinds <- map (F_P k_I) (toW db);
    [b, _] <-$2 (G11_A db q s_A k_X k_I sigmas xSet) _ _ (@GenRP (Blist) _ (RndNat (2^lambda)) _ _  (rpBad k_X xSet allXinds)) nil; 
    ret b.
  
  Theorem G11_G12_close : 
     | Pr[G11] - Pr[G12] | <= 0.

     unfold G11, G12.
     eapply leRat_trans.

     
     eapply evalDist_bind_distance; intuition; wftac.
     apply evalDist_bind_distance; intuition; wftac.
     apply evalDist_bind_distance; intuition; wftac.

     apply evalDist_bind_distance; intuition; wftac.
     admit.
     comp_simp.

     destruct a3.
     eapply (@RPS_G0_1_close _ _ _ _ _ _ _ _ 
                             (fun (n : nat) => (maxDB_Keywords * (maxDB_Keywords + maxQueries * 2) * maxDB_Size * n) / 2^lambda)).
     admit.
     

     eapply well_formed_RndNat.
     admit.
     
     SearchAbout RndNat.

     apply evalDist_bind_distance; intuition; wftac.
     admit.
     

   Qed.
    
    
  Print G9_A.

   k_X <--$$ {0,1}^lambda;
    k_I <--$$ {0,1}^lambda;
    wLoopRes <--$ oc_compMap _ (Initialize_wLoop_9 db k_I) (toW db);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <--$2$ TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <--$$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <--$ oc_compMap _ (GenTrans_9 edb k_X) (combine q stags_ts);
    $ ret (edb, searchRes).


  Print G10.



  (* Step 7.1: This proof is by a hybrid argument on the list of keywords.  Start by delaying some of the sampling *)
  Definition Initialize_7_1 (db : DB)(q : list Query) :=
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_7 db k_I k_Z) (toW db);
    k_X <-$ {0,1}^lambda;
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts);
    ret (edb, searchRes).

  Theorem G7_1_equiv : 
    Pr[G7] == Pr[G_gen Initialize_7_1].

    unfold G7, G_gen, Initialize_7, Initialize_7_1.
    
    (comp_skip; comp_simp; inline_first).
    do 3 (inline_first; comp_at comp_inline leftc 1%nat; comp_swap_l; comp_skip; comp_simp).
    repeat (inline_first; comp_skip; comp_simp).

  Qed.

  (* Step 7.2: Now put the game in the form of the hybrid argument. *)

  Require Import ListHybrid.

  Definition G7_2_A1 :=
    [db, q, s_A] <-$3 A1;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    ret (toW db, (k_I, k_Z, db, q, s_A)).

  Definition G7_2_A2 (s_A : Bvector lambda * Bvector lambda * DB * list Query * A_State) :=
    let '(k_I, k_Z, db, _, _) := s_A in
    Initialize_wLoop_7 db k_I k_Z.

  Definition G7_2_A3 (s : Bvector lambda * Bvector lambda * DB * list Query * A_State) wLoopRes :=
    let '(k_I, k_Z, db, q, s_A) := s in
    k_X <-$ {0,1}^lambda;
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts);
    A2 s_A edb (snd (split searchRes)).

  Definition G7_2 :=
    [lsa, s] <-$2 G7_2_A1;
    lsb <-$ compMap _ (G7_2_A2 s) lsa;
    G7_2_A3 s lsb.

  Theorem G7_2_equiv: 
    Pr[G_gen Initialize_7_1] == Pr[G7_2].

    unfold G7_2, G_gen, G7_2_A1, G7_2_A2, G7_2_A3, Initialize_7_1.
    do 3 (inline_first; comp_skip; comp_simp).
    inline_first; comp_skip.
    inline_first; comp_skip.


    remember ( @split
            (list
               (prod
                  (Bvector
                     (posnatToNat
                        (@natToPosnat
                           (plus (posnatToNat lambda) (posnatToNat lambda))
                           (nz_posnat_plus lambda lambda))))
                  (Bvector (posnatToNat lambda)))) 
            (list nat) x1) as z.
    destruct z.
    remember (split x1) as z.
    destruct z.

    assert (l2 = l0).
    assert (l2 = fst (split x1)).
    rewrite <- Heqz0.
    trivial.
    assert (l0 = fst ( ( @split
            (list
               (prod
                  (Bvector
                     (posnatToNat
                        (@natToPosnat
                           (plus (posnatToNat lambda) (posnatToNat lambda))
                           (nz_posnat_plus lambda lambda))))
                  (Bvector (posnatToNat lambda)))) 
            (list nat) x1))).
    rewrite <- Heqz.
    trivial.
    subst.
    trivial.
    subst.

    inline_first.
    comp_skip.
    reflexivity.

    comp_simp.
    inline_first.
    comp_skip.
    reflexivity.

    assert (l1 = l3).
    assert (l1 = snd (( @split
            (list
               (prod
                  (Bvector
                     (posnatToNat
                        (@natToPosnat
                           (plus (posnatToNat lambda) (posnatToNat lambda))
                           (nz_posnat_plus lambda lambda))))
                  (Bvector (posnatToNat lambda)))) 
            (list nat) x1) )).
    rewrite <- Heqz.
    trivial.

    assert (l3 = snd (split x1)).
    rewrite <- Heqz0.
    trivial.
    subst.
    trivial.
    subst.
    reflexivity.

  Qed.

  Definition G7_3_A2 (s_A : Bvector lambda * Bvector lambda * DB * list Query * A_State) :=
    let '(k_I, k_Z, db, _, _) := s_A in
    Initialize_wLoop_8 db k_I k_Z.

  Definition G7_3 :=
    [lsa, s] <-$2 G7_2_A1;
    lsb <-$ compMap _ (G7_3_A2 s) lsa;
    G7_2_A3 s lsb.

  Variable max_keywords : nat.
  Hypothesis max_keywords_correct : 
    forall db q s_A,
      In (db, q, s_A) (getSupport A1) ->
      (length (toW db) <= max_keywords)%nat.

  Theorem max_keywords_G7_2_A1 : 
    forall a b, 
      In (a, b) (getSupport G7_2_A1) ->
      (length a <= max_keywords)%nat.
    
    intuition.
    unfold G7_2_A1 in *.
    repeat simp_in_support.
    destruct x.
    destruct p0.
    repeat simp_in_support.
    eapply  max_keywords_correct; eauto.
  Qed.

  Require Import Encryption.

  Theorem G7_3_close : 
    | Pr[G7_2] - Pr[G7_3] | <= 0.

    unfold G7_2, G7_3.
    eapply evalDist_bind_distance.
    unfold G7_2_A1.
    wftac.
    intuition.
    intuition.

    eapply leRat_trans.
    eapply list_hybrid_close.
    intuition.

    Theorem G7_2_A2_wf : 
      forall x y,
        well_formed_comp (G7_2_A2 x y).

    Admitted.

    Theorem G7_3_A2_wf : 
      forall x y,
        well_formed_comp (G7_3_A2 x y).

    Admitted.

    eapply G7_3_A2_wf.

    intuition.
    unfold LH_G_0, LH_G_1.
    comp_simp.
    eapply evalDist_bind_distance; intuition.
    eapply compMap_wf; intuition.
    eapply G7_3_A2_wf.
   
    eapply leRat_trans.
    eapply eqRat_impl_leRat.
    eapply ratDistance_eqRat_compat.
    comp_swap_l.
    reflexivity.
    comp_swap_l.
    reflexivity.
    eapply evalDist_bind_distance; intuition.
    eapply compMap_wf; intuition.
    eapply G7_2_A2_wf.
    
    unfold G7_2_A2, G7_3_A2.

    Definition Initialize_indLoop_7_O k_I k_Z w (e : Identifier lambda * nat) :=
      [ind, c] <-2 e;
      e <--$ query ind;
      xind <- F_P k_I (Vector.to_list ind);
      z <- F_P k_Z (w ++ c);
      y <- xind * (inverse z);
      $ ret (@Vector.append bool lambda lambda e (natToBvector y), ind).
    
    Definition Initialize_wLoop_7_O db k_I k_Z w :=
      inds <- lookupInds db w;
      sigma <--$$ RndPerm (length inds);
      indLoopRes <--$ oc_compMap _ (Initialize_indLoop_7_O k_I k_Z w) (combine (permute (oneVector lambda) inds sigma) (allNatsLt (length inds)));
      $ ret (indLoopRes, sigma).

    Theorem hybrid_enc_equiv0 : 
      forall n a x z b1 a1 b2 b3 b4,
        evalDist
          (a4 <-$ Initialize_wLoop_7 b1 a1 b2 (nth n a nil);
           G7_2_A3 z (b3 ++ a4 :: b4)) x 
          ==
           evalDist
          (k <-$ {0, 1}^lambda;
           [b, _] <-$2 (a4 <--$ Initialize_wLoop_7_O b1 a1 b2 (nth n a nil); $ G7_2_A3 z (b3 ++ a4 :: b4)) _ _ (EncryptOracle Enc _ k) tt;
           ret b) x.

      intuition.
      unfold  Initialize_wLoop_7.
      comp_simp.
      comp_inline_l.
      comp_at comp_inline leftc 1%nat.
      comp_swap_l.
      comp_skip.
      unfold Initialize_wLoop_7_O.
      eapply comp_spec_eq_impl_eq.
      simpl.
      inline_first; comp_skip.
      inline_first. comp_simp.
      inline_first.
      comp_skip.

      eapply (@compMap_oc_spec _ _ eq _ _ eq).
      eapply list_pred_eq.
      intuition; subst.
      pairInv.

      unfold Initialize_indLoop_4, Initialize_indLoop_7_O.
      simpl.
      unfold EncryptOracle.
      inline_first.
      comp_skip; try apply (oneVector (lambda + lambda)).
      comp_simp.
      eapply comp_spec_ret; intuition.
      destruct b8.
      inline_first.
      comp_ret_r.
      comp_ret_r.
      unfold setLet.
      inline_first.
      comp_skip.
      simpl in H5.
      assert (a2 = l).
      eapply list_pred_eq_impl_eq.
      trivial.
      subst.

      remember (@split
         (list
            (prod (Bvector (plus (posnatToNat lambda) (posnatToNat lambda)))
               (Bvector (posnatToNat lambda)))) (list nat)
         (@app
            (prod
               (list
                  (prod
                     (Vector.t bool
                        (plus (posnatToNat lambda) (posnatToNat lambda)))
                     (Identifier (posnatToNat lambda)))) 
               (list nat)) b5
            (@cons
               (prod
                  (list
                     (prod
                        (Vector.t bool
                           (plus (posnatToNat lambda) (posnatToNat lambda)))
                        (Identifier (posnatToNat lambda)))) 
                  (list nat))
               (@pair
                  (list
                     (prod
                        (Vector.t bool
                           (plus (posnatToNat lambda) (posnatToNat lambda)))
                        (Identifier (posnatToNat lambda)))) 
                  (list nat) l b7) b6))) as z.
      destruct z.
      inline_first.
      comp_skip.
      inline_first.
      comp_skip.
      eapply comp_spec_eq_trans_l.
      eapply comp_spec_eq_symm.
      eapply comp_spec_right_ident.
      comp_skip.
      comp_simp.
      eapply comp_spec_eq_refl.
    Qed.

    Theorem hybrid_enc_equiv1 : 
      forall n a x z b1 a1 b2 b3 b4,
        evalDist
          (a4 <-$ Initialize_wLoop_8 b1 a1 b2 (nth n a nil);
           G7_2_A3 z (b3 ++ a4 :: b4)) x 
          ==
           evalDist
          (k <-$ {0, 1}^lambda;
           [b, _] <-$2 (a4 <--$ Initialize_wLoop_7_O b1 a1 b2 (nth n a nil); $ G7_2_A3 z (b3 ++ a4 :: b4)) _ _ (EncryptNothingOracle Enc _ (zeroVector lambda) k) tt;
           ret b) x.

      intuition.
      unfold  Initialize_wLoop_8.
      comp_simp.
      comp_inline_l.
      comp_at comp_inline leftc 1%nat.
      comp_swap_l.
      comp_skip.
      unfold Initialize_wLoop_7_O.
      eapply comp_spec_eq_impl_eq.
      simpl.
      inline_first; comp_skip.
      inline_first. comp_simp.
      inline_first.
      comp_skip.

      eapply (@compMap_oc_spec _ _ eq _ _ eq).
      eapply list_pred_eq.
      intuition; subst.
      pairInv.

      unfold Initialize_indLoop_8, Initialize_indLoop_7_O.
      simpl.
      unfold EncryptNothingOracle.
      inline_first.
      comp_skip; try apply (oneVector (lambda + lambda)).
      comp_simp.
      eapply comp_spec_ret; intuition.
      destruct b8.
      inline_first.
      comp_ret_r.
      comp_ret_r.
      unfold setLet.
      inline_first.
      comp_skip.
      simpl in H5.
      assert (a2 = l).
      eapply list_pred_eq_impl_eq.
      trivial.
      subst.

      remember (@split
         (list
            (prod (Bvector (plus (posnatToNat lambda) (posnatToNat lambda)))
               (Bvector (posnatToNat lambda)))) (list nat)
         (@app
            (prod
               (list
                  (prod
                     (Vector.t bool
                        (plus (posnatToNat lambda) (posnatToNat lambda)))
                     (Identifier (posnatToNat lambda)))) 
               (list nat)) b5
            (@cons
               (prod
                  (list
                     (prod
                        (Vector.t bool
                           (plus (posnatToNat lambda) (posnatToNat lambda)))
                        (Identifier (posnatToNat lambda)))) 
                  (list nat))
               (@pair
                  (list
                     (prod
                        (Vector.t bool
                           (plus (posnatToNat lambda) (posnatToNat lambda)))
                        (Identifier (posnatToNat lambda)))) 
                  (list nat) l b7) b6))) as z.
      destruct z.
      inline_first.
      comp_skip.
      inline_first.
      comp_skip.
      eapply comp_spec_eq_trans_l.
      eapply comp_spec_eq_symm.
      eapply comp_spec_right_ident.
      comp_skip.
      comp_simp.
      eapply comp_spec_eq_refl.
    Qed.

    rewrite hybrid_enc_equiv0 .
    rewrite hybrid_enc_equiv1 .

      inline_first.
      

      Set Printing All.
      Show.
      remember (split (b5 ++ (l, b7) :: b6)) as z.
      destruct z.
      
      comp_simp.
      inline_first
      inline_first; comp_skip; comp_simp.
      
      
      SearchAbout oc_compMap.
      
      inline_first.
      

    Qed

    .

    Qed.

    unfold Initialize_wLoop_7, Initialize_wLoop_8.
    comp_simp.
    

    eapply RndPerm_wf.

    eapply (@list_hybrid_close _ _ _ _ _ (G7_2_A2 (a1, b2, b1, b0, b)) (G7_2_A3 (a1, b2, b1, b0, b)) _ _ _ _ (G7_2_A3 (a1, b2, b1, b0, b))).
    eapply max_keywords_G7_2_A1.

    intuition.

    unfold LH_Gn.
    eapply evalDist_bind_distance.
    admit.
    intuition.
    intuition.
    comp_simp.

    destruct (ge_dec n (length a)).
    eapply evalDist_bind_distance; intuition.
    admit.

    repeat rewrite firstn_ge_all.
    intuition.
    omega.
    omega.
    repeat rewrite skipn_length_nil.
    eapply leRat_trans.
    eapply eqRat_impl_leRat.
    rewrite <- ratIdentityIndiscernables.
    intuition.
    eapply rat0_le_all.
    omega.
    omega.

    assert ( 
        evalDist 
          (lsb1 <-$ (foreach  (x in firstn n a)G7_3_A2 (a1, b2, b1, b0, b) x);
           lsb2 <-$ (foreach  (x in skipn (S n) a)G7_2_A2 (a1, b2, b1, b0, b) x);
           x <- nth n a nil;
           y <-$ G7_2_A2  (a1, b2, b1, b0, b) x;
           G7_2_A3 (a1, b2, b1, b0, b) (lsb1 ++ (y :: lsb2))
                 ) a0 == 
        evalDist 
          (lsb1 <-$ (foreach  (x in firstn n a)G7_3_A2 (a1, b2, b1, b0, b) x);
           lsb2 <-$ (foreach  (x in skipn n a)G7_2_A2 (a1, b2, b1, b0, b) x);
           G7_2_A3 (a1, b2, b1, b0, b) (lsb1 ++ lsb2)
                 ) a0
          ).

    comp_skip.
    destruct a.
    simpl in *.
    omega.
    Local Opaque evalDist.
    simpl.

    hwew

    SearchAbout firstn.
    comp_skip.

  Qed.

    [db, q, s_A] <-$3 A1;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_8 db k_I k_Z) (toW db);
    
    k_X <-$ {0,1}^lambda;
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts);
    A2 s_A edb (snd (split searchRes)).


  Definition Initialize_wLoop_6_1 db k_E k_I k_Z w :=
    inds <- lookupInds db w;
    sigma <-$ RndPerm (length inds);
    indLoopRes <-$ compMap _ (Initialize_indLoop_4 k_I k_Z k_E w) (combine (permute (oneVector lambda) inds sigma) (allNatsLt (length inds)));
    ret (indLoopRes, sigma).

  Definition Initialize_6_1 (db : DB)(q : list Query) :=
    
    k_X <--$$ {0,1}^lambda;
    k_I <--$$ {0,1}^lambda;
    k_Z <--$$ {0,1}^lambda;
    wLoopRes <--$ oc_compMap _ (fun w => k_E <--$ query w; $ Initialize_wLoop_6_1 db k_E k_I k_Z w) (toW db);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <--$2$ TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <--$$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts);
    $ ret (edb, searchRes).

  Definition G6_1_A :=
    [db, q, s_A] <--$3$ A1;
    z0 <--$ Initialize_5 db q; 
    [edb, ls]<-2 z0; 
    $ A2 s_A edb (snd (split ls)).




  Definition G6_1 :=
    [b, _] <-$2 G5_A _ _ (fun (s : unit)(x : Blist) => r <-$ {0, 1}^lambda; ret (r, s)) tt;
    ret b.

  Theorem G6_1_equiv :
    Pr[G6] == Pr[G6_1].


    unfold G6, G6_1, G5_A.

    eapply comp_spec_eq_impl_eq.
    do 4 (simpl; inline_first; comp_skip; comp_simp).
    simpl.
    inline_first.
    comp_skip.

    Theorem oc_compMap_equiv_inv : 
      

    SearchAbout oc_compMap.


    Theorem Init_5_o_equiv : 
      forall a b0,
        comp_spec (fun a b => fst a = fst b)
                  ((Initialize_5 a b0) _ _  (randomFunc ({ 0 , 1 }^lambda) (list_EqDec bool_EqDec)) nil)
                  ((Initialize_5 a b0) _ _ (fun (s : unit) (_ : Blist) => r <-$ { 0 , 1 }^lambda; ret (r, s)) tt).

      intuition.
      simpl; inline_first; comp_skip.
      inline_first

    Qed.


    simpl.

  Qed.


  Definition Initialize_wLoop_6_1 db k_I k_Z w :=
    inds <- lookupInds db w;
    sigma <--$$ RndPerm (length inds);
    k_E <--$$ ({0, 1}^lambda);
    indLoopRes <--$$ compMap _ (Initialize_indLoop_4 k_I k_Z k_E w) (combine (permute (oneVector lambda) inds sigma) (allNatsLt (length inds)));
    OC_Ret Blist (Bvector lambda) (ret (indLoopRes, sigma)).

  Definition Initialize_6_1 (db : DB)(q : list Query) :=
    
    k_X <--$$ {0,1}^lambda;
    k_I <--$$ {0,1}^lambda;
    k_Z <--$$ {0,1}^lambda;
    wLoopRes <--$ oc_compMap _ (Initialize_wLoop_6_1 db k_I k_Z) (toW db);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <--$2$ TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <--$$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts);
    $ ret (edb, searchRes).

  Definition G6_1_A :=
    [db, q, s_A] <--$3$ A1;
    z0 <--$ Initialize_6_1 db q; 
    [edb, ls]<-2 z0; 
    $ A2 s_A edb (snd (split ls)).
  
   Definition G6_1 :=
    [b, _] <-$2 G6_1_A _ _ (@randomFunc Blist (Bvector lambda) (Rnd lambda) _) nil;
    ret b.

  Theorem G6_1_equiv : 
    Pr[G6] == Pr[G6_1].

    unfold G6, G6_1, G5_A, G6_1_A, Initialize_5, Initialize_6_1.
    eapply comp_spec_eq_impl_eq.
    simpl; inline_first; comp_skip; comp_simp.

  Qed.

   

  Theorem G4_equiv :
    Pr[G3] == Pr[G4].


    eapply eq_impl_list_pred.
    rewrite H8.

    rewrite H8.

    des

    eapply list_
    SearchAbout length split.

*)

    (*
    assert (
        list_pred
     (fun a3 b2 : option (Vector.t bool lambda) =>
      match a3 with
      | Some x3 => match b2 with
                   | Some y => True
                   | None => False
                   end
      | None => match b2 with
                | Some _ => False
                | None => True
                end
      end)
     (ServerSearch_2 (XSetSetup_2 x0 x1 d l3)
        (map
           (fun c : nat => groupExp g (mult (F_P x0 k0) (F_P x2 (app k c))))
           (allNatsLt (length (fst (split l0))))) (fst (split l0)))
     (map
        (fun x3 : option (prod (Vector.t bool lambda) (Bvector lambda)) =>
         match x3 with
         | Some v => Some (fst v)
         | None => None
         end)
        (ServerSearch_4 (XSetSetup_2 x0 x1 d l3)
           (map
              (fun c : nat =>
               groupExp g (mult (F_P x0 k0) (F_P x2 (app k c))))
              (allNatsLt (length l0))) l0))
     ).
*)

    Unset Printing Notations.
    Show.

    f_equal.
    eapply map_ext_pred.
    eapply list_pred_getSomes.

    SearchAbout length split.
    f_equal.
    f_equal.
    

    Focus 2.
    assert (l2 = (fst (split b0))).
    rewrite <- Heqz0.
    trivial.
    subst.
    
    
    
    case_eq (arrayLookup (list_EqDec bool_EqDec) (combine (toW d) l2) b1); intuition.
    


    SearchAbout arrayLookupList.

    eapply list_pred_impl.
    eapply list_pred_eq.
    
    rewrite H7.
    comp_skip.
    inline_first.
  
    comp_skip.

    comp_skip.
    
    assert 

  Qed.




  Theorem G4_equiv : 
    Pr[G3] == Pr[G4].
    
    unfold G3, G4, G_gen, Initialize_3, Initialize_4.
    do 6 (comp_skip; comp_simp).

    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply compMap_spec.
    eapply list_pred_eq.
    intuition; subst.

    Theorem init_intLoop_4_spec : 
      forall x1 x2 y b0 z x,
      comp_spec (fun a b => fst b = a) 
                (Initialize_indLoop_2 x1 x2 y b0 (z, x))
                (Initialize_indLoop_4 x1 x2 y b0 (z, x)).

      intuition.
      unfold Initialize_indLoop_2, Initialize_indLoop_4.
      comp_skip; try
      eapply (oneVector (lambda + lambda)).

      eapply comp_spec_ret; intuition.
      
    Qed.
    
    Theorem init_wLoop_4_spec : 
      forall d x x1 x2 b0,
        comp_spec (fun a b => snd a = snd b /\ fst a = fst (split (fst b)))
                   (Initialize_wLoop_2 d x x1 x2 b0)
                   (Initialize_wLoop_4 d x x1 x2 b0).

      unfold Initialize_wLoop_2, Initialize_wLoop_4.
      intuition.
      comp_simp.
      comp_skip.
      comp_skip.
      eapply compMap_spec.
      eapply list_pred_eq.
      intuition; subst.
      eapply init_intLoop_4_spec.
      eapply comp_spec_ret; intuition.
      simpl.
      split_eq.
      eapply list_pred_impl.
      eauto.
      intuition.

    Qed.

    eapply init_wLoop_4_spec.

    remember (split a1) as z.
    destruct z.
    remember (split b0) as z.
    destruct z.
    remember ( split (foreach  (ls in l2)split ls)) as z.
    destruct z.
    comp_skip.
    eapply comp_spec_eq_refl_gen.
    f_equal.
    f_equal.
    assert (l0 = fst (split a1)).
    rewrite <- Heqz.
    trivial.
    subst.
    assert (l4 = fst (split (foreach  (ls in (fst (split b0)))split ls))).
    rewrite <- Heqz0.
    simpl.
    rewrite <- Heqz1.
    trivial.
    subst.
    split_eq.
    eapply list_pred_map_r'.
    split_eq.
    eapply list_pred_impl.
    eapply H6.
    intuition.
    
    subst.
    assert (l1 = l3).
    assert (l1 = snd (split a1)).
    rewrite <- Heqz.
    trivial.
    subst.
    assert (l3 = snd (split b0)).
    rewrite <- Heqz0.
    trivial.
    subst.
    split_eq.
    eapply list_pred_impl; eauto.
    intuition.
    subst.

    comp_skip.
    
    eapply (@compMap_spec _ _ _ _ _ _ eq (fun a b => fst a = fst b /\ snd a = fst (split (snd b)))).
    eapply list_pred_eq.
    intuition.
    subst.
    comp_skip.
    eapply comp_base_exists; eauto.
    eapply comp_base_exists; eauto.
    eapply comp_spec_ret; intuition.
    simpl.

    assert (list_pred (fun a b => a = fst (split b)) l0 l2).
    assert (l0 = fst (split a1)).
    rewrite <- Heqz.
    trivial.
    subst.
    assert (l2 = fst (split b0)).
    rewrite <- Heqz0.
    trivial.
    subst.
    split_eq.
    eapply list_pred_impl.
    eapply H6.
    intuition.

    unfold arrayLookupList.

    case_eq ( @arrayLookup Keyword
         (list
            (Vector.t bool (plus (posnatToNat lambda) (posnatToNat lambda))))
         (@list_EqDec bool bool_EqDec)
         (@combine Keyword
            (list
               (Vector.t bool
                  (plus (posnatToNat lambda) (posnatToNat lambda)))) 
            (toW d) l0) b2); intuition.


    Theorem arrayLookup_Some_list_pred : 
      forall (A B C : Set){eqda : EqDec A}(P : B -> C -> Prop)(lsa : list A) lsb lsc a b,
        list_pred P lsb lsc ->
        arrayLookup _ (combine lsa lsb) a = Some b->
        (exists c,
          arrayLookup _ (combine lsa lsc) a = Some c /\
          P b c).

      induction lsa; intuition; simpl in *.
      discriminate.
      destruct lsb.
      inversion H; clear H; subst.
      simpl in *.
      discriminate.
      
      inversion H; clear H; subst.
      simpl in *.
      case_eq (eqb a0 a); intuition.
      rewrite eqb_leibniz in H.
      subst.
      rewrite eqb_refl in *.
      inversion H0; clear H0; subst.
      econstructor; eauto.
      
      rewrite H in H0.
      eapply IHlsa; eauto.

    Qed.

    Theorem arrayLookup_None_combine : 
      forall (A B C : Set){eqd : EqDec A}(lsa : list A)(lsb : list B)(lsc : list C) a,
        arrayLookup _ (combine lsa lsb) a = None ->
        length lsb = length lsc ->
        arrayLookup _ (combine lsa lsc) a = None.

      induction lsa; intuition; simpl in *.
      destruct lsc; simpl in *.
      trivial.
      destruct lsb; simpl in *.
      omega.
      destruct ( eqb a0 a).
      discriminate.
      eauto.

    Qed.

    
    specialize (arrayLookup_Some_list_pred _ _ H14 H15); intuition.
    destruct H16.
    intuition.
    rewrite H17.
    trivial.
    erewrite arrayLookup_None_combine.
    trivial.
    eauto.
    assert (l0 = fst (split a1)).
    rewrite <- Heqz.
    trivial.
    subst.
    assert (l2 = fst (split b0)).
    rewrite <- Heqz0.
    trivial.
    subst.
    repeat rewrite split_length_l.
    eapply list_pred_length_eq; eauto.
    
    eapply comp_spec_ret; intuition.
    f_equal.

 
    eapply (@compMap_support _ _ 
                             (fun a b => 
                                map (fun v => Dec (F x a) (fst (splitVector lambda lambda v))) (fst (split (fst b))) = 
                                (snd (split (fst b)))
           )) in H5.

    Focus 2.
    intuition.
    unfold Initialize_wLoop_4 in H14.
    repeat simp_in_support.

    eapply (@compMap_support _ _
                             (fun a b => Dec (F x a4) (fst (splitVector lambda lambda (fst b))) = snd b)) in H16. 

    simpl.
    
    split_eq.
    eapply list_pred_map_l'.
    split_eq.

   

    eapply list_pred_impl_1_r.
    eapply H16.
    intuition.
    intuition.
    unfold Initialize_indLoop_4 in *.
    repeat simp_in_support.
    simpl.

   

    rewrite splitVector_append .
    simpl.
    eapply Enc_correct.
    trivial.

    assert (list_pred
         (fun (a : Keyword)
            (b : list (Vector.t bool (lambda + lambda) * Bvector lambda)) =>
          (foreach  (v in fst (split b))
           Dec (F x a) (fst (splitVector lambda lambda v))) =
          snd (split b)) (toW d) l2).

    assert (l2 = (fst (split b0))).
    rewrite <- Heqz0.
    trivial.
    subst.
    split_eq.
    eauto.

    eapply (@compMap_support _ _ (fun a b => snd b = arrayLookupList _ (combine (toW d) l2) a)) in H11.
    Focus 2.
    intuition.
    repeat simp_in_support.
    simpl.
    trivial.

    assert (list_pred 
              (fun a b => fst a = fst b /\
              fst (snd a) = fst (snd b) /\
            snd (snd a) = fst (split (snd (snd b))) /\ 
            snd (split (snd (snd b))) =
             map (fun v => Dec (F x (fst (fst a))) (fst (splitVector lambda lambda v))) (snd (snd a)))
              (combine l a2)
              (combine l b2)
           ).

    admit.

    eapply map_ext_pred.
    eauto.
    intuition.
    simpl in *.
    subst.
    unfold GenTrans_4.
    destruct b3.
    simpl.
    destruct p0.
    simpl in *.
    comp_simp.
    f_equal.
    eapply map_ext_pred.
    


    eapply list_pred_impl.
    eapply (@list_pred_combine_l _ _ _ (fun a b => a = fst b /\
                                       (fun (a : Keyword)
             (b : Tag *
                  list (Vector.t bool (lambda + lambda) * Identifier lambda)) =>
           snd b =
           arrayLookupList (list_EqDec bool_EqDec) (combine (toW d) l2) a) (fst a) (snd b)
                                         )
  (fun a b => (fun (a : Tag * list (Vector.t bool (lambda + lambda)))
             (b : Tag *
                  list (Vector.t bool (lambda + lambda) * Identifier lambda)) =>
           fst a = fst b /\ snd a = fst (split (snd b))) a (snd b))).
    eapply list_pred_symm.
    eapply (@list_pred_impl).
    eapply (@list_pred_combine_l _ _ _ eq (fun b a => snd b =
           arrayLookupList (list_EqDec bool_EqDec) (combine (toW d) l2) (fst a))).
    eapply list_pred_eq.
    eapply list_pred_symm.



    eapply (@list_pred_impl).
    eapply list_pred_fst_split_irr_if.
    eapply H11.
    intuition.
    intuition.

    admit.

    intuition.
    simpl in *.
    subst.
    destruct b3.
    simpl in *.
    subst.
    destruct p1. simpl in *. subst.
    

    eapply list_pred_I.
    

    simpl in *.
    eapply H14.

    intros.
    eapply H14.

    eapply list_pred_symm.
    eapply list_pred_impl.
    eapply list_pred_combine_l.
    eapply list_pred_I.
    admit.
    eapply list_pred_symm.
    eapply H12.
    intuition.
    simpl in *.
    subst.
    eapply H17.
    simpl in *.
    intuition.
    simpl in *; subst.
    simpl.

  
    

    SearchAbout list_pred split.

    T

    SearchAbout list_pred combine.
    

    admit.
    
    eapply map_ext_pred.
    eauto.
    intuition.
    simpl in *.
    subst.
    unfold GenTrans_3, GenTrans_4.
    destruct b3.
    simpl.
    destruct p0.
    comp_simp.
    f_equal.
    


    simpl in 

    eapply list_pred_combine_simple.
    eapply list_pred_eq.
    eapply H12.
    apply compMap_length in H10.
    rewrite H10.
    symmetry.
    eapply split_length_l.
    
    intuition.
    simpl in *.
    subst.
    unfold GenTrans_4.
    destruct b3.
    simpl.
    destruct p0.
    comp_simp.
    simpl.
    f_equal.
    eapply map_ext_pred.
    
    SearchAbout length split.

    unfold setLet.
    inline_first.
    comp_simp.

    remember (foreach  (ls in l2)split ls) as z.
    destruct z.
    
    remember (split ls) as z.

  Qed.


  Definition GenTrans_4 (edb : EDB) k_X k_Z  e : (list (Identifier lambda) * SearchTranscript) :=
    [q, stag_t_inds] <-2 e;
    [stag, t, inds] <-3 stag_t_inds;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    e <- F_P k_X x;
    xtokens <- map (fun (c : nat) => g^(e * (F_P k_Z (s ++ c)))) (allNatsLt (length t));
    res <- ServerSearch_2 xSet xtokens t;
    es <- getSomes res;
    (inds, (stag, (combine xtokens res))).

  Definition Initialize_4 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    stags_ts_inds <-$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x), lookupInds db x)) (fst (split q));
    searchRes <- map (GenTrans_4 edb k_X k_Z) (combine q stags_ts_inds);
    ret (edb, searchRes).

  Definition G4 := G_gen Initialize_4.

  Theorem G4_equiv : 
    Pr[G3] == Pr[G4].

    unfold G3, G4, G_gen, Initialize_3, Initialize_4.
    do 8 (comp_skip; comp_simp).
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply (@compMap_spec _ _ _ _ _ _ eq (fun a b => fst a = fst (fst b) /\ snd a = snd (fst b))).
    eapply list_pred_eq.
    intuition; subst.
    comp_skip.
    eapply comp_base_exists; eauto.
    eapply comp_base_exists; eauto.
    eapply comp_spec_ret; intuition.
    eapply comp_spec_ret; intuition.
    f_equal.
    eapply map_ext_pred.
    eapply list_pred_combine_simple.
    eapply list_pred_eq.
    eauto.
    eapply compMap_length in H7.
    rewrite H7.
    symmetry.
    eapply split_length_l.
    
    intuition.
    simpl in *.
    subst.
    unfold GenTrans_4.
    destruct b1.
    simpl.
    comp_simp.
    simpl.
    f_equal.
    

  Qed.

  (* Step 3: For the X, I, and Z PRFs, translate the game so that it interacts with the PRF as an oracle, then replace the PRF with a random function.  We only need to replace these three PRFs in order to get to the next step where we remove the decryption. *)

  
  (* Step 2.1 : It's a little easier if we turn some map operations into compMaps. SO we do that first. *)
  Definition XSetSetup_indLoop_2_1 k_X k_I w (ind : Bvector lambda) :=
    e <- F_P k_X w;
    xind <- F_P k_I (Vector.to_list ind);
    ret (g^(e * xind)).

  Definition XSetSetup_wLoop_2_1 k_X k_I db e :=
    [w, sigma] <-2 e;
    compMap _ (XSetSetup_indLoop_2_1 k_X k_I w) (permute (oneVector lambda) (lookupInds db w) sigma).
    
  Definition XSetSetup_2_1 k_X k_I db sigmas :=
    mapRes <-$ compMap _ (XSetSetup_wLoop_2_1 k_X k_I db) (combine (toW db) sigmas);
    ret flatten mapRes.

  Definition GenTrans_2_1 (edb : EDB) k_X k_Z k_S (e : Query * Tag) :=
    [q, stag] <-2 e;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    t <- TSetRetrieve tSet stag;
    e <- F_P k_X x;
    xtokens <-$ compMap _ (fun (c : nat) => ret g^(e * (F_P k_Z (s ++ c)))) (allNatsLt (length t));
    res <- ServerSearch_2 xSet xtokens t;
    es <- getSomes res;
    k_E <- F k_S s;
    inds <- map (Dec k_E) es;
    ret (inds, (stag, (combine xtokens res))).
  
  Definition Initialize_2_1 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet <-$ XSetSetup_2_1 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    stags <-$ compMap _ (TSetGetTag k_T) (fst (split q));
    searchRes <-$ compMap _ (GenTrans_2_1 edb k_X k_Z k_S) (combine q stags);
    ret (edb, searchRes).

  
  Theorem G2_1_equiv : 
    Pr[G2] == Pr[G_gen Initialize_2_1].

    unfold G2, G_gen, Initialize_2, Initialize_2_1.
    
    do 7 (comp_skip; comp_simp).
    comp_irr_r.
    
    Theorem compMap_wf : 
      forall (A B : Set)(eqdb : EqDec B)(ls : list A)(c : A -> Comp B),
        (forall a, In a ls -> well_formed_comp (c a)) ->
        well_formed_comp (compMap _ c ls).

      induction ls; intuition; simpl in *; wftac.
     
    Qed.

    Hint Resolve compMap_wf : wftac.

    unfold XSetSetup_2_1; wftac.
    eapply compMap_wf; intuition.
    unfold XSetSetup_wLoop_2_1.
    wftac.
    eapply compMap_wf.
    intuition.
    unfold XSetSetup_indLoop_2_1.
    wftac.

    comp_skip.
    comp_simp.
    comp_skip.
    
    comp_irr_r.
    eapply compMap_wf.
    intuition.
    unfold GenTrans_2_1.
    wftac.
    eapply compMap_wf.
    intuition.
    wftac.

    eapply evalDist_ret_eq.

    assert ( XSetSetup_2 x0 x1 d l1 = x4).

    unfold XSetSetup_2_1 in *.
    repeat simp_in_support.
    unfold XSetSetup_2.
    f_equal.
    
    eapply (@compMap_support _ _ (fun (a : Blist * (list nat)) b => b = XSetSetup_wLoop_2 x0 x1 d a)) in H9.
    eapply list_pred_eq_impl_eq.
    eapply list_pred_map_l'.
    eapply list_pred_impl.
    eapply H9.
    intuition.
    intuition.
    unfold XSetSetup_wLoop_2_1 in *.
    eapply (@compMap_support _ _ (fun a b => b = XSetSetup_indLoop_2 x0 x1 a2 a)) in H10.
    unfold XSetSetup_wLoop_2.
    eapply list_pred_eq_impl_eq.
    eapply list_pred_map_r'.
    eapply list_pred_symm.
    trivial.
    intuition.
    unfold XSetSetup_indLoop_2_1, XSetSetup_indLoop_2 in *.
    repeat simp_in_support.
    trivial.

    subst.
    f_equal.    

    apply (@compMap_support _ _ (fun a b => b = GenTrans_2 (t, XSetSetup_2 x0 x1 d l1) x0 x2 x a)) in H8.
    eapply list_pred_eq_impl_eq.
    eapply list_pred_map_l'.
    eapply list_pred_impl.
    eapply H8.
    intuition.
    intuition.
    unfold GenTrans_2, GenTrans_2_1 in *.
    comp_simp.
    repeat simp_in_support.

    eapply (@compMap_support _ _ (fun (a : nat) b => b =  g ^ (F_P x0 k0 * F_P x2 (k ++ a)))) in H11.

    assert (x4 = map (fun (a : nat) => g ^ (F_P x0 k0 * F_P x2 (k ++ a))) (allNatsLt (length (TSetRetrieve t b0)))).
    eapply list_pred_eq_impl_eq.
    eapply list_pred_map_r'.
    eapply list_pred_symm.
    trivial.
    subst.
    
    trivial.

    intuition.
    repeat simp_in_support.
    trivial.
   
  Qed.


  (* Step 2.2: We will need to modify the top-level game to apply the PRF definition.  Start by putting everything in one function. *)
  Definition G2_2  :=
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet <-$ XSetSetup_2_1 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    stags <-$ compMap _ (TSetGetTag k_T) (fst (split q));
    searchRes <-$ compMap _ (GenTrans_2_1 edb k_X k_Z k_S) (combine q stags);
    A2 s_A edb (snd (split searchRes)).
 
  Theorem G2_2_equiv : 
    Pr[G_gen Initialize_2_1] == Pr[G2_2].

    unfold G_gen, Initialize_2_1, G2_2.
    do 10 (comp_skip; comp_simp; inline_first).
    reflexivity.
  Qed.

  (* Step 2.3: replace the "X" PRF first.   Start by sampling the key at the top of beginning of the game.*)

    Definition G2_3  :=
    k_X <-$ {0,1}^lambda;
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet <-$ XSetSetup_2_1 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    stags <-$ compMap _ (TSetGetTag k_T) (fst (split q));
    searchRes <-$ compMap _ (GenTrans_2_1 edb k_X k_Z k_S) (combine q stags);
    A2 s_A edb (snd (split searchRes)).

    Theorem G2_3_equiv : 
      Pr[G2_2] == Pr[G2_3].

      unfold G2_2, G2_3.
      do 2 (comp_swap_r; comp_skip; comp_simp).

    Qed.
 
    (* Step 2.4 : Put the game in the form of the PRF definition. *)
     Fixpoint oc_compMap(A B C D : Set)(eqdb : EqDec B)(c : A -> OracleComp C D B)(ls : list A) : OracleComp C D (list B) :=
    match ls with
      | nil => $ (ret nil)
      | a :: ls' =>
        b <--$ c a;
          lsb' <--$ oc_compMap _ c ls';
          $ (ret (b :: lsb'))
    end. 
   
  Notation "'query' v" := (OC_Query  _ v) (at level 79) : comp_scope. 

  Definition XSetSetup_indLoop_2_4 k_I (w : Blist) (ind : Bvector lambda) :=
    e <--$ query w;
    xind <- F_P k_I (Vector.to_list ind);
    $ ret (g^(e * xind)).

  Definition XSetSetup_wLoop_2_4 k_I db e :=
    [w, sigma] <-2 e;
    oc_compMap _ (XSetSetup_indLoop_2_4 k_I w) (permute (oneVector lambda) (lookupInds db w) sigma).
    
  Definition XSetSetup_2_4 k_I db sigmas :=
    mapRes <--$ oc_compMap _ (XSetSetup_wLoop_2_4 k_I db) (combine (toW db) sigmas);
    $ ret flatten mapRes.

  Definition GenTrans_2_4 (edb : EDB) k_Z k_S (e : Query * Tag) :=
    [q, stag] <-2 e;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    t <- TSetRetrieve tSet stag;
    e <--$ query x;
    xtokens <--$$ compMap _ (fun (c : nat) => ret g^(e * (F_P k_Z (s ++ c)))) (allNatsLt (length t));
    res <- ServerSearch_2 xSet xtokens t;
    es <- getSomes res;
    k_E <- F k_S s;
    inds <- map (Dec k_E) es;
    $ ret (inds, (stag, (combine xtokens res))).

  Definition PRF_A_1 := 
    [db, q, s_A] <--$3$ A1;
    k_S <--$$ {0,1}^lambda;
    k_I <--$$ {0,1}^lambda;
    k_Z <--$$ {0,1}^lambda;
    wLoopRes <--$$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet <--$ XSetSetup_2_4 k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <--$2$ TSetSetup t;
    edb <- (tSet, xSet);
    stags <--$$ compMap _ (TSetGetTag k_T) (fst (split q));
    searchRes <--$ oc_compMap _ (GenTrans_2_4 edb k_Z k_S) (combine q stags);
    $ A2 s_A edb (snd (split searchRes)).

  Definition G2_4  :=
    k_X <-$ {0,1}^lambda;
    [r, _] <-$2 (PRF_A_1 _ _ (f_oracle F_P _ k_X) tt);
      ret r.

   
  Theorem compMap_oc_spec : 
    forall (C D : Set)(P2 : C -> D -> Prop)(A B : Set)(P1 : A -> B -> Prop)(eqdc : EqDec C)(eqdd : EqDec D)(E F S: Set)(eqds : EqDec S)(ls1 : list A)(ls2 : list B)(c1 : A -> Comp C)(c2 : B -> OracleComp E F D)o (s : S),
      list_pred P1 ls1 ls2 ->
      (forall a b z, P1 a b -> comp_spec (fun x y => P2 x (fst y)) (c1 a) (c2 b _ _ o z)) -> 
      comp_spec (fun a b => list_pred P2 a (fst b))
                (compMap _ c1 ls1)
                ((oc_compMap _ c2 ls2) _ _ o s).
    
    induction ls1; inversion 1; subst; intuition; simpl in *.
    comp_simp.
    eapply comp_spec_ret; simpl; econstructor.
    
    simpl.
    comp_skip.
    comp_simp.
    comp_skip.
    comp_simp.
    eapply comp_spec_ret; intuition.
    simpl.
    econstructor; eauto.
    
  Qed.
  
  Theorem G2_4_equiv : 
    Pr[G2_3] == Pr[G2_4].

    unfold G2_3, G2_4, PRF_A_1.
    eapply comp_spec_eq_impl_eq.
    simpl.
    (simpl; inline_first; comp_skip; comp_simp).
    simpl; inline_first.
    comp_skip.
    comp_simp.

    do 3 (simpl; inline_first; comp_skip; comp_simp).
    
    unfold XSetSetup_2_1, XSetSetup_2_4.
    simpl; inline_first.
    comp_skip.
    comp_ret_r.
    inline_first.
    comp_simp.
    simpl.
    inline_first.
    comp_skip.
    eapply (@compMap_oc_spec _ _ eq).
    eapply list_pred_eq.
    intuition; subst.
    pairInv.
    unfold XSetSetup_wLoop_2_1, XSetSetup_wLoop_2_4.
    eapply comp_spec_consequence.
    eapply (@compMap_oc_spec _ _ eq).
    eapply list_pred_eq.
    intuition; subst.
    unfold XSetSetup_indLoop_2_1, XSetSetup_indLoop_2_4.
    simpl.
    unfold f_oracle.
    comp_simp.
    eapply comp_spec_ret; intuition.
    intuition.
    eapply list_pred_eq_impl_eq.
    trivial.

    comp_simp.
    inline_first.
    comp_ret_r.
    comp_ret_r.
    comp_simp.
    inline_first.
    comp_skip.
    comp_ret_r.
    comp_simp.
    simpl.
    inline_first.
    comp_skip.
    comp_ret_r.
    comp_simp.
    inline_first.
    comp_skip.
    eapply (@compMap_oc_spec _ _ eq).
    eapply list_pred_eq.
    intuition; subst.
    pairInv.
    unfold GenTrans_2_1, GenTrans_2_4.
    comp_simp.
    inline_first.
    comp_skip.
    comp_simp.
    eapply comp_spec_ret; intuition.
    simpl.
    repeat f_equal.
    eapply list_pred_eq_impl_eq; trivial.
    eapply list_pred_eq_impl_eq; trivial.

    comp_simp.
    inline_first.
    eapply comp_spec_eq_trans_l.
    eapply comp_spec_eq_symm.
    eapply comp_spec_right_ident.
    comp_skip.
    assert (a0 = l1).
    eapply list_pred_eq_impl_eq.
    trivial.
    subst.
    assert (a1 = l2).
    eapply list_pred_eq_impl_eq.
    trivial.
    subst.
    eapply comp_spec_eq_refl.
    subst.
    comp_simp.
    eapply comp_spec_eq_refl.

  Qed.

  (* Step 2.5: replace the PRF with a random function. *)
  
  Definition G2_5  :=
    [r, _] <-$2 (PRF_A_1 _ _ (@randomFunc Blist nat (RndG) _) nil);
      ret r.

  Theorem G2_5_equiv : 
    | Pr[G2_4] - Pr[G2_5] | == PRF_Advantage (Rnd lambda) (RndG) F_P _ _ PRF_A_1.

    reflexivity.

  Qed.


  (* Step 3: prepare to replace all PRFs with random functions. We use a composite oracle to manage the 4 PRFs. *)

  Notation "'query' v" := (OC_Query  _ v) (at level 79) : comp_scope. 
              
  Instance sum_EqDec : 
    forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B),
      EqDec (A + B).

    intuition.
    exists 
      (fun x y => 
         match x with
             | inl a => 
               match y with
                 | inl a' => eqb a a'
                 | inr _ => false
               end
             | inr b =>
               match y with
                 | inl _ => false
                 | inr b' => eqb b b'
               end
         end).

    intuition; try discriminate.
    f_equal.
    eapply eqb_leibniz.
    trivial.
    inversion H; clear H; subst.
    eapply eqb_leibniz.
    trivial.

    f_equal.
    eapply eqb_leibniz.
    trivial.
    inversion H; clear H; subst.
    eapply eqb_leibniz.
    trivial.
  Qed.

  Definition mkCompositeOracle
             {A1 A2 B1 B2 S1 S2 : Set}
             {eqdb1 : EqDec B1}{eqdb2 : EqDec B2}
             {eqds1 : EqDec S1}{eqds2 : EqDec S2}
             (o1 : S1 -> A1 -> Comp (B1 * S1))
             (o2 : S2 -> A2 -> Comp (B2 * S2))
             (s : S1 * S2)(z : A1 + A2) :=
      match z with
        | inl a => [b, s'] <-$2 o1 (fst s) a; ret (inl b, (s', snd s))
        | inr a => [b, s'] <-$2 o2 (snd s) a; ret (inr b, (fst s, s'))
      end.

  Definition toL(A B : Type)(def : A)(x : A + B) : A :=
    match x with
      | inl a => a
      | inr _ => def
    end.

  Definition toR(A B : Type)(def : B)(x : A + B) : B :=
    match x with
      | inl _ => def
      | inr b => b
    end.


    (*       
       /  \
     / \  / \
    S  X  I Z *)

  Definition D_O := (Blist + Blist + (Blist + Blist))%type.
  Definition R_O := (Bvector lambda + nat + (nat + nat))%type.

  Definition QS (x : Blist) := @inl (Blist + Blist) (Blist + Blist) (@inl Blist Blist x).
  Definition QX (x : Blist) := @inl (Blist + Blist) (Blist + Blist) (@inr Blist Blist x).
  Definition QI (x : Blist) := @inr (Blist + Blist) (Blist + Blist) (@inl Blist Blist x).
  Definition QZ (x : Blist) := @inr (Blist + Blist) (Blist + Blist) (@inr Blist Blist x).

  Definition toS(r : R_O) := 
    x <- toL (inl nat (oneVector lambda)) r;
    toL (oneVector lambda) x.

  Definition toX(r : R_O) := 
    x <- toL (inl nat (oneVector lambda)) r;
    toR O x.
  
  Definition toI(r : R_O) := 
    x <- toR (inl nat O) r;
    toL O x.
  
  Definition toZ(r : R_O) := 
    x <- toR (inl nat O) r;
    toR O x.

  Definition sQuery(x : Blist) :=
    qRes <--$ query (QS x);
    $ ret (toS qRes).

  Definition xQuery(x : Blist) :=
    qRes <--$ query (QX x);
    $ ret (toX qRes).

  Definition iQuery(x : Blist) :=
    qRes <--$ query (QI x);
    $ ret (toI qRes).

  Definition zQuery(x : Blist) :=
    qRes <--$ query (QZ x);
    $ ret (toZ qRes).


  Fixpoint oc_compMap(A B C D : Set)(eqdb : EqDec B)(c : A -> OracleComp C D B)(ls : list A) : OracleComp C D (list B) :=
    match ls with
      | nil => $ (ret nil)
      | a :: ls' =>
        b <--$ c a;
          lsb' <--$ oc_compMap _ c ls';
          $ (ret (b :: lsb'))
    end.      

    Definition Initialize_indLoop_3 k_E w (e : Identifier lambda * nat) :=
    [ind, c] <-2 e;
    e <--$$ Enc k_E ind;
    xind <--$ iQuery (Vector.to_list ind);
    z <--$ zQuery (w ++ c);
    y <- xind * (inverse z);
    $ ret (Vector.append e (natToBvector y)).

  Definition Initialize_wLoop_3 db w :=
    inds <- lookupInds db w;
    sigma <--$$ RndPerm (length inds);
    k_E <--$ sQuery w;
    indLoopRes <--$ oc_compMap _ (Initialize_indLoop_3 k_E w) (combine (permute (oneVector lambda) inds sigma) (allNatsLt (length inds)));
    $ ret (indLoopRes, sigma).

  Definition XSetSetup_indLoop_3 w (ind : Bvector lambda) :=
    e <--$ xQuery w;
    xind <--$ iQuery (Vector.to_list ind);
    $ ret g^(e * xind).

  Definition XSetSetup_wLoop_3 db e :=
    [w, sigma] <-2 e;
    oc_compMap _ (XSetSetup_indLoop_3 w) (permute (oneVector lambda) (lookupInds db w) sigma).
    
  Definition XSetSetup_3 db sigmas :=
    loopRes <--$ oc_compMap _ (XSetSetup_wLoop_3 db) (combine (toW db) sigmas);
    $ ret flatten loopRes.


  Definition ServerSearch_3 := ServerSearch_2.

  Definition GenTrans_3 (edb : EDB) (e : Query * Tag) :=
    [q, stag] <-2 e;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    t <- TSetRetrieve tSet stag;
    e <--$ xQuery x;
    xtokens <--$ oc_compMap _ (fun (c : nat) => exp <--$ zQuery (s ++ c); $ ret g^(e * exp)) (allNatsLt (length t));
    res <- ServerSearch_2 xSet xtokens t;
    es <- getSomes res;
    k_E <--$ sQuery s;
    inds <- map (Dec k_E) es;
    $ ret (inds, (stag, (combine xtokens res))).

    Definition Initialize_3_oc (db : DB)(q : list Query) :=
    wLoopRes <--$ oc_compMap _ (Initialize_wLoop_3 db) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet <--$ XSetSetup_3 db sigmas;
    t <- combine (toW db) t_entries;
    tSetRes <--$$ TSetSetup t;
    [tSet, k_T] <-2 tSetRes;
    edb <- (tSet, xSet);
    stags <--$$ compMap _ (TSetGetTag k_T) (fst (split q));
    searchRes <--$ oc_compMap _ (GenTrans_3 edb) (combine q stags);
    $ ret (edb, searchRes).

  Definition Initialize_3 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    let o1 := mkCompositeOracle (f_oracle F _ k_S) (f_oracle F_P _ k_X) in
    let o2 := mkCompositeOracle (f_oracle F_P _ k_I) (f_oracle F_P _ k_Z) in
    let o := mkCompositeOracle o1 o2 in
    [r, _] <-$2 (Initialize_3_oc db q) _ _ o (tt, tt, (tt, tt)); 
      ret r.

  Definition G3 := G_gen Initialize_3.


  (* Step 2.1 : It's a little easier if we turn some map operations into compMaps. *)
  Definition XSetSetup_indLoop_2_1 k_X k_I w (ind : Bvector lambda) :=
    e <- F_P k_X w;
    xind <- F_P k_I (Vector.to_list ind);
    ret (g^(e * xind)).

  Definition XSetSetup_wLoop_2_1 k_X k_I db e :=
    [w, sigma] <-2 e;
    compMap _ (XSetSetup_indLoop_2_1 k_X k_I w) (permute (oneVector lambda) (lookupInds db w) sigma).
    
  Definition XSetSetup_2_1 k_X k_I db sigmas :=
    mapRes <-$ compMap _ (XSetSetup_wLoop_2_1 k_X k_I db) (combine (toW db) sigmas);
    ret flatten mapRes.

  Definition GenTrans_2_1 (edb : EDB) k_X k_Z k_S (e : Query * Tag) :=
    [q, stag] <-2 e;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    t <- TSetRetrieve tSet stag;
    e <- F_P k_X x;
    xtokens <-$ compMap _ (fun (c : nat) => ret g^(e * (F_P k_Z (s ++ c)))) (allNatsLt (length t));
    res <- ServerSearch_2 xSet xtokens t;
    es <- getSomes res;
    k_E <- F k_S s;
    inds <- map (Dec k_E) es;
    ret (inds, (stag, (combine xtokens res))).
  
  Definition Initialize_2_1 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet <-$ XSetSetup_2_1 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    stags <-$ compMap _ (TSetGetTag k_T) (fst (split q));
    searchRes <-$ compMap _ (GenTrans_2_1 edb k_X k_Z k_S) (combine q stags);
    ret (edb, searchRes).

  Theorem G2_1_equiv : 
    Pr[G2] == Pr[G_gen Initialize_2_1].

    unfold G2, G_gen, Initialize_2, Initialize_2_1.
    
    do 7 (comp_skip; comp_simp).
    comp_irr_r.
    
    Theorem compMap_wf : 
      forall (A B : Set)(eqdb : EqDec B)(ls : list A)(c : A -> Comp B),
        (forall a, In a ls -> well_formed_comp (c a)) ->
        well_formed_comp (compMap _ c ls).

      induction ls; intuition; simpl in *; wftac.
     
    Qed.

    Hint Resolve compMap_wf : wftac.

    unfold XSetSetup_2_1; wftac.
    eapply compMap_wf; intuition.
    unfold XSetSetup_wLoop_2_1.
    wftac.
    eapply compMap_wf.
    intuition.
    unfold XSetSetup_indLoop_2_1.
    wftac.

    comp_skip.
    comp_simp.
    comp_skip.
    
    comp_irr_r.
    eapply compMap_wf.
    intuition.
    unfold GenTrans_2_1.
    wftac.
    eapply compMap_wf.
    intuition.
    wftac.

    eapply evalDist_ret_eq.

    assert ( XSetSetup_2 x0 x1 d l1 = x4).

    unfold XSetSetup_2_1 in *.
    repeat simp_in_support.
    unfold XSetSetup_2.
    f_equal.
    
    eapply (@compMap_support _ _ (fun (a : Blist * (list nat)) b => b = XSetSetup_wLoop_2 x0 x1 d a)) in H9.
    eapply list_pred_eq_impl_eq.
    eapply list_pred_map_l'.
    eapply list_pred_impl.
    eapply H9.
    intuition.
    intuition.
    unfold XSetSetup_wLoop_2_1 in *.
    eapply (@compMap_support _ _ (fun a b => b = XSetSetup_indLoop_2 x0 x1 a2 a)) in H10.
    unfold XSetSetup_wLoop_2.
    eapply list_pred_eq_impl_eq.
    eapply list_pred_map_r'.
    eapply list_pred_symm.
    trivial.
    intuition.
    unfold XSetSetup_indLoop_2_1, XSetSetup_indLoop_2 in *.
    repeat simp_in_support.
    trivial.

    subst.
    f_equal.    

    apply (@compMap_support _ _ (fun a b => b = GenTrans_2 (t, XSetSetup_2 x0 x1 d l1) x0 x2 x a)) in H8.
    eapply list_pred_eq_impl_eq.
    eapply list_pred_map_l'.
    eapply list_pred_impl.
    eapply H8.
    intuition.
    intuition.
    unfold GenTrans_2, GenTrans_2_1 in *.
    comp_simp.
    repeat simp_in_support.

    eapply (@compMap_support _ _ (fun (a : nat) b => b =  g ^ (F_P x0 k0 * F_P x2 (k ++ a)))) in H11.

    assert (x4 = map (fun (a : nat) => g ^ (F_P x0 k0 * F_P x2 (k ++ a))) (allNatsLt (length (TSetRetrieve t b0)))).
    eapply list_pred_eq_impl_eq.
    eapply list_pred_map_r'.
    eapply list_pred_symm.
    trivial.
    subst.
    
    trivial.

    intuition.
    repeat simp_in_support.
    trivial.
   
  Qed.

  Theorem G3_equiv : 
    Pr[G_gen Initialize_2_1] == Pr[G3].

    unfold G3, G_gen, Initialize_2_1, Initialize_3, Initialize_3_oc.
    
    do 6 (comp_skip; comp_simp).

    eapply comp_spec_eq_impl_eq.
    simpl.
    inline_first.

    eapply (@comp_spec_seq _ _ (fun a b => a = fst b)); eauto with inhabited.
    
    Theorem compMap_oc_spec : 
      forall (C D : Set)(P2 : C -> D -> Prop)(A B : Set)(P1 : A -> B -> Prop)(eqdc : EqDec C)(eqdd : EqDec D)(E F S: Set)(eqds : EqDec S)(ls1 : list A)(ls2 : list B)(c1 : A -> Comp C)(c2 : B -> OracleComp E F D)o (s : S),
        list_pred P1 ls1 ls2 ->
        (forall a b z, P1 a b -> comp_spec (fun x y => P2 x (fst y)) (c1 a) (c2 b _ _ o z)) -> 
        comp_spec (fun a b => list_pred P2 a (fst b))
                  (compMap _ c1 ls1)
                  ((oc_compMap _ c2 ls2) _ _ o s).
      
      induction ls1; inversion 1; subst; intuition; simpl in *.
      comp_simp.
      eapply comp_spec_ret; simpl; econstructor.

      simpl.
      comp_skip.
      comp_simp.
      comp_skip.
      comp_simp.
      eapply comp_spec_ret; intuition.
      simpl.
      econstructor; eauto.

    Qed.

    eapply (comp_spec_consequence (fun a b => a = fst b)).
    eapply (@compMap_oc_spec _ _ eq).
    eapply list_pred_eq.
    intuition; subst.
    unfold Initialize_wLoop_2, Initialize_wLoop_3.
    simpl.
    comp_simp.
    inline_first.
    comp_skip.
    
    (* comp_simp gets a little slow here *)
    comp_ret_r.
    inline_first.
    unfold f_oracle.
    comp_ret_r.
    comp_simp.
    unfold toS.
    inline_first.
    unfold toL.
    comp_ret_r.
    comp_ret_r.
    simpl.
    
    comp_skip.
    eapply (@compMap_oc_spec _ _ eq).
    eapply list_pred_eq.
    intuition; subst.
    pairInv.
    unfold Initialize_indLoop_2, Initialize_indLoop_3.
    simpl.
    inline_first.
    comp_skip; try eapply (oneVector (lambda + lambda)).

    repeat (try comp_ret_r; inline_first).
    eapply comp_spec_ret.
    simpl.
    unfold toI.
    comp_simp.
    unfold toZ, toL, toR.
    comp_simp.
    trivial.

    comp_simp.
    eapply comp_spec_ret; intuition.
    simpl in *.
    f_equal.
    eapply list_pred_eq_impl_eq.
    trivial.

    intuition.
    eapply list_pred_eq_impl_eq; trivial.
    
    intuition.
    subst.
    destruct b0.
    simpl.
    comp_simp.
    simpl.
    unfold XSetSetup_2_1.
    inline_first.

    comp_skip.
    eapply (@compMap_oc_spec _ _ eq).
    eapply list_pred_eq.
    intuition; subst.
    pairInv.
    unfold XSetSetup_wLoop_2_1, XSetSetup_wLoop_3.
    eapply comp_spec_consequence.
    eapply (@compMap_oc_spec _ _ eq).
    eapply list_pred_eq.
    intuition; subst.
    unfold XSetSetup_indLoop_2_1, XSetSetup_indLoop_3.
    simpl.
    unfold f_oracle.
    inline_first.
    repeat  (comp_ret_r; inline_first).
    simpl.
    unfold toX, toI.
    comp_simp.
    unfold toR, toL.
    eapply comp_spec_ret; intuition.

    intuition.
    eapply list_pred_eq_impl_eq.
    trivial.

    comp_simp.
    inline_first.
    repeat comp_ret_r.
    comp_simp.
    inline_first.
    comp_skip.
    comp_ret_r.
    comp_simp.
    simpl.
    inline_first.
    comp_skip.
    comp_ret_r.
    comp_simp.
    inline_first.
    comp_skip.
    eapply (@compMap_oc_spec _ _ eq).
    eapply list_pred_eq.
    intuition; subst.
    pairInv.
    
    unfold GenTrans_2_1, GenTrans_3.
    inline_first.
    destruct a2.
    simpl.
    inline_first.
    unfold f_oracle.
    repeat (comp_ret_r;  inline_first).
    comp_skip.
    eapply (@compMap_oc_spec _ _ eq).
    eapply list_pred_eq.
    intuition; subst.
    simpl.
    inline_first.
    repeat (comp_ret_r; inline_first).
    unfold toX, toZ.
    comp_simp.
    unfold toR, toL.
    eapply comp_spec_ret; intuition.

    destruct b2.
    inline_first.
    repeat (comp_ret_r; inline_first).
    eapply comp_spec_ret; intuition.
    simpl in *.
    f_equal.
    f_equal.
    f_equal.
    f_equal.
    f_equal.
    eapply list_pred_eq_impl_eq.
    trivial.
    eapply list_pred_eq_impl_eq.
    trivial.
    
    f_equal.
    f_equal.
    eapply list_pred_eq_impl_eq.
    trivial.
    f_equal.
    f_equal.
    eapply list_pred_eq_impl_eq.
    trivial.
    eapply list_pred_eq_impl_eq.
    trivial.

    destruct b2.
    inline_first.
    repeat comp_ret_r.
    eapply comp_spec_ret; intuition.
    f_equal.
    f_equal.
    f_equal.
    eapply list_pred_eq_impl_eq.
    trivial.
    eapply list_pred_eq_impl_eq.
    trivial.
  Qed.

  Check F_P.



  (* Step 4: Replace PRFs with random functions. *)
  Definition Initialize_4 (db : DB)(q : list Query) :=

    let o1 := mkCompositeOracle 
                (@randomFunc Keyword (Bvector lambda) (Rnd lambda) _ ) 
                (@randomFunc Blist nat (RndNat lambda) _) in
    let o2 := mkCompositeOracle 
                (@randomFunc Blist nat (RndNat lambda) _)
                (@randomFunc Blist nat (RndNat lambda) _) in
    let o := mkCompositeOracle o1 o2 in
    [r, _] <-$2 (Initialize_3_oc db q) _ _ o (nil, nil, (nil, nil)); 
      ret r.

  Definition G4 := G_gen Initialize_4.
    
  Print OracleComp.
  
  Definition AWO_OracleClose_r (A B C D E : Set){eqda : EqDec A}{eqdb : EqDec B}{eqdc : EqDec C}{eqdd : EqDec D}
             (c : OracleComp (A + B) (C + D) E)
             (S : Set)(eqds : EqDec S)(o : S -> B -> Comp (D * S))(s : S) : OracleComp A C (E * S) :=
    OC_Run _ _ _ c 
           (fun s p => 
              match p with
                  | inl a => (z <--$ query a; $ ret (inl z, s))
                  | inr b => [d, s'] <--$2 $ o s b; $ ret (inr d, s')
              end) s.

  
  (* Replace one oracle at a time, in the order the keys are selected *)
  (* Step 3.1: We need to modify the top-level game to unify with the PRF definition.  Start by putting everything in one function. *)

  Definition G3_1 :=
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    let o1 := mkCompositeOracle (f_oracle F _ k_S) (f_oracle F_P _ k_X) in
    let o2 := mkCompositeOracle (f_oracle F_P _ k_I) (f_oracle F_P _ k_Z) in
    let o := mkCompositeOracle o1 o2 in
    [r, _] <-$2 (Initialize_3_oc db q) _ _ o (tt, tt, (tt, tt)); 
    [edb, ls] <-2 r;
    A2 s_A edb (snd (split ls)).
    

  Definition Initialize_3_1 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    let p := (
          
          )in
    [r, _] <-$2 p _ _ (f_oracle F _ k_S) tt;
      ret r.

    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    let o1 := mkCompositeOracle (f_oracle F _ k_S) (f_oracle F_P _ k_X) in
    let o2 := mkCompositeOracle (f_oracle F_P _ k_I) (f_oracle F_P _ k_Z) in
    let p := AWO_OracleClose_r  (Initialize_3_oc db q) _ o2 (tt, tt) in
    [r, _] <-$2 p _ _ o1 (tt, tt); 
      ret (fst r).

  Definition Initialize_3_2 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    let o2 := mkCompositeOracle (f_oracle F_P _ k_I) (f_oracle F_P _ k_Z) in
    
    let p := AWO_OracleClose_r  (Initialize_3_oc db q) _ o2 (tt, tt) in
    let p := AWO_OracleClose_r  p _ (f_oracle F_P _ k_X) tt in
    [r, _] <-$2 p _ _ (f_oracle F _ k_S) tt;
      ret (fst (fst r)).

  Theorem G_3_1_equiv : 
    Pr[G3] == Pr[G_gen Initialize_3_1].
    
    unfold G3, G_gen, Initialize_3, Initialize_3_1.
    do 6 (comp_skip; comp_simp).
    
    eapply comp_spec_eq_impl_eq.
    eapply (@comp_spec_seq _ _ (fun a b => fst a = fst (fst b)));
      eauto with inhabited.

    Theorem AWO_OracleClose_r_composite_equiv : 
      forall (A B C D E S1 S2: Set){eqda : EqDec A}{eqdb : EqDec B}{eqdc : EqDec C}{eqdd : EqDec D}{eqde : EqDec E}{eqds1 : EqDec S1}{eqds2 : EqDec S2}(c : OracleComp (A + B) (C + D) E)
             (o1 : S1 -> B -> Comp (D * S1))(o2 : S2 -> A -> Comp (C * S2))
             (s1 : S1) (s2 : S2),
      comp_spec (fun p1 p2 => (fst (fst p1) = fst p2 /\ 
                              snd (fst p1) = snd (snd p2) /\
                              snd p1 = fst (snd p2)))
                ((AWO_OracleClose_r c _ o1 s1) _ _ o2 s2) 
                (c _ _ (mkCompositeOracle o2 o1) (s2, s1)).

      intuition.
      unfold AWO_OracleClose_r, mkCompositeOracle.
      simpl.
      eapply comp_spec_eq_trans_r.
      Focus 2.
      eapply comp_spec_right_ident.
      comp_skip.
      eapply oc_base_exists; eauto; intuition;
      eapply comp_base_exists in X1;
      intuition.
      eapply oc_base_exists; eauto; intuition;
      eapply comp_base_exists in X1;
      intuition.

      eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun p1 p2 => (snd p1, fst p1) = p2)).
      trivial.
      intros.
      subst.
      simpl.
      intuition.
      simpl.
      inline_first.
      comp_skip.
      apply comp_base_exists in X1; intuition.
      apply comp_base_exists in X1; intuition.
      inline_first.
      simpl.
      eapply comp_spec_ret; intuition.

      simpl.
      inline_first.
      comp_skip.
      apply comp_base_exists in X1; intuition.
      apply comp_base_exists in X1; intuition.
      simpl.
      inline_first; comp_simp.
      eapply comp_spec_ret; intuition.

      eapply comp_spec_ret;  simpl in *; intuition.
      subst.
      destruct b; simpl in *; intuition.
      destruct p0; simpl in *; intuition.
      pairInv; intuition.

      subst.
      destruct b; simpl in *.
      destruct p0; simpl in *.
      pairInv; intuition.
      
    Qed.
    
  
    eapply comp_spec_symm.
    eapply comp_spec_consequence.
    eapply AWO_OracleClose_r_composite_equiv.
    intuition.
    intuition.
    simpl in *.
    comp_simp.
    simpl in *.
    eapply comp_spec_ret; intuition.
  Qed.

  Theorem G_3_2_equiv : 
     Pr[G_gen Initialize_3_1] == Pr[G_gen Initialize_3_2].

    unfold G_gen, Initialize_3_1, Initialize_3_2.
    do 6 (comp_skip; comp_simp).
    
    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply comp_spec_symm.
    eapply AWO_OracleClose_r_composite_equiv.
    simpl in H6.
    intuition.
    subst.
    comp_simp.
    simpl in H7.
    eapply comp_spec_ret; intuition.
    destruct p0; simpl; simpl in H7.
    destruct p0; simpl; simpl in H7.
    pairInv.
    trivial.

  Qed.


  (*Step 3.3: move things around and get the game to match the PRF definition. *)
  Definition Initialize_3_3 (db : DB)(q : list Query) :=
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    let o2 := mkCompositeOracle (f_oracle F_P _ k_I) (f_oracle F_P _ k_Z) in
    let p := AWO_OracleClose_r  (Initialize_3_oc db q) _ o2 (tt, tt) in
    let p := AWO_OracleClose_r  p _ (f_oracle F_P _ k_X) tt in
    r <-$
      (k_S <-$ {0,1}^lambda;
       ([r, _] <-$2 p _ _ (f_oracle F _ k_S) tt;
        ret r)); 
      ret (fst (fst r)).

  
  Theorem G_3_3_equiv : 
     Pr[G_gen Initialize_3_2] == Pr[G_gen Initialize_3_3].

    unfold G_gen, Initialize_3_2, Initialize_3_3.
    do 3 (comp_skip; comp_simp; inline_first; comp_at comp_inline leftc 1%nat; comp_swap_l).
    comp_skip.
    inline_first.
    comp_skip.
    comp_inline_l.
    comp_inline_r.
    comp_skip.
    comp_simp.
    intuition.
  Qed.

  (* Step 3.4 apply the PRF definition *)
  Definition Initialize_3_4 (db : DB)(q : list Query) :=
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    let o2 := mkCompositeOracle (f_oracle F_P _ k_I) (f_oracle F_P _ k_Z) in
    
    let p := AWO_OracleClose_r  (Initialize_3_oc db q) _ o2 (tt, tt) in
    let p := AWO_OracleClose_r  p _ (f_oracle F_P _ k_X) tt in
    r <-$
       ([r, _] <-$2 p _ _ (@randomFunc Blist (Bvector lambda) (Rnd lambda) _) nil;
        ret r);
      ret (fst (fst r)).

  Theorem G3_4_equiv : 
    | Pr[G_gen Initialize_3_3] - Pr[G_gen Initialize_3_4] | == PRF_Advantange.
  Qed.

  Theorem G3_3_equiv : 
     Pr[G_gen Initialize_3_2] == Pr[G_gen Initialize_3_3].

    unfold G_gen, Initialize_3_2, Initialize_3_3.
    (comp_skip; comp_simp; inline_first).
    comp_skip.

  Qed.



  Definition Initialize_3_2 (db : DB)(q : list Query) :=
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    let o2 := mkCompositeOracle (f_oracle F_P _ k_I) (f_oracle F_P _ k_Z) in
    
    let p := AWO_OracleClose_r  (Initialize_3_oc db q) _ o2 (tt, tt) in
    let p := AWO_OracleClose_r  p _ (f_oracle F_P _ k_X) tt in
    [r, _] <-$2 p _ _ (@randomFunc Keyword (Bvector lambda) (Rnd lambda) _ ) nil;
      ret (fst (fst r)).

   

    unfold toZ.
    unfold toR.
    
    comp_ret_r.
    comp_simp.

    Definition Initialize_3 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;

    let s_oracle := f_oracle F _ k_S in
    let x_oracle := f_oracle F_P _ k_X in
    let i_oracle := f_oracle F _ k_I in
    let z_oracle := f_oracle F _ k_Z in

    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    stags <-$ compMap _ (TSetGetTag k_T) (fst (split q));
    searchRes <- map (GenTrans_2 edb k_X k_Z k_S) (combine q stags);
    ret (edb, searchRes).

  Definition G3 := G_gen Initialize_3.
  

  We made it to G2!  continue here
     Next step: replace all PRFs with random functions

   (* Step 1.7: Simplify*)

  Definition Initialize_1_7 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet_raw <- map (XSetSetup_wLoop_2 k_X k_I db) (combine (toW db) sigmas);
    t <- combine (toW db) t_entries;
    xSet <- flatten xSet_raw;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    key <- (k_S, k_X, k_I, k_Z, k_T);
    stags <-$ compMap _ (TSetGetTag k_T) q
    searchRes <-$ map (GenTrans_2 edb k_X k_Z k_S) ls));
    ret (edb, searchRes).

  Definition Initialize_2 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    stags <-$ compMap _ (TSetGetTag k_T) (fst (split q));
    searchRes <- map (GenTrans_2 edb k_X k_Z k_S) (combine q stags);
    ret (edb, searchRes).



    subst.
    

    eapply list_pred_impl.
    eapply (@list_pred_combine_l _ _ _ (fun a b => a = fst b)).
    eapply list_pred_symm.
    eapply list_pred_impl.
    eapply list_pred_combine_l.
    eapply list_pred_eq.
    eapply list_pred_I.
    admit.
    intuition.
    eapply list_pred_symm.
    eapply list_pred_impl.
    eapply list_pred_combine_l.
    do 2 (split_subst; split_eq).
    eapply list_pred_impl.
    eapply H4.
    intuition.
    

    comp_skip.
    

    eapply Init_wLoop_1_4_spec.
    remember (split a1) as z.
    destruct z.
    remember (split b0) as z.
    destruct z.
    assert (l0 = l2).
    split_subst.
    symmetry.
    split_subst.
    symmetry.
    split_eq.
    trivial.

    subst.
    comp_skip.
    comp_skip.
    eapply compMap_spec.
    eapply list_pred_eq.
    intuition; subst.
    
    eapply comp_spec_eq_refl_gen.
    f_equal.
    f_equal.
    f_equal.


    
    assert (l1 = map (fun p => permute (oneVector lambda) (lookupInds d (fst p)) (snd p)) (combine (toW d) l3)).
    split_subst.
    split_eq.
    


   

    eapply (@map_ext_pred _ _ _ (fun a b => fst a = fst b /\ snd a = permute (oneVector lambda) (lookupInds d (fst a)) (snd b))).
    
    admit.
    intuition.
    simpl in*; subst.
    unfold XSetSetup_wLoop_1_4.
    comp_simp.
    simpl.
    intuition.

    eapply comp_spec_ret; intuition.
    
    f_equal.
    f_equal.
    

    eapply compMap_eq.

    eapply list_pred_eq_impl_eq.
    eapply list_pred_map_both'.

    unfold XSetSetup_wLoop_1_3.

    assert (list_pred 
              (fun (a : Blist * list (Bvector lambda)) (b : Blist * list nat) =>
                 (fst a = fst b) /\ snd a = (permute 

    eapply list_pred_impl.
    eapply list_pred_combine_l.
    eapply list_pred_symm.
    eapply list_pred_impl.
    eapply list_pred_combine_l.
    eapply list_pred_eq.
    eapply list_pred_I.

    eapply list_pre
    eapply list_pred_combine_l.

    eapply map_ext.

  Qed.

  (* Now we change how we deal with permutations to get game 2 *)
  Theorem G2_equiv : 
    Pr[G_gen Initialize_1_3] == Pr[G2].

    unfold G2, G_gen, Initialize_1_3, Initialize_2.
    do 6 (comp_skip; comp_simp).

    eapply comp_spec_eq_impl_eq.
    comp_skip.
    eapply compMap_spec.
    eapply list_pred_eq.
    intuition; subst.
    
    Theorem Init_wLoop_2_spec : forall d x x1 x2 b0,
      comp_spec (fun a b => fst a = fst b)
                (Initialize_wLoop_1_3 d x x1 x2 b0)
                (Initialize_wLoop_2 d x x1 x2 b0).

      intuition.
      unfold Initialize_wLoop_1_3, Initialize_wLoop_2.
      comp_simp.
      comp_skip.
      comp_skip.
      eapply compMap_spec.

      rewrite permute_length_eq.
      apply RndPerm_In_support_length in H.
      rewrite H.
      eapply list_pred_eq.
      intuition; subst.
      (*TODO: remove one of these procedures *)
      eapply comp_spec_eq_refl.
      eapply comp_spec_ret; intuition.
      simpl.
      eapply list_pred_eq_impl_eq.
      trivial.

    Qed.

    eapply Init_wLoop_2_spec.
    
    remember (split a1) as z.
    destruct z.
    remember (split b0) as z.
    destruct z.
    assert (l0 = l2).
    split_subst.
    symmetry.
    split_subst.
    symmetry.
    split_eq.
    trivial.
    subst.
    comp_skip.
    eapply

    intuition.
  Qed.

  (* Step 1.4: Change the setup routine so it returns the permutations rather than the indices *)
  Definition Initialize_wLoop_1_4 db k_S k_I k_Z w :=
    k_E <- F k_S w;
    inds <- lookupInds db w;
    sigma <-$ RndPerm (length inds);
    inds <- permute (oneVector lambda) inds sigma; 
    indLoopRes <-$ compMap _ (Initialize_indLoop_1_1 k_I k_Z k_E w) (combine inds (allNatsLt (length inds)));
    ret (indLoopRes, sigma).

  Definition XSetSetup_wLoop_1_4 k_X k_I e :=
    [w, sigma] <-2 e;
    map (XSetSetup_indLoop_1_1 k_X k_I w) (permute _ inds sigma).

  Definition Initialize_1_4 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_1_4 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    xSet_raw <- map (XSetSetup_wLoop_1_3 k_X k_I) (combine (toW db) sigmas);
    t <- combine (toW db) t_entries;
    xSet <- flatten xSet_raw;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    key <- (k_S, k_X, k_I, k_Z, k_T);
    searchRes <-$ compMap _ (OXT_Search edb key) q;
    ret (edb, searchRes).


   (* Step 1.1: have the init routine return the permutations used *)
   Definition Initialize_wLoop_1_1 db k_S k_I k_Z k_X w :=
    k_E <- F k_S w;
    inds <- lookupInds db w;
    sigma <-$ RndPerm (length inds);
    inds <- permute (oneVector lambda) inds sigma;
    indLoopRes <-$ compMap _ (OXT_EDBSetup_indLoop k_I k_Z k_E k_X w) (combine inds (allNatsLt (length inds)));
    ret (split indLoopRes, sigma).

  Definition Initialize_1_1 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_1_1 db k_S k_I k_Z k_X) (toW db);
    [wEntries, perms] <-2 split wLoopRes;
    [t_entries, xSet_raw] <-2 split wEntries;
    t <- combine (toW db) t_entries;
    xSet <- flatten xSet_raw;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    key <- (k_S, k_X, k_I, k_Z, k_T);
    searchRes <-$ compMap _ (OXT_Search edb key) q;
    ret (edb, searchRes).

  


  Theorem G1_1_equiv : 
    Pr[G_gen Initialize_1] == Pr[G_gen Initialize_1_1].

    unfold G_gen, Initialize_1, Initialize_1_1.
    do 6 (comp_skip; comp_simp).
    eapply comp_spec_eq_impl_eq.
    eapply comp_spec_seq; eauto with inhabited.

    eapply compMap_spec.
    eapply list_pred_eq.
    intuition; subst.
       
    Theorem Init_wLoop_1_1_spec : 
    forall d x x1 x2 x0 b0,
      comp_spec 
        (fun x y => 
           x = fst y) 
        (OXT_EDBSetup_wLoop d x x1 x2 x0 b0)
        (Initialize_wLoop_1_1 d x x1 x2 x0 b0).

      intuition.
      unfold OXT_EDBSetup_wLoop.
      unfold Initialize_wLoop_1_1.
      comp_simp.
      unfold shuffle.
      inline_first; comp_skip.
      comp_skip.
      eapply comp_spec_ret; intuition.
     
    Qed.

    eapply Init_wLoop_1_1_spec.
    intuition.
    remember (split b0) as z.
    destruct z.

    assert (fst (split b0) = a1).
    eapply fst_split_eq_list_pred.
    eapply list_pred_symm.
    eapply list_pred_impl.
    eauto.
    intuition.
    rewrite <- Heqz in H7.
    simpl in H7.
    subst.
    comp_simp.
    eapply comp_spec_eq_refl.
  Qed.
 
  (* Step 1.2: Split off the XSet computation *)
   Definition Initialize_wLoop_1_2 db k_S k_I k_Z k_X w :=
    k_E <- F k_S w;
    inds <- lookupInds db w;
    sigma <-$ RndPerm (length inds);
    inds <- permute (oneVector lambda) inds sigma;
    indLoopRes <-$ compMap _ (OXT_EDBSetup_indLoop k_I k_Z k_E k_X w) (combine inds (allNatsLt (length inds)));
    ret (split indLoopRes, sigma).

  Definition Initialize_1_2 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_1_2 db k_S k_I k_Z k_X) (toW db);
    [wEntries, perms] <-2 split wLoopRes;
    [t_entries, xSet_raw] <-2 split wEntries;
    t <- combine (toW db) t_entries;
    xSet <- flatten xSet_raw;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    key <- (k_S, k_X, k_I, k_Z, k_T);
    searchRes <-$ compMap _ (OXT_Search edb key) q;
    ret (edb, searchRes).


  Definition OXT_EDBSetup_indLoop_1_2 k_I k_Z k_E w (e : Identifier lambda * nat) :=
    [ind, c] <-2 e;
    xind <- F_P k_I (Vector.to_list ind);
    z <- F_P k_Z (w ++ c);
    y <- xind * (inverse z);
    e <-$ Enc k_E ind;
    ret (Vector.append e (natToBvector y)).

  Definition Initialize_wLoop_1_2 db k_S k_I k_Z w :=
    k_E <- F k_S w;
    inds <- lookupInds db w;
    sigma <-$ RndPerm (length inds);
    inds <- permute (oneVector lambda) inds sigma;
    indLoopRes <-$ compMap _ (OXT_EDBSetup_indLoop_1_2 k_I k_Z k_E w) (combine inds (allNatsLt (length inds)));
    ret (indLoopRes, sigma).

  Definition XSetSetup_indLoop_1_2 k_X k_I w (ind : Bvector lambda) :=
    e <- F_P k_X w;
    xind <- F_P k_I (Vector.to_list ind);
    g^(e * xind).
  
  Definition XSetSetup_wLoop_1_2 k_X k_I db e :=
    [w, sigma] <-2 e;
    map (XSetSetup_indLoop_1_2 k_X k_I w) (permute (oneVector lambda) (lookupInds db w) sigma).
    
  Definition XSetSetup_1_2 k_X k_I db perms :=
    flatten (map (XSetSetup_wLoop_1_2 k_X k_I db) (combine (toW db) perms)).

  Definition Initialize_1_2 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_1_2 db k_S k_I k_Z ) (toW db);
    [t_entries, perms] <-2 split wLoopRes;
    xSet <- XSetSetup_1_2 k_X k_I db perms;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    key <- (k_S, k_X, k_I, k_Z, k_T);
    searchRes <-$ compMap _ (OXT_Search edb key) q;
    ret (edb, searchRes).
  
  Theorem G1_2_equiv : 
    Pr[G_gen Initialize_1_1] == Pr[G_gen Initialize_1_2].

    unfold G_gen, Initialize_1_1, Initialize_1_2.
    do 6 (comp_skip; comp_simp).
    eapply comp_spec_eq_impl_eq.
    eapply comp_spec_seq; eauto with inhabited.
    eapply compMap_spec.
    eapply list_pred_eq.
    intuition; subst.
    
    Theorem Init_wLoop_1_2_spec : 
    forall d x x1 x2 x0 b0,
      comp_spec 
        (fun x y => 
           fst (fst x) = fst y /\ snd x = snd y) 
        (Initialize_wLoop_1_1 d x x1 x2 x0 b0) 
        (Initialize_wLoop_1_2 d x x1 x2 b0).

      intuition.
      unfold Initialize_wLoop_1_1.
      unfold Initialize_wLoop_1_2.
      comp_simp.
      comp_skip.
      eapply comp_spec_seq; eauto with inhabited.
      eapply compMap_spec.
      eapply list_pred_eq.
      intuition.
      subst.
      
      Theorem Init_indLoop_1_2_spec : 
        forall x1 x2 x3 x0 b0 e,
        comp_spec (fun p1 p2 => fst p1 = p2)
                  (OXT_EDBSetup_indLoop x1 x2 x3 x0 b0 e)
                  (OXT_EDBSetup_indLoop_1_2 x1 x2 x3 b0 e).

        intuition.
        unfold OXT_EDBSetup_indLoop, OXT_EDBSetup_indLoop_1_2.
        comp_simp.
        comp_skip; try eapply (oneVector (lambda + lambda)).
        eapply comp_spec_ret; intuition.

      Qed.

      eapply Init_indLoop_1_2_spec.
      intuition.
      eapply comp_spec_ret; intuition.
      simpl.
      eapply fst_split_eq_list_pred .
      eauto.

    Qed.

    eapply Init_wLoop_1_2_spec.
    intuition.
    
    remember (split a1) as z.
    destruct z.
    remember (split l0) as z.
    destruct z.
    remember (split b0) as z.
    destruct z.
    assert (fst (split (fst (split a1))) = fst (split b0)).
    
    eapply fst_split_eq_list_pred.

   Theorem list_pred_combine_l:
     forall (A B : Set) (lsa : list A) (lsb : list B) (P : A -> B -> Prop),
       list_pred P lsa lsb ->
       forall (C : Set) (lsc : list C) (P1 : A -> C -> Prop) (P2 : B -> C -> Prop),
         list_pred P1 lsa lsc ->
         list_pred P2 lsb lsc ->
         list_pred
           (fun (p : A * B) (c : C) =>
              P (fst p) (snd p) /\ P1 (fst p) c /\ P2 (snd p) c) 
           (combine lsa lsb) lsc.

     induction 1; intuition.
     inversion H; clear H; subst.
     simpl.
     econstructor.

     inversion H1; clear H1; subst.
     inversion H2; clear H2; subst.
     simpl.
     econstructor.
     intuition.
     eauto.

   Qed.

   Show.

   Theorem list_pred_fst_split_l : 
     forall (A B C : Set) P (ls1 : list (A * B))(ls2 : list C),
       list_pred (fun a b => P (fst a) b) ls1 ls2 ->
       list_pred P (fst (split ls1)) ls2.

     induction 1; intuition; simpl in *.
     econstructor.
     destruct a1.
     remember (split ls1) as z.
     destruct z.
     simpl in *.
     econstructor; eauto.
   Qed.

   eapply  list_pred_fst_split_l.

   eapply list_pred_symm.
   eapply  list_pred_fst_split_l.
   eapply list_pred_symm.
   eapply list_pred_impl.
   eauto.
   intuition.

   rewrite <- Heqz in H7.
   simpl in *.
   rewrite <- Heqz0 in H7.
   rewrite <- Heqz1 in H7.
   simpl in *.
   subst.
   
   comp_skip.
   assert (flatten l3 = XSetSetup_1_2 x0 x1 d l5).
   unfold XSetSetup_1_2.
   f_equal.
   eapply (@compMap_support _ _ (fun z1 z2 => in H4.

   eapply comp_spec_seq; eauto with inhabited.
   eapply compMap_spec.
   eapply list_pred_eq.
   intuition; subst.
   

    Theorem list_pred_fst_split_r : 
     forall (A B C : Set) P (ls1 : list (A * B))(ls2 : list C),
       list_pred (fun a b => P (fst a) b) ls1 ls2 ->
       list_pred P (fst (split ls1)) ls2.

     induction 1; intuition; simpl in *.
     econstructor.
     destruct a1.
     remember (split ls1) as z.
     destruct z.
     simpl in *.
     econstructor; eauto.
   Qed.

    SearchAbout list_pred zip.

  Qed.




  (* Step 1.1: switch to the G2 initialization loop and split the XSet setup and TSet setup routines *)
  Definition Initialize_1_1 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, perms] <-2 split wLoopRes;
    xSet <- XSetSetup_2 k_X k_I db perms;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    key <- (k_S, k_X, k_I, k_Z, k_T);
    searchRes <-$ compMap _ (OXT_Search edb key) q;
    ret (edb, searchRes).

  Theorem Init_indLoop_2_spec : 
    forall (x0 x1 x2 x a0 : Bvector lambda) b b1,
      comp_spec 
        (fun (x : Bvector (lambda + lambda) * nat) (y : Bvector (lambda + lambda)) => 
           fst x = y 
(* /\ snd x = g ^ (F_P x0 b * F_P x1 (Vector.to_list a0)) *) ) 
        (OXT_EDBSetup_indLoop x1 x2 (F x b) x0 b (a0, b1))
        (Initialize_indLoop_2 x1 x2 (F x b) b (a0, b1)).
    
    intuition.
    unfold OXT_EDBSetup_indLoop, Initialize_indLoop_2.
    comp_simp.
    comp_skip; try eapply (oneVector).
    eapply comp_spec_ret; intuition.

  Qed.
  
 

  Theorem Init_wLoop_2_spec : 
    forall d x x1 x2 b x0,
      comp_spec 
        (fun (x : list (Vector.t bool (lambda + lambda)) * list nat) y => 
           fst x = fst y) 
        (OXT_EDBSetup_wLoop d x x1 x2 x0 b)
        (Initialize_wLoop_2 d x x1 x2 b).
    
    intuition.
    unfold OXT_EDBSetup_wLoop, Initialize_wLoop_2.
    comp_simp.
    unfold shuffle.
    inline_first.
    comp_skip.
    rewrite permute_length_eq.
    
    eapply comp_spec_eq_trans_r.
    Focus 2.
    eapply comp_spec_right_ident.
    
    eapply comp_spec_seq; try eapply (nil, nil).
    rewrite (@RndPerm_In_support_length (length (lookupInds d b))); intuition.
   
    eapply (@compMap_spec _ _ _ _ _ _ _ (fun (x : Bvector (lambda + lambda) * nat) (y : Bvector (lambda + lambda)) => 
           fst x = y)).
    eapply list_pred_eq.
    intuition.
    subst.      
    eapply Init_indLoop_2_spec.
    
    intuition.
    eapply comp_spec_ret; intuition.
    
    eapply fst_split_eq_list_pred.
    trivial.
    
    Grab Existential Variables.
    apply nat.
    
  Qed.

  Theorem TSet_inhabited : TSet.

    assert (TSet * TSetKey).
    eapply comp_base_exists.
    eapply TSetSetup.
    eapply nil.
    intuition.
  Qed.

  Hint Resolve TSet_inhabited : inhabited.

  Require Import Permutation.

  Theorem G1_1_equiv : 
    Pr[G_gen Initialize_1] == Pr[G_gen Initialize_1_1].

    unfold G_gen, Initialize_1, Initialize_1_1.
    do 6 (comp_skip; comp_simp).
    eapply comp_spec_eq_impl_eq.
    eapply comp_spec_seq;
    eauto with inhabited.
    eapply compMap_spec.
    eapply list_pred_eq.
    intuition.
    subst.
    eapply Init_wLoop_2_spec.
    intuition.
    remember (split a1) as z.
    destruct z.

    assert (fst (split a1) = b0).
    eapply fst_split_eq_list_pred.
    eauto.
    rewrite <- Heqz in H7.
    simpl in H7.
    subst.

    comp_skip.

    eapply (@compMap_support _ _ (fun x y => Permutation (snd y) (XSetSetup_wLoop_2 x0 x1 d x))) in H4.

    assert (Permutation (flatten l1) (XSetSetup_2 x0 x1 d)).
    unfold XSetSetup_2.

    Theorem Permutation_flatten_list_pred :
      forall (A : Set)(ls1 ls2 : list (list A)),
        list_pred (fun a b => Permutation a b) ls1 ls2 ->
        Permutation (flatten ls1) (flatten ls2).

      induction 1; intuition; simpl in *.
      eapply Permutation_app'; eauto.
    Qed.

    eapply Permutation_flatten_list_pred.

   

    specialize (@list_pred_snd_split_irr _ (list (Bvector (lambda + lambda))) _ (fun x y => Permutation y (XSetSetup_wLoop_2 x0 x1 d x))); intuition.

    eapply list_pred_impl.
    eapply list_pred_map_r.
    eapply list_pred_symm.
    eapply H9.
    eapply H4.

    Theorem pair_snd_gen : 
      forall (A B : Type)(p : A * B) a b,
        (a, b) = p ->
        b = (snd p).

      intuition.
      pairInv.
      trivial.
      
    Qed.

    eapply pair_snd_gen.
    eauto.
    intuition.
    destruct H12.
    intuition.
    subst.
    trivial.

    

    SearchAbout snd.

    Check split.
    Theorem split_eq_gen : 
      forall (A B : Type)(l1 l2 : list (A * B)),
        l1 = l2 ->
        split l1 = split l2.

      intuition. subst. intuition.

    Qed.

    erewrite split_eq_gen.
    rewrite <- Heqz.

    remember ((@split
           (list (Bvector (plus (posnatToNat lambda) (posnatToNat lambda))))
           (list nat) a1)) as z.
    remember (split a1) as z.
    rewrite <- Heqz.
    

    SearchAbout Permutation flatten.

    f_equal.
    assert (l1 = snd (split a1)).
    rewrite <- Heqz.
    trivial.
    subst.
    
    
    eapply snd_split_eq_map_list_pred.
    eapply list_pred_symm.
    eauto.
    rewrite H9.
    clear H9.
    eapply comp_spec_eq_refl.
   
    intuition.
    
    unfold OXT_EDBSetup_wLoop in *.
    repeat simp_in_support.

    eapply (@compMap_support _ _ 
                             (fun (z1 : Identifier lambda * nat) (z2 : Bvector (lambda + lambda) * nat)
                              => snd z2 = g^((F_P x0 a2) * (F_P x1 (Vector.to_list (fst z1)))))) in H14.
                         
    eapply snd_split_eq_map_list_pred.
    eapply list_pred_symm.
    
    
    specialize (@compMap_support _ _ 
                                 (fun z y => @snd (Blist) nat y = 
                                             XSetSetup_indLoop_2 x0 x1 (fst z) x)
               _ 
               (fun z => OXT_EDBSetup_indLoop x1 x2 (F x a2) x0 a2 z)); intuition.
    
  Qed.

  (* Step 1.2 : factor out the tag calculation from the search loop *)
  Definition GenTrans_1_2 (edb : EDB) (k : Key) (e : Query * Tag) : (list (Identifier lambda) * SearchTranscript) :=
    [q, stag] <-2 e;
    t <- OXT_Search_ServerInit edb stag;
    xscript <- map (OXT_Search_Loop edb k q) (combine (allNatsLt (length t)) t);
    es <- getSomes (snd (split xscript));
    inds <- OXT_Search_ClientFinalize k q es;
    (inds, (stag, xscript)).

  Definition Initialize_1_2 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    t_entries <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    xSet <- XSetSetup_2 k_X k_I db;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    key <- (k_S, k_X, k_I, k_Z, k_T);
    stags <-$ compMap _ (TSetGetTag k_T) (fst (split q));
    searchRes <- map (GenTrans_1_2 edb key) (combine q stags);
    ret (edb, searchRes).

  Theorem G1_2_equiv : 
    Pr[G_gen Initialize_1_1] == Pr[G_gen Initialize_1_2].

  Admitted.

  (* simplify and re-order the transcript generation procedure to get to game 2*)
 
  Theorem G2_equiv : 
    Pr[G_gen Initialize_1_2] == Pr[G2].

  Admitted.


  (* Step 3: prepare to replace all the PRFs with random functions. *)
  (* We use a composite oracle to keep the complexity under control. *)
  
  Notation "'query' v" := (OC_Query  _ v) (at level 79) : comp_scope. 
              
  Instance sum_EqDec : 
    forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B),
      EqDec (A + B).

    intuition.
    exists 
      (fun x y => 
         match x with
             | inl a => 
               match y with
                 | inl a' => eqb a a'
                 | inr _ => false
               end
             | inr b =>
               match y with
                 | inl _ => false
                 | inr b' => eqb b b'
               end
         end).

    intuition; try discriminate.
    f_equal.
    eapply eqb_leibniz.
    trivial.
    inversion H; clear H; subst.
    eapply eqb_leibniz.
    trivial.

    f_equal.
    eapply eqb_leibniz.
    trivial.
    inversion H; clear H; subst.
    eapply eqb_leibniz.
    trivial.
  Qed.

  Definition mkCompositeOracle
             {A1 A2 B1 B2 S1 S2 : Set}
             {eqdb1 : EqDec B1}{eqdb2 : EqDec B2}
             {eqds1 : EqDec S1}{eqds2 : EqDec S2}
             (o1 : S1 -> A1 -> Comp (B1 * S1))
             (o2 : S2 -> A2 -> Comp (B2 * S2))
             (s : S1 * S2)(z : A1 + A2) :=
      match z with
        | inl a => [b, s'] <-$2 o1 (fst s) a; ret (inl b, (s', snd s))
        | inr a => [b, s'] <-$2 o2 (snd s) a; ret (inr b, (fst s, s'))
      end.

  Definition toL(A B : Type)(def : A)(x : A + B) : A :=
    match x with
      | inl a => a
      | inr _ => def
    end.

  Definition toR(A B : Type)(def : B)(x : A + B) : B :=
    match x with
      | inl _ => def
      | inr b => b
    end.

    (*       
       /  \
     / \  / \
    S  X  I Z *)

  Definition D_O := (Blist + Blist + (Blist + Blist))%type.
  Definition R_O := (Bvector lambda + nat + (nat + nat))%type.

  Definition QS (x : Blist) := @inl (Blist + Blist) (Blist + Blist) (@inl Blist Blist x).
  Definition QX (x : Blist) := @inl (Blist + Blist) (Blist + Blist) (@inr Blist Blist x).
  Definition QI (x : Blist) := @inr (Blist + Blist) (Blist + Blist) (@inl Blist Blist x).
  Definition QZ (x : Blist) := @inr (Blist + Blist) (Blist + Blist) (@inr Blist Blist x).

  Definition toS(r : R_O) := 
    x <- toL (inl nat (oneVector lambda)) r;
    toL (oneVector lambda) x.

  Definition toX(r : R_O) := 
    x <- toL (inl nat (oneVector lambda)) r;
    toR O x.
  
  Definition toI(r : R_O) := 
    x <- toR (inl nat O) r;
    toL O x.
  
  Definition toZ(r : R_O) := 
    x <- toR (inl nat O) r;
    toR O x.

  Definition sQuery(x : Blist) :=
    qRes <--$ query (QS x);
    $ ret (toS qRes).

  Definition xQuery(x : Blist) :=
    qRes <--$ query (QX x);
    $ ret (toX qRes).

  Definition iQuery(x : Blist) :=
    qRes <--$ query (QI x);
    $ ret (toI qRes).

  Definition zQuery(x : Blist) :=
    qRes <--$ query (QZ x);
    $ ret (toZ qRes).

  Definition Initialize_indLoop_3 k_E w (e : Identifier lambda * nat) : OracleComp D_O R_O (Bvector (lambda + lambda)) :=
    [ind, c] <-2 e;
    e <--$$ Enc k_E ind;
    xind <--$ xQuery (Vector.to_list ind);
    z <--$ zQuery (w ++ c);
    y <- xind * (inverse z);
    $ ret (Vector.append e (natToBvector y)).

  Fixpoint oc_compMap(A B C D : Set)(eqdb : EqDec B)(c : A -> OracleComp C D B)(ls : list A) : OracleComp C D (list B) :=
    match ls with
      | nil => $ (ret nil)
      | a :: ls' =>
        b <--$ c a;
          lsb' <--$ oc_compMap _ c ls';
          $ (ret (b :: lsb'))
    end.      

  Definition Initialize_wLoop_3 db w : OracleComp D_O R_O (list (Bvector (lambda + lambda))):=
    inds <- lookupInds db w;
    sigma <--$$ RndPerm (length inds);
    k_E <--$ sQuery w;
    oc_compMap _ (Initialize_indLoop_3 k_E w) (combine (permute (oneVector lambda) inds sigma) (allNatsLt (length inds))).

  Definition XSetSetup_indLoop_3 w (ind : Bvector lambda) :=
    e <--$ xQuery w;
    xind <--$ iQuery (Vector.to_list ind);
    $ ret (g^(e * xind)).

  Definition XSetSetup_wLoop_3 db w :=
    oc_compMap _ (XSetSetup_indLoop_3 w) (lookupInds db w).
    
  Definition XSetSetup_3 db :=
    ls <--$ oc_compMap _ (XSetSetup_wLoop_3 db) (toW db);
    $ ret removeDups _ (flatten ls).

  Definition GenTrans_3 (edb : EDB) (e : Query * Tag) :=
    [q, stag] <-2 e;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    t <- TSetRetrieve tSet stag;
    e <--$ xQuery x;
    xtokens <--$ oc_compMap _(fun (c : nat) => exp <--$ zQuery (s ++ c); $ ret g^(e * exp)) (allNatsLt (length t));
    res <- ServerSearch_2 xSet xtokens t;
    es <- getSomes res;
    k_E <--$ sQuery s;
    inds <- map (Dec k_E) es;
    $ ret (inds, (stag, (combine xtokens res))).

  Definition Initialize_3_oc (db : DB)(q : list Query) :=
    t_entries <--$ oc_compMap _ (Initialize_wLoop_3 db) (toW db);
    xSet <--$ XSetSetup_3 db;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <--$2$ TSetSetup t;
    edb <- (tSet, xSet);
    stags <--$$ compMap _ (TSetGetTag k_T) (fst (split q));
    searchRes <--$ oc_compMap _ (GenTrans_3 edb) (combine q stags);
    $ ret (edb, searchRes).

  Definition Initialize_3 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    let o1 := mkCompositeOracle (f_oracle F _ k_S) (f_oracle F_P _ k_X) in
    let o2 := mkCompositeOracle (f_oracle F_P _ k_I) (f_oracle F_P _ k_Z) in
    let o := mkCompositeOracle o1 o2 in
    [r, _] <-$2 (Initialize_3_oc db q) _ _ o (tt, tt, (tt, tt)); 
      ret r.

  Definition G3 := G_gen Initialize_3.

  Theorem G3_equiv : 
    Pr[G2] == Pr[G3].

  Admitted.

  Check F_P.
  
  (* Step 4: replace all PRFs with random functions. *)
   Definition Initialize_4 (db : DB)(q : list Query) :=
    let o1 := mkCompositeOracle (@randomFunc Keyword _ (Rnd lambda) _ ) (@randomFunc Blist _ (RndNat order) _) in
    let o2 := mkCompositeOracle (@randomFunc Blist _ (RndNat order) _) (@randomFunc Blist _ (RndNat order) _) in
    let o := mkCompositeOracle o1 o2 in
    [r, _] <-$2 (Initialize_3_oc db q) _ _ o (nil, nil, (nil, nil)); 
      ret r.

  Definition G4 := G_gen Initialize_4.

  Theorem G4_equiv : 
    Pr[G3] == Pr[G4].

  Admitted.

  (* Step 5: replace k_E with a randomly-selected value. *)
  Definition Initialize_wLoop_5 db w : OracleComp D_O R_O (list (Bvector (lambda + lambda))):=
    inds <- lookupInds db w;
    sigma <--$$ RndPerm (length inds);
    k_E <--$$ {0, 1}^lambda;
    oc_compMap _ (Initialize_indLoop_3 k_E w) (combine (permute (oneVector lambda) inds sigma) (allNatsLt (length inds))).
   Definition Initialize_5_oc (db : DB)(q : list Query) :=
    t_entries <--$ oc_compMap _ (Initialize_wLoop_5 db) (toW db);
    xSet <--$ XSetSetup_3 db;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <--$2$ TSetSetup t;
    edb <- (tSet, xSet);
    stags <--$$ compMap _ (TSetGetTag k_T) (fst (split q));
    searchRes <--$ oc_compMap _ (GenTrans_3 edb) (combine q stags);
    $ ret (edb, searchRes).

  Definition Initialize_5 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    let o1 := mkCompositeOracle (f_oracle F _ k_S) (f_oracle F_P _ k_X) in
    let o2 := mkCompositeOracle (f_oracle F_P _ k_I) (f_oracle F_P _ k_Z) in
    let o := mkCompositeOracle o1 o2 in
    [r, _] <-$2 (Initialize_5_oc db q) _ _ o (tt, tt, (tt, tt)); 
      ret r.

  Definition G5 := G_gen Initialize_5.
  
  Theorem G5_equiv : 
    Pr[G4] == Pr[G5].
    
  Admitted.


  (* Step 6: replace the answer computation with direct answer lookups. *)
  Definition GenTrans_6 (db : DB)(edb : EDB) (e : Query * Tag) :=
    [q, stag] <-2 e;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    t <- TSetRetrieve tSet stag;
    e <--$ xQuery x;
    xtokens <--$ oc_compMap _(fun (c : nat) => exp <--$ zQuery (s ++ c); $ ret g^(e * exp)) (allNatsLt (length t));
    res <- ServerSearch_2 xSet xtokens t;
    inds <- intersect (EqDec_dec _) (lookupInds db s) (lookupInds db x);
    $ ret (inds, (stag, (combine xtokens res))).

   Definition Initialize_6_oc (db : DB)(q : list Query) :=
     t_entries <--$ oc_compMap _ (Initialize_wLoop_5 db) (toW db);
     xSet <--$ XSetSetup_3 db;
     t <- combine (toW db) t_entries;
     [tSet, k_T] <--$2$ TSetSetup t;
     edb <- (tSet, xSet);
     stags <--$$ compMap _ (TSetGetTag k_T) (fst (split q));
     searchRes <--$ oc_compMap _ (GenTrans_6 db edb) (combine q stags);
     $ ret (edb, searchRes).

    Definition Initialize_6 (db : DB)(q : list Query) :=
    let o1 := mkCompositeOracle (@randomFunc Keyword _ (Rnd lambda) _ ) (@randomFunc Blist _ (RndNat order) _) in
    let o2 := mkCompositeOracle (@randomFunc Blist _ (RndNat order) _) (@randomFunc Blist _ (RndNat order) _) in
    let o := mkCompositeOracle o1 o2 in
    [r, _] <-$2 (Initialize_6_oc db q) _ _ o (nil, nil, (nil, nil)); 
      ret r.

    Definition G6 := G_gen Initialize_6.
    
    Theorem G6_close : 
      | Pr[G5] - Pr[G6] | <= 0.
      
      (* not really 0, but something small. *)
      (* These games are only different if we end up with collisions in some of the random functions or other issues (see below) *)

    Admitted.

    (* In the argument above, we mostly need to account for things that can go wrong, but we (may) also need to permute the initialization so the results come back in the correct order.  We can correct the order by choosing the identity permutation.     

Things that can go wrong:

1) TSet is incorrect
2) token collision: g ^ (F1(x) * F2(s ++ c)) for random functions F1 and F2.  We can show that this is a random function of (x, s, c), and therefore collisions are unlikely.  
3) XSet collision: there are two (keyword, index) pairs, (w1, i1) (w2, i2) for which g^(F1(w1) * F2(i1)) = g^(F1(w2) * F2(i2)).  Like before, use an argument that treats this whole thing as a random function
4) Decrypt function is incorrect (probability 0)
     *)
    
    (* G6 above is exacly G1 in the paper*)
    

    Definition whydoihavetodothingslikethistofixmyspacing := tt.

    (* Step 6: since


  (* Combine 2 (or more) oracles into a single "composite oracle".  We get back:
   1) The oracle itself
   2) A family of functions that injects arguments into the composite argument type.
   3) A function that takes a composite response and a composite argument and returns the desired response
   *)
  (* Inject argument into sum *)
  (* Give sum to composite oracle, get back product *)
  
  Inductive BinTreeStruct : Set :=
  | btsLeaf : BinTreeStruct
  | btsNode : BinTreeStruct -> BinTreeStruct -> BinTreeStruct.


  Inductive BinTree(A : Type) : BinTreeStruct -> Type :=
  | btLeaf : A -> BinTree A btsLeaf
  | btNode : 
      forall t1 t2,
        BinTree A t1 ->
        BinTree A t2 ->
        BinTree A (btsNode t1 t2).
  
  Fixpoint BinTree_interp(A : Type)(op : A -> A -> A)(b : BinTreeStruct)(t : BinTree A b) : A :=
    match t with
      | btLeaf a => a
      | btNode _ _ t1 t2 => op (BinTree_interp op t1) (BinTree_interp op t2)
    end.
  
  Definition BinTree_sum := BinTree_interp sum.
  Definition BinTree_prod := BinTree_interp prod.

  Inductive BinTreePath : BinTreeStruct -> Type :=
  | btpThis : BinTreePath btsLeaf
  | btpLeft: 
      forall t1 t2 (p : BinTreePath t1),
        BinTreePath (btsNode t1 t2)
  | btpRight: 
      forall t1 t2 (p : BinTreePath t2),
        BinTreePath (btsNode t1 t2).

  Definition binTreeLeft(bt :BinTreeStruct) : BinTreeStruct :=
    match bt with
      | btsLeaf => btsLeaf
      | btsNode t1 t2 => t1
    end.

  Definition binTreeRight(bt :BinTreeStruct) : BinTreeStruct :=
    match bt with
      | btsLeaf => btsLeaf
      | btsNode t1 t2 => t2
    end.

  Fixpoint treeEntry(T : BinTreeStruct)(A : Type)(X : BinTree A T) : forall (p : BinTreePath T), A :=
    match X with
      | btLeaf x => fun p => x 
      | btNode t1 t2 st1 st2 => fun p =>
        (match p in (BinTreePath T') return (
                (BinTreePath (binTreeLeft T') -> A) -> 
                (BinTreePath (binTreeRight T') -> A) -> 
                match T' return Type with
                    | btsLeaf => unit
                    | _ => A
                end
               ) with
          | btpThis => fun f1 f2 => tt
          | btpLeft t1' t2' p' => fun f1 f2 =>
            f1 p'
          | btpRight t1' t2' p' => fun f1 f2 =>
            f2 p' 
        end) (treeEntry st1) (treeEntry st2)                            
    end.

  (* Next: make a type for heteregeneous trees like in CPDT *)
          
  Fixpoint sumToTreePath(T : BinTree)(A : SetTree T) : forall (x : SetTree_sum A), BinTreePath T :=
    match A in (SetTree T') return (forall (x : SetTree_sum A), BinTreePath T') with
      | stLeaf _ => fun x => btpThis
      | stNode t1 t2 st1 st2 => 
        fun x =>
          match x with
            | inl x' => btpLeft t2 (sumToTreePath st1 x')
            | inr x' => btpRight t1 (sumToTreePath st2 x')
          end
    end.

  Fixpoint treePathToProdEntry(T : BinTree) : 
    forall (A : SetTree T)(p : BinTreePath T)(x : SetTree_prod A), treeEntryType A p :=
    match T with
      | btLeaf => 
        fun A => match A with
                   | 
      | _ => tt
    end.

  Fixpoint treePathToProdEntry(T : BinTree)(A : SetTree T) : 
    forall (p : BinTreePath T)(x : SetTree_prod A), treeEntryType A p :=
    match A in (SetTree T') return 
          (forall (p : BinTreePath T')(x : SetTree_prod A), treeEntryType A p) with
      | stLeaf _ => fun p x => x
      | stNode t1 t2 st1 st2 => 
        fun p x =>
          match p in (BinTreePath T') return
                ((forall (p': BinTreePath (binTreeLeft T')), (SetTree_prod st1) -> treeEntryType st1 p') ->
                (forall (p': BinTreePath t1), (SetTree_prod st1) -> treeEntryType st1 p') -> 
                unit)
          with
            | btpThis => fun f1 f2 => tt
            | btpLeft t1' t2' p' => 
              fun f1 f2 => 
              f1 p' (fst x)
            | btpRight t1' t2' p' => fun f1 f2 => 
              (treePathToProdEntry st2) p' (snd x)
          end
    end.
  

        (match p in (BinTreePath T') return (
                (BinTreePath (binTreeLeft T') -> Set) -> 
                (BinTreePath (binTreeRight T') -> Set) -> Set) with
          | btpThis => fun f1 f2 => unit
          | btpLeft t1' t2' p' => fun f1 f2 =>
            f1 p'
          | btpRight t1' t2' p' => fun f1 f2 =>
            f2 p' 
        end) (treeEntryType st1) (treeEntryType st2)                            
    end.


  Fixpoint toProdEntry(T : BinTree) : 
    forall (A B : SetTree T)(a : SetTree_sum A)(b : SetTree_prod B),  :=
    match T with
        | btLeaf => tt
        | btNode t1 t2 => tt
    end.

  Definition COracle(S A B : SetTree) :=
    SetTree_prod S -> SetTree_sum A -> Comp (SetTree_prod B * SetTree_prod S).

  Definition mkCompositeOracle
             {A1 A2 B1 B2 S1 S2 : Set}
             {eqdb1 : EqDec B1}{eqdb2 : EqDec B2}
             {eqds1 : EqDec S1}{eqds2 : EqDec S2}
             (d1 : B1)(d2 : B2)
             (o1 : S1 -> A1 -> Comp (B1 * S1))
             (o2 : S2 -> A2 -> Comp (B2 * S2))
             (s : S1 * S2)(z : A1 + A2) :=
      match z with
        | inl a => [b, s'] <-$2 o1 (fst s) a; ret ((b, d2), (s', snd s))
        | inr a => [b, s'] <-$2 o2 (snd s) a; ret ((d1, b), (fst s, s'))
      end.
 

  
  Definition OC_CQuery (A B : SetTree) : 
    forall (z : SetTree_sum A), 
      OracleComp (SetTree_sum A) (SetTree_prod B) 
                 (match z return Set with
                    | inl _ => B1
                    | inr _ => B2
                  end) :=
    fun z => 
      match z with
          | inl a => [b, _] <--$2 query z; $ ret b
          | inr a => [_, b] <--$2 query z; $ ret b
        end.

  (*       
       /  \
     / \  / \
    S  X  I Z *)

  Definition QS (x : Blist) := @inl (Blist + Blist) (Blist + Blist) (@inl Blist Blist x).
  Definition QX (x : Blist) := @inl (Blist + Blist) (Blist + Blist) (@inr Blist Blist x).
  Definition QI (x : Blist) := @inr (Blist + Blist) (Blist + Blist) (@inl Blist Blist x).
  Definition QZ (x : Blist) := @inr (Blist + Blist) (Blist + Blist) (@inr Blist Blist x).

  Definition D_O := (Blist + Blist + (Blist + Blist))%type.
  Definition R_O := (Bvector lambda * nat * (nat * nat))%type.
  Definition to_rVal (d : D_O)(r : R_O) :=
    match d with
        | inl x => 
          match x with
              | inl _ => fst (fst r)
              | inr _ => snd (fst r)
          end
        | inr x =>
          match x with
            | inl _ => fst (snd r)
            | inr _ => snd (snd r)
          end
    end.  


  

                                      

 


  Notation "'cquery' v" := (OC_CQuery v) (at level 79) : comp_scope.

  Definition Initialize_indLoop_3 k_E w (e : Identifier lambda * nat) :=
    [ind, c] <-2 e;
    e <--$$ Enc k_E ind;
    xind <--$ cquery (QI (Vector.to_list ind));
    z <--$ cquery (QZ (w ++ c));
    y <- xind * (inverse z);
    $ ret (Vector.append e (natToBvector y)).

  Fixpoint oc_compMap(A B C D : Set)(eqdb : EqDec B)(c : A -> OracleComp C D B)(ls : list A) : OracleComp C D (list B) :=
    match ls with
      | nil => $ (ret nil)
      | a :: ls' =>
        b <--$ c a;
          lsb' <--$ oc_compMap _ c ls';
          $ (ret (b :: lsb'))
    end.
           

  Definition Initialize_wLoop_3 db w : OracleComp D_O R_O (list (Bvector (lambda + lambda))):=
    inds <- lookupInds db w;
    sigma <--$$ RndPerm (length inds);
    k_E <--$ cquery (QS w);
    oc_compMap _ (Initialize_indLoop_3 k_E w) (combine (permute (oneVector lambda) inds sigma) (allNatsLt (length inds))).

  Definition XSetSetup_indLoop_2 k_X k_I w (ind : Bvector lambda) :=
    e <- F_P k_X w;
    xind <- F_P k_I (Vector.to_list ind);
    g^(e * xind).

  Definition XSetSetup_wLoop_2 k_X k_I db w :=
    map (XSetSetup_indLoop_2 k_X k_I w) (lookupInds db w).
    
  Definition XSetSetup_2 k_X k_I db :=
    removeDups _ (flatten (map (XSetSetup_wLoop_2 k_X k_I db) (toW db))).


  Definition ServerSearchLoop_2 (edb : EDB) e :=
    [xtoken, t_c] <-2 e;
    [_, xSet] <-2 edb;
    [e, y] <-2 splitVector lambda _ t_c;
    if (in_dec (EqDec_dec _) (xtoken^(bvectorToNat y)) xSet) then (Some e) else None.

  Definition ServerSearch_2 edb (xtokens : list nat) t :=
    map (ServerSearchLoop_2 edb) (combine xtokens t).

  Definition GenTrans_2 (edb : EDB) k_X k_Z k_S (e : Query * Tag) : (list (Identifier lambda) * SearchTranscript) :=
    [q, stag] <-2 e;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    t <- TSetRetrieve tSet stag;
    e <- F_P k_X x;
    xtokens <- map (fun (c : nat) => g^(e * (F_P k_Z (s ++ c)))) (allNatsLt (length t));
    res <- ServerSearch_2 edb xtokens t;
    es <- getSomes res;
    k_E <- F k_S s;
    inds <- map (Dec k_E) es;
    (inds, (stag, (combine xtokens res))).

  Definition Initialize_2 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    t_entries <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    xSet <- XSetSetup_2 k_X k_I db;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    stags <-$ compMap _ (TSetGetTag k_T) (fst (split q));
    searchRes <- map (GenTrans_2 edb k_X k_Z k_S) (combine q stags);
    ret (edb, searchRes).


  Theorem G2_equiv : 
    Pr[G_gen Initialize_1_3] ==  Pr[G2].

    unfold G2, G_gen, Initialize_1_3, Initialize_2.
    do 9 (comp_skip; comp_simp).
    eapply evalDist_ret_eq.
    f_equal.
    eapply map_ext.
    intuition.
    unfold GenTrans_1_3, GenTrans_2.
    comp_simp.
    eapply map_eq.

  Qed.


  Definition OXT_Search_Loop_Client (k : Key)(q : Query) c :=
    [k_S, k_X, k_I, k_Z, k_T] <-5 k;
    [s, x] <-2 q;
    computeXToken c k_Z k_X s x.

  Definition OXT_Search_Loop_Server (edb : EDB) xtoken t_c :=
    [_, xSet] <-2 edb;
    [e, y] <-2 splitVector lambda _ t_c;
    if (in_dec (EqDec_dec _) (xtoken^(bvectorToNat y)) xSet) then (Some e) else None.

   Definition OXT_Search_Loop edb k q (e : nat * Bvector (lambda + lambda)) :=
    [c, t_c] <-2 e;
    xtoken <- OXT_Search_Loop_Client k q c ;
    answer <- OXT_Search_Loop_Server edb xtoken t_c;
    (xtoken, answer).

  Definition Initialize_1_3 (db : DB)(q : list Query) :=
    k_S <-$ {0,1}^lambda;
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    t_entries <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    xSet <- XSetSetup_2 k_X k_I db;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <-$2 TSetSetup t;
    edb <- (tSet, xSet);
    key <- (k_S, k_X, k_I, k_Z, k_T);
    stags <-$ compMap _ (TSetGetTag k_T) (fst (split q));
    searchRes <- map (GenTrans_1_3 edb key) (combine q stags);
    ret (edb, searchRes).

  Theorem G1_3_equiv : 
    Pr[G_gen Initialize_1_2] == Pr[G_gen Initialize_1_3].

  Admitted.
  

  Theorem G0_equiv : 
    Pr[SSE_Sec_NA_Real OXT_EDBSetup _ OXT_Search A1 A2 ] == Pr[G0].

    unfold SSE_Sec_NA_Real, G0.
    comp_skip.
    comp_simp.
    unfold OXT_EDBSetup, Initialize_0.
    do 4 (inline_first; comp_skip).
    
    inline_first.
    eapply comp_spec_eq_impl_eq.
    eapply comp_spec_seq; eauto with inhabited.
    eapply compMap_spec.
    eapply list_pred_eq.
    intuition.
    subst.

    Theorem Init_indLoop_0_spec : 
      forall x1 x2 x b x0 a0 b1,
        comp_spec 
          (fun a b => fst a = b) 
          (OXT_EDBSetup_indLoop x1 x2 (F x b) x0 b (a0, b1))
          (Initialize_indLoop_0 x1 x2 (F x b) b (a0, b1)).

      intuition.
      unfold OXT_EDBSetup_indLoop, Initialize_indLoop_0.
      comp_simp.
      comp_skip; try eapply (oneVector).
      eapply comp_spec_ret; intuition.

    Qed.

    Theorem Init_wLoop_0_spec : forall d x x1 x2 b x0,
      comp_spec 
        (fun a b => fst a = b) 
        (OXT_EDBSetup_wLoop d x x1 x2 x0 b)
        (Initialize_wLoop_0 d x x1 x2 b).

      intuition.
      unfold OXT_EDBSetup_wLoop, Initialize_wLoop_0.
      comp_simp.
      unfold shuffle.
      inline_first.
      comp_skip.
      rewrite permute_length_eq.

      eapply comp_spec_eq_trans_r.
      Focus 2.
      eapply comp_spec_right_ident.

      eapply comp_spec_seq; try eapply (nil, nil).
      rewrite (@RndPerm_In_support_length (length (lookupInds d b))); intuition.
      eapply compMap_spec.
      eapply list_pred_eq.
      intuition.
      subst.      
      eapply Init_indLoop_0_spec.

      intuition.
      eapply comp_spec_ret; intuition.
     
      Theorem fst_split_eq_list_pred : 
        forall (A B : Set)(ls1 : list (A * B))(ls2 : list A),
          list_pred (fun a b => fst a = b) ls1 ls2 ->
          fst (split ls1) = ls2.

        induction 1; intuition; simpl in *.
        subst.
        destruct a1.
        remember (split ls1) as x.
        destruct x.
        simpl in *.
        f_equal.
      Qed.

      eapply fst_split_eq_list_pred.
      trivial.

      Grab Existential Variables.
      (* Not sure where this came from. *)
      apply nat.
      
    Qed.

    eapply Init_wLoop_0_spec.
    intuition.
    
    remember (split a0) as z.
    comp_simp.
    inline_first.
    assert (l0 = b).
    admit.
    subst.
    comp_skip.
    inline_first.

    Theorem OXT_Seqrch_0_equiv : 
      forall a x4 x0 x1 x2 b0 a2 l2,
        comp_spec
          (fun (b : Query * Tag) (c : list (Identifier lambda) * SearchTranscript) =>
             OXT_Search_0 (a2, l2) (x4, x0, x1, x2, b0) b = c)
          (z <-$ TSetGetTag b0 (fst a); ret (a, z))
          (OXT_Search (a2, l2) (x4, x0, x1, x2, b0) a).

      intuition.
      unfold OXT_Search.
      unfold OXT_Search_ClientInit.
      comp_skip.
      eapply comp_base_exists; eauto.
      eapply comp_base_exists; eauto.
      eapply comp_spec_ret.
      unfold OXT_Search_0.
      comp_simp.
      reflexivity.
    Qed.

    Theorem OXT_Search_0_loop_equiv : 
      forall (l : list Query) a2 l2 x4 x0 x1 x2 b0,
      comp_spec
        eq
        (compMap _ (OXT_Search (a2, l2) (x4, x0, x1, x2, b0)) l)
        (ls' <-$ compMap _ (fun x => stag <-$ TSetGetTag b0 (fst x); ret (x, stag)) l;
         ret (map (fun x => OXT_Search_0 (a2, l2) (x4, x0, x1, x2, b0) x) ls')).

      intuition.
       
      eapply comp_spec_eq_symm.
      eapply comp_spec_eq_trans.
      specialize  (@compMap_map_fission_eq Query
                                           (Query * Tag)
                  (list (Identifier lambda) * SearchTranscript)
                  (list (Identifier lambda) * SearchTranscript)
                  _ _ _ 
                  l
                  (fun x => z <-$ TSetGetTag b0 (fst x); ret (x, z))
                  (OXT_Search (a2, l2) (x4, x0, x1, x2, b0))
                  (OXT_Search_0 (a2, l2) (x4, x0, x1, x2, b0))
                  (fun x => x)); intuition.
      eapply H.

      intuition.
      eapply OXT_Seqrch_0_equiv.
      eapply comp_spec_consequence.
      eapply compMap_spec.
      eapply list_pred_eq.
      intuition.
      subst.
      eapply comp_spec_right_ident.
      intuition.
      eapply list_pred_eq_impl_eq.
      trivial.
    Qed.
    
    Show.

    eapply comp_spec_eq_trans.
    eapply comp_spec_seq_eq; eauto with inhabited.
    eapply OXT_Search_0_loop_equiv.
    intuition.
    eapply comp_spec_eq_refl.
    inline_first.
    eapply comp_spec_seq; eauto with inhabited.
    eapply compMap_spec.
    assert (list_pred (fun a b => fst a = b) l (fst (split l))).
    admit.
    eauto.
    intuition.
    subst.
    simpl.
    eapply comp_spec_eq_trans_r.
    Focus 2.
    eapply comp_spec_right_ident.
    comp_skip.
    eapply comp_base_exists; eauto.
    eapply comp_base_exists; eauto.
    assert (comp_spec (fun a b => snd a = b) (ret (a3, b1, b2)) (ret b2)).
    eapply comp_spec_ret; intuition.
    eauto.
    intuition.
    comp_simp.

    Theorem comp_spec_eq_refl_gen : 
      forall (A : Set)(eqd : EqDec A)(c1 c2 : Comp A),
        c1 = c2 ->
        comp_spec eq c1 c2.

      intuition.
      subst.
      eapply comp_spec_eq_refl.

    Qed.

    eapply comp_spec_eq_refl_gen.
    f_equal.
    f_equal.
    admit.

    f_equal.
    f_equal.
    unfold OXT_Search_0, GenTrans_0.
    
    unfold XSetSetup_0, XSetSetup_wLoop_0, XSetSetup_indLoop_0.

     Check compMap_support.

    Theorem compMap_support'
     : forall (A B : Set) (eqd : EqDec B)
         (c : A -> Comp B) (lsa : list A) (lsb : list B),
       In lsb (getSupport (compMap _ c lsa)) ->
       list_pred (fun a b => In b (getSupport (c a))) lsa lsb.
      
   
    eapply compMap_support in H4.
    

    unfold OXT_Search_0, GenTrans_0.
    comp_simp.
    
    eapply comp_spec_ret.

    eapply comp_spec_ret; intuition.
    assert ((fun a b => snd a = b) (a3, b1, b2) b2).
    trivial.
    eapply H15.
    eapply comp_spec_eq_trans.
    eapply comp_spec_eq_symm.
    eapply compMap_fission_eq.
    Check compMap_map_fission_eq.


    Print OXT_Search.

    eapply comp_spec_seq; eauto with inhabited.
    eapply compMap_spec.
    assert (list_pred (fun a b => fst a = b) l (fst (split l))).
    admit.
    eauto.
    intuition.
    subst.
    
  Qed.

  
  Definition x := tt.





  (* Step 2: Replace PRF F with a random function. We can use a non-adaptively-secure PRF, since k_S isn't used after initialization. *)

  (* Step 3: inputs to the random function are unique---replace outputs with random values. *)

  (* Step 4-6: Replace F_P with random functions (one for each key).  Use adapatively secure PRF. *)

  (* Step 7: Replace the "client finalize" step in the search protocol with a function that looks up the correct answers.  Use the correctness of the encryption and T-Set schemes to show that this is close. *)

  (* Step 8: Use IND-CPA to replace encryptions of indices with encryptions of 0^lambda. This is possible because decryption never happens. *)

  (* Step 9: 
    

End ESPADA_SSE_OXT.