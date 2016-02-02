(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by a BSD-style		*
 * license that can be found in the LICENSE file at the root	*
 * of the source tree.						*)
Set Implicit Arguments.

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

Section ESPADA_SSE_OXT_Games.

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

   Definition G1 := G_gen Initialize_1.

   Theorem SSE_G1_equiv :     
     Pr[SSE_Sec_NA_Real OXT_EDBSetup _ OXT_Search A1 A2 ] == Pr[G1].
   Abort.
   
   
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

  Theorem G1_G2_equiv : 
    Pr[G1] == Pr[G2].
  Abort.
    

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

  (* We need to show that the bad event is related to TSet correctness.  Put the game in the correct form.   *)
  Definition TSetCorA := 
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    k_Z <-$ {0,1}^lambda;
    wLoopRes <-$ compMap _ (Initialize_wLoop_2 db k_S k_I k_Z) (toW db);
    [t_entries, sigmas] <-2 split wLoopRes;
    t <- combine (toW db) t_entries;
    ret (t, (fst (split q))).

  Theorem G2_G3_close : 
    | Pr[G2] - Pr[G3] | <=  Pr[AdvCor _ TSetSetup TSetGetTag TSetRetrieve TSetCorA].

 Abort.


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
  
  Theorem G3_G4_equiv : 
    Pr[G3] == Pr[G4].
  Abort.

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

  Theorem G4_G4_equiv : 
    Pr[G4] == Pr[G5].

  Abort.

  (* Step 6: replace the PRF with a random function. *)
   Definition G6 :=
    [b, _] <-$2 G5_A _ _ (@randomFunc Blist (Bvector lambda) (Rnd lambda) _) nil;
    ret b.
  
   Theorem G5_G6_equiv : 
     | Pr[G5] - Pr[G6] | == PRF_Advantage (Rnd lambda) (Rnd lambda) F _ _ G5_A.

   Abort.

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

  Theorem G6_G7_equiv : 
    Pr[G6] == Pr[G7].
  Abort.

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
  
  Theorem G7_G8_equiv : 
    | Pr[G7] - Pr[G8] | <= IND_CPA_SecretKey_OI_Advantage (Rnd lambda) Enc 
      EncI_A1 EncI_A2 EncI_A3 _ _ (oneVector lambda).

  Abort.

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

  Theorem G8_G9_equiv : 
    Pr[G8] == Pr[G9].
  Abort.

  (* Step 10: Replace the PRF with a random function. *)
  Definition G10 :=
    [b, _] <-$2 G9_A _ _ (@randomFunc Blist nat (RndNat (2^lambda)) _ ) nil;
    ret b.
  
  Theorem G9_G10_quiv : 
  | Pr[G9] - Pr[G10] | <= PRF_Advantage (Rnd lambda) (RndNat (2^lambda)) F_P _ _ G9_A.
    
  Abort.

  
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

  
  Variable MaxMatchingIDs : nat.
  Hypothesis MaxMatchingIDs_correct : 
    forall db q s_A,
      In (db, q, s_A) (getSupport A1) ->
      forall w,
        (length (lookupInds db w) <= MaxMatchingIDs)%nat.

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

  Theorem G10_G11_equiv : 
    | Pr[G10] - Pr[G11] | <= (((MaxKeywords + MaxQueries) * MaxMatchingIDs)^2) * 
    MaxQueries * MaxMatchingIDs * MaxIDs *
      MaxKeywords * MaxMatchingIDs / 2 ^ lambda.
  Abort.

  (* Setp 12 : Add some bookkeeping so we can compute the transcript differently and replace the random function outputs with random values. *)
  

  (* Step 12: Remove some of the query blinding and simplify. *)
  Definition Initialize_indLoop_12 k_I k_E w (e : Identifier lambda * nat) :=
    [ind, c] <-2 e;
    e <--$$ Enc k_E (zeroVector lambda);
    xind <- F_P k_I (Vector.to_list ind);
    z <--$ OC_Query nat (w ++ c);
    $ ret (Vector.append e (natToBvector xind), (ind, z)).
  
  Definition Initialize_wLoop_12 db k_I e :=
    [w, sigma] <-2 e;
    inds <- lookupInds db w;
    k_E <--$$ {0, 1}^lambda;
    indLoopRes <--$ oc_compMap _ (Initialize_indLoop_12 k_I k_E w) (combine (permute inds sigma) (allNatsLt (length inds)));
    $ ret (indLoopRes, sigma).

    Definition GenTrans_12 (edb : EDB) k_X (e : Query * (Tag * list (Bvector (lambda + lambda) * (Bvector lambda * nat)))) :=
    [q, stag_t] <-2 e;
    [stag, t] <-2 stag_t;
    [s, x] <-2 q;
    [tSet, xSet] <-2 edb;
    e <- F_P k_X x;
    xtokens <--$ oc_compMap _ (fun (c : nat) => z <--$ query s ++ c; $ ret (g^(e * z), (g ^ e, z))) (allNatsLt (length t));
    res <- ServerSearch_11 xSet (snd (split xtokens)) t;
    es <- getSomes res;
    res <- map (fun z => match z with
                           | Some y => Some (fst y)
                           | None => None
                         end) res;
    inds <- map (fun x => snd x) es;
    $ ret (inds, (stag, (combine (fst (split xtokens)) res))).

   Definition Initialize_12 k_X k_I (db : DB)(q : list Query) sigmas xSet :=
    wLoopRes <--$ oc_compMap _ (Initialize_wLoop_11 db k_I) (combine (toW db) sigmas);
    [t_entries_pts, sigmas] <-2 split wLoopRes;
    t_entries <- map (fun v => (fst (split v))) t_entries_pts;
    t <- combine (toW db) t_entries;
    [tSet, k_T] <--$2$ TSetSetup t;
    t <- combine (toW db) t_entries_pts;
    edb <- (tSet, xSet);
    stags_ts <--$$ compMap _ (fun x => tag <-$ TSetGetTag k_T x; ret (tag, (arrayLookupList _ t x))) (fst (split q));
    searchRes <--$ oc_compMap _ (GenTrans_12 edb k_X) (combine q stags_ts);
    $ ret (edb, searchRes).

  Definition G12 :=
    k_X <-$ {0,1}^lambda;
    k_I <-$ {0,1}^lambda;
    [db, q, s_A] <-$3 A1;
    sigmas <-$ compMap _ (sampleSigmas_11 db) (toW db);
    xSet <- XSetSetup_2 k_X k_I db sigmas;
    [z, _] <-$2 (Initialize_12 k_X k_I db q sigmas xSet) _ _ (@randomFunc Blist nat (RndNat (2^lambda)) _ ) nil;
    [edb, ls] <-2 z;
     A2 s_A edb (snd (split ls)).

End ESPADA_SSE_OXT_Games.