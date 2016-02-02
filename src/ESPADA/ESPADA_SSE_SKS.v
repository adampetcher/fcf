(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments. 

Require Import FCF.
Require Import SSE.
Require Import TSet.
Require Import RndPerm.
Require Import CompFold.
Require Import Array.
Require Import PRF.
Require Import Encryption.
Require Import OracleCompFold.

Local Open Scope list_scope.

Section ESPADA_SSE_SKS.

  Variable lambda : posnat.
  Definition DB := DB lambda.

  (* PRF *)
  Variable F : Bvector lambda -> Keyword -> Bvector lambda.
  
  (* Encryption scheme *)
  Variable Enc : Bvector lambda -> Bvector lambda -> Comp (Bvector lambda).
  Variable Dec : Bvector lambda -> Bvector lambda -> Bvector lambda.

  (* TSet *)
  Variable TSet : Set.
  Hypothesis TSet_EqDec : EqDec TSet.
  Variable TSetKey : Set.
  Hypothesis TSetKey_EqDec : EqDec TSetKey.
  Variable Tag : Set.
  Hypothesis Tag_EqDec : EqDec Tag.
  Variable TSetSetup : T (pos (lambda)) -> Comp (TSet * TSetKey).
  Variable TSetGetTag : TSetKey -> Keyword -> Comp Tag. 
  Variable TSetRetrieve : TSet -> Tag -> (list (Bvector (lambda))).
  Variable Leakage_T : Set.
  Hypothesis Leakage_T_EqDec : EqDec Leakage_T.
  Variable L_T : T (pos (lambda)) -> list Keyword -> Leakage_T.
  Variable Sim_T : Leakage_T -> list (list (Bvector lambda)) -> Comp (TSet * list Tag).

  Definition lookupInds(db : DB)(w : Keyword) :=
    fold_left (fun ls p => if (in_dec (EqDec_dec _) w (snd p)) then (fst p :: ls) else ls) db nil.

  Definition toW (db : DB) :=
    removeDups _ (flatten (snd (split db))).

  Definition SKS_EDBSetup_indLoop k_e ind :=
    Enc k_e ind.
    
  Definition SKS_EDBSetup_wLoop db k_S w :=
    k_e <- F k_S w;
    inds <- lookupInds db w;
    t <-$ compMap _ (SKS_EDBSetup_indLoop k_e) inds;
    ret (w, t).

  Definition SKS_EDBSetup(db : DB) := 
    k_S <-$ {0, 1}^lambda;
    t <-$ compMap _ (SKS_EDBSetup_wLoop db k_S) (toW db);
    [tSet, k_T] <-$2 TSetSetup t;
    ret ((k_S, k_T), tSet).

  Definition SKS_Search tSet k w :=
    [k_S, k_T] <-2 k;
    (* client *)
    tag <-$ TSetGetTag k_T w;
    (* server *)
    t <- TSetRetrieve tSet tag;
    (* client *)
    k_e <- F k_S w;
    inds <- map (Dec k_e) t;
    (* Search returns the results and the transcript. *)
    ret (inds, (tag, t)).

  Definition EDB := TSet.
  Definition SearchTranscript := (Tag * list (Bvector lambda))%type.
  Definition Query := Keyword.
  Definition Identifier := Bvector lambda.

  Variable A_State : Set.
  Hypothesis A_State_EqDec : EqDec A_State.
  Variable A1 : Comp (DB * list Query * A_State).
  Variable A2 : A_State -> EDB -> list SearchTranscript -> Comp bool.
  Hypothesis A1_wf : well_formed_comp A1.
  Hypothesis A2_wf : forall x y z, well_formed_comp (A2 x y z).
  
  Definition zeroVector n := Vector.const false n.

  Definition SKS_resultsStruct db w :=
    k_e <-$ (Rnd lambda);
    inds <- lookupInds db w;
    compMap _ (fun _ => Enc k_e (zeroVector lambda)) inds.

  Definition L (db : DB) (qs : list Query) := 
    t_struct <-$ compMap _ (SKS_resultsStruct db) (toW db);
    t <- combine (toW db) t_struct;
    leak_T <- L_T t qs;
    ret (leak_T, map (arrayLookupList _ t) qs).

  Definition SKS_Sim (leak : _ * list (list (Bvector lambda))) :=
    [leak_T, resStruct] <-2 leak;
    [tSet, tags] <-$2 Sim_T leak_T resStruct;
    ret (tSet, (combine tags resStruct)).

    
  (* Step 1: inline and simplify *)
  Definition SKS_Search_1 tSet k_T w :=
    tag <-$ TSetGetTag k_T w;
    t <- TSetRetrieve tSet tag;
    ret (tag, t).

  Definition G1 :=
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0, 1}^lambda;
    t <-$ compMap _ (SKS_EDBSetup_wLoop db k_S) (toW db);
    [tSet, k_T] <-$2 TSetSetup t;
    ls <-$ compMap _ (SKS_Search_1 tSet k_T) q;
    A2 s_A tSet ls.


  (* Step 2: factor out some TSet computations and prepare to apply TSet correctness*)

  Definition G2 :=
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0, 1}^lambda;
    t <-$ compMap _ (SKS_EDBSetup_wLoop db k_S) (toW db);
    [tSet, k_T] <-$2 TSetSetup t;
    tags <-$ compMap _ (TSetGetTag k_T) q;
    rs <- map (TSetRetrieve tSet) tags;
    ls <- combine tags rs;
    A2 s_A tSet ls.

 
  (* Step 3: apply TSet correctness. *)
  Definition G3 :=
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0, 1}^lambda;
    t <-$ compMap _ (SKS_EDBSetup_wLoop db k_S) (toW db);
    [tSet, k_T] <-$2 TSetSetup t;
    tags <-$ compMap _ (TSetGetTag k_T) q;
    rs <- map (arrayLookupList _ t) q;
    ls <- combine tags rs;
    A2 s_A tSet ls.

  Definition TSetCor_A :=
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0, 1}^lambda;
    t <-$ compMap _ (SKS_EDBSetup_wLoop db k_S) (toW db);
    ret (t, q).


  (* Step 4: apply TSet security. *)
  Definition G4 :=
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0, 1}^lambda;
    t <-$ compMap _ (SKS_EDBSetup_wLoop db k_S) (toW db);
    inds <- map (lookupAnswers _ t) q;
    [tSet, tags] <-$2 Sim_T (L_T t q) inds;
    rs <- map (arrayLookupList _ t) q;
    ls <- combine tags rs;
    A2 s_A tSet ls.

  Definition TSetSec_A1 := 
    [db, q, s_A] <-$3 A1;
    k_S <-$ {0, 1}^lambda;
    t <-$ compMap _ (SKS_EDBSetup_wLoop db k_S) (toW db);
    rs <- map (arrayLookupList _ t) q;
    ret (t, q, (s_A, rs)).

  Definition TSetSec_A2 s p :=
    [s_A, rs] <-2 s;
    [tSet, tags] <-2 p;
    ls <- combine tags rs;
    A2 s_A tSet ls.

  (* Step 5-6: apply PRF definition. *)
  Definition SKS_EDBSetup_wLoop_5 db w :=
    k_e <--$ query w;
    inds <- lookupInds db w;
    t <--$$ compMap _ (SKS_EDBSetup_indLoop k_e) inds;
    $ ret (w, t).

  Definition PRF_A :=
    [db, q, s_A] <--$3$ A1;
    t <--$ oc_compMap _ (SKS_EDBSetup_wLoop_5 db) (toW db);
    inds <- map (lookupAnswers _ t) q;
    [tSet, tags] <--$2$ Sim_T (L_T t q) inds;
    rs <- map (arrayLookupList _ t) q;
    ls <- combine tags rs;
    $ A2 s_A tSet ls.

  Definition G5 :=
    k_S <-$ {0, 1}^lambda;
    [b, _] <-$2 PRF_A _ _ (f_oracle F _ k_S) tt;
    ret b.


  Definition G6 :=
    [b, _] <-$2 PRF_A _ _ (RndR_func (Rnd lambda) _) nil;
    ret b.

  
  (* Step 7: replace RF outputs with random values. *)
  Definition SKS_EDBSetup_wLoop_7 db w :=
    k_e <-$ (Rnd lambda);
    inds <- lookupInds db w;
    t <-$ compMap _ (SKS_EDBSetup_indLoop k_e) inds;
    ret (w, t).

  Definition G7 :=
    [db, q, s_A] <-$3 A1;
    t <-$ compMap _ (SKS_EDBSetup_wLoop_7 db) (toW db);
    inds <- map (lookupAnswers _ t) q;
    [tSet, tags] <-$2 Sim_T (L_T t q) inds;
    rs <- map (arrayLookupList _ t) q;
    ls <- combine tags rs;
    A2 s_A tSet ls.

  (* Step 8: apply encryption security definition. *)
  Definition G8 :=
    [db, q, s_A] <-$3 A1;
    t <-$ compMap _ (SKS_resultsStruct db) (toW db);
    t <- combine (toW db) t;
    inds <- map (lookupAnswers _ t) q;
    [tSet, tags] <-$2 Sim_T (L_T t q) inds;
    rs <- map (arrayLookupList _ t) q;
    ls <- combine tags rs;
    A2 s_A tSet ls.

  Definition Enc_A1 :=
    [db, q, s_A] <-$3 A1;
    ret ((map (pair db) (toW db)), (db, q, s_A)).

  Definition Enc_A2  e :=
    [db, w] <-2 e;
    oc_compMap _ (@OC_Query _ (Bvector lambda)) (lookupInds db w).

  Definition Enc_A3 s_A t :=
    [db, q, s_A] <-3 s_A;
    t <- combine (toW db) t;
    inds <- map (lookupAnswers _ t) q;
    [tSet, tags] <-$2 Sim_T (L_T t q) inds;
    rs <- map (arrayLookupList _ t) q;
    ls <- combine tags rs;
    A2 s_A tSet ls.

  Definition G7_G8_Distance :=
    IND_CPA_SecretKey_OI_Advantage (Rnd lambda) Enc Enc_A1 Enc_A2 Enc_A3 _ _(zeroVector lambda).

  (* G8 is equal to the ideal game*)                                 



End ESPADA_SSE_SKS.


