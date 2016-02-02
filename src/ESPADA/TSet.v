(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import FCF.
Require Import CompFold.
Require Import Array.

Local Open Scope array_scope.

Section TSet.
  
  Variable lambda : posnat. (* security parameter *)
  Definition T := list (Blist * (list (Bvector lambda))).
  Variable TSet : Set.
  Variable Tag : Set.
  Variable SecretKey : Set.
  Hypothesis Tag_EqDec : EqDec Tag.

  Variable TSetSetup : T -> Comp (TSet * SecretKey).
  Variable TSetGetTag : SecretKey -> Blist -> Comp Tag. 
  Variable TSetRetrieve : TSet -> Tag -> (list (Bvector lambda)).
  
  Section TSetCorrectness.
    
    Variable A : Comp (T * list Blist).

    Definition AdvCor_G :=
      [t, q] <-$2 A;
      [tSet, k_T] <-$2 TSetSetup t;
      tags <-$ compMap _ (TSetGetTag k_T) q;
      t_w <- map (TSetRetrieve tSet) tags;
      t_w_correct <- map (arrayLookupList _ t) q;
      ret (negb (eqb t_w t_w_correct)).

    Definition AdvCor := Pr[AdvCor_G].

    (* AdvCor should be small for a correct TSet. *)
      
  End TSetCorrectness. 
  
  (* Security against a non-adaptive adversary.  In this definition, the adversary must choose the list of queries before seeing the encrypted structure. *)   
  Section TSetSecurity.
    
    Variable Leakage : Set.
    Variable L : T -> list Blist -> Leakage.
    
    Variable A_State : Set.
    Variable A1 : Comp (T * list Blist * A_State).
    Variable A2 : A_State -> TSet * list Tag -> Comp bool.
    Definition A := (A1, A2).

    (* For simplicity, we remove duplicates from the list of queries before processing it.  *)

    Definition TSetReal :=
      [t, q, s_A] <-$3 A1;
      [tSet, k_T] <-$2 TSetSetup t;
      tags <-$ foreach (x in q) (TSetGetTag k_T x);
      A2 s_A (tSet, tags).


    Variable Sim :  Leakage -> list (list (Bvector lambda)) -> Comp (TSet * list Tag).
    
    Definition lookupAnswers (t : Array Blist (list (Bvector lambda))) (q : Blist) :=
      arrayLookupList _ t q.

    Definition TSetIdeal :=
      [t, q, s_A] <-$3 A1;
      T_qs <- foreach (x in q) (lookupAnswers t x);
      [tSet, tags] <-$2 Sim (L t q) T_qs;
      A2 s_A (tSet, tags).
    
    Definition TSetAdvantage := | Pr[TSetReal] - Pr[TSetIdeal] |.
    
  End TSetSecurity.    
  
End TSet.