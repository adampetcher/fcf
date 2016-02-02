Set Implicit Arguments.

Require Import FCF.
Require Import CompFold.
Require Import Array.

Local Open Scope type_scope.
Local Open Scope list_scope.

Section SSE.

  Variable lambda : nat.
  Definition Identifier := Bvector lambda.
  Definition Keyword := Blist.
  Definition DB_Entry := (Identifier * list Keyword).
  Definition DB := list DB_Entry.
  Variable Query : Set.
  
  Variable SecretKey : Set.
  Variable EDB : Set.
  Variable EDBSetup : DB -> Comp (SecretKey * EDB).
  Variable SearchTranscript : Set.
  Hypothesis SearchTranscript_EqDec : EqDec SearchTranscript.
  Variable SearchProtocol : EDB -> SecretKey -> Query -> Comp (list Identifier * SearchTranscript).
  
  Section SSE_Security_NA.

    Variable A_State : Set.
    Variable A1 : Comp (DB * list Query * A_State).
    Variable A2 : A_State -> EDB -> list SearchTranscript -> Comp bool.

    Variable Leakage : Set.
    Variable L : DB -> list Query -> Comp Leakage.
    Variable Sim : Leakage -> Comp (EDB * list SearchTranscript).
    
    Definition SSE_Sec_NA_Real := 
      [db, q, s_A] <-$3 A1;
      [k, edb] <-$2 EDBSetup db;
      ls <-$ compMap _ (SearchProtocol edb k) q;
      A2 s_A edb (snd (split ls)).

    Definition SSE_Sec_NA_Ideal :=
      [db, q, s_A] <-$3 A1;
      leak <-$ L db q;
      [edb, t] <-$2 Sim leak;
      A2 s_A edb t.

    Definition SSE_NA_Advantage := 
      | Pr[SSE_Sec_NA_Real] - Pr[SSE_Sec_NA_Ideal] |.

  End SSE_Security_NA.
  
End SSE.