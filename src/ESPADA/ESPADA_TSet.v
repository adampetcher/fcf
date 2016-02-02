Set Implicit Arguments.

Require Import FCF.
Require Import Array.
Require Import CompFold.
Require Import RndNat.
Require Import RndListElem. 

Require Import TSet.
Require Import PRF.

Local Open Scope array_scope.
Local Open Scope list_scope.

Notation "! x" := (negb x) (at level 50).
Infix "=?" := eqb (at level 70) : comp_scope. 
Notation " x '!=' y " := (negb (eqb x y)) (at level 70) : comp_scope. 

Notation "'loop_over' ( init , ls ) c " := 
    (compFold _ (foldBody_option _ c%comp) (Some init) ls)
             (right associativity, at level 85) : comp_scope.
  Notation "'loop_over*' ( init , ls ) c " := 
    (compFold _ (foldBody_option _ c%comp) (init) ls)
             (right associativity, at level 85) : comp_scope.
        

(* The ESPADA TSet implementation. *)
Section ESPADA_TSet.
  
    (* For simplicity, we use lambda as the bit length of the strings in T.  We could generalize this to a polynomial function of lambda. *)
  Variable lambda : posnat.

    (* A TSet is an array of B buckets of size N.  The protocol determines B and S from the size of the data structure that will be encrypted.  We make B and S variables because several things depend on them.  We prove security for all B S, and for all adversaries that provide a structure of size N such that B and S are correct with respect to N. *)
  Variable tSize bigB bigS : posnat.
  Variable bucketSize : nat -> (posnat * posnat).

  Variable F : Bvector lambda -> nat -> nat * Bvector lambda * Bvector (S lambda).
  Variable F_bar : Bvector lambda -> Blist -> Bvector lambda.

  (* F maps a pair of (tag, nat) to a nat (indicating the bucket) and a couple of bit vectors.  The bucket index must be less than the number of buckets.  We could enforce this using a sigma type, but that doesn't match the definition for RndNat. *)
  Hypothesis F_b_correct : 
    forall k b i v1 v2,
      (b, v1, v2) = F k i ->
      b < bigB.
            

  Definition TSet_Record := (Bvector lambda * Bvector (S lambda))%type.
  Definition TSet := list (list (option TSet_Record)).

  (* The TSet is constructed using a helper structure that keeps track of which positions are free in the TSet. *)
  Definition FreeList := list (list nat).
  
  (* toW returns all the keywords in the structure.  We removeDups because an array may have additional (dead) entries for some keyword. *)
  Definition toW (bigT : T lambda) :=
    removeDups _ (fst (unzip bigT)).
  
  (* bigN is the total size of the structure.  Note that we can't simply sum over all entries in the structure because there may be dead entries.  *)
  Definition bigN (bigT : T lambda) := 
    bigW <- toW bigT;
    fold_left (fun acc w => acc + length (arrayLookupList _ bigT w))%nat bigW O.

  (* tSetUpdate replace the value at some location in the TSet. *)
  Definition tSetUpdate (tSet : TSet)(b j : nat)(r : TSet_Record) : TSet :=
    let bucket := nth b tSet nil in
    let bucket' := listReplace bucket j (Some r) None in
    listReplace tSet b bucket' nil.


   Local Open Scope vector_scope.
  Definition ESPADA_TSetSetup_tLoop (stag : Bvector lambda)(length : nat)(acc : TSet * FreeList)(e : nat * Bvector lambda) :=
    [tSet, free] <-2 acc;
    [i, s_i] <-2 e;
    [b, bigL, bigK] <-3 F stag i;
    free_b <- nth b free nil;
    j <-$? (rndListElem _ free_b) ;
    free <- listReplace free b (removeFirst (EqDec_dec _) free_b j) nil;
    bet <- (S i) != length;
    newRecord <- (bigL, (bet :: s_i) xor bigK);
    tSet <- tSetUpdate tSet b j newRecord; 
    ret (tSet, free).
  
  Definition initFree :=
    for ( _ '< bigB) 
        (for (i '< bigS) i). 
         
  Definition ESPADA_TSetSetup_wLoop (bigT : T lambda) (k_T : Bvector lambda)(acc : TSet * FreeList)(w : Blist) :=
    [tSet, free] <-2 acc;
    stag <- F_bar k_T w;
    t <- lookupAnswers _ bigT w;
    ls <- zip (allNatsLt (length t)) t;
    loop_over ((tSet, free), ls) (ESPADA_TSetSetup_tLoop stag (length t)).

 
  Definition ESPADA_TSetSetup_trial (bigT : T lambda) :=
    k_T <-$ {0, 1} ^ lambda;
    loopRes <-$ loop_over ((nil, initFree), (toW bigT)) (ESPADA_TSetSetup_wLoop bigT k_T) ;
    ret (loopRes, k_T).

  Definition getTSet(opt : option (TSet * FreeList)) :=
    match opt with
      | None => nil
      | Some p => fst p
    end.

  Definition isSome (A : Set)(opt : option A) :=
     if opt then true else false.

  Definition ESPADA_TSetSetup t := 
    [res, k_T] <-$2 Repeat (ESPADA_TSetSetup_trial t) (fun p => isSome (fst p));
    ret (getTSet res, k_T).

  Definition ESPADA_TSetGetTag (k_T : Bvector lambda) w :=
    ret (F_bar k_T w).

  Definition ESPADA_TSetRetrieve_tLoop tSet stag i :=
    [b, L, K] <-3 F stag i;
    B <- nth b tSet nil;
    t <- arrayLookupOpt _ B L;
    match t with
        | None => None
        | Some u => 
          v <- u xor K;
          bet <- Vector.hd v;
          s <- Vector.tl v;
          Some (s, bet)
    end.

  Local Open Scope list_scope.
  Fixpoint ESPADA_TSetRetrieve_h tSet stag i (fuel : nat) :=
    match fuel with
      | O => nil
      | S fuel' =>
        match (ESPADA_TSetRetrieve_tLoop tSet stag i) with
          | Some (v, bet) =>
            v :: (if (bet) then (ESPADA_TSetRetrieve_h tSet stag (S i) fuel') else nil)
          | None => nil
        end
      end.
    
  Variable maxMatches : nat.

  Definition ESPADA_TSetRetrieve tSet stag :=
    ESPADA_TSetRetrieve_h tSet stag O maxMatches.

End ESPADA_TSet.