
Set Implicit Arguments.

Require Import FCF.
Require Import TSet.
Require Import ESPADA_TSet.
Require Import CompFold.
Require Import Array.
Require Import ESPADA_TSet_Once_Games.
Require Import HasDups.
Require Import PRF.

Local Open Scope list_scope.


Section ESPADA_TSet_Once_correct.
  
  Variable lambda : posnat.
  Variable tSize bigB bigS maxMatches : posnat.
  
  Variable F : Bvector lambda -> nat -> nat * Bvector lambda * Bvector (S lambda).
  Variable F_bar : Bvector lambda -> Blist -> Bvector lambda.
  
  Variable A1 : Comp ((T lambda * list Blist)).
  Hypothesis A1_wf : well_formed_comp A1.

  Variable maxKeywords : nat.
  
  Definition initFree := initFree bigB bigS.
  Definition ESPADA_TSetRetrieve := ESPADA_TSetRetrieve lambda F maxMatches.
  
  (* Inline and simplify *)
  Definition ESPADA_TSetCorr_G1 := 
    [t, l] <-$2 A1;
    [tSet_opt, k_T] <-$2 ESPADA_TSetSetup_trial bigB bigS F F_bar t;
    tSet <- getTSet tSet_opt;
    tags <- map (F_bar k_T) l;
    bad <- negb
        (eqb (foreach  (x in tags)ESPADA_TSetRetrieve tSet x)
             (foreach  (x in l)arrayLookupList (list_EqDec bool_EqDec) t x));
    ret ((if (tSet_opt) then true else false) && bad).
  
  Definition ESPADA_TSetSetup_tLoop_6 := 
    @ESPADA_TSetSetup_tLoop_6 lambda.
  
  (* Use part of the correctness proof to replace tags with random values. *)
  Definition ESPADA_TSetCorr_G3 :=
    [t, q] <-$2 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    inds <- map (fun x => lookupIndex (EqDec_dec _) allQs x O) q;
    allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
    ts <- map (arrayLookupList _ t) allQs;
    ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip allTags ts);
    loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_6) (Some (nil, initFree)) (flatten ts_recsList);
    tSet <- getTSet loopRes;
    tags <- map (fun i => nth i allTags (Vector.const false lambda)) inds;
    bad <- negb
        (eqb (foreach  (x in tags)ESPADA_TSetRetrieve tSet x)
             (foreach  (x in q)arrayLookupList (list_EqDec bool_EqDec) t x));
    ret ((if loopRes then true else false) && bad).

   (* Simplify.  We don't need to rebuild the list of queries and tags. *)
   Definition ESPADA_TSetCorr_G4 :=
     [t, q] <-$2 A1;
     q <- removeDups _ q;
     allQs <- combineKeywords q (toW t);
     allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
     ts <- map (arrayLookupList _ t) allQs;
     ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip allTags ts);
     loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_6) (Some (nil, initFree)) (flatten ts_recsList);
     tSet <- getTSet loopRes;
     tags <- firstn (length q) allTags;
     bad <- negb
         (eqb (foreach  (x in tags)ESPADA_TSetRetrieve tSet x)
             (foreach  (x in q)arrayLookupList (list_EqDec bool_EqDec) t x));
     ret ((if loopRes then true else false) && bad).

   (* Put everything into the T-Set (and the list used to create it) *)

   Definition TSetCorr_5_Record := (Bvector lambda * ((Blist * Bvector lambda * nat * nat * Bvector lambda * nat * Bvector (S lambda)) * (Bvector (S lambda))))%type.
   
   Definition TSetCorr_5 := list (list (option TSetCorr_5_Record)).
   
   Definition tSetUpdate_Corr_5(tSet : TSetCorr_5) (b j : nat)
              (r :  TSetCorr_5_Record) :=
     let bucket := nth b tSet nil in
     let bucket' := listReplace bucket j (Some r) None in
     listReplace tSet b bucket' nil.
   
   
   Definition ESPADA_TSetSetup_tLoop_Corr_5 (acc : TSetCorr_5 * FreeList)
              (e :  Blist * Bvector lambda * nat * nat * Vector.t bool lambda * nat * Bvector lambda *
                    Vector.t bool (S lambda)) :=
     [tSet, free]<-2 acc;
     (let '(q, tag, i, len, s_i, b, bigL, bigK) := e in
      free_b <- nth b free nil;
      opt_j <-$ RndListElem.rndListElem nat_EqDec free_b;
      match opt_j with
        | Some j =>
          free0 <-
                listReplace free b (removeFirst (EqDec_dec nat_EqDec) free_b j) nil;
        bet <- (if eq_nat_dec (S i) len then false else true);
        newRecord <- (bigL, ((q, tag, i, len, s_i, b, bigK), (Vector.cons bool bet lambda s_i xor bigK)));
        tSet0 <- tSetUpdate_Corr_5 tSet b j newRecord; ret Some (tSet0, free0)
                                                     | None => ret None
      end).
   
   Definition getTSet_Corr_5 (o : option (TSetCorr_5 * FreeList)) :=
     match o with
       | None => nil
       | Some p => fst p
     end.
   
   Definition ESPADA_TSetRetrieve_tLoop_Corr_5 (tSet : TSetCorr_5) stag i :=
    [b, L, K] <-3 F stag i;
     B <- nth b tSet nil;
     t <- arrayLookupOpt _ B L;
     match t with
       | None => None
       | Some p => 
         [_, u] <-2 p;
           v <- u xor K;
           bet <- Vector.hd v;
           s <- Vector.tl v;
           Some (s, bet)
    end.
   
   Fixpoint ESPADA_TSetRetrieve_h_Corr_5 (tSet : TSetCorr_5) stag i (fuel : nat) :=
     match fuel with
       | O => nil
       | S fuel' =>
         match (ESPADA_TSetRetrieve_tLoop_Corr_5 tSet stag i) with
           | Some (v, bet) =>
             v :: (if (bet) then (ESPADA_TSetRetrieve_h_Corr_5 tSet stag (S i) fuel') else nil)
          | None => nil
         end
     end.
   
  Definition ESPADA_TSetRetrieve_Corr_5 tSet stag :=
    ESPADA_TSetRetrieve_h_Corr_5 tSet stag O maxMatches.
  
  Definition ESPADA_TSetCorr_G5 :=
    [t, q] <-$2 A1;
    q <- removeDups _ q;
    allQs <- combineKeywords q (toW t);
    allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
    ts <- map (arrayLookupList _ t) allQs;
    ts_recsList <- map (fun p => [q, tag, ls] <-3 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (q, tag, i, len, s_i, b, bigL, bigK)) ls) (zip (zip allQs allTags) ts);
    loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_Corr_5) (Some (nil, initFree)) (flatten ts_recsList);
    tSet <- getTSet_Corr_5 loopRes;
    tags <- firstn (length q) allTags;
    bad <- negb
        (eqb (foreach  (x in tags)ESPADA_TSetRetrieve_Corr_5 tSet x)
             (foreach  (x in q)arrayLookupList (list_EqDec bool_EqDec) t x));
    ret ((if loopRes then true else false) && bad).

  (* Assume no collisions in labels within a bucket *)
  Fixpoint labelIn_6(ls : list (option TSetCorr_5_Record)) l :=
    match ls with
      | nil => false
      | o :: ls' =>
        match o with
          | None => labelIn_6 ls' l
          | Some (l', _) =>
            if (eqb l l') then true else (labelIn_6 ls' l)
        end
    end.
  
  
  Fixpoint bucketLabelCollision_6 (ls : list (option TSetCorr_5_Record)) :=
    match ls with
      | nil => false
      | o :: ls' =>
        match o with
          | None => bucketLabelCollision_6 ls' 
          | Some (l, _) =>
            labelIn_6 ls' l || bucketLabelCollision_6 ls'
        end
    end.
  
  
  Fixpoint labelCollision_6 (ls : list (list (option TSetCorr_5_Record))) :=
    match ls with
      | nil => false
      | b :: ls' =>
        bucketLabelCollision_6 b || labelCollision_6 ls'
    end.
  
  
  Definition ESPADA_TSetCorr_G6 :=
    [t, q] <-$2 A1;
    q <- removeDups _ q;
    allQs <- combineKeywords q (toW t);
    allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
    ts <- map (arrayLookupList _ t) allQs;
    ts_recsList <- map (fun p => [q, tag, ls] <-3 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (q, tag, i, len, s_i, b, bigL, bigK)) ls) (zip (zip allQs allTags) ts);
    loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_Corr_5) (Some (nil, initFree)) (flatten ts_recsList);
    tSet <- getTSet_Corr_5 loopRes;
    tags <- firstn (length q) allTags;
    bad <- negb
        (eqb (foreach  (x in tags)ESPADA_TSetRetrieve_Corr_5 tSet x)
             (foreach  (x in q)arrayLookupList (list_EqDec bool_EqDec) t x));
    ret ((if loopRes then true else false) && (labelCollision_6 (tSet) || bad)).

  (* Don't randomize order during TSet setup.  Always succeed (possibly by overfilling a bucket)*)
  Fixpoint labelIn_7(ls : list (TSetCorr_5_Record)) l :=
    match ls with
      | nil => false
      |  (l', _) :: ls' =>
         if (eqb l l') then true else (labelIn_7 ls' l)
    end.
  
  Fixpoint bucketLabelCollision_7 (ls : list ( TSetCorr_5_Record)) :=
    match ls with
      | nil => false
      | (l, _) :: ls' =>
        labelIn_7 ls' l || bucketLabelCollision_7 ls'
    end.
  
  
  Fixpoint labelCollision_7 (ls : list (list ( TSetCorr_5_Record))) :=
    match ls with
      | nil => false
      | b :: ls' =>
        bucketLabelCollision_7 b || labelCollision_7 ls'
    end.
  
  Definition TSetCorr_7 := list (list (TSetCorr_5_Record)).
  
  Definition ESPADA_TSetSetup_tLoop_Corr_7 (tSet : TSetCorr_7)
             (e :  Blist * Bvector lambda * nat * nat * Vector.t bool lambda * nat * Bvector lambda *
                   Vector.t bool (S lambda)) :=
    (let '(q, tag, i, len, s_i, b, bigL, bigK) := e in
     bet <- (if eq_nat_dec (S i) len then false else true);
     newRecord <- (bigL, ((q, tag, i, len, s_i, b, bigK), (Vector.cons bool bet lambda s_i xor bigK)));
     newBucket <- (nth b tSet nil) ++ (newRecord :: nil); 
     listReplace tSet b newBucket nil
    ).
  
  Definition ESPADA_TSetRetrieve_tLoop_Corr_7 (tSet : TSetCorr_7) stag i :=
    [b, L, K] <-3 F stag i;
    B <- nth b tSet nil;
    t <- arrayLookup _ B L;
    match t with
      | None => None
      | Some p => 
        [_, u] <-2 p;
          v <- u xor K;
          bet <- Vector.hd v;
          s <- Vector.tl v;
          Some (s, bet)
    end.

  Fixpoint ESPADA_TSetRetrieve_h_Corr_7 (tSet : TSetCorr_7) stag i (fuel : nat) :=
    match fuel with
      | O => nil
      | S fuel' =>
        match (ESPADA_TSetRetrieve_tLoop_Corr_7 tSet stag i) with
          | Some (v, bet) =>
            v :: (if (bet) then (ESPADA_TSetRetrieve_h_Corr_7 tSet stag (S i) fuel') else nil)
          | None => nil
        end
          
    end.
  
  Definition ESPADA_TSetRetrieve_Corr_7 tSet stag :=
    ESPADA_TSetRetrieve_h_Corr_7 tSet stag O maxMatches.
  
  Definition ESPADA_TSetCorr_G7 :=
    [t, q] <-$2 A1;
    q <- removeDups _ q;
    allQs <- combineKeywords q (toW t);
    allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
    ts <- map (arrayLookupList _ t) allQs;
    ts_recsList <- map (fun p => [q, tag, ls] <-3 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (q, tag, i, len, s_i, b, bigL, bigK)) ls) (zip (zip allQs allTags) ts);
    tSet <- fold_left ( ESPADA_TSetSetup_tLoop_Corr_7) (flatten ts_recsList) nil;
     tags <- firstn (length q) allTags;
     bad <- negb
         (eqb (foreach  (x in tags)ESPADA_TSetRetrieve_Corr_7 tSet x)
              (foreach  (x in q)arrayLookupList (list_EqDec bool_EqDec) t x));
     ret (labelCollision_7 ( tSet) || bad).

  (* flatten the list *)
  Definition TSetCorr_8_Record := ((nat * Bvector lambda) * ((Blist * Bvector lambda * nat * nat * Bvector lambda * nat * Bvector (S lambda)) * (Bvector (S lambda))))%type.
  
  Fixpoint labelIn_8 (Z : Set)(ls : list ((nat * Bvector lambda) * Z)) l :=
    match ls with
      | nil => false
      |  (l', _) :: ls' =>
         if (eqb l l') then true else (labelIn_8 ls' l)
    end.
  
  Fixpoint labelCollision_8 (Z : Set)(ls : list ((nat * Bvector lambda) * Z)) :=
    match ls with
      | nil => false
      | (l, _) :: ls' =>
        labelIn_8 ls' l || labelCollision_8 ls'
    end.
  
  Definition TSetCorr_8 := list (TSetCorr_8_Record).
  
    Definition ESPADA_TSetSetup_tLoop_Corr_8
               (e :  Blist * Bvector lambda * nat * nat * Vector.t bool lambda * nat * Bvector lambda *
                     Vector.t bool (S lambda)) :=
      (let '(q, tag, i, len, s_i, b, bigL, bigK) := e in
       ((b, bigL), ((q, tag, i, len, s_i, b, bigK), (Vector.cons bool (if eq_nat_dec (S i) len then false else true) lambda s_i xor bigK)))
      ).
    
    Definition ESPADA_TSetRetrieve_tLoop_Corr_8 (tSet : TSetCorr_8) stag i :=
      [b, L, K] <-3 F stag i;
      t <- arrayLookup _ tSet (b, L);
      match t with
        | None => None
        | Some p => 
          [_, u] <-2 p;
          v <- u xor K;
          bet <- Vector.hd v;
          s <- Vector.tl v;
          Some (s, bet)
      end.
    
    Fixpoint ESPADA_TSetRetrieve_h_Corr_8 (tSet : TSetCorr_8) stag i (fuel : nat) :=
      match fuel with
        | O => nil
        | S fuel' =>
        match (ESPADA_TSetRetrieve_tLoop_Corr_8 tSet stag i) with
          | Some (v, bet) =>
            v :: (if (bet) then (ESPADA_TSetRetrieve_h_Corr_8 tSet stag (S i) fuel') else nil)
          | None => nil
        end
      end.
    
    Definition ESPADA_TSetRetrieve_Corr_8 tSet stag :=
      ESPADA_TSetRetrieve_h_Corr_8 tSet stag O maxMatches.
    
    Definition ESPADA_TSetCorr_G8 :=
      [t, q] <-$2 A1;
      q <- removeDups _ q;
      allQs <- combineKeywords q (toW t);
      allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
      ts <- map (arrayLookupList _ t) allQs;
      ts_recsList <- map (fun p => [q, tag, ls] <-3 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (q, tag, i, len, s_i, b, bigL, bigK)) ls) (zip (zip allQs allTags) ts);
      tSet <- map ( ESPADA_TSetSetup_tLoop_Corr_8) (flatten ts_recsList) ;
      tags <- firstn (length q) allTags;
      bad <- negb
         (eqb (foreach  (x in tags)ESPADA_TSetRetrieve_Corr_8 tSet x)
              (foreach  (x in q)arrayLookupList (list_EqDec bool_EqDec) t x));
      ret (labelCollision_8 ( tSet) || bad).
    
    (* assume no collisions in tags or F output *)
    Definition labelCollision_9_tag t :=
      hasDups _ (map (F t) (allNatsLt maxMatches)).
    
    Fixpoint getAllLabels tags :=
      match tags with
        | nil => nil
        | t :: tags' =>
          (map (fun i => fst (F t i)) (allNatsLt (S maxMatches))) ++ (getAllLabels tags')
      end.
    
    Definition labelCollision_9 tags :=
      hasDups _ (getAllLabels tags).
    
    Definition ESPADA_TSetCorr_G9 :=
      [t, q] <-$2 A1;
      q <- removeDups _ q;
      allQs <- combineKeywords q (toW t);
      allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
      ts <- map (arrayLookupList _ t) allQs;
      ts_recsList <- map (fun p => [q, tag, ls] <-3 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (q, tag, i, len, s_i, b, bigL, bigK)) ls) (zip (zip allQs allTags) ts);
      tSet <- map ( ESPADA_TSetSetup_tLoop_Corr_8) (flatten ts_recsList) ;
      bad <- negb
          (eqb (foreach  (x in allTags)ESPADA_TSetRetrieve_Corr_8 tSet x)
               (foreach  (x in allQs)arrayLookupList (list_EqDec bool_EqDec) t x));
      ret ((labelCollision_9 allTags) || bad).

    (* use the stored values and counts rather than the encryptions *)
    Definition ESPADA_TSetRetrieve_tLoop_Corr_10 (tSet : TSetCorr_8) stag i :=
      [b, L, K] <-3 F stag i;
      t <- arrayLookup _ tSet (b, L);
      match t with
        | None => None
        | Some (q, tag, i, len, s_i, b, bigK, u) => 
          Some (s_i, if (eq_nat_dec (S i) len) then false else true)
      end.
    
    Fixpoint ESPADA_TSetRetrieve_h_Corr_10 (tSet : TSetCorr_8) stag i (fuel : nat) :=
      match fuel with
        | O => nil
        | S fuel' =>
          match (ESPADA_TSetRetrieve_tLoop_Corr_10 tSet stag i) with
            | Some (v, b) =>
              v :: (if b then (ESPADA_TSetRetrieve_h_Corr_10 tSet stag (S i) fuel') else nil)
            | None => nil
          end
      end.
    
    Definition ESPADA_TSetRetrieve_Corr_10 tSet stag :=
      ESPADA_TSetRetrieve_h_Corr_10 tSet stag O maxMatches.
    
    Definition ESPADA_TSetCorr_G10  :=
      [t, q] <-$2 A1;
      q <- removeDups _ q;
      allQs <- combineKeywords q (toW t);
      allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
      ts <- map (arrayLookupList _ t) allQs;
      ts_recsList <- map (fun p => [q, tag, ls] <-3 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (q, tag, i, len, s_i, b, bigL, bigK)) ls) (zip (zip allQs allTags) ts);
      tSet <- map ( ESPADA_TSetSetup_tLoop_Corr_8) (flatten ts_recsList) ;
      bad <- negb
          (eqb (foreach  (x in allTags)ESPADA_TSetRetrieve_Corr_10 tSet x)
               (foreach  (x in allQs)arrayLookupList (list_EqDec bool_EqDec) t x));
      ret ((labelCollision_9 allTags) || bad).
    

    (* Simplify *)
    Definition TSetCorr_11_Record := ((nat * Bvector lambda) * ((Blist * Bvector lambda * nat * nat * Bvector lambda)))%type.
    
    Definition TSetCorr_11 := list TSetCorr_11_Record.
    
    Definition ESPADA_TSetRetrieve_tLoop_Corr_11 (tSet : TSetCorr_11) stag i :=
      [b, L, K] <-3 F stag i;
      t <- arrayLookup _ tSet (b, L);
      match t with
        | None => None
        | Some (q, tag, i, len, s_i) => 
            Some (s_i, if (eq_nat_dec (S i) len) then false else true)
      end.
    
    Fixpoint ESPADA_TSetRetrieve_h_Corr_11 (tSet : TSetCorr_11) stag i (fuel : nat) :=
      match fuel with
        | O => nil
        | S fuel' =>
          match (ESPADA_TSetRetrieve_tLoop_Corr_11 tSet stag i) with
            | Some (v, b) =>
              v :: (if b then (ESPADA_TSetRetrieve_h_Corr_11 tSet stag (S i) fuel') else nil)
          | None => nil
          end
      end.
    
    Definition ESPADA_TSetRetrieve_Corr_11 tSet stag :=
      ESPADA_TSetRetrieve_h_Corr_11 tSet stag O maxMatches.
    
    Definition ESPADA_TSetCorr_G11  :=
      [t, q] <-$2 A1;
      q <- removeDups _ q;
      allQs <- combineKeywords q (toW t);
      allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
      ts <- map (arrayLookupList _ t) allQs;
      ts_recsList <- map (fun p => [q, tag, ls] <-3 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; ((b, bigL), (q, tag, i, len, s_i))) ls) (zip (zip allQs allTags) ts);
      tSet <- (flatten ts_recsList) ;
      bad <- negb
          (eqb (foreach  (x in allTags)ESPADA_TSetRetrieve_Corr_11 tSet x)
               (foreach  (x in allQs)arrayLookupList (list_EqDec bool_EqDec) t x));
      ret ((labelCollision_9 allTags) || bad).

    (* lookup by tag and index---this is the same as long as there are no collisions. *)
    Definition TSetCorr_12_Record := ((Bvector lambda * nat) * ((Blist  * nat * Bvector lambda)))%type.
    
    Definition TSetCorr_12 := list TSetCorr_12_Record.
    
    Definition ESPADA_TSetRetrieve_tLoop_Corr_12 (tSet : TSetCorr_12) stag i :=
      t <- arrayLookup _ tSet (stag, i);
      match t with
        | None => None
      | Some (q, len, s_i) => 
        Some (s_i, if (eq_nat_dec (S i) len) then false else true)
      end.
    
    Fixpoint ESPADA_TSetRetrieve_h_Corr_12 (tSet : TSetCorr_12) stag i (fuel : nat) :=
      match fuel with
        | O => nil
        | S fuel' =>
          match (ESPADA_TSetRetrieve_tLoop_Corr_12 tSet stag i) with
            | Some (v, b) =>
              v :: (if b then (ESPADA_TSetRetrieve_h_Corr_12 tSet stag (S i) fuel') else nil)
            | None => nil
          end
    end.
    
    Definition ESPADA_TSetRetrieve_Corr_12 tSet stag :=
      ESPADA_TSetRetrieve_h_Corr_12 tSet stag O maxMatches.
    
    Definition ESPADA_TSetCorr_G12  :=
      [t, q] <-$2 A1;
      q <- removeDups _ q;
      allQs <- combineKeywords q (toW t);
      allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
      ts <- map (arrayLookupList _ t) allQs;
      ts_recsList <- map (fun p => [q, tag, ls] <-3 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; ((tag, i), (q, len, s_i))) ls) (zip (zip allQs allTags) ts);
      tSet <- (flatten ts_recsList) ;
      bad <- negb
        (eqb (foreach  (x in allTags)ESPADA_TSetRetrieve_Corr_12 tSet x)
             (foreach  (x in allQs)arrayLookupList (list_EqDec bool_EqDec) t x));
      ret ((labelCollision_9 allTags) || bad).

    (* Look up using the keyword and index *)
    Definition TSetCorr_13_Record := ((Blist * nat) * (nat * (Bvector lambda)))%type.
    
    Definition TSetCorr_13 := list TSetCorr_13_Record.
    
    Definition ESPADA_TSetRetrieve_tLoop_Corr_13 (tSet : TSetCorr_13) q i :=
      t <- arrayLookup _ tSet (q, i);
      match t with
        | None => None
        | Some (len, s_i) => 
          Some (s_i, if (eq_nat_dec (S i) len) then false else true)
      end.
    
    Fixpoint ESPADA_TSetRetrieve_h_Corr_13 (tSet : TSetCorr_13) q i (fuel : nat) :=
      match fuel with
        | O => nil
        | S fuel' =>
          match (ESPADA_TSetRetrieve_tLoop_Corr_13 tSet q i) with
            | Some (v, b) =>
              v :: (if b then (ESPADA_TSetRetrieve_h_Corr_13 tSet q (S i) fuel') else nil)
            | None => nil
          end
      end.
    
    Definition ESPADA_TSetRetrieve_Corr_13 tSet q :=
      ESPADA_TSetRetrieve_h_Corr_13 tSet q O maxMatches.
    
    Definition ESPADA_TSetCorr_G13  :=
      [t, q] <-$2 A1;
      q <- removeDups _ q;
      allQs <- combineKeywords q (toW t);
      allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
      ts <- map (arrayLookupList _ t) allQs;
      ts_recsList <- map (fun p => [q, tag, ls] <-3 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; ((q, i), (len, s_i))) ls) (zip (zip allQs allTags) ts);
      tSet <- (flatten ts_recsList) ;
      bad <- negb
          (eqb (foreach  (x in allQs)ESPADA_TSetRetrieve_Corr_13 tSet x)
               (foreach  (x in allQs)arrayLookupList (list_EqDec bool_EqDec) t x));
      ret ((labelCollision_9 allTags) || bad).

    (* Now we can replace the retrieve function with a simple array lookup. *)
    Definition TSetCorr_14_Record := (Bvector lambda)%type.
    
    Definition TSetCorr_14 := list (Blist * list TSetCorr_14_Record).
    
    Definition ESPADA_TSetRetrieve_Corr_14 (tSet : TSetCorr_14) (q : Blist) :=
      arrayLookupList _ tSet q.
    
    Definition ESPADA_TSetCorr_G14  :=
      [t, q] <-$2 A1;
      q <- removeDups _ q;
      allQs <- combineKeywords q (toW t);
      allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
      ts <- map (arrayLookupList _ t) allQs;
      tSet <- combine allQs ts;
      bad <- negb
          (eqb (foreach  (x in allQs)ESPADA_TSetRetrieve_Corr_14 tSet x)
             (foreach  (x in allQs)arrayLookupList (list_EqDec bool_EqDec) t x));
      ret ((labelCollision_9 allTags) || bad).

    (* "bad" is always false.  Simplify *)  
    Definition ESPADA_TSetCorr_G15  :=
      [t, q] <-$2 A1;
      q <- removeDups _ q;
      allQs <- combineKeywords q (toW t);
      allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
      ret ((labelCollision_9 allTags)).


    (* factor out the calls to the PRF and prepare to apply the PRF definition. *)
    Definition PRFI_A1 :=
      [t, q] <-$2 A1;
      q <- removeDups _ q;
      allQs <- combineKeywords q (toW t);
      ret (map (fun _ => allNatsLt (S maxMatches)) allQs, tt).
    
    Definition PRFI_A2 (s : unit) (l : list (list (nat * Bvector lambda * Bvector (S lambda))))  :=
      ret (hasDups _ (fst (split (flatten l)))).
    
    Definition ESPADA_TSetCorr_G16  :=
      [lsD, s_A] <-$2 PRFI_A1;
      allLabels <-$ compMap _ (fun ls => k <-$ {0, 1}^lambda; ret (map (F k) ls)) lsD;
      PRFI_A2 s_A allLabels.
    
    (* Replace PRF with random function *)
    Definition RndF_R :=
      n <-$ RndNat bigB;
      l <-$ {0, 1}^lambda;
      k <-$ {0, 1}^(S lambda);
      ret (n, l, k).
    
    Definition ESPADA_TSetCorr_G17  :=
      [lsD, s_A] <-$2 PRFI_A1;
      allLabels <-$ compMap _ (fun lsD => [lsR, _] <-$2 oracleMap _ _ (RndR_func RndF_R _) nil lsD; ret lsR) lsD;
      PRFI_A2 s_A allLabels.
    
    (* No duplicates in input---replace random function output with random values *)
    Definition ESPADA_TSetCorr_G18  :=
      [t, q] <-$2 A1;
      q <- removeDups _ q;
      allQs <- combineKeywords q (toW t);
      lsD <- map (fun _ => allNatsLt (S maxMatches)) allQs;
      allLabels <-$ compMap _ (fun lsD => compMap _ (fun _ => RndF_R) lsD) lsD;
      ret (hasDups _ (fst (split (flatten allLabels)))).

    (* get labels for the maximum number of keywords *)
    Definition ESPADA_TSetCorr_G19 := 
      allLabels <-$ compMap _ (fun _ => b <-$ RndNat bigB; l <-$ {0, 1}^lambda; ret (b, l)) (allNatsLt (maxKeywords * (S maxMatches)));
      ret (hasDups _ allLabels).
    
    (* The chance of duplicates in labels is sufficiently small---ignore buckets. *)
    Definition ESPADA_TSetCorr_G20 := 
      allLabels <-$ compMap _ (fun _ => {0, 1}^lambda) (allNatsLt (maxKeywords * (S maxMatches)));
      ret (hasDups _ allLabels).


End ESPADA_TSet_Once_correct.