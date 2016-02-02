(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
Set Implicit Arguments.

Require Import FCF.
Require Import CompFold.
Require Import TSet.
Require Import RndListElem.
Require Import List.
Require Import RndNat.
Require Import Array.
Require Import PRF.
Require Export ESPADA_TSet.

Section ESPADA_TSet_Games.

  Variable lambda : posnat.
  Variable tSize bigB bigS : posnat.
  Variable bucketSize : nat -> (posnat * posnat).
  Variable F : Bvector lambda -> nat -> nat * Bvector lambda * Bvector (S lambda).
  Variable F_bar : Bvector lambda -> Blist -> Bvector lambda.

  Definition TSet := (@TSet lambda).
  Definition ESPADA_TSetSetup_trial := (@ESPADA_TSetSetup_trial lambda bigB bigS F F_bar).
  Definition ESPADA_TSetSetup_tLoop := (@ESPADA_TSetSetup_tLoop lambda F).
  Definition ESPADA_TSetSetup_wLoop := (@ESPADA_TSetSetup_wLoop lambda F F_bar).
  Definition initFree := (@initFree bigB bigS).

  (* The adversary *)
  Variable A_State : Set.
  Hypothesis A_State_EqDec : EqDec A_State.
  Variable A1 : Comp (T lambda * list Blist * A_State).
  Variable A2 : A_State -> (option TSet) * list (Bvector lambda) -> Comp bool.

  Definition getTSet_opt(opt : option (TSet * FreeList)) :=
    match opt with
      | None => None
      | Some p => Some (fst p)
    end.

   Definition ESPADA_TSetSetup_once t := 
    [res, k_T] <-$2 ESPADA_TSetSetup_trial t;
    ret (getTSet_opt res, k_T).

   Definition randomTSetEntry (acc : TSet * FreeList) :=
    label <-$ {0, 1} ^ lambda;
    value <-$ {0, 1} ^ (S lambda);
    [tSet, free] <-2 acc;
    (* To match the actual setup routine, we choose b uniformly at random and fail if that bucket is empty. *)
    b <-$ [0 .. bigB);
    free_b <- nth b free nil;
    j <-$? (rndListElem _ free_b);
    free <- listReplace free b (removeFirst (EqDec_dec _) free_b j) nil;
    tSet <- tSetUpdate tSet b j (label, value);
    ret (tSet, free).

  Definition ESPADA_TSetSetup_Sim_wLoop (tSet_free : TSet * FreeList) e :=
    [tSet, free] <-2 tSet_free;
    [stag, t] <-2 e;
    ls <- zip (allNatsLt (length t)) t;
    loop_over ((tSet, free), ls) (ESPADA_TSetSetup_tLoop stag (length t)).


  Definition ESPADA_TSet_Sim_trial (leak : nat * list (nat))(ts : list (list (Bvector lambda))) :=
    [n, eqPattern ] <-2 leak;
    qTags <-$ foreach (_ in (removeDups _ eqPattern)) ({0, 1} ^ lambda);
    uniqueTs <- map (fun n => nth (firstIndexOf (EqDec_dec _ ) eqPattern n O) ts nil) (removeDups _ eqPattern);
    loopRes <-$ loop_over ((nil, initFree), (zip qTags uniqueTs)) ESPADA_TSetSetup_Sim_wLoop;
    loopRes <-$ loop_over* (loopRes, (allNatsLt (minus n (length (flatten uniqueTs))))) (fun acc i => randomTSetEntry acc);
    tags <- map (fun i => nth i qTags (Vector.const false lambda)) eqPattern;
    ret (loopRes, tags).

  Definition ESPADA_TSet_Sim (leak : nat * list nat)(ts : list (list (Bvector lambda))) :=
    [trialRes, tags] <-$2 Repeat (ESPADA_TSet_Sim_trial leak ts) (fun p => isSome (fst p));
    ret (getTSet trialRes, tags).
 
  Definition ESPADA_TSet_Sim_once (leak : nat * list nat)(ts : list (list (Bvector lambda))) :=
    [trialRes, tags] <-$2 ESPADA_TSet_Sim_trial leak ts;
    ret (getTSet_opt trialRes, tags).

  Definition bigN (bigT : T lambda) := 
    bigW <- toW bigT;
    fold_left (fun acc w => acc + length (arrayLookupList _ bigT w))%nat bigW O.

   Definition L_T bigT (q : list Blist) := 
     inds <- map (fun x => lookupIndex (EqDec_dec _) (removeDups _ q) x O) q;
     (bigN bigT, inds).

   (* The sequence of games starts from real and moves toward ideal. *)

   (* Step 1 : Inline and simplify. *)
   Definition ESPADA_TSet_1 :=
     [t, q, s_A]<-$3 A1;
     k_T <-$ {0, 1} ^ lambda;
     loopRes <-$ compFold _ (foldBody_option _ (ESPADA_TSetSetup_wLoop t k_T)) (Some (nil, initFree)) (toW t);
     tSet <- getTSet_opt loopRes;
     tags <- map (F_bar k_T) q;
     A2 s_A (tSet, tags).

   (* Step 2: pull out the stag computation and answer lookup.  We switch to the simulator setup loop because it happens to work here.  *)
   Definition ESPADA_TSet_2 :=
     [t, q, s_A]<-$3 A1;
     k_T <-$ {0, 1} ^ lambda;
     stags <- map (F_bar k_T) (toW t);
     ts <- map (arrayLookupList _ t) (toW t);
     loopRes <-$ compFold _ (foldBody_option _ (ESPADA_TSetSetup_Sim_wLoop)) (Some (nil, initFree)) (zip stags ts);
     tSet <- getTSet_opt loopRes;
     tags <- map (F_bar k_T) q;
     A2 s_A (tSet, tags).
   
   (* Step 3: initialize the TSet using all keywords -- including those that are in the the queries but not in the structure. *)
   Local Open Scope list_scope.
   
   
   Definition combineKeywords (q1 q2 : list Blist):=
     q1 ++ (removePresent (EqDec_dec _) q1 q2).
   
   Definition ESPADA_TSet_3 :=
     [t, q, s_A]<-$3 A1;
     allQs <- combineKeywords (toW t) (removeDups _ q);
     allTags <-$ (k_T <-$ {0, 1} ^ lambda; ret (map (F_bar k_T) allQs));
     inds <- map (fun x => lookupIndex (EqDec_dec _) allQs x O) q;
     ts <- map (arrayLookupList _ t) allQs;
     loopRes <-$ compFold _ (foldBody_option _ (ESPADA_TSetSetup_Sim_wLoop)) (Some (nil, initFree)) (zip allTags ts);
     tSet <- getTSet_opt loopRes;
     tags <- map (fun i => nth i allTags (Vector.const false lambda)) inds;
     A2 s_A (tSet, tags).
   
   (* Step 4 : flatten the list. *)
   Definition numberedMap(A B : Set)(f : nat -> nat -> A -> B)(ls : list A) :=
     map (fun p => [i, a] <-2 p; f i (length ls) a) (zip (allNatsLt (length ls)) ls).
   
   Definition ESPADA_TSetSetup_tLoop_4 (acc : TSet * FreeList) (e : nat * nat * Bvector lambda * Bvector lambda) :=
     [tSet, free] <-2 acc;
     let '(i, len, tag, s_i) := e in
     [b, bigL, bigK] <-3 F tag i;
       free_b <- nth b free nil;
       opt_j <-$ rndListElem _ (free_b);
    match opt_j with
      | None => ret None
      | Some j =>
        free <- listReplace free b (removeFirst (EqDec_dec _) free_b j) nil;
          bet <- if (eq_nat_dec (S i) len) then false else true;
                                                        newRecord <- (bigL, BVxor _ (Vector.cons _ bet _ s_i) bigK);
                                                        tSet <- tSetUpdate tSet b j newRecord; 
                                                        ret (Some (tSet, free))
    end.    

   Definition ESPADA_TSet_4 :=
     [t, q, s_A]<-$3 A1;
     allQs <- combineKeywords (toW t) (removeDups _ q);
     allTags <-$ (k_T <-$ {0, 1} ^ lambda; ret (map (F_bar k_T) allQs));
     inds <- map (fun x => lookupIndex (EqDec_dec _) allQs x O) q;
     ts <- map (arrayLookupList _ t) allQs;
     (* Put all the required information in each answer entry so we can flatten the list. *)
     ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => (i, len, tag, s_i)) ls) (zip allTags ts);
     loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_4) (Some (nil, initFree)) (flatten ts_recsList);
     tSet <- getTSet_opt loopRes;
     tags <- map (fun i => nth i allTags (Vector.const false lambda)) inds;
     A2 s_A (tSet, tags).

   (* Todo : fix the numbering *)
   
  (* Step 6 : factor out the inner PRF*)
  Definition ESPADA_TSetSetup_tLoop_6 (acc : TSet * FreeList) e :=
    [tSet, free] <-2 acc;
    let '(i, len, s_i, b, bigL, bigK) := e in
      free_b <- nth b free nil;
      opt_j <-$ rndListElem _ (free_b);
      match opt_j with
        | None => ret None
        | Some j =>
            free <- listReplace free b (removeFirst (EqDec_dec _) free_b j) nil;
            bet <- if (eq_nat_dec (S i) len) then false else true;
            newRecord <- (bigL, BVxor _ (Vector.cons _ bet _ s_i) bigK);
            tSet <- tSetUpdate tSet b j newRecord; 
            ret (Some (tSet, free))
    end. 

  Definition ESPADA_TSet_6 :=
    [t, q, s_A]<-$3 A1;
    allQs <- combineKeywords (toW t) (removeDups _ q);
    inds <- map (fun x => lookupIndex (EqDec_dec _) allQs x O) q;
    allTags <-$ (k_T <-$ {0, 1} ^ lambda; ret (map (F_bar k_T) allQs));
    ts <- map (arrayLookupList _ t) allQs;
    ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip allTags ts);
    loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_6) (Some (nil, initFree)) (flatten ts_recsList);
    tSet <- getTSet_opt loopRes;
    tags <- map (fun i => nth i allTags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).

  (* Step 7 : change the initialization order so that queried keywords are initialized first.  This makes the order match the simulator. *)
  Definition ESPADA_TSet_7 :=
    [t, q, s_A]<-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    inds <- map (fun x => lookupIndex (EqDec_dec _) allQs x O) q;
    allTags <-$ (k_T <-$ {0, 1} ^ lambda; ret (map (F_bar k_T) allQs));
    ts <- map (arrayLookupList _ t) allQs;
    ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip allTags ts);
    loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_6) (Some (nil, initFree)) (flatten ts_recsList);
    tSet <- getTSet_opt loopRes;
    tags <- map (fun i => nth i allTags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).

  
  (* Step 8 : replace the first PRF with a random function *)
  Definition F_bar_random := (@randomFunc Blist _ (Rnd lambda) _).
  Definition ESPADA_TSet_8 :=
    [t, q, s_A]<-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    inds <- map (fun x => lookupIndex (EqDec_dec _) allQs x O) q;
    [allTags, _] <-$2 oracleMap _ _ F_bar_random nil allQs;
    ts <- map (arrayLookupList _ t) allQs;
    ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip allTags ts);
    loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_6) (Some (nil, initFree)) (flatten ts_recsList);
    tSet <- getTSet_opt loopRes;
    tags <- map (fun i => nth i allTags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).

  (* Step 9 : There are no duplicates in the random function inputs, replace the outputs with random values *)
  Definition ESPADA_TSet_9 :=
    [t, q, s_A]<-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    inds <- map (fun x => lookupIndex (EqDec_dec _) allQs x O) q;
    allTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) allQs;
    ts <- map (arrayLookupList _ t) allQs;
    ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip allTags ts);
    loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_6) (Some (nil, initFree)) (flatten ts_recsList);
    tSet <- getTSet_opt loopRes;
    tags <- map (fun i => nth i allTags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).

  (* Step 10 : Split the init loop into two parts.  First initialize the queried keywords, then initialize the rest *)
  Definition ESPADA_TSet_10 :=
    [t, q, s_A]<-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
    q_ts <- map (arrayLookupList _ t) (removeDups _ q);
    q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip qTags q_ts);
    loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_6) (Some (nil, initFree)) (flatten q_ts_recsList);

    otherTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (skipn (length (removeDups _ q)) allQs);
    other_ts <- map (arrayLookupList _ t) (skipn (length (removeDups _ q)) allQs);
    other_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip otherTags other_ts);
    loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_6) loopRes (flatten other_ts_recsList);  
    inds <- map (fun x => lookupIndex (EqDec_dec _) allQs x O) q;
    tags <- map (fun i => nth i qTags (Vector.const false lambda)) inds;
    tSet <- getTSet_opt loopRes;
    A2 s_A (tSet, tags).

  (* Step 11 : We will replace F with a random function only where it is used to initialize non-queried keywords.  Start by calling the PRF in a way that matches the definition. *)
   Definition ESPADA_TSet_11 :=
     [t, q, s_A]<-$3 A1;
    allQs <- combineKeywords (removeDups _ q) (toW t);
    qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
    q_ts <- map (arrayLookupList _ t) (removeDups _ q);
    q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip qTags q_ts);
    loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_6) (Some (nil, initFree)) (flatten q_ts_recsList);
    
    other_ts <- map (arrayLookupList _ t) (skipn (length (removeDups _ q)) allQs);
    ins_F <- map (fun ls => allNatsLt (length ls)) other_ts;
    outs_F <-$ compMap _ (fun ls => k <-$ {0, 1}^lambda; ret (map (F k) ls)) ins_F;
    
    other_ts_recsList <- map (fun p => [locs, ls] <-2 p; numberedMap (fun i len loc_s_i => [loc, s_i] <-2 loc_s_i; [b, bigL, bigK] <-3 loc; (i, len, s_i, b, bigL, bigK)) (zip locs ls)) (zip outs_F other_ts);
    loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_6) loopRes (flatten other_ts_recsList);

    tSet <- getTSet_opt loopRes;
    inds <- map (fun x => lookupIndex (EqDec_dec _) allQs x O) q;
    tags <- map (fun i => nth i qTags (Vector.const false lambda)) inds;
    A2 s_A (tSet, tags).

   (* Step 12 : Replace PRF F with a random function. *)
   Definition RndF_range :=
      b <-$ [0 .. bigB);
      x <-$ {0, 1} ^ lambda;
      y <-$ {0, 1} ^ (S lambda);
      ret (b, x, y).
   Definition F_random := (@randomFunc nat _ (RndF_range) _).

   Definition ESPADA_TSet_12 :=
     [t, q, s_A]<-$3 A1;
     allQs <- combineKeywords (removeDups _ q) (toW t);
     qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
     q_ts <- map (arrayLookupList _ t) (removeDups _ q);
     q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip qTags q_ts);
     loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_6) (Some (nil, initFree)) (flatten q_ts_recsList);
     
     other_ts <- map (arrayLookupList _ t) (skipn (length (removeDups _ q)) allQs);
     ins_F <- map (fun ls => allNatsLt (length ls)) other_ts;
     outs_F <-$ compMap _ (fun lsD => [lsR, _] <-$2 oracleMap _ _ (F_random) nil lsD; ret lsR) ins_F;
     
     other_ts_recsList <- map (fun p => [locs, ls] <-2 p; numberedMap (fun i len loc_s_i => [loc, s_i] <-2 loc_s_i; [b, bigL, bigK] <-3 loc; (i, len, s_i, b, bigL, bigK)) (zip locs ls)) (zip outs_F other_ts);
     loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_6) loopRes (flatten other_ts_recsList);
     
     tSet <- getTSet_opt loopRes; 
     inds <- map (fun x => lookupIndex (EqDec_dec _) allQs x O) q;
     tags <- map (fun i => nth i qTags (Vector.const false lambda)) inds;
     A2 s_A (tSet, tags).
   
   (* Step 13 : There are no duplicates in the inputs to the random function (all inputs are the set of natural numbers less than k for some k), so we can replace the outputs with random values. *)

   Definition ESPADA_TSet_13 :=
     [t, q, s_A]<-$3 A1;
     allQs <- combineKeywords (removeDups _ q) (toW t);
     qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
     q_ts <- map (arrayLookupList _ t) (removeDups _ q);
     q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => [b, bigL, bigK] <-3 F tag i; (i, len, s_i, b, bigL, bigK)) ls) (zip qTags q_ts);
     loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_6) (Some (nil, initFree)) (flatten q_ts_recsList);
     other_ts <- map (arrayLookupList _ t) (skipn (length (removeDups _ q)) allQs);
     outs_F <-$ compMap _ (fun ls => compMap _ (fun _ => RndF_range) ls) other_ts;
     
     other_ts_recsList <- map (fun p => [locs, ls] <-2 p; numberedMap (fun i len loc_s_i => [loc, s_i] <-2 loc_s_i; [b, bigL, bigK] <-3 loc; (i, len, s_i, b, bigL, bigK)) (zip locs ls)) (zip outs_F other_ts);
     loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_6) loopRes (flatten other_ts_recsList);
     tSet <- getTSet_opt loopRes;
     inds <- map (fun x => lookupIndex (EqDec_dec _) allQs x O) q;
     tags <- map (fun i => nth i qTags (Vector.const false lambda)) inds;
     A2 s_A (tSet, tags).

   (* Step 14 : put the inner PRF calls (and random sampling) back into the inner loops. *)
   Definition ESPADA_TSetSetup_tLoop_14 (acc : TSet * FreeList) (e : nat * nat * Bvector lambda) :=
    [tSet, free] <-2 acc;
     let '(i, len, s_i) := e in
     b <-$ [0 .. bigB);
     bigL <-$ { 0 , 1 }^lambda; 
     enc_val <-$ (
               bigK <-$ { 0 , 1 }^S lambda;
               bet <- if (eq_nat_dec (S i) len) then false else true;
               ret (BVxor _ (Vector.cons _ bet _ s_i) bigK));
    free_b <- nth b free nil;
    opt_j <-$ rndListElem _ (free_b);
    match opt_j with
      | None => ret None
      | Some j =>
          free <- listReplace free b (removeFirst (EqDec_dec _) free_b j) nil;
          
          newRecord <- (bigL, enc_val);
          tSet <- tSetUpdate tSet b j newRecord; 
          ret (Some (tSet, free))
    end.    

   Definition ESPADA_TSet_14 :=
     [t, q, s_A]<-$3 A1;
     allQs <- combineKeywords (removeDups _ q) (toW t);
     qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
     q_ts <- map (arrayLookupList _ t) (removeDups _ q);
     q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => (i, len, tag, s_i)) ls) (zip qTags q_ts);
     loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_4) (Some (nil, initFree)) (flatten q_ts_recsList);
     other_ts <- map (arrayLookupList _ t) (skipn (length (removeDups _ q)) allQs);
     other_ts_recsList <- map (fun ls => numberedMap (fun i len e => (i, len, e)) ls) other_ts;
     loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_14) loopRes (flatten other_ts_recsList);
     tSet <- getTSet_opt loopRes;
     inds <- map (fun x => lookupIndex (EqDec_dec _) allQs x O) q;
     tags <- map (fun i => nth i qTags (Vector.const false lambda)) inds;
     A2 s_A (tSet, tags).


   (* Step 15 : Now we can replace the second part with a loop that creates random entries (as in the simulator) *)
   Definition ESPADA_TSetSetup_tLoop_15 (acc : TSet * FreeList) (e : nat * nat * Bvector lambda) :=
     [tSet, free] <-2 acc;
     b <-$ [0 .. bigB);
     bigL <-$ { 0 , 1 }^lambda; 
     bigK <-$ { 0 , 1 }^S lambda;
    (*  let '(len, i, s_i) := e in *)
       free_b <- nth b free nil;
       opt_j <-$ rndListElem _ (free_b);
       match opt_j with
         | None => ret None
         | Some j =>
           free <- listReplace free b (removeFirst (EqDec_dec _) free_b j) nil;
             tSet <- tSetUpdate tSet b j (bigL, bigK);
             ret (Some (tSet, free))
       end.  

   Definition ESPADA_TSet_15 :=
     [t, q, s_A]<-$3 A1;
     allQs <- combineKeywords (removeDups _ q) (toW t);
     qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
     q_ts <- map (arrayLookupList _ t) (removeDups _ q);
     q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => (i, len, tag, s_i)) ls) (zip qTags q_ts);
     loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_4) (Some (nil, initFree)) (flatten q_ts_recsList);
     other_ts <- map (arrayLookupList _ t) (skipn (length (removeDups _ q)) allQs);
     other_ts_recsList <- map (fun ls => numberedMap (fun i len e => (i, len, e)) ls) other_ts;
     loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_15) loopRes (flatten other_ts_recsList);
     tSet <- getTSet_opt loopRes;
     inds <- map (fun x => lookupIndex (EqDec_dec _) allQs x O) q;
     tags <- map (fun i => nth i qTags (Vector.const false lambda)) inds;
     A2 s_A (tSet, tags).
   
   (* Step 16 : After the one-time pad argument, many values are no longer used.  Simplify. *)

   Definition ESPADA_TSet_16 :=
     [t, q, s_A]<-$3 A1;
     allQs <- combineKeywords (removeDups _ q) (toW t);
     qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
     q_ts <- map (arrayLookupList _ t) (removeDups _ q);
     q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => (i, len, tag, s_i)) ls) (zip qTags q_ts);
     loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_4) (Some (nil, initFree)) (flatten q_ts_recsList);
     other_ts <- map (arrayLookupList _ t) (skipn (length (removeDups _ q)) allQs);
     loopRes <-$ compFold _ (foldBody_option _ (fun acc e => randomTSetEntry acc)) loopRes (flatten other_ts);
     tSet <- getTSet_opt loopRes;
     inds <- map (fun x => lookupIndex (EqDec_dec _) allQs x O) q;
     tags <- map (fun i => nth i qTags (Vector.const false lambda)) inds;
     A2 s_A (tSet, tags).

    (* Step 17 : don't look up answers for the non-queried keywords *)
   Definition ESPADA_TSet_17 :=
     [t, q, s_A]<-$3 A1;
     qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
     q_ts <- map (arrayLookupList _ t) (removeDups _ q);
     q_ts_recsList <- map (fun p => [tag, ls] <-2 p; numberedMap (fun i len s_i => (i, len, tag, s_i)) ls) (zip qTags q_ts);
     loopRes <-$ compFold _ (foldBody_option _ ESPADA_TSetSetup_tLoop_4) (Some (nil, initFree)) (flatten q_ts_recsList);
     loopRes <-$ compFold _ (foldBody_option _ (fun acc e => randomTSetEntry acc)) loopRes (allNatsLt (minus (bigN t) (length (flatten q_ts))));
     tSet <- getTSet_opt loopRes;
     inds <- map (fun x => lookupIndex (EqDec_dec _) (removeDups _ q) x O) q;
     tags <- map (fun i => nth i qTags (Vector.const false lambda)) inds;
     A2 s_A (tSet, tags).
   

  (* Step 18 : un-flatten the list in the first step *)
   Definition ESPADA_TSet_18 := 
     [t, q, s_A]<-$3 A1;
     qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ q);
     q_ts <- map (arrayLookupList _ t) (removeDups _ q);
     loopRes <-$ compFold _ (foldBody_option _ (ESPADA_TSetSetup_Sim_wLoop)) (Some (nil, initFree)) (zip qTags q_ts);
     loopRes <-$ compFold _ (foldBody_option _ (fun acc e => randomTSetEntry acc)) loopRes (allNatsLt (minus (bigN t) (length (flatten q_ts))));
     tSet <- getTSet_opt loopRes;
     inds <- map (fun x => lookupIndex (EqDec_dec _) (removeDups _ q) x O) q;
     tags <- map (fun i => nth i qTags (Vector.const false lambda)) inds;
     A2 s_A (tSet, tags).

   (* Step 19: use (the body of) the leakage function to produce the required information. *)
   Definition ESPADA_TSet_19 := 
     [t, q, s_A]<-$3 A1;
     ts <- map (arrayLookupList _ t) q;
     eqPattern <- map (fun x => lookupIndex (EqDec_dec _) (removeDups _ q) x O) q;
     qTags <-$ compMap _ (fun _ => {0, 1} ^ lambda) (removeDups _ eqPattern);

     q_ts <- map (fun n => nth (firstIndexOf (EqDec_dec _ ) eqPattern n O) ts nil) (removeDups _ eqPattern);

     loopRes <-$ compFold _ (foldBody_option _ (ESPADA_TSetSetup_Sim_wLoop)) (Some (nil, initFree)) (zip qTags q_ts);
     loopRes <-$ compFold _ (foldBody_option _ (fun acc e => randomTSetEntry acc)) loopRes (allNatsLt (minus (bigN t) (length (flatten q_ts))));
     tSet <- getTSet_opt loopRes;
     inds <- map (fun x => lookupIndex (EqDec_dec _) (removeDups _ q) x O) q;
     tags <- map (fun i => nth i qTags (Vector.const false lambda)) inds;
     A2 s_A (tSet, tags).

   (* The previous game is identical to the ideal functionality with the ESPADA TSet simulator and leakage function. *)


End ESPADA_TSet_Games.