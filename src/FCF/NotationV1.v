Set Implicit Arguments.

Require Import Comp.

Local Open Scope comp_scope.

Notation "'ret' v" := (Ret (EqDec_dec _) v)
  (at level 75).

Notation "{ 0 , 1 } ^ n" := (Rnd n)
  (right associativity, at level 77) : comp_scope.

Notation "{ 0 , 1 }" := (Bind (Rnd 1) (fun m => ret (Vector.hd m)))
  (right associativity, at level 75) : comp_scope.

Notation "x <-$ c1 ; c2" := (@Bind _ _ c1%comp (fun x => c2)) 
  (right associativity, at level 81, c1 at next level) : comp_scope.

(* setLet enables "let" notation but ensures that the first type is in Set.  This helps check some errors in definitions. *)
Definition setLet(A : Set)(B : Type)(a : A)(f : A -> B) := f a.

Notation "x <- e1 ; e2" := (setLet e1 (fun x => e2)) (right associativity, at level 81, e1 at next level) : comp_scope.

Notation "[ x1 , x2 ] <-2 e1 ; c2" := (let '(x1, x2) := e1 in c2) (right associativity, at level 81, e1 at next level) : comp_scope.

Notation "[ x1 , x2 , x3 ] <-3 e1 ; c2" := (let '(x1, x2, x3) := e1 in c2) (right associativity, at level 81, e1 at next level) : comp_scope.

Notation "[ x1 , x2 , x3 , x4 ] <-4 e1 ; c2" := (let '(x1, x2, x3, x4) := e1 in c2) (right associativity, at level 81, e1 at next level) : comp_scope.

Notation "[ x1 , x2 , x3 , x4 , x5 ] <-5 e1 ; c2" := (let '(x1, x2, x3, x4, x5) := e1 in c2) (right associativity, at level 81, e1 at next level) : comp_scope.

Notation "[ x1 , x2 , x3 ] <-$3 c1 ; c2" := 
  (Bind c1%comp (fun z => let '(x1, x2, x3) := z in c2)) (right associativity, at level 81, c1 at next level, only parsing) : comp_scope.

Notation "[ x1 , x2 ] <-$2 c1 ; c2" := 
  (Bind c1%comp (fun z => let '(x1, x2) := z in c2)) (right associativity, at level 81, c1 at next level, only parsing) : comp_scope.


Notation "x <-? c1 ; c2" := (maybeBind c1 (fun x => (c2)))
                              (right associativity, at level 81, c1 at next level) : comp_scope.

Definition maybeBindComp(A B : Set)(eqdb : EqDec B)(c : Comp (option A))(f : A -> Comp B) : Comp (option B) :=
  opt_a <-$ c;
  match opt_a with
    | None => ret None
    | Some a => b <-$ (f a); ret (Some b)
  end.

Notation "x <-$? c1 ; c2" := 
   (maybeBindComp _ (c1)%comp (fun x => (c2)%comp))
                              (right associativity, at level 81, c1 at next level) : comp_scope.



Infix "xor" := (BVxor _) (at level 30).

Notation "x <--$ c1 ; c2" := (OC_Bind c1%comp (fun x => c2)) 
  (right associativity, at level 81, c1 at next level) : comp_scope.

Notation "[ x1 , x2 , x3 ] <--$3 c1 ; c2" := 
  (OC_Bind c1%comp (fun z => let '(x1, x2, x3) := z in c2)) (right associativity, at level 81, c1 at next level, only parsing) : comp_scope.

Notation "[ x1 , x2 ] <--$2 c1 ; c2" := 
  (OC_Bind c1%comp (fun z => let '(x1, x2) := z in c2)) (right associativity, at level 81, c1 at next level, only parsing) : comp_scope.

Notation "$ c" := (OC_Ret _ _ c) (at level 79) : comp_scope.