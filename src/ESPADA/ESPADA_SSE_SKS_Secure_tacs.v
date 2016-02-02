(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by a BSD-style		*
 * license that can be found in the LICENSE file at the root	*
 * of the source tree.						*)

Set Implicit Arguments.

Require Import FCF.
Require Import CompFold.
Require Import OracleCompFold.

Ltac skip := (inline_first; comp_skip; comp_simp).

Ltac identSkipSpec_l := eapply comp_spec_eq_trans_l; [eapply comp_spec_eq_symm; eapply comp_spec_right_ident | idtac]; comp_skip.

Ltac identSkipSpec_r := eapply comp_spec_eq_trans_r; [idtac | eapply comp_spec_right_ident]; comp_skip.

Ltac identSkip_l :=
  match goal with
    | [|- evalDist ?x _ == evalDist _ _] => rewrite <- (@evalDist_right_ident _ _ x); comp_skip
    | [|- comp_spec _ _ _ ] => identSkipSpec_l
  end.

Ltac identSkip_r :=
  match goal with
    | [|- evalDist _ _ == evalDist ?x _] => rewrite <- (@evalDist_right_ident _ _ x); comp_skip
    | [|- comp_spec _ _ _ ] => identSkipSpec_r
  end.

Ltac lpTac :=
  try match goal with
        | [|- list_pred _ ?a ?a] => eapply list_pred_eq
        | [H : list_pred (fun x y => snd x = y) _ _ |- _ ] => apply snd_split_eq_list_pred in H
        | [H : list_pred (fun x y => fst y = x) _ _ |- _ ] => apply list_pred_symm in H; apply fst_split_eq_list_pred in H 
        | [ |- map _ ?ls = combine ?ls (map _ ?ls) ] => rewrite combine_map_eq
        | [ |- map _ _  = map _ _ ] => eapply map_ext_pred
        | [ |- _] => eapply list_pred_combine_r
        | [ H : fst ?b = snd ?b |- _ ] => destruct b; simpl in *; subst
        | [ H : list_pred eq _ _ |- _] => eapply list_pred_eq_impl_eq in H; subst
        | [ |- list_pred _ _ (map _ _ )] => eapply list_pred_map_r
        | [ |- list_pred _ (map _ _ ) _] => eapply list_pred_map_l
    end; intuition; subst.

Ltac existTac :=
  match goal with
    | [H : Comp ?A |- ?A ] => eapply comp_base_exists; intuition
  end.

Ltac specTac :=
  try match goal with    
        | [ |- comp_spec _ _ _  ] => eapply comp_spec_eq_refl  
        | [ |- comp_spec _ (Bind _ _) (Bind _ _)] => comp_skip; try existTac
        | [ |- comp_spec _ (compMap _ _ _ ) (compMap _ _ _ ) ] => eapply compMap_spec  
        | [ |- comp_spec _ (Ret _ (?b, ?a)) (Ret _ ?a )] => eapply (comp_spec_ret _ _ (fun a b => snd a = b)); intuition
        | [|- comp_spec _ ?a ?a] => eapply comp_spec_consequence; [eapply comp_spec_eq_refl | intuition] 
        | [|- comp_spec eq ((evalDist_OC (oc_compMap _ _ _)) _ _ _ _) ((evalDist_OC (oc_compMap _ _ _)) _ _ _ _)] => eapply  oc_compMap_eq 
        | [|- comp_spec _ (compMap _ _ _) ((evalDist_OC (oc_compMap _ _ _)) _ _ _ _)] => eapply compMap_oc_spec
        | [|- comp_spec _ ((evalDist_OC (oc_compMap _ _ _)) _ _ _ _) (compMap _ _ _)] => eapply comp_spec_symm; eapply compMap_oc_spec
        | [H : eqb _ _ = true |- _] => rewrite eqb_leibniz in H
        | [|- comp_spec _ (?f ?a) (?f ?b) ] => case_eq (eqb a b); intuition
      end; try lpTac; subst.

Ltac distTac := 
  match goal with 
    | [H : eqb _ _ = true |- _] => rewrite eqb_leibniz in H
    | [H : negb _ = false |- _] => apply negb_false_iff in H
    | [ |- evalDist (Bind ?a _) _ == evalDist (Bind ?a _) _] => comp_skip
    | [H : ?a = ?b |- evalDist (Bind (?f ?a) _) _ == evalDist (Bind (?f ?b) _ ) _ ] => rewrite H
    | [H : ?a <> ?b |- evalDist (Bind (?f ?a) _) _ == evalDist (Bind (?f ?b) _ ) _ ] => comp_irr_l; comp_irr_r; repeat rewrite evalDist_ret_0; intuition; pairInv
    | [|- evalDist (Bind (?f ?a) _) _ == evalDist (Bind (?f ?b) _ ) _] => destruct (EqDec_dec _ a b)
    | [ |- evalDist (compMap _ _ _) _ == evalDist (compMap _ _ _) _ ] => eapply compMap_eq
  end.