From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Soundness.LogicalRelation Require Import Definitions.

Ltac basic_invert_glu_sort_elem H :=
  progress simp glu_sort_elem in H;
  dependent destruction H;
  try rewrite <- glu_sort_elem_equation_1 in *.

Ltac basic_glu_sort_elem_econstructor :=
  progress simp glu_sort_elem;
  econstructor;
  try rewrite <- glu_sort_elem_equation_1 in *.

Ltac invert_glu_rel1 :=
  match goal with
  | H : pi_glu_typ_pred _ _ _ _ _ _ _ _ |- _ =>
      progressive_invert H
  | H : pi_glu_exp_pred _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      progressive_invert H
  | H : nat_glu_typ_pred _ _ _ _ |- _ =>
      progressive_invert H
  | H : nat_glu_exp_pred _ _ _ _ _ _ |- _ =>
      progressive_invert H
  | H : neut_glu_typ_pred _ _ _ _ |- _ =>
      progressive_invert H
  | H : neut_glu_exp_pred _ _ _ _ _ _ |- _ =>
      progressive_invert H
  end.

#[global]
Ltac simpl_glu_rel :=
  apply_equiv_left;
  repeat invert_glu_rel1;
  apply_equiv_left;
  destruct_all;
  gen_presups.
