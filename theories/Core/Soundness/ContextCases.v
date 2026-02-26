From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations.

Lemma glu_rel_ctx_empty {P} (pred_P : PredicativeSig P) : {{ ⟪ pred_P ⟫ ⊩ ⋅ }}.
Proof.
  do 2 econstructor; reflexivity.
Qed.

#[export]
Hint Resolve glu_rel_ctx_empty : mcpts.

Lemma glu_rel_ctx_extend {P} (pred_P : PredicativeSig P) : forall {Γ A s s'},
    {{ ⟪ pred_P ⟫ ⊩ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ A : Sort@s @ s' }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ, A@s }}.
Proof.
  intros * [Sb].
  intros HA.
  assert {{ Γ ⊢ A : Sort@s }} by mauto 3.
  inversion_clear HA.
  destruct_conjs.
  eexists.
  econstructor; mauto 3; try reflexivity.
Qed.

#[export]
Hint Resolve glu_rel_ctx_extend : mcpts.


Lemma glu_rel_ctx_extend_unsorted {P} (pred_P : PredicativeSig P) : forall {Γ A s so},
    {{ ⟪ pred_P ⟫ ⊩ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u A : Sort@s @ so }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ, A@s }}.
Proof.
  intros * [Sb] HA.
  assert {{ Γ ⊢ A : Sort@s }} by mauto 3.
  inversion_clear HA.
  destruct_conjs.
  eexists.
  econstructor; mauto 3; try reflexivity.
  intros.
  assert (glu_rel_exp_with_sub_unsorted pred_P so Δ A {{{ Sort@s }}} σ ρ) by mauto 3.
  dependent destruction H4.
  - inversion_clear H7.
    simpl_glu_rel.
    econstructor; mauto 3.
  - simplify_evals.
    invert_glu_sort_elem H6.
    simpl_glu_rel.
    unfold glu_sort_typ_rec in *.
    destruct_conjs.
    econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_ctx_extend_unsorted : mcpts.
