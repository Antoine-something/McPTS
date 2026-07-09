From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Soundness Require Import LogicalRelation.
From McPTS.Core.Semantic Require Import Realizability.
Import Domain_Notations.

Lemma glu_rel_ctx_empty {P} (pred_P : PredicativeSig P) : {{ ⟪ pred_P ⟫ ⊩ ⋅ with nil}}.
Proof.
  do 2 econstructor; reflexivity.
Qed.

#[export]
  Hint Resolve glu_rel_ctx_empty : mcpts.

Lemma glu_rel_typ_to_wf_exp {P} (pred_P : PredicativeSig P) : forall {anns Γ A s},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ A @ s }} ->
    {{ Γ ⊢ A : Sort@s }}.
Proof.
  intros * [Sb].
  destruct_conjs.
  assert (exists env_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}) as [env_rel] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_rel }}) as [ρ] by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Γ ⊢s Id ® ρ ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto 3).
  assert (glu_rel_typ_with_sub pred_P s Γ A {{{ Id }}} ρ) by mauto 3.
  dependent destruction H4.
  assert {{ Γ ⊢ A[Id] : Sort@s }} by (eapply glu_sort_elem_sort_lvl; mauto 2).
  mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_typ_to_wf_exp : mcpts.

Lemma glu_rel_ctx_extend_sorted {P} (pred_P : PredicativeSig P) : forall {anns Γ A s},
    {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ, A with (so_Some s)::anns}}.
Proof.
  intros * [Sb] HA.
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩ A @ s }} by mauto 2.
  assert {{ Γ ⊢ A : Sort@s }} by mauto 4.
  inversion HA; subst.
  destruct_conjs.
  handle_functional_glu_ctx_env P.
  eexists.
  econstructor; mauto 3; try reflexivity.
Qed.

Lemma glu_rel_ctx_extend_unsorted {P} (pred_P : PredicativeSig P) : forall {anns Γ A},
    {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ, A with so_None::anns}}.
Proof.
  intros * [Sb] HA.
  inversion HA; subst.
  destruct_conjs.
  handle_functional_glu_ctx_env P.
  eexists.
  econstructor; mauto 3; try reflexivity.
Qed.

Lemma glu_rel_ctx_extend {P} (pred_P : PredicativeSig P) : forall {anns Γ A so},
    {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A @ so }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ, A with so::anns}}.
Proof.
  intros.
  destruct so;
    mauto 2 using glu_rel_ctx_extend_sorted, glu_rel_ctx_extend_unsorted.
Qed.

#[export]
  Hint Resolve glu_rel_ctx_extend : mcpts.
