From Coq Require Import Morphisms_Relations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import LogicalRelation SortCases.
Import Domain_Notations.

Proposition valid_ctx_empty {P : PtsSig} {pred_P : PredicativeSig P} :
  {{ ⟪ pred_P ⟫ ⊨ ⋅ }}.
Proof.
  do 2 econstructor.
  apply Equivalence_Reflexive.
Qed.

#[export]
Hint Resolve valid_ctx_empty : mcpts.

Lemma rel_ctx_extend {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ Γ' A A' s},
    {{ ⟪ pred_P ⟫ ⊨ Γ ≈ Γ' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ ⊨ Γ, A::Sort@s ≈ Γ', A'::Sort@s }}.
Proof with intuition.
  intros * [] [env_relΓ]%rel_exp_of_typ_inversion1.
  pose env_relΓ.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists.
  per_ctx_env_econstructor; eauto.
  - instantiate (1 := fun ρ ρ' (equiv_ρ_ρ' : env_relΓ ρ ρ') m m' =>
                        forall s R,
                          rel_typ pred_P s A ρ A' ρ' R ->
                          R m m').
    intros.
    (on_all_hyp: destruct_rel_by_assumption env_relΓ).
    match_by_head (@per_sort P) ltac:(fun H => destruct H as [elem_relA]).
    econstructor; eauto.
    apply -> per_sort_elem_morphism_iff; eauto.
    split; intros; destruct_by_head (@rel_typ P); handle_per_sort_elem_irrel...
    assert (rel_typ pred_P s A ρ A' ρ' elem_relA) by mauto.
    intuition.
  - apply Equivalence_Reflexive.
Qed.


Lemma rel_ctx_extend_unsorted {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ Γ' A A' s},
    {{ ⟪ pred_P ⟫ ⊨ Γ ≈ Γ' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ ⊨ Γ, A::Sort@s ≈ Γ', A'::Sort@s }}.
Proof with intuition.
  intros * [] [env_relΓ]%rel_exp_unsorted_of_typ_inversion1.
  pose env_relΓ.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists.
  per_ctx_env_econstructor; eauto.
  - instantiate (1 := fun ρ ρ' (equiv_ρ_ρ' : env_relΓ ρ ρ') m m' =>
                        forall s R,
                          rel_typ pred_P s A ρ A' ρ' R ->
                          R m m').
    intros.
    (on_all_hyp: destruct_rel_by_assumption env_relΓ).
    match_by_head (@per_sort P) ltac:(fun H => destruct H as [elem_relA]).
    econstructor; eauto.
    apply -> per_sort_elem_morphism_iff; eauto.
    split; intros; destruct_by_head (@rel_typ P); handle_per_sort_elem_irrel...
    assert (rel_typ pred_P s A ρ A' ρ' elem_relA) by mauto.
    intuition.
  - apply Equivalence_Reflexive.
Qed.


Lemma rel_ctx_extend' {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ A s},
    {{ ⟪ pred_P ⟫ Γ ⊨ A : Sort@s }} ->
    {{ ⟪ pred_P ⟫ ⊨ Γ, A::Sort@s }}.
Proof.
  intros.
  eapply rel_ctx_extend; eauto.
  destruct H as [? []].
  eexists. eassumption.
Qed.

#[export]
Hint Resolve rel_ctx_extend rel_ctx_extend_unsorted rel_ctx_extend' : mcpts.
