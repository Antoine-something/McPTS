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

Lemma rel_ctx_empty {P} {pred_P : PredicativeSig P} :
  {{ ⟪ pred_P ⟫ ⊨ ⋅ ≈ ⋅ }}.
Proof.
  apply valid_ctx_empty.
Qed.

#[export]
Hint Resolve rel_ctx_empty : mcpts.

Lemma rel_ctx_extend {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ Γ' A A' s},
    {{ ⟪ pred_P ⟫ ⊨ Γ ≈ Γ' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ ⊨ Γ, A@s ≈ Γ', A'@s }}.
Proof with intuition.
  intros * [] [env_relΓ]%rel_exp_unsorted_of_typ_inversion1.
  pose env_relΓ.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists.
  per_ctx_env_econstructor; eauto.
  - instantiate (1 := fun ρ ρ' (equiv_ρ_ρ' : env_relΓ ρ ρ') m m' =>
                        forall R,
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

Lemma rel_ctx_extend_het {P} {pred_P : PredicativeSig P} : forall {Γ Δ A A' s},
    {{ ⟪ pred_P ⟫ ⊨ Γ ≈ Δ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u A : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨u A : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨u A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ ⊨ Γ, A@s ≈ Δ, A'@s }}.
Proof.
  intros * [] [env_relΓ]%rel_exp_unsorted_of_typ_inversion1 []%rel_exp_unsorted_of_typ_inversion1
             [env_relΔ]%rel_exp_unsorted_of_typ_inversion1 []%rel_exp_unsorted_of_typ_inversion1
             []%rel_exp_unsorted_of_typ_inversion1 []%rel_exp_unsorted_of_typ_inversion1.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists.
  per_ctx_env_econstructor; eauto.
  - instantiate (1 := fun ρ ρ' (equiv_ρ_ρ' : x ρ ρ') m m' =>
                        forall R,
                          rel_typ pred_P s A ρ A' ρ' R ->
                          R m m').
    intros.
    (on_all_hyp: destruct_rel_by_assumption x).
    match_by_head (@per_sort P) ltac:(fun H => destruct H as [elem_relA]).
    econstructor; eauto.
    destruct_by_head (@per_sort P).
    simplify_evals.
    handle_per_sort_elem_irrel.
    apply -> per_sort_elem_morphism_iff; [apply H2 | reflexivity | reflexivity |].
    split; intros; destruct_by_head (@rel_typ P); handle_per_sort_elem_irrel;
      assert (rel_typ pred_P s A ρ A' ρ' x1) by mauto;
      intuition.
    
  - apply Equivalence_Reflexive.
Qed.

Lemma rel_ctx_extend' {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ A s},      
    {{ ⟪ pred_P ⟫ Γ ⊨u A : Sort@s }} ->
    {{ ⟪ pred_P ⟫ ⊨ Γ, A@s }}.
Proof.
  intros.
  eapply rel_ctx_extend; eauto.
  destruct H as [? []].
  eexists. eassumption.
Qed.

#[export]
Hint Resolve rel_ctx_extend rel_ctx_extend_het rel_ctx_extend' : mcpts.
