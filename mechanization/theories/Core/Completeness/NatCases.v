From Coq Require Import Morphisms_Relations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import LogicalRelation SubstitutionCases TermStructureCases SortCases.
From McPTS.Core.Semantic Require Import Realizability.
Import Domain_Notations.

Lemma rel_exp_of_nat_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M'},
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : ℕ }} ->
    exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}),
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      rel_exp M ρ M' ρ' per_nat.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists.
  eexists; [eassumption |].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ P).
  invert_rel_typ_body.
  apply H3.
Qed.

Lemma rel_exp_unsorted_of_nat_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M'},
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : ℕ }} ->
    exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}),
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      rel_exp M ρ M' ρ' per_nat.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists.
  eexists; [eassumption |].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  invert_rel_typ_unsorted_body.
  invert_per_sort_elem H1.
  apply_relation_equivalence.
  apply H2.
Qed.

Lemma rel_exp_of_nat {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' s} {r : Ru_nat P s},
    (exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}),
      forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
        rel_exp M ρ M' ρ' per_nat) ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : ℕ }}.
Proof.
  intros * Hru [env_relΓ].
  destruct_conjs.
  eexists. 
  split.
  eassumption.
  intros.
  eexists.
  intros.
  eexists; split; mauto.
  econstructor; mauto.
  per_sort_elem_econstructor; mauto.
  reflexivity.
Qed.

Lemma rel_exp_unsorted_of_nat {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' s} {r : Ru_nat P s},
    (exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}),
      forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
        rel_exp M ρ M' ρ' per_nat) ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : ℕ }}.
Proof.
  intros * Hru [env_relΓ].
  destruct_conjs.
  eexists. 
  split.
  eassumption.
  intros.
  eexists; split; mauto.
  econstructor; mauto.
  econstructor; mauto.
  per_sort_elem_econstructor; mauto.
  reflexivity.
Qed.


#[export]
Hint Resolve rel_exp_unsorted_of_nat : mcpts.

Ltac eexists_rel_exp_unsorted_of_nat :=
  unshelve eapply (rel_exp_unsorted_of_nat _);
  shelve_unifiable;
  [eassumption| eexists; eexists ];
  [eassumption|];
intros.


Lemma valid_exp_unsorted_nat {P} {pred_P : PredicativeSig P} : forall {Γ s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ ⊨ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u ℕ : Sort@s }}.
Proof.
  intros * Hru [env_relΓ].
  eexists_rel_exp_untyped.
  intros.
  eexists; split; econstructor; mauto.
  econstructor; mauto. eexists; mauto.
  eexists; per_sort_elem_econstructor; mauto.
  reflexivity.
Qed.

#[export]
Hint Resolve valid_exp_unsorted_nat : mcpts.

Lemma rel_exp_unsorted_nat_sub {P} {pred_P : PredicativeSig P}: forall {Γ σ Δ s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u ℕ[σ] ≈ ℕ : Sort@s }}.
Proof.
  intros * Hru Hσ.
  invert_rel_sub Hσ env_relΓ.  
  eexists_rel_exp_of_sort.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor; mauto.
  eexists.
  per_sort_elem_econstructor; mauto.
  reflexivity.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_nat_sub : mcpts.

Lemma valid_exp_unsorted_zero {P} {pred_P : PredicativeSig P} : forall {Γ s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ ⊨ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u zero : ℕ }}.
Proof.
  intros * Hru [env_relΓ].
  apply (@rel_exp_unsorted_of_nat) with (s := s); mauto.
Qed.

#[export]
Hint Resolve valid_exp_unsorted_zero : mcpts.

Lemma rel_exp_unsorted_zero_sub {P} {pred_P : PredicativeSig P} : forall {Γ σ Δ s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u zero[σ] ≈ zero : ℕ }}.
Proof.
  intros * Hru Hσ.
  invert_rel_sub Hσ env_relΓ.    
  eexists_rel_exp_unsorted_of_nat.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_zero_sub : mcpts.

Lemma rel_exp_unsorted_succ_sub {P} {pred_P : PredicativeSig P} : forall {Γ σ Δ M s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨u M : ℕ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u (succ M)[σ] ≈ succ (M[σ]) : ℕ }}.
Proof.
  intros * Hru Hσ [env_relΔ]%rel_exp_unsorted_of_nat_inversion.
  destruct_all.
  invert_rel_sub Hσ.
  eexists_rel_exp_unsorted_of_nat.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_succ_sub : mcpts.

Lemma rel_exp_unsorted_succ_cong {P} {pred_P : PredicativeSig P} : forall {Γ M M' s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : ℕ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u succ M ≈ succ M' : ℕ }}.
Proof.
  intros * Hru [env_relΓ]%rel_exp_unsorted_of_nat_inversion.
  destruct_all.
  eexists_rel_exp_unsorted_of_nat.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_succ_cong : mcpts.

Lemma rel_exp_unsorted_of_sub_id_zero_inversion  {P} {pred_P : PredicativeSig P} : forall {Γ M M' A s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A[Id,,zero] }} ->
    exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}) s',
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
    exists elem_rel, rel_typ pred_P s' A d{{{ ρ ↦ zero }}} A d{{{ ρ' ↦ zero }}} elem_rel /\ rel_exp M ρ M' ρ' elem_rel.
Proof.
  intros * Hru HM.
  invert_rel_exp_unsorted HM env_relΓ.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  invert_rel_typ_unsorted_body.
  mauto.
Qed.

Lemma rel_exp_of_sub_id_zero : forall {Γ M M' A},
    (exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ env_rel }}) i,
      forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      exists elem_rel, rel_typ i A d{{{ ρ ↦ zero }}} A d{{{ ρ' ↦ zero }}} elem_rel /\ rel_exp M ρ M' ρ' elem_rel) ->
    {{ Γ ⊨ M ≈ M' : A[Id,,zero] }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  eexists.
  split; econstructor; mauto.
Qed.

Ltac eexists_rel_exp_of_sub_id_zero :=
  apply rel_exp_of_sub_id_zero;
  eexists_rel_exp.

Lemma rel_exp_of_sub_wkwk_succ_var1_inversion : forall {Γ M M' A},
    {{ Γ, ℕ, A ⊨ M ≈ M' : A[Wk∘Wk,,succ(#1)] }} ->
    exists env_rel (_ : {{ EF Γ, ℕ, A ≈ Γ, ℕ, A ∈ per_ctx_env ↘ env_rel }}) i,
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
    exists elem_rel, rel_typ i A d{{{ ρ ↯ ↯ ↦ succ ^(ρ 1) }}} A d{{{ ρ' ↯ ↯ ↦ succ ^(ρ' 1) }}} elem_rel /\ rel_exp M ρ M' ρ' elem_rel.
Proof.
  intros * HM.
  invert_rel_exp HM env_relΓℕA.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓℕA).
  destruct_by_head rel_typ.
  invert_rel_typ_body_nouip.
  mauto.
Qed.
