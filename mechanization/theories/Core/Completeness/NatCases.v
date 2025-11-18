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
  eassumption.
Qed.

Lemma rel_exp_of_nat {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' s} {r : Ru_nat P s},
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
