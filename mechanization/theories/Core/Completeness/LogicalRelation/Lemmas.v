From Coq Require Import Morphisms Morphisms_Relations RelationClasses Relation_Definitions.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness.LogicalRelation Require Import Definitions Tactics.
Import Domain_Notations.

Add Parametric Morphism {P : PtsSig} M ρ M' ρ' : (rel_exp M ρ M' ρ')
    with signature (@relation_equivalence (domain P)) ==> iff as rel_exp_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism {P : PtsSig} σ ρ σ' ρ' : (rel_sub σ ρ σ' ρ')
    with signature (@relation_equivalence (env P)) ==> iff as rel_sub_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; intuition.
Qed.

Lemma rel_exp_implies_rel_typ {P : PtsSig} {pred_P : PredicativeSig P} : forall {s A ρ A' ρ'},
    rel_exp A ρ A' ρ' (per_sort pred_P s) ->
    exists R, rel_typ pred_P s A ρ A' ρ' R.
Proof.
  intros.
  destruct_by_head (@rel_exp P).
  destruct_by_head (@per_sort P).
  mauto.
Qed.

#[export]
Hint Resolve rel_exp_implies_rel_typ : mcpts.

Lemma rel_typ_implies_rel_exp {P : PtsSig} {pred_P : PredicativeSig P} : forall {s A ρ A' ρ' R},
    rel_typ pred_P s A ρ A' ρ' R ->
    rel_exp A ρ A' ρ' (per_sort pred_P s).
Proof.
  intros.
  destruct_by_head (@rel_typ P).
  mauto.
Qed.

#[export]
Hint Resolve rel_typ_implies_rel_exp : mcpts.

Lemma rel_exp_clean_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ env_rel A M M'},
    {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : A }} ->
    exists s,
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
    exists (elem_rel : relation (domain P)),
      rel_typ pred_P s A ρ A ρ' elem_rel /\ rel_exp M ρ M' ρ' elem_rel.
Proof.
  intros * ? [].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists.
  eassumption.
Qed.

Ltac invert_rel_exp H :=
  (unshelve (epose proof (rel_exp_clean_inversion _ H); deex); shelve_unifiable; [eassumption |]; clear H)
  + dependent destruction H.
