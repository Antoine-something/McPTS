From Coq Require Import Morphisms Morphisms_Relations RelationClasses Relation_Definitions.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness.LogicalRelation Require Import Definitions Tactics.
Import Domain_Notations.

Add Parametric Morphism {P : PtsSig} Δ M ρ M' ρ' : (rel_exp Δ M ρ M' ρ')
    with signature (@relation_equivalence (domain P)) ==> iff as rel_exp_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism {P : PtsSig} Δ σ ρ σ' ρ' : (rel_sub Δ σ ρ σ' ρ')
    with signature (@relation_equivalence (env P)) ==> iff as rel_sub_morphism.
Proof.
  intros R R' HRR'.
  split; intros []; econstructor; intuition.
Qed.

(* Lemma rel_exp_implies_rel_typ {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ s A ρ A' ρ'}, *)
(*     rel_exp Δ A ρ A' ρ' (per_sort pred_P Δ s) -> *)
(*     exists R, rel_typ pred_P Δ s A ρ A' ρ' R. *)
(* Proof. *)
(*   intros. *)
(*   destruct_by_head (@rel_exp P). *)
(*   destruct_by_head (@per_sort P). *)
(*   mauto. *)
(* Qed. *)

Lemma rel_exp_implies_rel_typ_unsorted {P} {pred_P : PredicativeSig P} : forall {Δ A ρ A' ρ'},
    rel_exp Δ A ρ A' ρ' (per_typ pred_P Δ) ->
    exists R, rel_typ_unsorted pred_P Δ A ρ A' ρ' R.
Proof.
  intros.
  destruct_by_head (@rel_exp P).
  destruct_by_head (@per_typ P).
  mauto.
Qed.

#[export]
Hint Resolve rel_exp_implies_rel_typ_unsorted : mcpts.

(* Lemma rel_typ_implies_rel_exp {P : PtsSig} {pred_P : PredicativeSig P} : forall {s A ρ A' ρ' R}, *)
(*     rel_typ pred_P s A ρ A' ρ' R -> *)
(*     rel_exp A ρ A' ρ' (per_sort pred_P s). *)
(* Proof. *)
(*   intros. *)
(*   destruct_by_head (@rel_typ P). *)
(*   mauto. *)
(* Qed. *)

Lemma rel_typ_unsorted_implies_rel_exp {P} {pred_P : PredicativeSig P} : forall {Δ A ρ A' ρ' R},
    rel_typ_unsorted pred_P Δ A ρ A' ρ' R ->
    rel_exp Δ A ρ A' ρ' (per_typ pred_P Δ).
Proof.
  intros.
  destruct_by_head (@rel_typ_unsorted P).
  mauto.
Qed.

#[export]
Hint Resolve rel_typ_unsorted_implies_rel_exp : mcpts.

(* Lemma rel_exp_clean_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ env_rel A M M'}, *)
(*     {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P Δ ↘ env_rel }} -> *)
(*     {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ M ≈ M' : A }} -> *)
(*     exists s, *)
(*     forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}), *)
(*     exists (elem_rel : relation (domain P)), *)
(*       rel_typ pred_P Δ s A ρ A ρ' elem_rel /\ rel_exp M ρ M' ρ' elem_rel. *)
(* Proof. *)
(*   intros * ? []. *)
(*   destruct_conjs. *)
(*   handle_per_ctx_env_irrel. *)
(*   eexists. *)
(*   eassumption. *)
(* Qed. *)

(* Ltac invert_rel_exp H := *)
(*   (unshelve (epose proof (rel_exp_clean_inversion _ H); deex); shelve_unifiable; [eassumption |]; clear H) *)
(*   + dependent destruction H. *)

Lemma rel_exp_unsorted_clean_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ env_rel A M M'},
    {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P Δ ↘ env_rel }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ M' : A }} ->
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
    exists (elem_rel : relation (domain P)),
      rel_typ_unsorted pred_P Δ A ρ A ρ' elem_rel /\ rel_exp Δ M ρ M' ρ' elem_rel.
Proof.
  intros * ? [].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eassumption.
Qed.

Ltac invert_rel_exp_unsorted_clean H :=
  (unshelve (epose proof (rel_exp_unsorted_clean_inversion _ H); deex); shelve_unifiable; [eassumption |]; clear H).

Tactic Notation "invert_rel_exp_unsorted" hyp(H) :=
  invert_rel_exp_unsorted_clean H
  + dependent destruction H.

Tactic Notation "invert_rel_exp_unsorted" hyp(H) simple_intropattern(l) :=
  invert_rel_exp_unsorted_clean H
  + (destruct H as [l [? H]]; deex_in H).

(* Lemma rel_exp_implies_rel_exp_unsorted {P} {pred_P : PredicativeSig P} : forall {Γ M M' A}, *)
(*     {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : A }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A }}. *)
(* Proof. *)
(*   intros. *)
(*   inversion_clear H. *)
(*   destruct_conjs. *)
(*   econstructor; split; mauto. *)
(*   intros. *)
(*   assert (exists elem_rel : relation (domain P), *)
(*              rel_typ pred_P H0 A ρ A ρ' elem_rel /\ rel_exp M ρ M' ρ' elem_rel) by mauto. *)
(*   destruct_conjs. *)
(*   eexists; split; mauto. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve rel_exp_implies_rel_exp_unsorted : mcpts. *)

Lemma rel_sub_clean_inversion1_left {P} {pred_P : PredicativeSig P} : forall {Δ Γ Γ' Γ'' env_relΓ σ σ'},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ env_relΓ }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s σ ≈ σ' : Γ'' }} ->
    exists env_relΓ'',
      {{ EF Γ'' ≈ Γ'' ∈ per_ctx_env pred_P Δ ↘ env_relΓ'' }} /\
        (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
            rel_sub Δ σ ρ σ' ρ' env_relΓ'').
Proof.
  intros * ? [].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists; eexists; [eassumption |].
  eassumption.
Qed.

Lemma rel_sub_clean_inversion1_right {P} {pred_P : PredicativeSig P} : forall {Δ Γ Γ' Γ'' env_relΓ σ σ'},
    {{ EF Γ' ≈ Γ ∈ per_ctx_env pred_P Δ ↘ env_relΓ }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s σ ≈ σ' : Γ'' }} ->
    exists env_relΓ'',
      {{ EF Γ'' ≈ Γ'' ∈ per_ctx_env pred_P Δ ↘ env_relΓ'' }} /\
        (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
            rel_sub Δ σ ρ σ' ρ' env_relΓ'').
Proof.
  intros * ? [].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists; eexists; [eassumption |].
  eassumption.
Qed.

Lemma rel_sub_clean_inversion2_left {P} {pred_P : PredicativeSig P} : forall {Δ Γ σ σ' Γ' Γ'' env_relΓ'},
    {{ EF Γ' ≈ Γ'' ∈ per_ctx_env pred_P Δ ↘ env_relΓ' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s σ ≈ σ' : Γ' }} ->
    exists env_relΓ,
      {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P Δ ↘ env_relΓ }} /\
        (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
            rel_sub Δ σ ρ σ' ρ' env_relΓ').
Proof.
  intros * ? [].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists; eexists; [eassumption |].
  eassumption.
Qed.

Lemma rel_sub_clean_inversion2_right {P} {pred_P : PredicativeSig P} : forall {Δ Γ σ σ' Γ' Γ'' env_relΓ'},
    {{ EF Γ'' ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ env_relΓ' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s σ ≈ σ' : Γ' }} ->
    exists env_relΓ,
      {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P Δ ↘ env_relΓ }} /\
        (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
            rel_sub Δ σ ρ σ' ρ' env_relΓ').
Proof.
  intros * ? [].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists; eexists; [eassumption |].
  eassumption.
Qed.

Lemma rel_sub_clean_inversion3_left_left {P} {pred_P : PredicativeSig P} : forall {Δ Γ1 Γ1' env_relΓ1 σ σ' Γ2 Γ2' env_relΓ2},
    {{ EF Γ1 ≈ Γ1' ∈ per_ctx_env pred_P Δ ↘ env_relΓ1 }} ->
    {{ EF Γ2 ≈ Γ2' ∈ per_ctx_env pred_P Δ ↘ env_relΓ2 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ1 ⊨s σ ≈ σ' : Γ2 }} ->
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ1 }}),
      rel_sub Δ σ ρ σ' ρ' env_relΓ2.
Proof.
  intros * HΓ ?.
  intros []%(rel_sub_clean_inversion1_left HΓ).
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eassumption.
Qed.

Lemma rel_sub_clean_inversion3_left_right {P} {pred_P : PredicativeSig P} : forall {Δ Γ1 Γ1' env_relΓ1 σ σ' Γ2 Γ2' env_relΓ2},
    {{ EF Γ1 ≈ Γ1' ∈ per_ctx_env pred_P Δ ↘ env_relΓ1 }} ->
    {{ EF Γ2' ≈ Γ2 ∈ per_ctx_env pred_P Δ ↘ env_relΓ2 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ1 ⊨s σ ≈ σ' : Γ2 }} ->
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ1 }}),
      rel_sub Δ σ ρ σ' ρ' env_relΓ2.
Proof.
  intros * HΓ ?.
  intros []%(rel_sub_clean_inversion1_left HΓ).
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eassumption.
Qed.

Lemma rel_sub_clean_inversion3_right_left {P} {pred_P : PredicativeSig P}  : forall {Δ Γ1 Γ1' env_relΓ1 σ σ' Γ2 Γ2' env_relΓ2},
    {{ EF Γ1' ≈ Γ1 ∈ per_ctx_env pred_P Δ ↘ env_relΓ1 }} ->
    {{ EF Γ2 ≈ Γ2' ∈ per_ctx_env pred_P Δ ↘ env_relΓ2 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ1 ⊨s σ ≈ σ' : Γ2 }} ->
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ1 }}),
      rel_sub Δ σ ρ σ' ρ' env_relΓ2.
Proof.
  intros * HΓ ?.
  intros []%(rel_sub_clean_inversion1_right HΓ).
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eassumption.
Qed.

Lemma rel_sub_clean_inversion3_right_right {P} {pred_P : PredicativeSig P} : forall {Δ Γ1 Γ1' env_relΓ1 σ σ' Γ2 Γ2' env_relΓ2},
    {{ EF Γ1' ≈ Γ1 ∈ per_ctx_env pred_P Δ ↘ env_relΓ1 }} ->
    {{ EF Γ2' ≈ Γ2 ∈ per_ctx_env pred_P Δ ↘ env_relΓ2 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ1 ⊨s σ ≈ σ' : Γ2 }} ->
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ1 }}),
      rel_sub Δ σ ρ σ' ρ' env_relΓ2.
Proof.
  intros * HΓ ?.
  intros []%(rel_sub_clean_inversion1_right HΓ).
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eassumption.
Qed.

Ltac invert_rel_sub_clean H :=
  let H' := fresh "H" in
  (unshelve (epose proof (rel_sub_clean_inversion3_left_left _ _ H) as H'); shelve_unifiable; [eassumption | eassumption |]; clear H)
  + (unshelve (epose proof (rel_sub_clean_inversion3_left_right _ _ H) as H'); shelve_unifiable; [eassumption | eassumption |]; clear H)
  + (unshelve (epose proof (rel_sub_clean_inversion3_right_left _ _ H) as H'); shelve_unifiable; [eassumption | eassumption |]; clear H)
  + (unshelve (epose proof (rel_sub_clean_inversion3_right_right _ _ H) as H'); shelve_unifiable; [eassumption | eassumption |]; clear H)
  + (unshelve (epose proof (rel_sub_clean_inversion2_left _ H) as H'; deex_in H'; destruct H'); shelve_unifiable; [eassumption |]; clear H)
  + (unshelve (epose proof (rel_sub_clean_inversion2_right _ H) as H'; deex_in H'; destruct H'); shelve_unifiable; [eassumption |]; clear H)
  + (unshelve (epose proof (rel_sub_clean_inversion1_left _ H) as H'; deex_in H'; destruct H'); shelve_unifiable; [eassumption |]; clear H)
  + (unshelve (epose proof (rel_sub_clean_inversion1_right _ H) as H'; deex_in H'; destruct H'); shelve_unifiable; [eassumption |]; clear H).

Tactic Notation "invert_rel_sub" hyp(H) :=
  invert_rel_sub_clean H
  + (simpl in H; unfold rel_sub_under_ctx in H; do 2 (deex_in H; destruct H as [? H])).

Tactic Notation "invert_rel_sub" hyp(H) simple_intropattern(l) :=
  invert_rel_sub_clean H
  + (destruct H as [l [? H]]; deex_in H; destruct H as []).
