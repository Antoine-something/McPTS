From Coq Require Import Morphisms_Relations RelationClasses.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import LogicalRelation SortCases.
Import Domain_Notations.

Lemma rel_exp_sub_cong {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ M M' A σ σ' Γ},
    {{ ⟪ pred_P ⟫ Δ ⊨ M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M[σ] ≈ M'[σ'] : A[σ] }}.
Proof with mautosolve.
  intros * [env_relΔ] [env_relΓ].
  destruct_conjs.
  pose env_relΔ.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eassumption).
  assert (env_relΓ ρ ρ) by (etransitivity; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  handle_per_sort_elem_irrel.
  match goal with
  | _: {{ ⟦ σ ⟧s ρ ↘ ^?ρ0 }},
      _: {{ ⟦ σ ⟧s ρ' ↘ ^?ρ'0 }} |- _ =>
      rename ρ0 into ρσ;
      rename ρ'0 into ρ'σ
  end.
  assert (env_relΔ ρσ ρ'σ) by (etransitivity; [|symmetry; eassumption]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp P).
  handle_per_sort_elem_irrel.
  eexists.
  split...
Qed.

#[export]
Hint Resolve rel_exp_sub_cong : mcpts.

Lemma rel_exp_sub_id {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M A},
    {{ ⟪ pred_P ⟫ Γ ⊨ M : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M[Id] ≈ M : A }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp P).
  eexists.
  split...
Qed.

#[export]
Hint Resolve rel_exp_sub_id : mcpts.

Lemma rel_exp_sub_compose {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ τ Γ' σ Γ'' M A},
    {{ ⟪ pred_P ⟫ Γ ⊨s τ : Γ' }} ->
    {{ ⟪ pred_P ⟫ Γ' ⊨s σ : Γ'' }} ->
    {{ ⟪ pred_P ⟫ Γ'' ⊨ M : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M[σ ∘ τ] ≈ M[σ][τ] : A[σ ∘ τ] }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΓ']]] [? [? [env_relΓ'']]] HM.
  destruct_conjs.
  invert_rel_exp HM.
  pose env_relΓ'.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eassumption).
  assert (env_relΓ ρ ρ) by (etransitivity; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  handle_per_sort_elem_irrel.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  handle_per_sort_elem_irrel.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ'').
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp P).
  handle_per_sort_elem_irrel.
  eexists.
  split; econstructor...
Qed.

#[export]
Hint Resolve rel_exp_sub_compose : mcpts.

Lemma rel_exp_conv {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' A A' s},
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : A' }}.
Proof with mautosolve.
  intros * [env_relΓ] HA.
  destruct_conjs.
  invert_rel_exp_of_typ HA.
  eexists_rel_exp.
  intros.
  assert (env_relΓ ρ ρ) by (etransitivity; [| symmetry]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@per_sort P).
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp P).
  handle_per_sort_elem_irrel.
  eexists.
  split; econstructor; mauto.
  etransitivity; [symmetry |].
Admitted.

#[export]
Hint Resolve rel_exp_conv : mcpts.

Lemma rel_exp_sym {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' A},
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M' ≈ M : A }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ); destruct_conjs.
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp P).
  handle_per_sort_elem_irrel.
  eexists.
  split; econstructor; mauto.
  symmetry...
Qed.

#[export]
Hint Resolve rel_exp_sym : mcpts.

Lemma rel_exp_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M1 M2 M3 A},
    {{ ⟪ pred_P ⟫ Γ ⊨ M1 ≈ M2 : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M2 ≈ M3 : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M1 ≈ M3 : A }}.
Proof with mautosolve.
  intros * [env_relΓ] HM2M3.
  destruct_conjs.
  invert_rel_exp HM2M3.
  eexists_rel_exp.
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eauto).
  assert (env_relΓ ρ' ρ') by (etransitivity; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ); destruct_conjs.
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp P).
  handle_per_sort_elem_irrel.
  eexists.
  split; econstructor; mauto.
  etransitivity...
Qed.

#[export]
Hint Resolve rel_exp_trans : mcpts.

#[export]
Instance rel_exp_PER {P : PtsSig} {pred_P : PredicativeSig P} {Γ A} : PER (rel_exp_under_ctx pred_P Γ A).
Proof.
  split; mauto.
Qed.

Lemma presup_rel_exp {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' A},
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ ⊨ Γ }} /\ {{ ⟪ pred_P ⟫ Γ ⊨ M : A }} /\ {{ ⟪ pred_P ⟫ Γ ⊨ M' : A }} /\ exists s, {{ ⟪ pred_P ⟫ Γ ⊨ A : Sort@s }}.
Proof.
  intros *.
  assert (Hpart : {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : A }} -> {{ ⟪ pred_P ⟫ Γ ⊨ M : A }} /\ {{ ⟪ pred_P ⟫ Γ ⊨ M' : A }})
    by (split; unfold valid_exp_under_ctx; etransitivity; [|symmetry|symmetry|]; eassumption).
  intros Hrel; repeat split;
    try solve [intuition]; clear Hpart;
    destruct Hrel as [env_relΓ];
    destruct_conjs.
  - eexists; eassumption.
  - destruct_by_head (@valid_exp_under_ctx P).
    destruct_conjs.
    eexists.
    eexists_rel_exp_of_typ.
    intros.
    (on_all_hyp: destruct_rel_by_assumption env_relΓ).
    eapply rel_typ_implies_rel_exp; eauto.
Qed.


(* Lemma rel_exp_eq_subtyp : forall Γ M M' A A', *)
(*     {{ Γ ⊨ M ≈ M' : A }} -> *)
(*     {{ Γ ⊨ A ⊆ A' }} -> *)
(*     {{ Γ ⊨ M ≈ M' : A' }}. *)
(* Proof. *)
(*   intros * [env_relΓ [? [i]]] [? [? [j]]]. *)
(*   pose env_relΓ. *)
(*   handle_per_ctx_env_irrel. *)
(*   eexists_rel_exp_with (max i j). *)
(*   intros. *)
(*   (on_all_hyp: destruct_rel_by_assumption env_relΓ). *)
(*   destruct_by_head rel_typ. *)
(*   destruct_by_head rel_exp. *)
(*   simplify_evals. *)
(*   eexists. *)
(*   split; econstructor; eauto using per_sort_elem_cumu_max_right. *)
(*   handle_per_sort_elem_irrel. *)
(*   eapply per_elem_subtyping_gen with (i := max i j); try eassumption. *)
(*   - eauto using per_subtyp_cumu_right. *)
(*   - eauto using per_sort_elem_cumu_max_right. *)
(*   - symmetry. eauto using per_sort_elem_cumu_max_right. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve rel_exp_eq_subtyp : mcpts. *)
