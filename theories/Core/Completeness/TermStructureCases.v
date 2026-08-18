From Coq Require Import Morphisms_Relations RelationClasses.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import LogicalRelation SortCases.
Import Domain_Notations.


Lemma rel_exp_sub_cong {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ Γ' M M' A σ σ'},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ' ⊨u M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s σ ≈ σ' : Γ' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M[σ] ≈ M'[σ'] : A[σ] }}.
Proof with mautosolve.
  intros * [env_relΓ'] [env_relΓ].
  destruct_conjs.
  pose env_relΓ'.
  handle_per_ctx_env_irrel.
  eexists; split; [eassumption |].
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eassumption).
  assert (env_relΓ ρ ρ) by (etransitivity; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  handle_per_typ_elem_irrel.
  match goal with
  | _: {{ Δ ▶  ⟦ σ ⟧s ρ ↘ ^?ρ0 }},
      _: {{ Δ ▶  ⟦ σ ⟧s ρ' ↘ ^?ρ'0 }} |- _ =>
      rename ρ0 into ρσ;
      rename ρ'0 into ρ'σ
  end.
  assert (env_relΓ' ρσ ρ'σ) by (etransitivity; [|symmetry; eassumption]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  handle_per_typ_elem_irrel.

  eexists.
  split; mauto.
Qed.

#[export]
Hint Resolve rel_exp_sub_cong : mcpts.

Lemma rel_exp_sub_sort_rel_exp_no_sub {P} {pred_P : PredicativeSig P} : forall {Δ Γ A B σ s},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u A ≈ B : Sort@s[σ] }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u A ≈ B : Sort@s }}.
Proof.
  intros * [relΓ []].
  eexists; split; mauto 2.
  intros.
  specialize (H0 ρ ρ' equiv_ρ_ρ') as [elem_rel []].
  destruct H0.
  simplify_evals.
  assert (per_typ_elem pred_P Δ (per_sort pred_P Δ s) d{{{ Sort@s }}} d{{{ Sort@s }}}) by (econstructor; reflexivity).
  handle_per_typ_elem_irrel.
  eexists; split; mauto 2.
  econstructor; mauto 2.
Qed.

#[local]
Hint Resolve rel_exp_sub_sort_rel_exp_no_sub : mcpts.

Lemma rel_exp_sub_cong_sort {P} {pred_P : PredicativeSig P} : forall {Δ Γ Γ' A A' s σ σ'},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ' ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s σ ≈ σ' : Γ' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u A[σ] ≈ A'[σ'] : Sort@s }}.
Proof with mautosolve.
  intros.
  assert {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u A[σ] ≈ A'[σ'] : Sort@s[σ] }} by mauto 2.
  mauto 2.
Qed.

#[export]
Hint Resolve rel_exp_sub_cong_sort : mcpts.

Lemma rel_exp_sub_id {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ M A},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M : A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M[Id] ≈ M : A }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  eexists; split; [eassumption|].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  eexists.
  split...
Qed.

#[export]
Hint Resolve rel_exp_sub_id : mcpts.

Lemma rel_exp_sub_compose {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ τ Γ' σ Γ'' M A},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s τ : Γ' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ' ⊨s σ : Γ'' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ'' ⊨u M : A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M[σ ∘ τ] ≈ M[σ][τ] : A[σ ∘ τ] }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΓ']]] [? [? [env_relΓ'']]] HM.
  destruct_conjs.
  invert_rel_exp_unsorted HM.
  pose env_relΓ'.
  handle_per_ctx_env_irrel.
  eexists; split; [eassumption |].
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eassumption).
  assert (env_relΓ ρ ρ) by (etransitivity; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  handle_per_typ_elem_irrel.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  handle_per_typ_elem_irrel.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ'').
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  handle_per_typ_elem_irrel.
  eexists.
  split; econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_exp_sub_compose : mcpts.

Lemma rel_exp_sub_compose_sort {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ τ Γ' σ Γ'' A s},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s τ : Γ' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ' ⊨s σ : Γ'' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ'' ⊨u A : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u A[σ∘τ] ≈ A[σ][τ] : Sort@s }}.
Proof with mautosolve.
  intros.
  assert {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u A[σ∘τ] ≈ A[σ][τ] : Sort@s[σ∘τ] }} by mauto 2.
  mauto 2.
Qed.

#[export]
Hint Resolve rel_exp_sub_compose_sort : mcpts.


Lemma rel_exp_conv_typ {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ M M' A A'},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A ≈ A' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ M' : A' }}.
Proof with mautosolve.
  intros.
  invert_rel_exp_unsorted H;
    inversion_clear H0;
    destruct_conjs.
  rename x into env_relΓ.
  rename x0 into env_relΓ0.
  eexists.
  split; [eassumption|].
  assert (env_relΓ <~> env_relΓ0) by (eapply per_ctx_env_right_irrel; mauto).
  apply_relation_equivalence.

  intros.
  assert (equiv_ρ_ρ : env_relΓ ρ ρ) by (etransitivity; [|symmetry]; eassumption).
  assert (equiv_ρ'_ρ : env_relΓ ρ' ρ) by (symmetry; mauto).
  assert (equiv_ρ'_ρ' : env_relΓ ρ' ρ') by (etransitivity; [|symmetry]; eassumption).

  assert (exists elem_rel : relation (domain P), rel_typ_unsorted pred_P Δ A ρ A ρ' elem_rel /\ rel_exp Δ M ρ M' ρ' elem_rel) by mauto.
  assert (exists elem_rel : relation (domain P), rel_typ_unsorted pred_P Δ A ρ' A' ρ' elem_rel) by mauto.
  assert (exists elem_rel : relation (domain P), rel_typ_unsorted pred_P Δ A ρ A' ρ elem_rel) by mauto.
  destruct_conjs.
  eexists; split; mauto 2.

  destruct_by_head (@rel_typ_unsorted P).
  handle_per_typ_elem_irrel.
  econstructor; mauto.
  symmetry in H11.
  transitivity a1; mauto.
  transitivity a'1; mauto.
Qed.

Lemma rel_typ_implies_rel_typ_unsorted {P} {pred_P : PredicativeSig P} : forall {Δ Γ A A' s},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A ≈ A' }}.
Proof.
  intros * [relΓ []].
  eexists; split; mauto 2.
  intros.
  specialize (H0 _ _ equiv_ρ_ρ') as [elem_rel []].
  destruct H1.
  destruct H0.
  simplify_evals.
  assert (per_typ_elem pred_P Δ (per_sort pred_P Δ s) d{{{ Sort@s }}} d{{{ Sort@s }}}) by (eapply per_typ_sort; reflexivity).
  handle_per_typ_elem_irrel.
  destruct H3 as [].
  assert (per_typ_elem pred_P Δ x m m') by mauto 3.
  eexists.
  econstructor; mauto 2.
Qed.

Lemma rel_exp_conv {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ M M' A A' s},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ M' : A' }}.
Proof with mautosolve.
  intros.
  assert {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A ≈ A' }} by (eapply rel_typ_implies_rel_typ_unsorted; mauto 2).
  eapply rel_exp_conv_typ; mauto 2.
Qed.

#[export]
Hint Resolve rel_exp_conv : mcpts.

Lemma rel_exp_sym {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ M M' A},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M' ≈ M : A }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  eexists; split; [eassumption|].
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ); destruct_conjs.
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  handle_per_typ_elem_irrel.
  eexists.
  split; econstructor; mauto.

  eapply per_typ_elem_sym; mauto.
Qed.

#[export]
Hint Resolve rel_exp_sym : mcpts.

Lemma rel_exp_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ M1 M2 M3 A},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M1 ≈ M2 : A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M2 ≈ M3 : A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M1 ≈ M3 : A }}.
Proof with mautosolve.
  intros * [env_relΓ] HM2M3.
  destruct_conjs.
  invert_rel_exp_unsorted HM2M3.
  eexists; split; [eassumption |].
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eauto).
  assert (env_relΓ ρ' ρ') by (etransitivity; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ); destruct_conjs.
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  handle_per_typ_elem_irrel.
  eexists.
  split; econstructor; mauto.
  eapply per_typ_elem_trans; mauto.
Qed.

#[export]
Hint Resolve rel_exp_trans : mcpts.

#[export]
Instance rel_exp_unsorted_PER {P : PtsSig} {pred_P : PredicativeSig P} {Δ Γ A} : PER (rel_exp_under_ctx_unsorted pred_P Δ Γ A).
Proof.
  split; mauto.
Qed.

Lemma rel_typ_sort_refl {P} {pred_P : PredicativeSig P} : forall {Δ Γ s},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ Sort@s ≈ Sort@s }}.
Proof.
  intros * [env_relΓ].
  eexists; split; [eassumption|].
  intros.
  eexists.
  repeat (econstructor; mauto).
Qed.


Lemma rel_typ_of_rel_sort {P} {pred_P : PredicativeSig P} : forall {Δ Γ A A' s},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A ≈ A' }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists; split; [eassumption|].
  intros.
  assert (exists elem_rel : relation (domain P),
      rel_typ_unsorted pred_P Δ {{{ Sort@s }}} ρ {{{ Sort@s }}} ρ' elem_rel /\
      rel_exp Δ A ρ A' ρ' elem_rel) by mauto.
  destruct_conjs.


  destruct_by_head (@rel_typ_unsorted P).
  assert (per_typ_elem pred_P Δ (per_sort pred_P Δ s) a a').
  {
    inversion H2; inversion H4; subst.
    econstructor; reflexivity.
  }
  handle_per_typ_elem_irrel.
  specialize (H0 _ _ equiv_ρ_ρ') as [elem_rel []].
  destruct_by_head (@rel_exp).
  destruct_rel_typ_unsorted.
  simplify_evals.
  handle_per_typ_elem_irrel.
  destruct H11.
  assert (per_typ_elem pred_P Δ x m0 m'0) by mauto 3.
  eexists; mauto.  
Qed.

#[export]
Hint Resolve rel_typ_of_rel_sort : mcpts.

Lemma val_typ_of_val_sort {P} {pred_P : PredicativeSig P} : forall {Δ Γ A s},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u A : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A }}.
Proof.
  intros * HA.
  eapply rel_typ_of_rel_sort; mauto.
Qed.

#[export]
Hint Resolve val_typ_of_val_sort : mcpts.

Lemma rel_typ_sub_cong {P} {pred_P : PredicativeSig P} : forall {Δ Γ Γ' σ σ' A A'},
      {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s σ ≈ σ' : Γ' }} ->
      {{ ⟪ pred_P ⟫ Δ ▶ Γ' ⊨ A ≈ A' }} ->
      {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A[σ] ≈ A'[σ'] }}.
Proof.
  intros * [env_relΓ [? [env_relΔ]]] [?].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists; split; [eassumption|].
  intros.

  assert (rel_sub Δ σ ρ σ' ρ' env_relΔ) by mauto.
  destruct_by_head (@rel_sub P).
  assert (exists elem_rel : relation (domain P), rel_typ_unsorted pred_P Δ A ρσ A' ρ'σ' elem_rel) by mauto.
  destruct_conjs.
  destruct_by_head (@rel_typ_unsorted P).
  eexists; econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_typ_sub_cong : mcpts.

Lemma val_typ_sub {P} {pred_P : PredicativeSig P} : forall {Δ Γ Γ' σ A},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s σ : Γ' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ' ⊨ A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A[σ] }}.
Proof.
  intros * Hσ HA.
  eapply rel_typ_sub_cong; mauto.
Qed.

#[export]
Hint Resolve val_typ_sub : mcpts.

Lemma rel_typ_sub_compose {P} {pred_P : PredicativeSig P} : forall {Δ Γ τ Γ' σ Γ'' A},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s τ : Γ' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ' ⊨s σ : Γ'' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ'' ⊨ A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A[σ ∘ τ] ≈ A[σ][τ] }}.
Proof.
  intros * [env_relΓ [? [env_relΓ']]] [? [? [env_relΓ'']]] HA.
  destruct HA.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists; split; [eassumption |].

  intros.
  assert (rel_sub Δ τ ρ τ ρ' env_relΓ') by mauto.
  destruct_by_head (@rel_sub P).
  assert (rel_sub Δ σ ρσ σ ρ'σ' env_relΓ'') by mauto.
  destruct_by_head (@rel_sub P).
  assert (exists elem_rel : relation (domain P), rel_typ_unsorted pred_P Δ A ρσ0 A ρ'σ'0 elem_rel) by mauto.
  destruct_conjs.
  destruct_by_head (@rel_typ_unsorted P).

  eexists.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_typ_sub_compose : mcpts.

Lemma rel_typ_sub_id {P} {pred_P : PredicativeSig P} : forall {Δ Γ A},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A[Id] ≈ A }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists; split; [eassumption|].
  intros.
  assert (exists elem_rel : relation (domain P), rel_typ_unsorted pred_P Δ A ρ A ρ' elem_rel) by mauto.
  destruct_conjs.
  destruct_by_head (@rel_typ_unsorted).
  eexists; econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_typ_sub_id : mcpts.


Lemma rel_typ_sym {P} {pred_P : PredicativeSig P} {Δ Γ A B} :
  {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A ≈ B }} ->
  {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ B ≈ A }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists; split; [eassumption |].
  intros.
  symmetry in equiv_ρ_ρ'.
  assert (exists elem_rel : relation (domain P), rel_typ_unsorted pred_P Δ A ρ' B ρ elem_rel) by mauto.
  destruct_conjs.
  destruct_by_head (@rel_typ_unsorted P).
  exists H1.
  econstructor; mauto.
  symmetry.
  eassumption.
Qed.

#[export]
Hint Resolve rel_typ_sym : mcpts.

Lemma rel_typ_trans {P} {pred_P : PredicativeSig P} {Δ Γ A1 A2 A3} :
  {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A1 ≈ A2 }} ->
  {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A2 ≈ A3 }} ->
  {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A1 ≈ A3 }}.
Proof.
  intros * [env_relΓ] [env_relΓ'].
  destruct_conjs.
  handle_per_ctx_env_irrel.

  eexists; split; [eassumption|].
  intros.
  assert (equiv_ρ_ρ : env_relΓ ρ ρ) by (etransitivity; [|symmetry]; eassumption).
  assert (exists elem_rel : relation (domain P), rel_typ_unsorted pred_P Δ A1 ρ A2 ρ elem_rel) by mauto.
  assert (exists elem_rel : relation (domain P), rel_typ_unsorted pred_P Δ A2 ρ A3 ρ' elem_rel) by mauto.
  destruct_conjs.
  destruct_by_head (@rel_typ_unsorted).
  handle_per_typ_elem_irrel.
  eexists; econstructor; mauto.
  etransitivity; mauto.
Qed.

#[export]
Hint Resolve rel_typ_trans : mcpts.

#[export]
Instance rel_typ_under_ctx_PER {P : PtsSig} {pred_P : PredicativeSig P} {Δ Γ} : PER (rel_typ_under_ctx pred_P Δ Γ).
Proof.
  split; mauto.
Qed.

Lemma presup_rel_exp {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ M M' A},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ }} /\ {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M : A }} /\ {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M' : A }} /\ {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A }}.
Proof.
  intros *.
  assert (Hpart : {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ M' : A }} -> {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M : A }} /\ {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M' : A }}) by (split; unfold valid_exp_under_ctx_unsorted; etransitivity; [|symmetry|symmetry|]; eassumption).
  intros Hrel; repeat split;
    try solve [intuition]; clear Hpart;
    destruct Hrel as [env_relΓ];
    destruct_conjs.
  - eexists; eassumption.
  - destruct_by_head (@valid_exp_under_ctx_unsorted P).
    destruct_conjs.
    eexists_rel_exp_of_typ.
    intros.
    (on_all_hyp: destruct_rel_by_assumption env_relΓ).
    eapply rel_typ_unsorted_implies_rel_exp; eauto.
Qed.

#[export]
Hint Resolve presup_rel_exp : mcpts.

Lemma rel_exp_eq_subtyp{P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ M M' A A',
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A ⊆ A' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ M' : A' }}.
Proof.
  intros * HM [env_relΓ [? ?]].
  invert_rel_exp_unsorted HM.
  econstructor; split; try eassumption.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  simplify_evals.
  eexists.
  split; econstructor; eauto using per_sort_elem_cumu.
  handle_per_sort_elem_irrel.
  eapply per_elem_subtyping_gen; [| | | try eassumption].
  - eauto.
  - eauto using per_sort_elem_cumu.
  - symmetry.
    eauto using per_sort_elem_cumu.
Qed.

#[export]
Hint Resolve rel_exp_eq_subtyp : mcpts.
