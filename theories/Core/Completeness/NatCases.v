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


Ltac invert_rel_exp_2 H l :=
  (unshelve (epose proof (rel_exp_clean_inversion _ H); deex); shelve_unifiable; [eassumption |]; clear H)
    + (destruct H as [l [? H]]; deex_in H).



Lemma rel_exp_of_sub_id_zero_inversion  {P} {pred_P : PredicativeSig P} : forall {Γ M M' A},
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : A[Id,,zero] }} ->
    exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}) s,
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
    exists elem_rel, rel_typ pred_P s A d{{{ ρ ↦ zero }}} A d{{{ ρ' ↦ zero }}} elem_rel /\ rel_exp M ρ M' ρ' elem_rel.
Proof.
  intros * HM.
  invert_rel_exp_2 HM env_relΓ.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ P).
  simplify_evals.
  mauto.
Qed.


Lemma rel_exp_unsorted_of_sub_id_zero_inversion  {P} {pred_P : PredicativeSig P} : forall {Γ M M' A},
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A[Id,,zero] }} ->
    exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}),
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
    exists elem_rel, rel_typ_unsorted pred_P A d{{{ ρ ↦ zero }}} A d{{{ ρ' ↦ zero }}} elem_rel /\ rel_exp M ρ M' ρ' elem_rel.
Proof.
  intros * HM.
  invert_rel_exp_unsorted HM env_relΓ.
  eexists_rel_exp_untyped.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  simplify_evals.
  mauto.
Qed.

Lemma rel_exp_unsorted_of_sub_id_zero {P} {pred_P : PredicativeSig P} : forall {Γ M M' A},
    (exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}),
      forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      exists elem_rel, rel_typ_unsorted pred_P A d{{{ ρ ↦ zero }}} A d{{{ ρ' ↦ zero }}} elem_rel /\ rel_exp M ρ M' ρ' elem_rel) ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A[Id,,zero] }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp_untyped.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  eexists.
  split; econstructor; mauto.
Qed.

Ltac eexists_rel_exp_unsorted_of_sub_id_zero :=
  apply rel_exp_unsorted_of_sub_id_zero;
  eexists_rel_exp_untyped.


Lemma rel_exp_of_sub_wkwk_succ_var1_inversion {P} {pred_P : PredicativeSig P} : forall {Γ M M' A s s'} (r : Ru_nat P s),
    {{ ⟪ pred_P ⟫ Γ, ℕ@s, A@s' ⊨ M ≈ M' : A[Wk∘Wk,,succ(#1)] }} ->
    exists env_rel (_ : {{ EF Γ, ℕ@s, A@s' ≈ Γ, ℕ@s, A@s' ∈ per_ctx_env pred_P ↘ env_rel }}) s'',
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}) d d',
      env_lookup ρ 1 d -> env_lookup ρ' 1 d' ->
    exists elem_rel, rel_typ pred_P s'' A d{{{ ρ ↯ ↯ ↦ succ d }}} A d{{{ ρ' ↯ ↯ ↦ succ d' }}} elem_rel /\ rel_exp M ρ M' ρ' elem_rel.
Proof.
  intros * ? HM.
  invert_rel_exp_2 HM env_relΓℕA.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓℕA).
  destruct_by_head (@rel_typ P).
  invert_rel_typ_body.
  mauto.
Qed.

Lemma rel_exp_unsorted_of_sub_wkwk_succ_var1_inversion {P} {pred_P : PredicativeSig P} : forall {Γ M M' A s s'} (r : Ru_nat P s),
    {{ ⟪ pred_P ⟫ Γ, ℕ@s, A@s' ⊨u M ≈ M' : A[Wk∘Wk,,succ(#1)] }} ->
    exists env_rel (_ : {{ EF Γ, ℕ@s, A@s' ≈ Γ, ℕ@s, A@s' ∈ per_ctx_env pred_P ↘ env_rel }}),
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}) d d',
      env_lookup ρ 1 d -> env_lookup ρ' 1 d' ->
    exists elem_rel, rel_typ_unsorted pred_P A d{{{ ρ ↯ ↯ ↦ succ d }}} A d{{{ ρ' ↯ ↯ ↦ succ d' }}} elem_rel /\ rel_exp M ρ M' ρ' elem_rel.
Proof.
  intros * ? HM.
  invert_rel_exp_unsorted HM env_relΓ.
  eexists_rel_exp_untyped.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  invert_rel_typ_unsorted_body_nouip; mauto.
Qed.

Lemma rel_exp_unsorted_of_sub_id_N {P} {pred_P : PredicativeSig P} : forall {Γ M M' N A s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ Γ ⊨u N : ℕ }} ->
    (exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}),
      forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      exists n n',
        {{ ⟦ N ⟧ ρ ↘ n }} /\
          {{ ⟦ N ⟧ ρ' ↘ n' }} /\
          exists elem_rel, rel_typ_unsorted pred_P A d{{{ ρ ↦ n }}} A d{{{ ρ' ↦ n' }}} elem_rel /\ rel_exp M ρ M' ρ' elem_rel) ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A[Id,,N] }}.
Proof.
  intros * Hru []%rel_exp_unsorted_of_nat_inversion [env_relΓ].
  destruct_conjs.
  pose env_relΓ.
  handle_per_ctx_env_irrel.
  eexists_rel_exp_untyped.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  eexists; split; mauto.
  econstructor; mauto.
Qed.

Ltac eexists_rel_exp_unsorted_of_sub_id_N r :=
  apply (@rel_exp_unsorted_of_sub_id_N) with (r := r); [eassumption |];
  eexists_rel_exp_untyped.


Ltac invert_rel_exp_of_typ_2 H l :=
  (unshelve epose proof (rel_exp_of_typ_inversion2 _ _ H); shelve_unifiable; [eassumption |]; clear H)
  + (pose proof (rel_exp_of_typ_inversion1 _ H) as [l []]; clear H)
  + invert_rel_exp_2 H l.

Ltac invert_rel_exp_of_typ_unsorted_2 H l :=
  (unshelve epose proof (rel_exp_of_typ_unsorted_inversion2 _ _ H); shelve_unifiable; [eassumption |]; clear H)
  + (pose proof (rel_exp_of_typ_unsorted_inversion1 _ H) as [l []]; clear H)
  + invert_rel_exp_2 H l.

Ltac invert_rel_exp_unsorted_of_typ_unsorted_2 H l :=
  (unshelve epose proof (rel_exp_unsorted_of_typ_inversion2 _ _ H); shelve_unifiable; [eassumption |]; clear H)
  + (pose proof (rel_exp_unsorted_of_typ_inversion1 _ H) as [l []]; clear H)
  + invert_rel_exp_2 H l.

Lemma eval_natrec_sub_neut {P} {pred_P : PredicativeSig P} : forall {Γ env_relΓ σ Δ env_relΔ MZ MZ' MS MS' A A' s m m' s'} (r : Ru_nat P s'),
    {{ DF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }} ->
    {{ DF Δ ≈ Δ ∈ per_ctx_env pred_P ↘ env_relΔ }} ->
    {{ ⟪ pred_P ⟫ Δ, ℕ@s' ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨u MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Δ, ℕ@s', A@s ⊨u MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Dom m ≈ m' ∈ per_bot }} ->
    (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) ρσ ρ'σ' mz mz',
        {{ ⟦ σ ⟧s ρ ↘ ρσ }} ->
        {{ ⟦ σ ⟧s ρ' ↘ ρ'σ' }} ->
        {{ Dom ρσ ≈ ρ'σ' ∈ env_relΔ }} ->
        {{ ⟦ MZ ⟧ ρσ ↘ mz }} ->
        {{ ⟦ MZ' ⟧ ρ'σ' ↘ mz' }} ->
        {{ Dom rec m under ρσ return A | zero -> mz | succ -> MS end ≈ rec m' under ρ' return A'[q σ] | zero -> mz' | succ -> MS'[q (q σ)] end ∈ per_bot }}).
Proof.
  intros * ?.
  intros equiv_Γ_Γ equiv_Δ_Δ
         [env_relΔℕ]%rel_exp_unsorted_of_typ_inversion1
         []%rel_exp_unsorted_of_sub_id_zero_inversion
         [env_relΔℕA]%(rel_exp_unsorted_of_sub_wkwk_succ_var1_inversion r)
         equiv_m_m'.
  destruct_conjs.
  pose env_relΔℕA.
  pose env_relΔℕ.
  handle_per_ctx_env_irrel.
  invert_per_ctx_envs_unsorted_of pred_P env_relΔℕA.
  handle_per_ctx_env_irrel.
  invert_per_ctx_envs_unsorted_of pred_P env_relΔℕ.
  handle_per_ctx_env_irrel.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head (@rel_typ_unsorted P).

  simplify_evals.
  invert_per_sort_elem H14.

  invert_rel_typ_body.
  destruct_by_head (@rel_exp P).

  functional_eval_rewrite_clear.
  match goal with
  | _: {{ ⟦ σ ⟧s ρ ↘ ^?ρ1 }},
      _: {{ ⟦ σ ⟧s ρ' ↘ ^?ρ2 }} |- _ =>
      rename ρ1 into ρσ;
      rename ρ2 into ρ'σ
  end.
  intro t.
  assert {{ Dom ⇑! ℕ t ≈ ⇑! ℕ t ∈ (@per_nat P) }} by mauto.

  assert {{ Dom ρσ ↦ ⇑! ℕ t ≈ ρ'σ ↦ ⇑! ℕ t ∈ env_relΔℕ }} as HinΔℕs.
  {
    apply_relation_equivalence; econstructor; mauto 2.
    eapply H12; mauto.
  }
  (on_all_hyp: fun H => destruct (H _ _ HinΔℕs)).
  assert {{ Dom succ (⇑! ℕ t) ≈ succ (⇑! ℕ t) ∈ per_nat }} by mauto.
  assert {{ Dom ρσ ↦ succ (⇑! ℕ t) ≈ ρ'σ ↦ succ (⇑! ℕ t) ∈ env_relΔℕ }} as HinΔℕsuccs.
  {
    apply_relation_equivalence; econstructor; mauto 2.
    eapply H12; mauto.
  }
  (on_all_hyp: fun H => destruct (H _ _ HinΔℕsuccs)).
  assert {{ Dom ρσ ↦ ⇑! ℕ t ≈ ρ'σ ↦ ⇑! ℕ t ∈ env_relΔℕ }} as HinΔℕs'.
  {
    apply_relation_equivalence; econstructor; mauto 2.
    eapply H12; mauto.
  }
  assert {{ Dom ρσ ↦ succ (⇑! ℕ t) ≈ ρ'σ ↦ succ (⇑! ℕ t) ∈ env_relΔℕ }} as HinΔℕsuccs'.
  {
    apply_relation_equivalence; econstructor; mauto 2.
    eapply H12; mauto.
  }

  assert {{ Dom zero ≈ zero ∈ (@per_nat P) }}  by econstructor.
  assert {{ Dom ρσ ↦ zero ≈ ρ'σ ↦ zero ∈ env_relΔℕ }} as HinΔℕz.
  {
    apply_relation_equivalence; econstructor; mauto 2.
    eapply H12; mauto.
  }
  apply_relation_equivalence.

  (on_all_hyp: fun H => destruct (H _ _  HinΔℕs')).
  (on_all_hyp: fun H => destruct (H _ _ HinΔℕsuccs')).
  (on_all_hyp: fun H => destruct (H _ _ HinΔℕz)).
  destruct_by_head (@per_sort P).

  assert (per_typ_elem pred_P x1 m0 m'0) by mauto 2.
  assert (per_typ_elem pred_P x0 m1 m'1) by mauto 2.
  assert (per_typ_elem pred_P x m2 m'2) by mauto 2.
  handle_per_typ_elem_irrel.

  handle_per_sort_elem_irrel.
  rename a' into a''.
  rename m'0 into a'.
  rename a1 into asucc.
  rename m'1 into asucc'.

  assert {{ Dom (ρσ ↦ ⇑! ℕ t) ↦ ⇑! a (S t) ≈ (ρ'σ ↦ ⇑! ℕ t) ↦ ⇑! a' (S t) ∈ env_relΔℕA }} as HinΔℕA.
  {
    apply_relation_equivalence.
    eexists; mauto.
    simpl.
    eapply per_bot_then_per_elem; mauto.
  }
  apply_relation_equivalence.

  edestruct (H3 _ _ HinΔℕA d{{{ ⇑! ℕ t }}} d{{{ ⇑! ℕ t }}}); [do 2 econstructor | do 2 econstructor |].
  destruct_conjs.
  destruct_by_head (@rel_typ_unsorted P).
  handle_per_typ_elem_irrel.
  destruct_by_head (@rel_exp P).
  (on_all_hyp: fun H => edestruct (per_sort_then_per_top_typ H (S t)) as [? []]).
  functional_read_rewrite_clear.
  (on_all_hyp: fun H => unshelve epose proof (per_elem_then_per_top H _ t) as [? []]; shelve_unifiable; [eassumption |]).
  (on_all_hyp: fun H => unshelve epose proof (per_elem_then_per_top H _ (S (S t))) as [? []]; shelve_unifiable; [eassumption |]).
  functional_read_rewrite_clear.
  destruct (equiv_m_m' t) as [? []].
  do 3 econstructor; mauto.
  repeat econstructor; mauto.
Qed.


Corollary eval_natrec_neut {P} {pred_P : PredicativeSig P}: forall {Γ env_relΓ MZ MZ' MS MS' A A' m m' s s'} {r : Ru_nat P s'},
    {{ DF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ@s' ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ@s', A@s ⊨u MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Dom m ≈ m' ∈ per_bot }} ->
    (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) mz mz',
        {{ ⟦ MZ ⟧ ρ ↘ mz }} ->
        {{ ⟦ MZ' ⟧ ρ' ↘ mz' }} ->
        {{ Dom rec m under ρ return A | zero -> mz | succ -> MS end ≈ rec m' under ρ' return A' | zero -> mz' | succ -> MS' end ∈ per_bot }}).
Proof.
  intros.
  assert {{ Dom rec m under ρ return A | zero -> mz | succ -> MS end ≈ rec m' under ρ' return A'[q Id] | zero -> mz' | succ -> MS'[q (q Id)] end ∈ per_bot }} by (mauto using ((@eval_natrec_sub_neut) )).
  etransitivity; [eassumption |].
  intros t.
  match_by_head (@per_bot P) ltac:(fun H => specialize (H t) as [? []]).
  eexists; split; [eassumption |].
  dir_inversion_by_head (@read_ne P); subst.
  simplify_evals.
  mauto.
Qed.

Lemma eval_natrec_rel {P} {pred_P : PredicativeSig P}: forall {Γ env_relΓ MZ MZ' MS MS' A A' s m m' s'} {r : Ru_nat P s'},
    {{ DF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ@s' ⊨u A : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ@s' ⊨u A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ@s' ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ@s', A@s ⊨u MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Dom m ≈ m' ∈ per_nat }} ->
    (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
      forall elem_rel,
        rel_typ pred_P s A d{{{ ρ ↦ m }}} A d{{{ ρ' ↦ m' }}} elem_rel ->
        exists r r',
          {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
            {{ rec m' ⟦return A' | zero -> MZ' | succ -> MS' end⟧ ρ' ↘ r' }} /\
            {{ Dom r ≈ r' ∈ elem_rel }}).
Proof.
  intros * ? equiv_Γ_Γ [env_relΓℕ]%rel_exp_unsorted_of_typ_inversion1 [] []
             HMZ HMS equiv_m_m'.
  destruct_conjs.
  induction equiv_m_m'.
  - intros.
    apply rel_exp_unsorted_of_sub_id_zero_inversion in HMZ as [];
    destruct_conjs.
    pose env_relΓℕ.
    destruct_by_head (@rel_typ P).
    invert_per_ctx_envs.
    handle_per_ctx_env_irrel.
    rename x1 into env_relΓ.
    (on_all_hyp: destruct_rel_by_assumption env_relΓ).
    destruct_by_head (@rel_exp P).
    destruct_by_head (@rel_typ_unsorted P).
    simplify_evals.
    pose proof (per_typ_elem_and_per_sort_elem_implies_per_sort_elem pred_P ltac:(eassumption) ltac:(eassumption)).
    handle_per_sort_elem_irrel.
    do 3 eexists; repeat split; mauto.
  - intros.
    assert {{ ⟪ pred_P ⟫ Γ, ℕ@s' ⊨u A ≈ A : Sort@s }} as HA by (etransitivity; mauto).
    invert_rel_exp_of_typ HA.
    apply (rel_exp_unsorted_of_sub_wkwk_succ_var1_inversion r) in HMS as [env_relΓℕA].
    destruct_conjs.
    pose env_relΓℕA.

    invert_per_ctx_envs.
    pose env_relΓℕ.
    handle_per_ctx_env_irrel.

    (on_all_hyp_rev: destruct_rel_by_assumption env_relΓ).
    destruct_by_head (@rel_typ P).
    simplify_evals.
    handle_per_sort_elem_irrel.
    invert_rel_typ_body.
    match goal with
    | _: env_relΓ ρ ?ρ0 |- _ =>
        rename ρ0 into ρ'
    end.
    assert {{ Dom ρ ↦ m ≈ ρ' ↦ m' ∈ env_relΓℕ }}. {
      apply_relation_equivalence.
      econstructor; mauto.
      intuition.
    }
    (on_all_hyp: destruct_rel_by_assumption env_relΓℕ).
    assert {{ Dom ρ ↦ m ≈ ρ' ↦ m' ∈ env_relΓℕ }} as HinΓℕ.
    {
      apply_relation_equivalence; econstructor; mauto.
      intuition.
    }
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕ)).
    destruct_by_head (@per_sort P).
    assert (env_relΓℕ d{{{ ρ ↦ m }}} d{{{ ρ' ↦ m' }}}).
    {
      apply_relation_equivalence.
      eexists; mauto.
      simpl.
      intuition.
    }
    assert (x0 d{{{ ρ ↦ m }}} d{{{ ρ' ↦ m' }}}).
    {
      apply_relation_equivalence.
      econstructor; mauto.
      intuition.
    }
    assert (rel_typ pred_P s A d{{{ ρ ↦ m }}} A d{{{ ρ' ↦ m' }}} (head_rel0 _ _ ltac:(eassumption))) by mauto 2.
    unshelve epose proof (IHequiv_m_m' _ _ equiv_ρ_ρ' _ _) as [? [? [? []]]]; shelve_unifiable; [solve [mauto] |].

    handle_per_sort_elem_irrel.
    match goal with
    | _: {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ ^?r0 }},
        _: {{ rec m' ⟦return A' | zero -> MZ' | succ -> MS' end⟧ ρ' ↘ ^?r0' }} |- _ =>
        rename r0 into rm;
        rename r0' into rm'
    end.
    assert {{ Dom (ρ ↦ m) ↦ rm ≈ (ρ' ↦ m') ↦ rm' ∈ env_relΓℕA }} as HinΓℕA by (apply_relation_equivalence; mauto).

    apply_relation_equivalence.
    (on_all_hyp: fun H => directed edestruct (H _ _ HinΓℕA m m' ltac:(mauto 3) ltac:(mauto 3))).
    destruct_conjs.
    assert (exists elem_rel : relation (domain P),
               rel_typ_unsorted pred_P A d{{{ (((ρ ↦ m) ↦ rm) ↯) ↯ ↦ succ m }}} A d{{{ (((ρ' ↦ m') ↦ rm') ↯) ↯ ↦ succ m' }}} elem_rel /\
                 rel_exp MS d{{{ (ρ ↦ m) ↦ rm }}} MS' d{{{ (ρ' ↦ m') ↦ rm' }}} elem_rel) by mauto.

    assert (rel_typ pred_P s' {{{ ℕ }}} ρ {{{ ℕ }}} ρ' (head_rel _ _ equiv_ρ_ρ')) by mauto 2.
    destruct_conjs.
    destruct_by_head (@rel_typ_unsorted P).
    destruct_by_head (@rel_typ P).
    destruct_by_head (@rel_exp P).
    invert_rel_typ_unsorted_body.
    invert_rel_typ_body.
    pose proof (per_typ_elem_and_per_sort_elem_implies_per_sort_elem pred_P ltac:(eassumption) ltac:(eassumption)).
    handle_per_sort_elem_irrel.
    do 2 eexists; repeat split; mauto.

  - destruct HMZ.
    destruct HMS.
    destruct_conjs.
    intros.
    match goal with
    | _: per_bot m ?n |- _ =>
        rename n into m'
    end.
    handle_per_ctx_env_irrel.
    invert_per_ctx_envs_of pred_P env_relΓℕ.
    pose env_relΓℕ.
    handle_per_ctx_env_irrel.

    (on_all_hyp: destruct_rel_by_assumption env_relΓ).
    (on_all_hyp_rev: destruct_rel_by_assumption env_relΓ).
    assert (rel_typ pred_P s' {{{ ℕ }}} ρ {{{ ℕ }}} ρ' (head_rel _ _ equiv_ρ_ρ')) by mauto 2.
    invert_rel_typ_body.
    destruct_by_head (@rel_typ P).
    invert_rel_typ_body.
    assert {{ Dom ⇑ a m ≈ ⇑ a' m' ∈ per_nat }} by (econstructor; eassumption).
    assert {{ Dom ρ ↦ ⇑ a m ≈ ρ' ↦ ⇑ a' m' ∈ env_relΓℕ }} as HinΓℕ.
    {
      apply_relation_equivalence.
      eexists; mauto.
      intuition.
    }
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕ)).
    destruct_conjs.
    destruct_by_head (@per_sort P).
    destruct_by_head (@rel_typ_unsorted).
    destruct_by_head (@rel_typ).
    destruct_by_head (@rel_exp P).
    invert_rel_typ_unsorted_body.
    assert (x <~> per_sort pred_P s).
    {
      inversion_clear_by_head (per_typ_elem pred_P x d{{{ Sort @ s }}} d{{{ Sort @ s }}}); auto.
      invert_per_sort_elems; auto.
    }
    unfold per_sort in *.
    invert_rel_typ_body.
    destruct_conjs.
    handle_per_sort_elem_irrel.

    do 2 eexists.
    repeat split; only 1-2: mauto.

    eapply per_bot_then_per_elem; [eassumption |].
    eapply (@eval_natrec_neut P pred_P Γ env_relΓ MZ MZ' MS MS' A A'); try (exact r); eauto.
    + assert {{ EF Γ, ℕ@s' ≈ Γ, ℕ@s' ∈ per_ctx_env pred_P ↘ env_relΓℕ }} by (per_ctx_env_econstructor; eauto).
      eexists_rel_exp_of_sort.
      apply_relation_equivalence.
      intros.
      assert (exists elem_rel : relation (domain P),
                 rel_typ_unsorted pred_P {{{ Sort@s }}} ρ {{{ Sort@s }}} ρ' elem_rel /\
                   rel_exp A ρ A' ρ' elem_rel) by mauto.
      destruct_conjs.
      destruct_by_head (@rel_typ_unsorted).
      invert_rel_typ_unsorted_body.
      eassumption.

    + eexists_rel_exp_unsorted_of_sub_id_zero.
      intros.

      assert (exists elem_rel : relation (domain P),
                 rel_typ_unsorted pred_P {{{ A[Id,,zero] }}} ρ {{{ A[Id,,zero] }}} ρ' elem_rel /\
                   rel_exp MZ ρ MZ' ρ' elem_rel) by mauto 2.
      destruct_conjs.
      destruct_by_head (@rel_typ_unsorted).
      destruct_by_head (@rel_exp).
      simplify_evals.
      eexists; split;
        econstructor; eauto.
    + econstructor; split; eauto.
Qed.

Lemma rel_exp_unsorted_natrec_cong_rel_typ {P} {pred_P : PredicativeSig P} : forall {Γ A A' s M M' env_relΓ s'} {r : Ru_nat P s'},
    {{ DF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ@s' ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : ℕ }} ->
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) n n',
      {{ ⟦ M ⟧ ρ ↘ n }} ->
      {{ ⟦ M' ⟧ ρ' ↘ n' }} ->
      exists elem_rel,
        rel_typ pred_P s A d{{{ ρ ↦ n }}} A d{{{ ρ' ↦ n' }}} elem_rel.
Proof.
  intros.
  assert {{ ⟪ pred_P ⟫ ⊨ Γ }} by (eexists; eauto).
  assert {{ ⟪ pred_P ⟫ Γ ⊨u ℕ : Sort@s' }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : ℕ[Id] }} by mauto 5.
  assert {{ ⟪ pred_P ⟫ Γ ⊨s Id,,M ≈ Id,,M' : Γ, ℕ@s' }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ ⊨s Id,,M : Γ, ℕ@s' }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u A[Id,,M] ≈ A[Id,,M'] : Sort@s[Id,,M] }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u A[Id,,M] ≈ A[Id,,M'] : Sort@s }} as HAId by mauto.

  apply rel_exp_unsorted_of_typ_inversion1 in HAId.
  destruct_conjs.
  invert_per_ctx_envs.
  handle_per_ctx_env_irrel.
  (on_all_hyp_rev: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@per_sort P).
  invert_rel_typ_unsorted_body_nouip.
  apply rel_exp_implies_rel_typ.
  econstructor; mauto.
Qed.

Lemma rel_exp_unsorted_natrec_cong {P} {pred_P : PredicativeSig P} : forall {Γ MZ MZ' MS MS' A A' s M M' s'} {r : Ru_nat P s'},
    {{ ⟪ pred_P ⟫ Γ, ℕ@s' ⊨u A : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ@s' ⊨u A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ@s' ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ@s', A@s ⊨u MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : ℕ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }}.
Proof.
  intros * Hru HA HA' HAA' ? ? [env_relΓ]%rel_exp_unsorted_of_nat_inversion.
  destruct_all.
  pose env_relΓ.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u M : ℕ }}.
  {
    unfold valid_exp_under_ctx_unsorted.
    etransitivity.
    simple apply (@rel_exp_unsorted_of_nat P) with (s := s'); mauto.
    mauto.
  }
  assert {{ ⟪ pred_P ⟫ Γ ⊨u M : ℕ }} as []%rel_exp_unsorted_of_nat_inversion by eassumption.
  destruct_all.
  handle_per_ctx_env_irrel.
  apply (@rel_exp_unsorted_of_sub_id_N) with (s := s'); [mauto | eassumption |].
  eexists_rel_exp_untyped.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  functional_eval_rewrite_clear.
  assert (exists elem_rel, rel_typ pred_P s A d{{{ ρ ↦ m }}} A d{{{ ρ' ↦ m' }}} elem_rel) as [elem_rel]
      by mauto using rel_exp_unsorted_natrec_cong_rel_typ.
  assert (exists elem_rel, rel_typ pred_P s A d{{{ ρ ↦ m }}} A d{{{ ρ' ↦ m'0 }}} elem_rel) as []
      by mauto using rel_exp_unsorted_natrec_cong_rel_typ.
  do 2 eexists.
  repeat split; [eassumption | eassumption |].
  eexists.
  destruct_by_head (@rel_typ P).
  handle_per_sort_elem_irrel.
  split; [econstructor; mautosolve 3 |].

  assert (exists r r',
             {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
               {{ rec m'0 ⟦return A' | zero -> MZ' | succ -> MS' end⟧ ρ' ↘ r' }} /\
               {{ Dom r ≈ r' ∈ elem_rel }}) by mauto 4 using eval_natrec_rel.
  destruct_conjs.
  econstructor; only 1-2: econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_natrec_cong : mcpts.

Lemma eval_natrec_sub_rel {P} {pred_P : PredicativeSig P} : forall {Γ env_relΓ σ Δ env_relΔ MZ MZ' MS MS' A A' s m m' s'} {r : Ru_nat P s'},
    {{ DF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }} ->
    {{ DF Δ ≈ Δ ∈ per_ctx_env pred_P ↘ env_relΔ }} ->
    {{ ⟪ pred_P ⟫ Δ, ℕ@s' ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨u MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Δ, ℕ@s', A@s ⊨u MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Dom m ≈ m' ∈ per_nat }} ->
    (forall ρ ρ'
        (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }})
        o o' elem_rel,
        {{ ⟦ σ ⟧s ρ ↘ o }} ->
        {{ ⟦ σ ⟧s ρ' ↘ o' }} ->
        {{ Dom o ≈ o' ∈ env_relΔ }} ->
        rel_typ pred_P s A d{{{ o ↦ m }}} A d{{{ o' ↦ m' }}} elem_rel ->
        exists r r',
          {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ o ↘ r }} /\
            {{ rec m' ⟦return A'[q σ] | zero -> MZ'[σ] | succ -> MS'[q (q σ)] end⟧ ρ' ↘ r' }} /\
            {{ Dom r ≈ r' ∈ elem_rel }}).
Proof.
  intros * r equiv_Γ_Γ equiv_Δ_Δ HA HMZ HMS equiv_m_m'.
  induction equiv_m_m'; intros;
    apply rel_exp_unsorted_of_typ_inversion1 in HA as [env_relΔℕ];
    apply rel_exp_unsorted_of_sub_id_zero_inversion in HMZ as [];
    destruct_conjs;
    pose env_relΔℕ.
  - handle_per_ctx_env_irrel.
    invert_per_ctx_envs.
    handle_per_ctx_env_irrel.
    (on_all_hyp: destruct_rel_by_assumption env_relΔ).
    destruct_by_head (@rel_typ_unsorted P).
    destruct_by_head (@rel_typ P).
    destruct_by_head (@rel_exp P).
    handle_per_typ_elem_irrel.
    pose proof (per_typ_elem_and_per_sort_elem_implies_per_sort_elem pred_P ltac:(eassumption) ltac:(eassumption)).
    handle_per_sort_elem_irrel.
    do 2 eexists; repeat split; only 1-2: econstructor; mauto.
  - match goal with
    | _: per_nat m ?n |- _ =>
        rename n into m'
    end.
    assert {{ ⟪ pred_P ⟫ Δ, ℕ@s' ⊨u A ≈ A : Sort@s }} as []%rel_exp_unsorted_of_typ_inversion1 by (etransitivity; mauto).
    apply (rel_exp_unsorted_of_sub_wkwk_succ_var1_inversion r) in HMS as [env_relΔℕA].
    destruct_conjs.
    pose env_relΔℕA.
    handle_per_ctx_env_irrel.
    invert_per_ctx_envs_of pred_P env_relΔℕA.
    handle_per_ctx_env_irrel.
    invert_per_ctx_envs_of pred_P env_relΔℕ.
    handle_per_ctx_env_irrel.
    (on_all_hyp_rev: destruct_rel_by_assumption env_relΔ).
    match goal with
    | _: {{ ⟦ σ ⟧s ρ ↘ ^?ρ1 }},
        _: {{ ⟦ σ ⟧s ρ' ↘ ^?ρ2 }} |- _ =>
        rename ρ1 into ρσ;
        rename ρ2 into ρ'σ
    end.
    simplify_evals.
    invert_rel_typ_body.

    assert {{ Dom ρσ ↦ m ≈ ρ'σ ↦ m' ∈ env_relΔℕ }}.
    {
      apply_relation_equivalence.
      econstructor; mauto.
      intuition.
    }
    (on_all_hyp: destruct_rel_by_assumption env_relΔℕ).
    assert {{ Dom ρσ ↦ m ≈ ρ'σ ↦ m' ∈ env_relΔℕ }} as HinΔℕ.
    {
      apply_relation_equivalence.
      econstructor; mauto.
      intuition.
    }
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΔℕ)).
    destruct_by_head (@per_sort P).

    assert (env_relΔℕ d{{{ ρσ ↦ m }}} d{{{ ρ'σ ↦ m' }}}) by mauto.
    simplify_evals.
    handle_per_sort_elem_irrel.
    assert (rel_typ pred_P s A d{{{ ρσ ↦ m }}} A d{{{ ρ'σ ↦ m' }}} (head_rel _ _ ltac:(eassumption))) by mauto 2.

    unshelve epose proof (IHequiv_m_m' _ _ equiv_ρ_ρ' _ _ _ _ _ _ _) as [? [? [? []]]]; shelve_unifiable; only 4: solve [mauto]; eauto.

    handle_per_sort_elem_irrel.
    handle_per_typ_elem_irrel.
    match goal with
    | _: {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ^_ ↘ ^?r0 }},
        _: {{ rec m' ⟦return A'[q σ] | zero -> MZ'[σ] | succ -> MS'[q (q σ)] end⟧ ^_ ↘ ^?r0' }} |- _ =>
        rename r0 into rm;
        rename r0' into rm'
    end.
    assert {{ Dom (ρσ ↦ m) ↦ rm ≈ (ρ'σ ↦ m') ↦ rm' ∈ env_relΔℕA }} as HinΔℕA by (apply_relation_equivalence; mauto).
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΔℕA)).
    destruct_conjs.
    destruct_by_head (@rel_typ_unsorted P).
    destruct_by_head (@rel_typ P).
    destruct_by_head (@rel_exp P).
    handle_per_sort_elem_irrel.

    assert (exists elem_rel : relation (domain P),
               rel_typ_unsorted pred_P A d{{{ (((ρσ ↦ m) ↦ rm) ↯) ↯ ↦ succ m }}} A d{{{ (((ρ'σ ↦ m') ↦ rm') ↯) ↯ ↦ succ m' }}} elem_rel /\
                 rel_exp MS d{{{ (ρσ ↦ m) ↦ rm }}} MS' d{{{ (ρ'σ ↦ m') ↦ rm' }}} elem_rel) by mauto.
    destruct_conjs.
    destruct_by_head (@rel_typ_unsorted P).
    destruct_by_head (@rel_exp P).
    simplify_evals.
    pose proof (per_typ_elem_and_per_sort_elem_implies_per_sort_elem pred_P ltac:(eassumption) ltac:(eassumption)).
    handle_per_sort_elem_irrel.

    do 2 eexists; repeat split; only 1-2: repeat econstructor; mauto.
  - match goal with
    | _: per_bot m ?n |- _ =>
        rename n into m'
    end.
    handle_per_ctx_env_irrel.
    invert_per_ctx_envs.
    handle_per_ctx_env_irrel.
    (on_all_hyp: destruct_rel_by_assumption env_relΔ).
    (on_all_hyp_rev: destruct_rel_by_assumption env_relΔ).
    invert_rel_typ_body.
     match goal with
    | _: {{ ⟦ σ ⟧s ρ ↘ ^?ρ1 }},
        _: {{ ⟦ σ ⟧s ρ' ↘ ^?ρ2 }} |- _ =>
        rename ρ1 into ρσ;
        rename ρ2 into ρ'σ
    end.
    assert {{ Dom ⇑ a m ≈ ⇑ a' m' ∈ per_nat }} by (econstructor; eassumption).
    assert {{ Dom ρσ ↦ ⇑ a m ≈ ρ'σ ↦ ⇑ a' m' ∈ env_relΔℕ }} as HinΔℕ.
    {
      apply_relation_equivalence.
      econstructor; mauto.
      intuition.
    }
    apply_relation_equivalence.
    (on_all_hyp: fun H => directed destruct (H _ _ HinΔℕ)).
    unfold per_sort in *.
    destruct_conjs.
    destruct_by_head (@rel_typ_unsorted P).
    destruct_by_head (@rel_typ P).
    destruct_by_head (@rel_exp P).
    invert_rel_typ_unsorted_body.
    handle_per_sort_elem_irrel.
    do 2 eexists.
    repeat split; only 1-2: repeat econstructor; mauto.

    eapply per_bot_then_per_elem; [eassumption |].
    eapply (@eval_natrec_sub_neut _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' r); only 7: eauto; mauto 2.
    + assert {{ EF Δ, ℕ@s' ≈ Δ, ℕ@s' ∈ per_ctx_env pred_P ↘ env_relΔℕ }} by (per_ctx_env_econstructor; eauto).
      eexists_rel_exp_of_sort.
      apply_relation_equivalence.
      eauto.
    + eexists_rel_exp_unsorted_of_sub_id_zero.
      eauto.
Qed.

Lemma rel_exp_unsorted_natrec_sub_rel_typ {P} {pred_P : PredicativeSig P} : forall {Γ σ Δ A s M env_relΓ s'} {r : Ru_nat P s'},
    {{ DF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ, ℕ@s' ⊨u A : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨u M : ℕ }} ->
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
    exists elem_rel,
      rel_typ pred_P s {{{ A[σ,,M[σ]] }}} ρ {{{ A[σ,,M[σ]] }}} ρ' elem_rel.
Proof.
  intros.
  assert {{ ⟪ pred_P ⟫ ⊨ Γ }} by (eexists; eauto).
  assert {{ ⟪ pred_P ⟫ ⊨ Δ }} by (eapply presup_rel_sub; eauto).
  assert {{ ⟪ pred_P ⟫ Γ ⊨u M[σ] : ℕ[σ] }} by mauto.
  assert {{ ⟪ pred_P ⟫ Δ ⊨u ℕ : Sort@s' }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ ⊨s σ,,M[σ] : Δ, ℕ@s' }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u A[σ,,M[σ]] : Sort@s[σ,,M[σ]] }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u A[σ,,M[σ]] : Sort@s }} as HAσ by mauto.
  apply rel_exp_unsorted_of_typ_inversion1 in HAσ.
  destruct_conjs.
  invert_per_sort_elems.
  handle_per_ctx_env_irrel.
  (on_all_hyp_rev: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@per_sort).
  mauto.
Qed.


Lemma rel_exp_unsorted_natrec_sub {P} {pred_P : PredicativeSig P} : forall {Γ σ Δ MZ MS A s M s'} {r : Ru_nat P s'},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ, ℕ@s' ⊨u A : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨u MZ : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Δ, ℕ@s', A@s ⊨u MS : A[Wk∘Wk,,succ(#1)] }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨u M : ℕ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }}.
Proof.
  intros * ? [env_relΓ [? [env_relΔ]]] HA ? ? []%rel_exp_unsorted_of_nat_inversion.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists_rel_exp_untyped.
  intros.
  assert (exists elem_rel, rel_typ pred_P s {{{ A[σ,,M[σ]] }}} ρ {{{ A[σ,,M[σ]] }}} ρ' elem_rel) as [elem_rel]
      by (eapply (@rel_exp_unsorted_natrec_sub_rel_typ); only 6: eassumption; mauto; eexists; mauto).
  eexists.
  destruct_by_head (@rel_typ P).
  split; [econstructor; mautosolve 3 |].
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  invert_rel_typ_body.
  match goal with
  | _: {{ ⟦ σ ⟧s ^?ρ0 ↘ ^?ρσ0 }},
      _: {{ ⟦ A ⟧ ρσ ↦ ^?m0 ↘ ^?a0 }},
        _: {{ ⟦ A ⟧ ^?ρσ0 ↦ ^?m0' ↘ ^?a0' }} |- _ =>
      rename ρ0 into ρ';
      rename ρσ0 into ρ'σ;
      rename a0 into a;
      rename m0 into m;
      rename a0' into a';
      rename m0' into m'
  end.
  enough (exists r r',
             {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρσ ↘ r }} /\
               {{ rec m' ⟦return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end⟧ ρ' ↘ r' }} /\
               {{ Dom r ≈ r' ∈ elem_rel }})
    by (destruct_conjs; econstructor; mauto).
  mauto 4 using eval_natrec_sub_rel.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_natrec_sub : mcpts.

Lemma rel_exp_unsorted_nat_beta_zero {P} {pred_P : PredicativeSig P} : forall {Γ MZ MS A s s'} {r : Ru_nat P s'},
    {{ ⟪ pred_P ⟫ Γ ⊨u MZ : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ@s', A@s ⊨u MS : A[Wk∘Wk,,succ(#1)] }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }}.
Proof.
  intros * ?.
  intros [env_relΓ]%rel_exp_unsorted_of_sub_id_zero_inversion [env_relΓℕA]%(rel_exp_unsorted_of_sub_wkwk_succ_var1_inversion r).
  destruct_conjs.
  assert {{ ⟪ pred_P ⟫ ⊨ Γ, ℕ@s' }} as [env_relΓℕ] by (invert_per_ctx_envs_unsorted_of pred_P env_relΓℕA; eexists; eauto).
  destruct_conjs.
  pose env_relΓℕ.
  pose env_relΓℕA.
  invert_per_ctx_envs_of pred_P env_relΓℕA.
  handle_per_ctx_env_irrel.
  invert_per_ctx_envs_of pred_P env_relΓℕ.
  eexists_rel_exp_unsorted_of_sub_id_zero.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted).
  invert_rel_typ_unsorted_body_nouip.
  destruct_by_head (@rel_exp).
  match goal with
  | _: env_relΓ ρ ?ρ0 |- _ =>
      rename ρ0 into ρ'
  end.
  invert_per_sort_elems.
  assert {{ Dom zero ≈ zero ∈ (@per_nat P) }} by econstructor.
  assert {{ Dom ρ ↦ zero ≈ ρ' ↦ zero ∈ env_relΓℕ }}.
  {
    apply_relation_equivalence. econstructor; mauto.
    intuition.
  }
  (on_all_hyp: destruct_rel_by_assumption env_relΓℕ).
  handle_per_typ_elem_irrel.
  eexists.
  split; mauto.
Qed.

#[export]
  Hint Resolve rel_exp_unsorted_nat_beta_zero : mcpts.

Lemma rel_exp_unsorted_nat_beta_succ_rel_typ {P} {pred_P : PredicativeSig P} : forall {Γ env_relΓ A s M s'} {r : Ru_nat P s'},
    {{ DF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ@s' ⊨u A : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M : ℕ }} ->
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
    exists elem_rel,
      rel_typ pred_P s {{{ A[Id,,succ M] }}} ρ {{{ A[Id,,succ M] }}} ρ' elem_rel.
Proof.
  intros.
  assert {{ ⟪ pred_P ⟫ ⊨ Γ }} by (eexists; eauto).
  assert {{ ⟪ pred_P ⟫ Γ ⊨u ℕ : Sort@s' }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u ℕ ≈ ℕ[Id] : Sort@s' }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u succ M : ℕ[Id] }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ ⊨s Id,,succ M : Γ, ℕ@s' }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u A[Id,,succ M] : Sort@s }} as HAId by mauto.
  apply rel_exp_unsorted_of_typ_inversion1 in HAId.
  destruct_conjs.
  invert_per_sort_elems.
  handle_per_ctx_env_irrel.
  (on_all_hyp_rev: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@per_sort).
  mauto.
Qed.

Lemma rel_exp_unsorted_nat_beta_succ {P} {pred_P : PredicativeSig P} : forall {Γ MZ MS A s M s'} {r : Ru_nat P s'},
    {{ ⟪ pred_P ⟫ Γ, ℕ@s' ⊨u A : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u MZ : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ@s', A@s ⊨u MS : A[Wk∘Wk,,succ(#1)] }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M : ℕ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u rec succ M return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }}.
Proof.
  intros * Hru HA ? ? [env_relΓ]%rel_exp_unsorted_of_nat_inversion.
  destruct_all.
  eexists_rel_exp_untyped.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  assert (exists elem_rel,
             rel_typ pred_P s {{{ A[Id,,succ M] }}} ρ {{{ A[Id,,succ M] }}} ρ' elem_rel) as [elem_rel]
      by (eapply (@rel_exp_unsorted_nat_beta_succ_rel_typ P); mauto).
  destruct_by_head (@rel_typ P).
  eexists.
  split; [econstructor; mautosolve 3 |].
  invert_rel_typ_body.

  match goal with
  | _: env_relΓ ?ρ0 ?ρ'0 |- _ =>
      rename ρ0 into ρ;
      rename ρ'0 into ρ'
  end.
  assert (exists r r',
             {{ rec succ m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
               {{ rec succ m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ' ↘ r' }} /\
               {{ Dom r ≈ r' ∈ elem_rel }}) by (eapply (@eval_natrec_rel P); mauto).
  destruct_conjs.
  dir_inversion_by_head (@eval_natrec P); subst.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_nat_beta_succ : mcpts.
