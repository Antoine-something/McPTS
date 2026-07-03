From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness Require Import LogicalRelation TermStructureCases SortCases.
Import Domain_Notations.

Lemma presup_glu_rel_sub {P} (pred_P : PredicativeSig P) : forall {anns Γ σ anns' Δ},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} /\ {{ ⟪ pred_P ⟫ ⊩ Δ with anns'}}.
Proof.
  intros * [].
  destruct_conjs.
  split; eexists; eassumption.
Qed.

Lemma presup_left_glu_rel_sub {P} (pred_P : PredicativeSig P) : forall {anns Γ σ anns' Δ},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ with anns }}.
Proof.
  intros * []%presup_glu_rel_sub.
  eassumption.
Qed.

#[export]
Hint Resolve presup_left_glu_rel_sub : mcpts.

Lemma presup_right_glu_rel_sub {P} (pred_P : PredicativeSig P) : forall {anns Γ σ anns' Δ},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }} ->
    {{ ⟪ pred_P ⟫ ⊩ Δ with anns' }}.
Proof.
  intros * []%presup_glu_rel_sub.
  eassumption.
Qed.

#[export]
Hint Resolve presup_right_glu_rel_sub : mcpts.

Lemma glu_rel_sub_id {P} (pred_P : PredicativeSig P) : forall {anns Γ},
    {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s Id : Γ with anns }}.
Proof.
  intros * [Sb].
  do 2 eexists; repeat split; mauto.
  intros.
  econstructor; mauto.
  enough {{ Δ ⊢s σ ≈ Id∘σ : Γ }} as <-; mauto.
Qed.

#[export]
Hint Resolve glu_rel_sub_id : mcpts.

Lemma glu_rel_sub_weaken {P} (pred_P : PredicativeSig P) : forall {anns Γ A so},
    {{ ⟪ pred_P ⟫ ⊩ Γ, A with (so::anns)}} ->
    {{ ⟪ pred_P ⟫ Γ, A with (so::anns) ⊩s Wk : Γ with anns }}.
Proof.
  intros * [SbΓA].
  inversion_clear H;
    handle_functional_glu_ctx_env P;
    do 2 eexists; repeat split;
    only 1, 4: econstructor; try reflexivity; mauto;
    intros;
    destruct_by_head (@cons_glu_sub_pred P);
    econstructor; mauto.
Qed.

#[export]
Hint Resolve glu_rel_sub_weaken : mcpts.

Lemma glu_rel_sub_compose {P} (pred_P : PredicativeSig P) : forall {anns1 anns2 anns3 Γ1 σ2 Γ2 σ1 Γ3},
    {{ ⟪ pred_P ⟫ Γ1 with anns1 ⊩s σ2 : Γ2 with anns2 }} ->
    {{ ⟪ pred_P ⟫ Γ2 with anns2 ⊩s σ1 : Γ3 with anns3 }} ->
    {{ ⟪ pred_P ⟫ Γ1 with anns1 ⊩s σ1 ∘ σ2 : Γ3 with anns3 }}.
Proof.
  intros * Hσ2 Hσ1.
  assert {{ Γ2 ⊢s σ1 : Γ3 }} by mauto 3.
  assert {{ Γ1 ⊢s σ2 : Γ2 }} by mauto 3.
  destruct Hσ2 as [SbΓ1 [SbΓ2]].
  destruct_conjs.
  invert_glu_rel_sub Hσ1.
  destruct_conjs.
  do 2 eexists; repeat split; mauto.
  intros.
  handle_functional_glu_ctx_env P.
  destruct_glu_rel_sub_with_sub.
  destruct_glu_rel_sub_with_sub.
  simplify_evals.
  econstructor; mauto 3.
  enough {{ Δ ⊢s (σ1 ∘ σ2) ∘ σ ≈ σ1 ∘ (σ2 ∘ σ) : Γ3 }} as -> by eassumption.
  mauto 3.
Qed.

#[export]
  Hint Resolve glu_rel_sub_compose : mcpts.

Lemma glu_rel_exp_with_sub_implies_glu_rel_exp_with_sub_unsorted {P} (pred_P : PredicativeSig P) : forall {s Δ A M σ ρ},
    glu_rel_exp_with_sub pred_P s Δ M A σ ρ ->
    glu_rel_exp_with_sub_unsorted pred_P (Some s) Δ M A σ ρ.
Proof.
  intros.
  inversion H; subst.
  econstructor; mauto 3.
Qed.

#[export]
  Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_exp_with_sub_unsorted : mcpts.

Lemma glu_rel_typ_with_sub_implies_glu_rel_typ_with_sub_unsorted {P} (pred_P : PredicativeSig P) : forall {s Δ A σ ρ},
    glu_rel_typ_with_sub pred_P s Δ A σ ρ ->
    glu_rel_typ_with_sub_unsorted pred_P (Some s) Δ A σ ρ.
Proof.
  intros.
  inversion H; subst.
  econstructor; mauto 3.
Qed.

#[export]
  Hint Resolve glu_rel_typ_with_sub_implies_glu_rel_typ_with_sub_unsorted : mcpts.


Lemma glu_rel_sub_extend_unsorted {P} (pred_P : PredicativeSig P) : forall {anns Γ σ anns' Δ M A},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }} ->
    {{ ⟪ pred_P ⟫ Δ with anns' ⊩u A @ ^None }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A[σ] @ ^None }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s (σ ,, M) : Δ , A with None::anns' }}.
Proof.
  intros * Hσ HA HM.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ A  }} by mauto 3.
  assert {{ Γ ⊢ M : A[σ] }} by mauto 3.
  destruct Hσ as [SbΓ [SbΔ]].
  destruct_conjs.
  inversion HA; subst.
  inversion HM; subst.
  destruct_conjs.
  do 2 eexists; repeat split; mauto.
  - econstructor; mauto 3; try reflexivity; intros; mauto 4.
    
  - intros.
    handle_functional_glu_ctx_env P.
    assert (x0 Δ0 σ0 ρ) by (apply_predicate_equivalence; eassumption).
    destruct_glu_rel_sub_with_sub.
    destruct_glu_rel_exp_with_sub_unsorted.

    simplify_evals.
    match_by_head (@glu_typ_elem P) ltac:(fun H => directed inversion H); subst.
    apply_predicate_equivalence.
    unfold top_sort_glu_exp_pred in *.
    destruct_conjs.
    handle_functional_glu_sort_elem P.
    
    rename m into a.
    econstructor; mauto 4.
    assert {{ Δ0 ⊢s σ0 : Γ }} by mauto 4.
    assert {{ Δ0 ⊢s (σ,,M)∘σ0 : Δ, A }} by mauto 4.
    assert {{ Δ0 ⊢s (σ,,M)∘σ0 ≈ (σ∘σ0),,M[σ0] : Δ, A }} by mauto 3.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) : Δ }} by mauto 4.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ Wk∘((σ∘σ0),,M[σ0]) : Δ }} by mauto 4.
    assert {{ Δ0 ⊢ M[σ0] : A[σ][σ0] }} by mauto 4.
    assert {{ Δ0 ⊢ M[σ0] : A[σ∘σ0] }} by mauto 4.
    assert {{ Δ0 ⊢s Wk∘((σ∘σ0),,M[σ0]) ≈ σ∘σ0 : Δ }} by mauto 4.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ σ∘σ0 : Δ }} by mauto 3.
    econstructor; mauto 4.
    + assert {{ Δ, A ⊢s Wk : Δ }} by mauto 4.
      assert {{ Δ, A ⊢ A[Wk] }} by mauto 3.
      assert {{ Δ0 ⊢ A[Wk][(σ,,M)∘σ0] ≈ A[Wk∘((σ,,M)∘σ0)]  }} as -> by (symmetry; mauto 3).
      assert {{ Δ0 ⊢ A[Wk∘((σ,,M)∘σ0)] ≈ A[σ∘σ0] }} as -> by mauto 3.
      assert {{ Δ0 ⊢ A[σ∘σ0] ≈ A[σ][σ0] }} by mauto 3.
      rewrite -> H33.
      assert {{ Δ, A ⊢ #0 : A[Wk] }} by mauto 3.
      assert {{ Δ0 ⊢ #0[(σ,,M)∘σ0] ≈ #0[(σ∘σ0),,M[σ0]] : A[Wk][(σ,,M)∘σ0] }} by mauto 3.
      assert {{ Δ0 ⊢ #0[(σ,,M)∘σ0] ≈ #0[(σ∘σ0),,M[σ0]] : A[σ][σ0] }} as -> by mauto 4.
      assert {{ Δ0 ⊢ #0[(σ∘σ0),,M[σ0]] ≈ M[σ0] : A[σ∘σ0] }} by mauto 4.
      assert {{ Δ0 ⊢ #0[(σ∘σ0),,M[σ0]] ≈ M[σ0] : A[σ][σ0] }} as -> by (eapply wf_exp_eq_conv; mauto 4).
      apply_predicate_equivalence.
      split; mauto.
    + simpl.
      apply_predicate_equivalence.
      eapply glu_ctx_env_sub_resp_sub_eq with (Sb := SbΔ) (σ := {{{ σ∘σ0 }}}); mauto 3.
Qed.


Lemma glu_rel_sub_extend_sorted {P} (pred_P : PredicativeSig P) : forall {anns s Γ σ anns' Δ M A},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }} ->
    {{ ⟪ pred_P ⟫ Δ with anns' ⊩u A @ ^(Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A[σ] @ ^(Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s (σ ,, M) : Δ , A with (Some s)::anns' }}.
Proof.
  intros * Hσ HA HM.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ A : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ M : A[σ] }} by mauto 3.
  destruct Hσ as [SbΓ [SbΔ]].
  destruct_conjs.
  inversion HA; subst.
  inversion HM; subst.
  destruct_conjs.
  do 2 eexists; repeat split; mauto.
  - econstructor; mauto 3; try reflexivity; intros; mauto 4.
    
  - intros.
    handle_functional_glu_ctx_env P.
    assert (x0 Δ0 σ0 ρ) by (apply_predicate_equivalence; eassumption).
    
    destruct_glu_rel_sub_with_sub.
    assert (x Δ0 {{{ σ∘σ0 }}} ρ') by (apply_predicate_equivalence; eassumption).
    
    destruct_glu_rel_exp_with_sub_unsorted.
    simplify_evals.
    econstructor; mauto.
    apply_predicate_equivalence.
    
    rename m into a.

    assert {{ Δ0 ⊢s σ0 : Γ }} by mauto 4.
    assert {{ Δ0 ⊢s (σ,,M)∘σ0 : Δ, A }} by mauto 4.
    assert {{ Δ0 ⊢s (σ,,M)∘σ0 ≈ (σ∘σ0),,M[σ0] : Δ, A }} by mauto 3.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) : Δ }} by mauto 4.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ Wk∘((σ∘σ0),,M[σ0]) : Δ }} by mauto 4.
    assert {{ Δ0 ⊢ M[σ0] : A[σ][σ0] }} by mauto 4.
    assert {{ Δ0 ⊢ M[σ0] : A[σ∘σ0] }} by mauto 4.
    assert {{ Δ0 ⊢s Wk∘((σ∘σ0),,M[σ0]) ≈ σ∘σ0 : Δ }} by mauto 4.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ σ∘σ0 : Δ }} by mauto 3.
    econstructor; mauto 4.
    + econstructor; mauto 4.
    + assert {{ Δ, A ⊢s Wk : Δ }} by mauto 4.
      assert {{ Δ, A ⊢ A[Wk] }} by mauto 3.
      assert {{ Δ0 ⊢ A[Wk][(σ,,M)∘σ0] ≈ A[Wk∘((σ,,M)∘σ0)] : Sort@s }} as -> by (symmetry; mauto 3).
      assert {{ Δ0 ⊢ A[Wk∘((σ,,M)∘σ0)] ≈ A[σ∘σ0] : Sort@s }} as -> by mauto 3.
      assert {{ Δ0 ⊢ A[σ∘σ0] ≈ A[σ][σ0] : Sort@s }} by mauto 3.
      rewrite -> H29.
      assert {{ Δ, A ⊢ #0 : A[Wk] }} by mauto 3.
      assert {{ Δ0 ⊢ #0[(σ,,M)∘σ0] ≈ #0[(σ∘σ0),,M[σ0]] : A[Wk][(σ,,M)∘σ0] }} by mauto 3.
      assert {{ Δ0 ⊢ #0[(σ,,M)∘σ0] ≈ #0[(σ∘σ0),,M[σ0]] : A[σ][σ0] }} as -> by mauto 4.
      assert {{ Δ0 ⊢ #0[(σ∘σ0),,M[σ0]] ≈ M[σ0] : A[σ∘σ0] }} by mauto 4.
      assert {{ Δ0 ⊢ #0[(σ∘σ0),,M[σ0]] ≈ M[σ0] : A[σ][σ0] }} as -> by (eapply wf_exp_eq_conv; mauto 4).
      mauto 2.
    + simpl.
      apply_predicate_equivalence.
      eapply glu_ctx_env_sub_resp_sub_eq with (Sb := SbΔ) (σ := {{{ σ∘σ0 }}}); mauto 3.
Qed.

Lemma glu_rel_sub_extend {P} (pred_P : PredicativeSig P) : forall {anns so Γ σ anns' Δ M A},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }} ->
    {{ ⟪ pred_P ⟫ Δ with anns' ⊩u A @ so }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A[σ] @ so }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s (σ ,, M) : Δ , A with so::anns' }}.
Proof.
  intros.
  destruct so; mauto 2 using glu_rel_sub_extend_sorted, glu_rel_sub_extend_unsorted.
Qed.

#[export]
Hint Resolve glu_rel_sub_extend : mcpts.

Lemma glu_rel_sub_conv_helper {P} (pred_P : PredicativeSig P) : forall {anns anns' Γ Γ' Sb Sb'},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ EG Γ' ∈ glu_ctx_env pred_P anns' ↘ Sb' }} ->
    {{ ⊢ Γ ⊆ Γ' }} ->
    (Sb -∙> Sb').
Proof.
  intros.
  eapply glu_ctx_env_resp_per_ctx_helper; mauto 2.
Qed.

Lemma glu_rel_sub_conv {P} (pred_P : PredicativeSig P) : forall {anns Γ σ anns' Δ anns'' Δ'},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }} ->
    {{ ⟪ pred_P ⟫ ⊩ Δ' with anns'' }} ->
    {{ ⊢ Δ ⊆ Δ' }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ' with anns'' }}.
Proof.
  intros * [SbΓ [SbΔ [? []]]] [SbΔ'] HΔΔ'.
  assert (SbΔ -∙> SbΔ') by (eapply glu_rel_sub_conv_helper; mauto 2).
  econstructor.
  do 2 eexists; repeat split; mauto 3.
  intros.
  destruct_glu_rel_sub_with_sub.
  eapply H3 in H6.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_sub_conv : mcpts.
