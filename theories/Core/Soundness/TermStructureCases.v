From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import SystemAnnotated.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations.


Lemma presup_glu_rel_exp_unsorted_typ {P} (pred_P : PredicativeSig P) : forall {s anns Γ M A},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} /\ {{ ⟪ pred_P ⟫ Γ with anns ⊩u A : Sort@s @ ^so_None }}.
Proof.
  intros * [SbΓ []].
  split; [eexists; eassumption |].
  eexists; intuition.
  specialize (H0 Δ σ ρ H1).
  inversion_clear H0.
  econstructor; try reflexivity; mauto 2.
  - econstructor; try reflexivity.
  - split; [mauto 3|].
    do 2 eexists; split; mauto 2.
    eapply glu_sort_elem_trm_typ; mauto 2.
Qed.

Lemma presup_glu_rel_exp_unsorted_sort {P} (pred_P : PredicativeSig P) : forall {anns Γ M A},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} /\ (exists s, {{ Γ ⊢ A ≈ Sort@s }} ).
Proof.
  intros * [SbΓ []].
  split; [eexists; eassumption |].

  assert (exists env_relΓ, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }}) as [env_relΓ] by mauto 2.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ [ρ' []]] by (eauto using per_ctx_then_per_env_initial_env).
  assert {{ Γ ⊢s Id ® ρ ∈ SbΓ }} by (eapply initial_env_glu_rel_exp; mauto 2).
  assert (glu_rel_exp_with_sub_unsorted pred_P so_None Γ M A {{{ Id }}} ρ) by mauto 2.
  inversion_clear H5.
  inversion_clear H9.
  simpl_glu_rel.
  assert {{ Γ ⊢ A }} by mauto 3.
  assert {{ Γ ⊢ A[Id] ≈ A }} by mauto 3.
  assert {{ Γ ⊢ A ≈ Sort@s0 }} by mauto 3.
  eauto.
Qed.

Lemma presup_glu_rel_typ_unsorted_typ {P} (pred_P : PredicativeSig P) : forall {s anns Γ A},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} /\ {{ ⟪ pred_P ⟫ Γ with anns ⊩u A : Sort@s @ ^so_None }}.
Proof.
  intros * [SbΓ []].
  split; [eexists; eassumption |].
  eexists; intuition.
  specialize (H0 Δ σ ρ H1).
  inversion_clear H0.
  econstructor; try reflexivity; mauto 2.
  - econstructor; try reflexivity.
  - split; [mauto 3|].
    do 2 eexists; split; mauto 2.
Qed.

Lemma presup_glu_rel_typ_unsorted_sort {P} (pred_P : PredicativeSig P) : forall {anns Γ A},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} /\ (exists s, {{ Γ ⊢ A ≈ Sort@s }}).
Proof.
  intros * [SbΓ []].
  split; [eexists; eassumption |].
  assert (exists env_relΓ, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }}) as [env_relΓ] by mauto 2.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ [ρ' []]] by (eauto using per_ctx_then_per_env_initial_env).
  assert {{ Γ ⊢s Id ® ρ ∈ SbΓ }} by (eapply initial_env_glu_rel_exp; mauto 2).
  assert (glu_rel_typ_with_sub_unsorted pred_P so_None Γ A {{{ Id }}} ρ) by mauto 2.
  inversion_clear H5.
  inversion_clear H8.
  simpl_glu_rel.
  assert {{ Γ ⊢ A }} by mauto 3.
  assert {{ Γ ⊢ A[Id] ≈ A }} by mauto 3.
  assert {{ Γ ⊢ A ≈ Sort@s0 }} by mauto 3.
  eauto.
Qed.  

Lemma presup_ctx_glu_rel_exp_unsorted {P} (pred_P : PredicativeSig P) : forall {so anns Γ M A},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A @ so }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ with anns }}.
Proof.
  intros *.
  dependent destruction so.
  - intros * []%presup_glu_rel_exp_unsorted_sort;
    eassumption.
  - intros * []%presup_glu_rel_exp_unsorted_typ;
    eassumption.
Qed.

#[export]
Hint Resolve presup_ctx_glu_rel_exp_unsorted : mcpts.

Lemma presup_typ_glu_rel_exp_unsorted_typ {P} (pred_P : PredicativeSig P) : forall {s anns Γ M A},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A : Sort@s @ ^so_None }}.
Proof.
  intros * []%presup_glu_rel_exp_unsorted_typ;
    eassumption.
Qed.

#[export]
  Hint Resolve presup_typ_glu_rel_exp_unsorted_typ : mcpts.

Lemma presup_typ_glu_rel_typ_unsorted_typ {P} (pred_P : PredicativeSig P) : forall {s anns Γ A},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A : Sort@s @ ^so_None }}.
Proof.
  intros * []%presup_glu_rel_typ_unsorted_typ;
    eassumption.
Qed.

#[export]
  Hint Resolve presup_typ_glu_rel_typ_unsorted_typ : mcpts.

Lemma presup_typ_glu_rel_exp_unsorted_sort {P} (pred_P : PredicativeSig P) : forall {anns Γ M A},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A @ ^so_None }} ->
    exists s, {{ Γ ⊢ A ≈ Sort@s }}.
Proof.
  intros * []%presup_glu_rel_exp_unsorted_sort;
    eassumption.
Qed.

#[export]
Hint Resolve presup_typ_glu_rel_exp_unsorted_sort : mcpts.

Lemma presup_typ_glu_rel_typ_unsorted_sort {P} (pred_P : PredicativeSig P) : forall {anns Γ A},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A @ ^so_None }} ->
    exists s, {{ Γ ⊢ A ≈ Sort@s }}.
Proof.
  intros * []%presup_glu_rel_typ_unsorted_sort;
    eassumption.
Qed.

#[export]
Hint Resolve presup_typ_glu_rel_typ_unsorted_sort : mcpts.

Lemma glu_rel_ctx_ann_lookup {P} (pred_P : PredicativeSig P) : forall {anns Γ x A},
    {{ #x : A ∈ Γ }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} ->
    exists so, {{ #x : A @ so ∈ Γ with anns }}.
Proof.
  intros * H.
  gen anns.
  induction H.
  - intros * [Sb];
      inversion_clear H;
      repeat econstructor.
  - intros * [Sb];
      inversion_clear H0;
      apply_predicate_equivalence;
      assert {{ ⟪ pred_P ⟫ ⊩ Γ with anns0 }} by (exists TSb; mauto);
      assert (exists so : SortOption P, {{ # n : A @ so ∈ Γ with anns0 }}) as [so] by mauto 2;
      repeat econstructor; mauto.
Qed.

#[export]
Hint Resolve glu_rel_ctx_ann_lookup : mcpts.


Lemma glu_rel_exp_vlookup {P} (pred_P : PredicativeSig P) : forall {anns so Γ x A},
    {{ #x : A ∈ Γ }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} ->
    {{ #x : A @ so ∈ Γ with anns }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u #x : A @ so}}.
Proof.
  intros * Hx.
  gen anns so.
  dependent induction Hx; intros * [Sb];
    match_by_head1 (@glu_ctx_env P) ltac:(fun H => invert_glu_ctx_env H).

  - eexists.
    split; [econstructor |]; try reflexivity; mauto.
    intros.
    destruct_by_head (@cons_glu_sub_pred P).
    inversion H6; subst.
    assert (glu_rel_typ_with_sub_unsorted pred_P (so_Some s) Δ A {{{ Wk∘σ }}} d{{{ ρ ↯ }}}) by mauto 2.
    inversion H10; subst.
    handle_functional_glu_sort_elem P.
    inversion H3; subst.
    econstructor; mauto.
  - intros.
    inversion H3; subst.
    econstructor; split; [econstructor|]; mauto.
    intros.
    apply_predicate_equivalence.
    inversion_clear H4.
    assert (glu_rel_typ_with_sub_unsorted pred_P so_None Δ A {{{ Wk∘σ }}} d{{{ ρ ↯ }}}) by mauto 2.
    inversion_clear H4.
    handle_functional_glu_typ_elem P.
    econstructor; mauto 4.
  - intros.
    inversion_clear H3.
    assert (glu_ctx_env pred_P ((so_Some s)::anns0) Sb {{{ Γ, B }}}) by (econstructor; mauto).
    specialize (IHHx so anns0 ltac:(econstructor; mauto 2) H4).
    destruct so.
    + assert {{ Γ ⊢ A }} by mauto 3.
      inversion_clear IHHx.
      destruct_conjs.
      handle_functional_glu_ctx_env P.
      do 2 eexists.
      * econstructor; try reflexivity; mauto.
      * intros.
        destruct_by_head (@cons_glu_sub_pred P).
        rewrite <- H9 in H12.
        destruct_glu_rel_exp_with_sub_unsorted; simplify_evals.
        econstructor; mauto.
        assert {{ ⊢ Γ, B }} by mauto 3.
        assert (typ_rel0 Δ {{{ A[Wk∘σ] }}}) by (eapply glu_typ_elem_trm_typ; mauto 2).
        assert {{ Δ ⊢ A[Wk∘σ]  }} by (eapply glu_typ_elem_typ_escape; mauto 2).
        assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] }} as -> by mauto 4.
        assert {{ Γ ⊢ #n : A }} by mauto 5.
        assert {{ Γ, B ⊢ A[Wk] }} by mauto 4.
        assert {{ Γ, B ⊢ #n[Wk] : A[Wk] }} by mauto 4.
        assert {{ Γ, B ⊢ #n[Wk] ≈ #(S n) : A[Wk] }} by mauto 3.
        assert {{ Δ ⊢ #n[Wk][σ] ≈ #(S n)[σ] : A[Wk∘σ] }} as <- by (eapply wf_exp_eq_conv'; mauto 3).
        assert {{ Δ ⊢ #n[Wk∘σ] ≈ #n[Wk][σ] : A[Wk∘σ] }} as <- by mauto 4.
        eassumption.
    + assert {{ Γ ⊢ A : Sort@s0 }} by mauto 3.
      inversion_clear IHHx.
      destruct_conjs.
      handle_functional_glu_ctx_env P.
      do 2 eexists.
      * econstructor; try reflexivity; mauto.
      * intros.
        destruct_by_head (@cons_glu_sub_pred P).
        rewrite <- H9 in H12.
        destruct_glu_rel_exp_with_sub_unsorted; simplify_evals.
        econstructor; mauto.
        assert {{ ⊢ Γ, B }} by mauto 3.
        assert {{ Δ ⊢ A[Wk∘σ] : Sort@s0 }} by (eapply glu_sort_elem_trm_sort_lvl; mauto 3).
        assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] : Sort@s0 }} as -> by mauto 4.
        assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] }} by (eapply wf_typ_eq_sorted; mauto 3).
        assert {{ Γ ⊢ #n : A }} by mauto 5.
        assert {{ Γ, B ⊢ A[Wk] }} by mauto 4.
        assert {{ Γ, B ⊢ #n[Wk] : A[Wk] }} by mauto 4.
        assert {{ Γ, B ⊢ #n[Wk] ≈ #(S n) : A[Wk] }} by mauto 3.
        assert {{ Δ ⊢ #n[Wk][σ] ≈ #(S n)[σ] : A[Wk∘σ] }} as <- by (eapply wf_exp_eq_conv'; mauto 3).
        assert {{ Δ ⊢ #n[Wk∘σ] ≈ #n[Wk][σ] : A[Wk∘σ] }} as <- by mauto 4.
        eassumption.
  - intros.
    inversion_clear H3.
    assert (glu_ctx_env pred_P (so_None::anns0) Sb {{{ Γ, B }}}) by (econstructor; mauto).
    specialize (IHHx so anns0 ltac:(econstructor; mauto 2) H4).
    handle_functional_glu_ctx_env P.
    destruct so.
    + assert {{ Γ ⊢ A }} by mauto 3.
      inversion_clear IHHx.
      destruct_conjs.
      handle_functional_glu_ctx_env P.
      do 2 eexists.
      * econstructor; try reflexivity; mauto.
      * intros.
        destruct_by_head (@cons_glu_sub_pred P).
        rewrite <- H8 in H12.
        destruct_glu_rel_exp_with_sub_unsorted; simplify_evals.
        econstructor; mauto.
        assert {{ ⊢ Γ, B }} by mauto 3.
        assert (typ_rel0 Δ {{{ A[Wk∘σ] }}}) by (eapply glu_typ_elem_trm_typ; mauto 2).
        assert {{ Δ ⊢ A[Wk∘σ]  }} by (eapply glu_typ_elem_typ_escape; mauto 2).
        assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] }} as -> by mauto 4.
        assert {{ Γ ⊢ #n : A }} by mauto 5.
        assert {{ Γ, B ⊢ A[Wk] }} by mauto 4.
        assert {{ Γ, B ⊢ #n[Wk] : A[Wk] }} by mauto 4.
        assert {{ Γ, B ⊢ #n[Wk] ≈ #(S n) : A[Wk] }} by mauto 3.
        assert {{ Δ ⊢ #n[Wk][σ] ≈ #(S n)[σ] : A[Wk∘σ] }} as <- by (eapply wf_exp_eq_conv'; mauto 3).
        assert {{ Δ ⊢ #n[Wk∘σ] ≈ #n[Wk][σ] : A[Wk∘σ] }} as <- by mauto 4.
        eassumption.
    + assert {{ Γ ⊢ A : Sort@s }} by mauto 3.
      inversion_clear IHHx.
      destruct_conjs.
      handle_functional_glu_ctx_env P.
      do 2 eexists.
      * econstructor; try reflexivity; mauto.
      * intros.
        destruct_by_head (@cons_glu_sub_pred P).
        rewrite <- H8 in H12.
        destruct_glu_rel_exp_with_sub_unsorted; simplify_evals.
        econstructor; mauto.
        assert {{ ⊢ Γ, B }} by mauto 3.
        assert {{ Δ ⊢ A[Wk∘σ] : Sort@s }} by (eapply glu_sort_elem_trm_sort_lvl; mauto 3).
        assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] : Sort@s }} as -> by mauto 4.
        assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] }} by (eapply wf_typ_eq_sorted; mauto 3).
        assert {{ Γ ⊢ #n : A }} by mauto 5.
        assert {{ Γ, B ⊢ A[Wk] }} by mauto 4.
        assert {{ Γ, B ⊢ #n[Wk] : A[Wk] }} by mauto 4.
        assert {{ Γ, B ⊢ #n[Wk] ≈ #(S n) : A[Wk] }} by mauto 3.
        assert {{ Δ ⊢ #n[Wk][σ] ≈ #(S n)[σ] : A[Wk∘σ] }} as <- by (eapply wf_exp_eq_conv'; mauto 3).
        assert {{ Δ ⊢ #n[Wk∘σ] ≈ #n[Wk][σ] : A[Wk∘σ] }} as <- by mauto 4.
        eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_vlookup : mcpts.


Lemma glu_rel_exp_sub_typ_unsorted {P} (pred_P : PredicativeSig P) : forall {anns Γ σ anns' Δ M A s},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }} ->
    {{ ⟪ pred_P ⟫ Δ with anns' ⊩u M : A @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M[σ] : A[σ] @ ^(so_Some s) }}.
Proof.
  intros * Hσ HM.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ M : A }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Δ with anns' ⊩u A : Sort@s @ ^so_None }} by mauto 3.
  destruct Hσ as [SbΓ [SbΔ]].
  destruct_conjs.
  inversion_clear HM as [? []].
  assert {{ Δ ⊢ A : Sort@s }} by mauto 3.
  eexists; split; mauto.
  intros Δ' τ ρ ?.
  destruct_glu_rel_sub_with_sub.
  handle_functional_glu_ctx_env P.
  rewrite <- H12 in H10.
  assert (glu_rel_exp_with_sub_unsorted pred_P (so_Some s) Δ' M A {{{ σ∘τ }}} ρ') by mauto 3.
  inversion_clear H3.
  assert {{ Dom a ≈ a ∈ per_sort pred_P s }} as [] by mauto.
  econstructor; mauto.

  assert {{ Δ' ⊢ A[σ][τ] ≈ A[σ∘τ] : Sort@s }} as -> by (symmetry; mauto 4).
  assert {{ Δ' ⊢ M[σ][τ] ≈ M[σ∘τ] : A[σ∘τ] }} as ->; mauto 3.
  symmetry; mauto 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_sub_typ_unsorted : mcpts.

Lemma glu_rel_exp_sub_sort_unsorted {P} (pred_P : PredicativeSig P) : forall {anns Γ σ anns' Δ M A},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }} ->
    {{ ⟪ pred_P ⟫ Δ with anns' ⊩u M : A @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M[σ] : A[σ] @ ^so_None }}.
Proof.
  intros * Hσ HM.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ M : A }} by mauto 3.
  destruct Hσ as [SbΓ [SbΔ]].
  destruct_conjs.
  inversion_clear HM as [? []].
  eexists; split; mauto.
  intros Δ' τ ρ ?.
  destruct_glu_rel_sub_with_sub.
  handle_functional_glu_ctx_env P.
  rewrite <- H10 in H8.
  assert (glu_rel_exp_with_sub_unsorted pred_P so_None Δ' M A {{{ σ∘τ }}} ρ') by mauto 3.
  inversion_clear H2.
  inversion H13; subst.
  simpl_glu_rel.
  inversion H19; subst.
  econstructor; mauto 3.
  eapply H15.
  split; [mauto 4|].
  do 2 eexists; split; mauto 3.
  assert {{ Δ' ⊢ M[σ∘τ] ≈ M[σ][τ] : Sort@s }} as <- by mauto 4.
  eassumption.
Qed.

#[export]
  Hint Resolve glu_rel_exp_sub_sort_unsorted : mcpts.

Lemma glu_rel_exp_sub_unsorted {P} (pred_P : PredicativeSig P) : forall {anns Γ σ anns' Δ M A so},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }} ->
    {{ ⟪ pred_P ⟫ Δ with anns' ⊩u M : A @ so }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M[σ] : A[σ] @ so }}.
Proof.
  intros.
  destruct so; mauto.
Qed.

#[export]
  Hint Resolve glu_rel_exp_sub_unsorted : mcpts.

Lemma glu_rel_typ_sub_typ_unsorted {P} (pred_P : PredicativeSig P) : forall {anns Γ σ anns' Δ A s},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }} ->
    {{ ⟪ pred_P ⟫ Δ with anns' ⊩u A @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A[σ] @ ^(so_Some s) }}.
Proof.
  intros * Hσ HA.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ A }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Δ with anns' ⊩u A @ ^(so_Some s) }} by mauto 3.
  destruct Hσ as [SbΓ [SbΔ]].
  destruct_conjs.
  assert {{ ⟪ pred_P ⟫ Δ with anns' ⊩u A : Sort@s @ ^so_None }} as HA' by mauto 2.
  inversion_clear HA as [? []].
  assert {{ Δ ⊢ A : Sort@s }} by mauto 3.
  eexists; split; mauto.
  intros Δ' τ ρ ?.
  destruct_glu_rel_sub_with_sub.
  handle_functional_glu_ctx_env P.
  rewrite <- H12 in H10.
  assert (glu_rel_typ_with_sub_unsorted pred_P (so_Some s) Δ' A {{{ σ∘τ }}} ρ') by mauto 3.
  inversion_clear H3.
  assert {{ Dom a ≈ a ∈ per_sort pred_P s }} as [] by mauto.
  econstructor; mauto.

  assert {{ Δ' ⊢ A[σ][τ] ≈ A[σ∘τ] : Sort@s }} as -> by (symmetry; mauto 4).
  eassumption.
Qed.

#[export]
Hint Resolve glu_rel_typ_sub_typ_unsorted : mcpts.

Lemma glu_rel_typ_sub_sort_unsorted {P} (pred_P : PredicativeSig P) : forall {anns Γ σ anns' Δ A},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }} ->
    {{ ⟪ pred_P ⟫ Δ with anns' ⊩u A @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A[σ] @ ^so_None }}.
Proof.
  intros * Hσ HA.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ A }} by mauto 3.
  destruct Hσ as [SbΓ [SbΔ]].
  destruct_conjs.
  inversion_clear HA as [? []].

  eexists; split; mauto.
  intros Δ' τ ρ ?.
  destruct_glu_rel_sub_with_sub.
  handle_functional_glu_ctx_env P.
  rewrite <- H10 in H8.
  assert (glu_rel_typ_with_sub_unsorted pred_P so_None Δ' A {{{ σ∘τ }}} ρ') by mauto 3.
  inversion_clear H2.
  inversion H12; subst.
  simpl_glu_rel.
  inversion H18; subst.
  econstructor; mauto 3.
  eapply H2.
  econstructor; mauto 4.
  symmetry; mauto 4.
Qed.

#[export]
Hint Resolve glu_rel_typ_sub_sort_unsorted : mcpts.

Lemma glu_rel_typ_sub_unsorted {P} (pred_P : PredicativeSig P) : forall {anns Γ σ anns' Δ A so},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }} ->
    {{ ⟪ pred_P ⟫ Δ with anns' ⊩u A @ so }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A[σ] @ so }}.
Proof.
  intros; destruct so; mauto.
Qed.

#[export]
Hint Resolve glu_rel_typ_sub_unsorted : mcpts.

Ltac rewrite_Sb Sb Δ σ ρ :=
  match goal with
  | H : Sb <∙> ?Sb', H2 : ?Sb' Δ σ ρ |- _ =>
      assert (Sb Δ σ ρ) by (rewrite <- H in H2; mauto 2)
  end.

Lemma glu_rel_exp_conv_unsorted {P} (pred_P : PredicativeSig P) : forall {anns Γ M A A' so so'},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A @ so }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A' @ so' }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A' @ so' }}.
Proof.
  intros * [Sb [? HA]] [SbA' [? HA']] ?.

  all: (
         assert {{ ⟪ pred_P ⟫ Γ ⊨ A ⊆ A' }} as [env_relΓ [? rel_subtyp]] by (eapply completeness_fundamental; mauto 2);
         handle_functional_glu_ctx_env P;
         assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ [ρ']] by (eauto using per_ctx_then_per_env_initial_env);
         destruct_conjs;
         destruct_rel_by_assumption env_relΓ rel_subtyp;

         destruct_by_head (@rel_typ_unsorted P);
         destruct_by_head (@rel_exp);
         simplify_evals;
         
         assert {{ Γ ⊢s Id ® ρ ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto 2);
         destruct_glu_rel_exp_with_sub;
         simplify_evals;
         
         eexists; split; [eauto |];
         intros;
         
         unshelve (epose proof HA Δ σ ρ0 _ as glu_relA); mauto 2;
         dependent destruction glu_relA;
         
         assert (env_relΓ ρ0 ρ0) by (eapply glu_ctx_env_per_env; mauto 2);
         assert (exists R0 R0' : relation (domain P),
               rel_typ_unsorted pred_P A ρ0 A ρ0 R0 /\ rel_typ_unsorted pred_P A' ρ0 A' ρ0 R0' /\ rel_exp A ρ0 A' ρ0 (per_subtyp pred_P)
           ) by mauto;
         destruct_conjs;
         destruct_by_head (@rel_typ_unsorted P);
         destruct_by_head (@rel_exp);
         simplify_evals;

         assert (per_typ_elem pred_P (per_sort pred_P s) d{{{ Sort@s }}} d{{{ Sort@s }}}) by (eapply per_typ_sort; reflexivity);
         rewrite_Sb SbA' Δ σ ρ0;
         unshelve (epose proof (HA' Δ σ ρ0 _) as glu_relA'); mauto 2;
         inversion glu_relA'; subst;
         simplify_evals
       ).
  - inversion H18; subst.
    inversion H28; subst.
    apply_predicate_equivalence.

    econstructor; mauto 3.

    epose proof per_subtyp_sort_inv_right pred_P H31 as [s'' []].
    inversion H25; subst.

    unfold top_sort_glu_exp_pred in *.
    unfold top_sort_glu_typ_pred in *.
    destruct_conjs.
    handle_functional_glu_sort_elem P.

    epose proof glu_sort_elem_cumu pred_P H35 H38 as [? []].
    epose proof glu_sort_elem_typ_cumu pred_P H35 H38 H13 H39.
    handle_functional_glu_sort_elem P.
    split; mauto 4.
  - inversion H18; subst.
    apply_predicate_equivalence.  
    unfold top_sort_glu_exp_pred in *.
    destruct_conjs.
    
    epose proof per_subtyp_sort_inv_left pred_P H31 as [s'' []].
    inversion H36; subst.
    
    
    epose proof glu_sort_elem_cumu pred_P H37 H34 as [? []].
    epose proof glu_sort_elem_typ_cumu pred_P H37 H34 H36 H35.
    invert_glu_sort_elem H26.
    
    unfold sort_glu_exp_pred' in *.
    unfold glu_sort_typ_rec in *.
    simpl_glu_rel.
    apply_predicate_equivalence.
    
    assert {{ Δ ⊢ M[σ] : Sort@s'' }} by (eapply glu_sort_elem_sort_lvl; mauto 2).
    
    econstructor; mauto 2.
    econstructor; mauto 3.
    split; [eassumption|].
    econstructor; mauto 3.
  - epose proof per_subtyp_sort_inv_right pred_P H30 as [s'' []].
    inversion H25; subst.

    invert_glu_sort_elem H17.
    unfold sort_glu_exp_pred' in *.
    unfold glu_sort_typ_rec in *.

    handle_functional_glu_sort_elem P.
    destruct_conjs.
    
    epose proof glu_sort_elem_cumu pred_P H27 H33 as [? []].
    epose proof glu_sort_elem_typ_cumu pred_P H27 H33 H35 H34.
    inversion H29; subst.
    simpl_glu_rel.

    econstructor; mauto 4.
    apply_predicate_equivalence.
    split; mauto 4.
  - econstructor; mauto.  
    eapply glu_sort_elem_per_subtyp_trm_conv; mauto 3.
Qed.
#[export]
  Hint Resolve glu_rel_exp_conv_unsorted : mcpts.

Lemma glu_rel_exp_conv {P} (pred_P : PredicativeSig P) : forall {anns Γ M A A' s s'},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ M : A @ s }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ A' @ s' }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ M : A' @ s' }}.
Proof. mauto. Qed.

#[export]
  Hint Resolve glu_rel_exp_conv : mcpts.

Lemma glu_rel_exp_conv_sort {P} (pred_P : PredicativeSig P) : forall {anns Γ M A s s'},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ M : A @ s }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ A @ s' }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ M : A @ s' }}.
Proof.
  intros * [SbΓ []] [SbΓ' []].
  handle_functional_glu_ctx_env P.
  eexists; split; mauto 2.
  intros.
  assert (SbΓ' Δ σ ρ) by (eapply H4; eassumption).
  destruct_glu_rel_exp_with_sub.
  destruct_glu_rel_typ_with_sub.
  simplify_evals.
  econstructor; mauto 3.

  assert (per_sort pred_P s a a) by mauto 3.
  eapply (glu_sort_elem_exp_conv pred_P H9 H7 H10); mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_exp_conv_sort : mcpts.

Lemma glu_rel_exp_conv_sort_unsorted {P} (pred_P : PredicativeSig P) : forall {anns Γ M A so so'},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A @ so }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A @ so' }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A @ so' }}.
Proof.
  intros * [SbΓ []] [SbΓ' []].
  handle_functional_glu_ctx_env P.
  eexists; split; mauto 2.
  intros.
  assert (SbΓ' Δ σ ρ) by (eapply H4; eassumption).
  assert (glu_rel_exp_with_sub_unsorted pred_P so Δ M A σ ρ) by mauto 2.
  dependent destruction H5.
  - inversion_clear H8.
    assert (glu_rel_typ_with_sub_unsorted pred_P so' Δ A σ ρ) by mauto 2.
    dependent destruction H8.
    + inversion_clear H13.
      simpl_glu_rel.
      handle_per_sort_elem_irrel.
      inversion H; subst.
      invert_glu_sort_elem H13.
    + simpl_glu_rel.
      subst.
      simplify_evals.
      
      invert_glu_sort_elem H12.
      unfold sort_glu_exp_pred' in *.
      unfold glu_sort_typ_rec in *.
      simpl_glu_rel.

      assert {{ Δ ⊢ Sort@s0 ≈ Sort@s }} by mauto 4.
      assert {{ Δ ⊢ M[σ] : Sort@s0 }} by (eapply glu_sort_elem_sort_lvl; mauto 2).
      assert {{ Δ ⊢ M[σ] : A[σ] }} by mauto 3.

      assert (SbΓ' Δ σ ρ) by (rewrite <- H4 in H6; mauto 2).
      assert (glu_rel_typ_with_sub_unsorted pred_P (so_Some s1) Δ A σ ρ) by mauto 2.
      assert (glu_rel_exp_with_sub_unsorted pred_P so_None Δ M A σ ρ) by mauto 2.
      dependent destruction H18.
      dependent destruction H21.
      handle_functional_glu_sort_elem P.

      inversion H24; subst.
      inversion H21; subst.
      invert_glu_sort_elem H19.
      apply_predicate_equivalence.
      unfold top_sort_glu_exp_pred in *.
      destruct_conjs.

      econstructor; mauto 4.
      econstructor; mauto 4.
      split; mauto 4.
      econstructor; mauto 4.
  - assert (glu_rel_typ_with_sub_unsorted pred_P so' Δ A σ ρ) by mauto 2.
    dependent destruction H9.
    + inversion_clear H11.
      subst.
      simplify_evals.
      invert_glu_sort_elem H7.
      simpl_glu_rel.
      econstructor; mauto 3.
      * econstructor; reflexivity.
      * split; mauto 3.
    + simplify_evals.
      econstructor; mauto 3.
      assert (per_sort pred_P s a a) by mauto 3.
      eapply (glu_sort_elem_exp_conv pred_P H9 H7 H10); mauto 2.
Qed.

#[export]
  Hint Resolve glu_rel_exp_conv_sort_unsorted : mcpts.
