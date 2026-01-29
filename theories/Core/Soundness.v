From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Semantic Require Export NbE.
From McPTS.Core.Soundness Require Export FundamentalTheorem.
From McPTS.Core.Soundness.Extension Require Export SystemAnnotated.
Import Domain_Notations.

Theorem full_soundness {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    exists W, nbe Γ M A W /\ {{ Γ ⊢ M ≈ W : A }}.
Proof.
  intros * H.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ ⟪ pred_P ⟫ ⊨ Γ }} as [env_relΓ] by (apply completeness_fundamental_ctx; eassumption).
  destruct (soundness_fundamental_exp pred_P full_P _ _ _ H) as [s [Sb []]].
  pose proof (per_ctx_then_per_env_initial_env ltac:(eassumption)) as [p].
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Γ ⊢s Id ® p ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto).
  destruct_glu_rel_exp_with_sub.
  assert {{ Γ ⊢ M[Id] : A[Id] ® m ∈ glu_elem_top pred_P s a }} as [] by (eapply realize_glu_elem_top; mauto).
  match_by_head (@per_top P) ltac:(fun H => destruct (H (length Γ)) as [W []]).
  eexists.
  split; [econstructor |]; try eassumption.
  assert {{ Γ ⊢ A[Id] ≈ A : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ A[Id][Id] ≈ A : Sort@s }} as HA by (transitivity {{{ A[Id] }}}; mauto 3).
  assert {{ Γ ⊢ M[Id][Id] ≈ W : A[Id][Id] }} as HM by mauto 3.
  assert {{ Γ ⊢ M[Id][Id] ≈ W : A }} as HM' by mauto 3.
  assert {{ Γ ⊢ M[Id] ≈ M : A }} by mauto 3.
  assert {{ Γ ⊢ M[Id][Id] ≈ M : A }} by (transitivity {{{ M[Id] }}}; mauto 3).
  transitivity {{{ M[Id][Id] }}}; mauto 3.
Qed.

Theorem full_soundness' {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ : ctx P} {M A W},
    {{ Γ ⊢ M : A }} ->
    nbe Γ M A W ->
    {{ Γ ⊢ M ≈ W : A }}.
Proof.
  intros * [? []]%(full_soundness pred_P full_P) ?.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.

Lemma full_soundness_ty {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    exists W, nbe_ty Γ A W /\ {{ Γ ⊢ A ≈ W }}.
Proof.
  intros.
  assert (exists s, {{ Γ ⊢ A : Sort@s }}) as [s] by (eapply wf_typ_full_implies_wf_exp; mauto 2).
  assert (exists W, nbe Γ A {{{ Sort@s }}} W /\ {{ Γ ⊢ A ≈ W : Sort@s }}) as [W [?%nbe_type_to_nbe_ty Heq]] by mauto using full_soundness.
  eexists; split; mauto 3.
Qed.

Lemma full_soundness_ty' {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ : ctx P} {A W},
    {{ Γ ⊢ A }} ->
    nbe_ty Γ A W ->
    {{ Γ ⊢ A ≈ W }}.
Proof.
  intros.
  assert (exists B', nbe_ty Γ A B' /\ {{ Γ ⊢ A ≈ B' }}) as [? [? Heq]] by mauto using full_soundness_ty.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.
