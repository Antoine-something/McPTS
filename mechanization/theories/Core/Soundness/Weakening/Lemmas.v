From Coq Require Import Program.Equality.

From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Soundness.Weakening Require Import Definitions.
From McPTS.Core.Syntactic Require Export Corollaries.
Import Syntax_Notations.

Lemma weakening_escape {P : PtsSig} : forall (Γ : ctx P) σ Δ,
    {{ Γ ⊢w σ : Δ }} ->
    {{ Γ ⊢s σ : Δ }}.
Proof.
  induction 1;
    match goal with
    | H : _ |- _ =>
        solve [gen_presup H; trivial]
    end.
Qed.

#[export]
Hint Resolve weakening_escape : mcpts.


Ltac saturate_weakening_escape1 :=
  match goal with
  | H : {{ ^_ ⊢w ^_ : ^_ }} |- _ =>
      pose proof (weakening_escape _ _ _ H);
      fail_if_dup
  end.

Ltac saturate_weakening_escape :=
  repeat saturate_weakening_escape1.

Lemma weakening_resp_equiv {P} : forall (Γ : ctx P) σ σ' Δ,
    {{ Γ ⊢w σ : Δ }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢w σ' : Δ }}.
Proof.
  induction 1; mauto.
Qed.

Lemma ctxeq_weakening {P} : forall (Γ : ctx P) σ Δ,
    {{ Γ ⊢w σ : Δ }} ->
    forall Γ',
      {{ ⊢ Γ ≈ Γ' }} ->
      {{ Γ' ⊢w σ : Δ }}.
Proof.
  induction 1; mauto.
Qed.

Lemma weakening_conv {P} : forall (Γ : ctx P) σ Δ,
    {{ Γ ⊢w σ : Δ }} ->
    forall Δ',
      {{ ⊢ Δ ≈ Δ' }} ->
      {{ Γ ⊢w σ : Δ' }}.
Proof.
  induction 1; mauto.
Qed.

#[export]
Hint Resolve weakening_conv : mcpts.

Lemma weakening_compose {P} : forall (Γ' : ctx P) σ' Γ'',
    {{ Γ' ⊢w σ' : Γ'' }} ->
    forall Γ σ,
      {{ Γ ⊢w σ : Γ' }} ->
      {{ Γ ⊢w σ' ∘ σ : Γ'' }}.
Proof with mautosolve.
  induction 1; intros.
  - gen_presup H.
    assert {{ ⊢ Γ ≈ Δ }} by mauto.
    eapply weakening_resp_equiv; [mauto 2 |].
    transitivity {{{ Id ∘ σ0 }}}...
  - eapply wk_p; eauto.
    transitivity {{{ (Wk ∘ τ) ∘ σ0 }}}; mauto 4.
    eapply wf_sub_eq_compose_assoc; revgoals...
Qed.

#[export]
Hint Resolve weakening_compose : mcpts.

Lemma weakening_id {P} : forall (Γ : ctx P),
    {{ ⊢ Γ }} ->
    {{ Γ ⊢w Id : Γ }}.
Proof.
  mauto.
Qed.

Lemma weakening_wk {P} : forall (Γ : ctx P) A,
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢w Wk : Γ }}.
Proof.
  intros.
  eapply wk_p; mauto 3.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve weakening_id weakening_wk : mcpts.
