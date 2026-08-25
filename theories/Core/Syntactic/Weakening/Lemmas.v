From Coq Require Import Program.Equality.

From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic.Weakening Require Import Definitions.
From McPTS.Core.Syntactic Require Export Corollaries.
Import Syntax_Notations.

Lemma weakening_escape {P} : forall (Δ : gctx P) Γ Γ' σ,
    {{ Δ ▶ Γ ⊢w σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }}.
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
  | H : {{ ^_ ▶ ^_ ⊢w ^_ : ^_ }} |- _ =>
      pose proof (weakening_escape _ _ _ H);
      fail_if_dup
  end.

Ltac saturate_weakening_escape :=
  repeat saturate_weakening_escape1.

Lemma weakening_resp_equiv {P} : forall (Δ : gctx P) Γ Γ' σ σ',
    {{ Δ ▶ Γ ⊢w σ : Γ'}} ->
    {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ' }} ->
    {{ Δ ▶ Γ ⊢w σ' : Γ' }}.
Proof.
  induction 1; mauto.
Qed.

Lemma ctxeq_weakening {P} : forall (Δ : gctx P) Γ Γ' σ,
    {{ Δ ▶ Γ ⊢w σ : Γ' }} ->
    forall Γ'',
      {{ Δ ▶ Γ ≈ Γ'' }} ->
      {{ Δ ▶ Γ'' ⊢w σ : Γ' }}.
Proof.
  induction 1; mauto.
Qed.

Lemma weakening_conv {P} : forall (Δ : gctx P) Γ Γ' σ,
    {{ Δ ▶ Γ ⊢w σ : Γ' }} ->
    forall Γ'',
      {{ Δ ▶ Γ' ⊆ Γ'' }} ->
      {{ Δ ▶ Γ ⊢w σ : Γ'' }}.
Proof.
  induction 1; mauto.
Qed.

#[export]
Hint Resolve weakening_conv : mcpts.

Lemma weakening_compose {P} : forall (Δ : gctx P) Γ' Γ'' σ',
    {{ Δ ▶ Γ' ⊢w σ' : Γ'' }} ->
    forall Γ σ,
      {{ Δ ▶ Γ ⊢w σ : Γ' }} ->
      {{ Δ ▶ Γ ⊢w σ' ∘ σ : Γ'' }}.
Proof with mautosolve.
  induction 1; intros.
  - gen_presup H.
    assert {{ Δ ▶ Γ ⊆ Γ' }} by mauto.
    eapply weakening_resp_equiv with (σ := σ0); [mauto 2 |].
    transitivity {{{ Id ∘ σ0 }}}...
  - saturate_weakening_escape.
    gen_presups.
    eapply wk_p; eauto.
    transitivity {{{ (Wk ∘ τ) ∘ σ0 }}}; mauto 4.
    eapply wf_sub_eq_compose_assoc; mauto 3.
    econstructor; mauto 3.
    econstructor; mauto 3.
Qed.

#[export]
Hint Resolve weakening_compose : mcpts.

Lemma weakening_id {P} : forall (Δ : gctx P) Γ,
    {{ Δ ▶ Γ }} ->
    {{ Δ ▶ Γ ⊢w Id : Γ }}.
Proof.
  mauto.
Qed.

Lemma weakening_wk {P} : forall (Δ : gctx P) Γ A,
    {{ Δ ▶ Γ, A }} ->
    {{ Δ ▶ Γ, A ⊢w Wk : Γ }}.
Proof.
  intros.
  eapply wk_p; mauto 3.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve weakening_id weakening_wk : mcpts.

Lemma gctx_weakening_backwards_fresh {P} : forall {Δ Δ' : gctx P},
    {{ ▶w Δ < Δ' }} ->
    forall x,
      {{ `#x ∉ Δ' }} ->
      {{ `#x ∉ Δ }}.
Proof.
  induction 1; intros * HxfreshinΔ'; mauto 2;
    inversion HxfreshinΔ'; subst; mauto 3.
Qed.

#[export]
Hint Resolve gctx_weakening_backwards_fresh : mcpts.

Lemma gctx_weakening_preserves_lookups {P} : forall {Δ Δ' : gctx P},
    {{ ▶w Δ < Δ' }} ->
    forall x B,
      {{ `#x : B ∈ Δ }} ->
      {{ `#x : B ∈ Δ' }}.
Proof.
  induction 1; intros * HxinΔ; mauto 2;
    inversion HxinΔ; subst; mauto 3.
  - pose proof (IHgctx_weakening _ _ HxinΔ).
    mauto 3.
  - pose proof (IHgctx_weakening _ _ HxinΔ).
    mauto 3.
Qed.

#[export]
Hint Resolve gctx_weakening_preserves_lookups : mcpts.

Lemma gctx_weakening_presup {P} : forall {Δ Δ' : gctx P},
    {{ ▶w Δ < Δ' }} ->
    {{ ▶ Δ }} /\ {{ ▶ Δ' }}.
Proof.
  induction 1; split; destruct_pairs; mauto 3.
Qed.

#[export]
Hint Resolve gctx_weakening_presup : mcpts.
 
Lemma strong_gctx_weakening {P : PtsSig} :
  (forall (Δ : gctx P) Γ, {{ Δ ▶ Γ }} -> forall Δ', {{ ▶w Δ < Δ' }} -> {{ Δ' ▶ Γ }}) /\
    (forall (Δ : gctx P) Γ Γ', {{ Δ ▶ Γ ⊆ Γ' }} -> forall Δ', {{ ▶w Δ < Δ' }} -> {{ Δ' ▶ Γ ⊆ Γ' }}) /\
    (forall (Δ : gctx P) Γ A M, {{ Δ ▶ Γ ⊢ M : A }} -> forall Δ', {{ ▶w Δ < Δ' }} -> {{ Δ' ▶ Γ ⊢ M : A }}) /\
    (forall (Δ : gctx P) Γ A M M', {{ Δ ▶ Γ ⊢ M ≈ M' : A }} -> forall Δ', {{ ▶w Δ < Δ' }} -> {{ Δ' ▶ Γ ⊢ M ≈ M' : A }}) /\
    (forall (Δ : gctx P) Γ A, {{ Δ ▶ Γ ⊢ A }} -> forall Δ', {{ ▶w Δ < Δ' }} -> {{ Δ' ▶ Γ ⊢ A }}) /\
    (forall (Δ : gctx P) Γ A A', {{ Δ ▶ Γ ⊢ A ≈ A' }} -> forall Δ', {{ ▶w Δ < Δ' }} -> {{ Δ' ▶ Γ ⊢ A ≈ A' }}) /\
    (forall (Δ : gctx P) Γ A A', {{ Δ ▶ Γ ⊢ A ⊆ A' }} -> forall Δ', {{ ▶w Δ < Δ' }} -> {{ Δ' ▶ Γ ⊢ A ⊆ A' }}) /\
    (forall (Δ : gctx P) Γ Γ' σ, {{ Δ ▶ Γ ⊢s σ : Γ' }} -> forall Δ', {{ ▶w Δ < Δ' }} -> {{ Δ' ▶ Γ ⊢s σ : Γ' }}) /\
    (forall (Δ : gctx P) Γ Γ' σ σ', {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ' }} -> forall Δ', {{ ▶w Δ < Δ' }} -> {{ Δ' ▶ Γ ⊢s σ ≈ σ' : Γ' }}).
Proof.
  apply syntactic_wf_local_mut_ind;
    intros;
    try mauto 2;
    try solve [econstructor; mauto 3].

  all:
    match goal with
    | [H : {{ ▶w ^?Δ < ^?Δ' }} |- _ ] =>
        let HΔ := fresh "HΔ" in
        let HΔ' := fresh "HΔ'" in
        pose proof gctx_weakening_presup H as [HΔ HΔ']
    end;
    mauto 3.

  pose proof (H _ H2).
  pose proof (H0 _ H2).
  pose proof (H1 _ H2).
  econstructor; mauto 3.
Qed.  
