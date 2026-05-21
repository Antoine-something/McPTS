From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export System CtxSub.
Import Syntax_Notations.


Lemma ctx_eq_refl {P : PtsSig} : forall {Γ : ctx P}, {{ ⊢ Γ }} -> {{ ⊢ Γ ≈ Γ }}.
Proof with mautosolve.
  induction 1; mauto 2.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve ctx_eq_refl : mcpts.

Lemma ctx_eq_sym {P : PtsSig} : forall {Γ Δ : ctx P}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ ≈ Γ }}.
Proof.
  intros.
  symmetry.
  eassumption.
Qed.

#[export]
Hint Resolve ctx_eq_sym : mcpts.

Lemma ctxeq_exp {P : PtsSig} : forall {Γ : ctx P} {Δ M A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ M : A }} -> {{ Δ ⊢ M : A }}.
Proof. mauto 4. Qed.

Lemma ctxeq_exp_eq {P : PtsSig} : forall {Γ : ctx P} {Δ M M' A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ M ≈ M' : A }} -> {{ Δ ⊢ M ≈ M' : A }}.
Proof. mauto 4. Qed.

Lemma ctxeq_sub {P : PtsSig} : forall {Γ : ctx P} {Δ σ Γ'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ : Γ' }} -> {{ Δ ⊢s σ : Γ' }}.
Proof. mauto 4. Qed.

Lemma ctxeq_sub_eq {P : PtsSig} : forall {Γ : ctx P} {Δ σ σ' Γ'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
Proof. mauto 4. Qed. 

Lemma ctxeq_subtyp {P} : forall {Γ : ctx P} {Δ A A'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ A ⊆ A' }} -> {{ Δ ⊢ A ⊆ A' }}.
Proof. mauto 4. Qed.

Lemma ctxeq_typ {P : PtsSig} : forall {Γ : ctx P} {Δ A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ A }} -> {{ Δ ⊢ A }}.
Proof. mauto 4. Qed.

Lemma ctxeq_typ_eq {P : PtsSig} : forall {Γ : ctx P} {Δ A B}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ A ≈ B }} -> {{ Δ ⊢ A ≈ B }}.
Proof. mauto 4. Qed.

#[export]
Hint Resolve ctxeq_exp ctxeq_exp_eq ctxeq_sub ctxeq_sub_eq ctxeq_subtyp ctxeq_typ ctxeq_typ_eq : mcpts.

Lemma ctx_eq_trans {P : PtsSig} : forall {Γ0 Γ1 Γ2 : ctx P}, {{ ⊢ Γ0 ≈ Γ1 }} -> {{ ⊢ Γ1 ≈ Γ2 }} -> {{ ⊢ Γ0 ≈ Γ2 }}.
Proof with mautosolve.
  intros * HΓ01.
  gen Γ2.
  induction HΓ01; mauto.
  intros.
  inversion_clear H5.
  assert {{ ⊢ Γ ≈ Δ0 }} by mauto 2.
  econstructor; mauto 3.
  etransitivity; mauto 2.
  eapply ctxeq_exp_eq; mauto 2.
Qed.

#[export]
Hint Resolve ctx_eq_trans : mcpts.

#[export]
Instance wf_ctx_PER {P : PtsSig} : PER (@wf_ctx_eq P).
Proof.
  split.
  - eauto using ctx_eq_sym.
  - eauto using ctx_eq_trans.
Qed.



Add Parametric Morphism {P : PtsSig} : (@wf_exp P)
  with signature wf_ctx_eq ==> eq ==> eq ==> iff as ctxeq_exp_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P : PtsSig} : (@wf_exp_eq P)
  with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as ctxeq_exp_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P} : (@wf_typ P)
  with signature wf_ctx_eq ==> eq ==> iff as ctxeq_typ_morphism.
Proof.
  intros. split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} : (@wf_typ_eq P)
  with signature wf_ctx_eq ==> eq ==> eq ==> iff as ctxeq_typ_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P : PtsSig} : (@wf_sub P)
  with signature wf_ctx_eq ==> eq ==> eq ==> iff as ctxeq_sub_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P : PtsSig} : (@wf_sub_eq P)
  with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as ctxeq_sub_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.
