From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import System.

Lemma ctx_eq_refl {P : PtsSig} : forall {Γ : Ctx P}, {{ ⊢ Γ }} -> {{ ⊢ Γ ≈ Γ }}.
Proof with mautosolve.
  intros *.
  induction 1; econstructor; mauto 2; econstructor; mauto 2.
Qed.

#[export]
Hint Resolve ctx_eq_refl : mcpts.

Lemma ctx_eq_sym {P : PtsSig} : forall {Γ Δ : Ctx P}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ ≈ Γ }}.
Proof.
  intros.
  symmetry.
  eassumption.
Qed.

#[export]
Hint Resolve ctx_eq_sym : mcpts.

Lemma ctxeq_exp {P : PtsSig} : forall {Γ : Ctx P} {Δ M A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ M : A }} -> {{ Δ ⊢ M : A }}.
Proof. mauto. Admitted.

Lemma ctxeq_exp_eq {P : PtsSig} : forall {Γ : Ctx P} {Δ M M' A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ M ≈ M' : A }} -> {{ Δ ⊢ M ≈ M' : A }}.
Proof. mauto. Admitted.

Lemma ctxeq_sub {P : PtsSig} : forall {Γ : Ctx P} {Δ σ Γ'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ : Γ' }} -> {{ Δ ⊢s σ : Γ' }}.
Proof. mauto. Admitted.

Lemma ctxeq_sub_eq {P : PtsSig} : forall {Γ : Ctx P} {Δ σ σ' Γ'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
Proof. mauto. Admitted.

#[export]
Hint Resolve ctxeq_exp ctxeq_exp_eq ctxeq_sub ctxeq_sub_eq : mcpts.


Lemma ctx_eq_trans {P : PtsSig} : forall {Γ0 Γ1 Γ2 : Ctx P}, {{ ⊢ Γ0 ≈ Γ1 }} -> {{ ⊢ Γ1 ≈ Γ2 }} -> {{ ⊢ Γ0 ≈ Γ2 }}.
Proof with mautosolve.
  intros * HΓ01.
  gen Γ2.
  induction HΓ01 as [|Γ0 ? s01 T0 T1]; mauto.
  inversion_clear 1 as [|? Γ2' s12 ? T2].
  clear Γ2; rename Γ2' into Γ2.
  assert {{ ⊢ Γ0 ≈ Γ2 }} by mauto.
  assert {{ Γ0 ⊢ T0 ≈ T2 : Sort@s01 }}.
  {
    transitivity {{{ T1 }}}; mauto.
  }
  econstructor...
Qed.

#[export]
Hint Resolve ctx_eq_trans : mcpts.

#[export]
Instance wf_ctx_PER {P : PtsSig} : PER (@eq_ctx P).
Proof.
  split.
  - eauto using ctx_eq_sym.
  - eauto using ctx_eq_trans.
Qed.



Add Parametric Morphism {P : PtsSig} : (@wf_exp P)
  with signature eq_ctx ==> eq ==> eq ==> iff as ctxeq_exp_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P : PtsSig} : (@eq_exp P)
  with signature eq_ctx ==> eq ==> eq ==> eq ==> iff as ctxeq_exp_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P : PtsSig} : (@wf_sub P)
  with signature eq_ctx ==> eq ==> eq ==> iff as ctxeq_sub_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P : PtsSig} : (@eq_sub P)
  with signature eq_ctx ==> eq ==> eq ==> eq ==> iff as ctxeq_sub_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.
