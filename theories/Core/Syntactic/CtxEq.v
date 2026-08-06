From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export System CtxSub.
Import Syntax_Notations.

(** * Stability of judgments under global context equality *)
#[local]
Ltac solve_gctxeq :=
  intros; assert {{ ⊢ Δ' ⊆ Δ }} as -> by mauto 3; eassumption.
  
Lemma gctxeq_wf_ctx {P : PtsSig} : forall {Δ Δ' : gctx P} {Γ}, {{ ⊢ Δ ≈ Δ' }} -> {{ Δ ⊢ Γ }} -> {{ Δ' ⊢ Γ }}.
Proof. solve_gctxeq. Qed.

Lemma gctxeq_wf_ctx_subtyp {P : PtsSig} : forall {Δ Δ' : gctx P} {Γ Γ'}, {{ ⊢ Δ ≈ Δ' }} -> {{ Δ ⊢ Γ ⊆ Γ' }} -> {{ Δ' ⊢ Γ ⊆ Γ' }}.
Proof. solve_gctxeq. Qed.

Lemma gctxeq_wf_ctx_eq {P : PtsSig} : forall {Δ Δ' : gctx P} {Γ Γ'}, {{ ⊢ Δ ≈ Δ' }} -> {{ Δ ⊢ Γ ≈ Γ' }} -> {{ Δ' ⊢ Γ ≈ Γ' }}.
Proof. solve_gctxeq. Qed.

Lemma gctxeq_wf_exp {P : PtsSig} : forall {Δ Δ' : gctx P} {Γ A M}, {{ ⊢ Δ ≈ Δ' }} -> {{ Δ ; Γ ⊢ M : A }} -> {{ Δ' ; Γ ⊢ M : A }}.
Proof. solve_gctxeq. Qed.

Lemma gctxeq_wf_exp_eq {P : PtsSig} : forall {Δ Δ' : gctx P} {Γ A M M'}, {{ ⊢ Δ ≈ Δ' }} -> {{ Δ ; Γ ⊢ M ≈ M' : A }} -> {{ Δ' ; Γ ⊢ M ≈ M' : A }}.
Proof. solve_gctxeq. Qed.

Lemma gctxeq_wf_typ {P : PtsSig} : forall {Δ Δ' : gctx P} {Γ A}, {{ ⊢ Δ ≈ Δ' }} -> {{ Δ ; Γ ⊢ A }} -> {{ Δ' ; Γ ⊢ A }}.
Proof. solve_gctxeq. Qed.

Lemma gctxeq_wf_typ_eq {P : PtsSig} : forall {Δ Δ' : gctx P} {Γ A A'}, {{ ⊢ Δ ≈ Δ' }} -> {{ Δ ; Γ ⊢ A ≈ A' }} -> {{ Δ' ; Γ ⊢ A ≈ A' }}.
Proof. solve_gctxeq. Qed.

Lemma gctxeq_wf_typ_subtyp {P : PtsSig} : forall {Δ Δ' : gctx P} {Γ A A'}, {{ ⊢ Δ ≈ Δ' }} -> {{ Δ ; Γ ⊢ A ⊆ A' }} -> {{ Δ' ; Γ ⊢ A ⊆ A' }}.
Proof. solve_gctxeq. Qed.

Lemma gctxeq_wf_sub {P : PtsSig} : forall {Δ Δ' : gctx P} {Γ Γ' σ}, {{ ⊢ Δ ≈ Δ' }} -> {{ Δ ; Γ ⊢s σ : Γ' }} -> {{ Δ' ; Γ ⊢s σ : Γ' }}.
Proof. solve_gctxeq. Qed.

Lemma gctxeq_wf_sub_eq {P : PtsSig} : forall {Δ Δ' : gctx P} {Γ Γ' σ σ'}, {{ ⊢ Δ ≈ Δ' }} -> {{ Δ ; Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ' ; Γ ⊢s σ ≈ σ' : Γ' }}.
Proof. solve_gctxeq. Qed.

#[export]
Hint Resolve gctxeq_wf_ctx gctxeq_wf_ctx_subtyp gctxeq_wf_ctx_eq gctxeq_wf_exp gctxeq_wf_exp_eq gctxeq_wf_typ gctxeq_wf_typ_eq gctxeq_wf_typ_subtyp gctxeq_wf_sub gctxeq_wf_sub_eq : mcpts. 

Lemma wf_gctx_eq_trans {P : PtsSig} : forall {Δ0 Δ1 Δ2 : gctx P}, {{ ⊢ Δ0 ≈ Δ1 }} -> {{ ⊢ Δ1 ≈ Δ2 }} -> {{ ⊢ Δ0 ≈ Δ2 }}.
Proof with mautosolve.
  intros * HΔ01.
  gen Δ2.
  induction HΔ01; mauto.
  intros.
  inversion_clear H7.
  assert {{ ⊢ Δ ≈ Δ'0 }} by mauto 2.
  econstructor; mauto 3.
  etransitivity; mauto 2.
  eapply gctxeq_wf_typ_eq; mauto 2.
Qed.

#[export]
Hint Resolve wf_gctx_eq_trans : mcpts.

#[export]
Instance wf_ctx_PER {P : PtsSig} : PER (@wf_gctx_eq P).
Proof.
  split.
  - eauto using wf_gctx_eq_sym.
  - eauto using wf_gctx_eq_trans.
Qed.

(** ** Rewrite rules based on context equality *)
Add Parametric Morphism {P : PtsSig} : (@wf_ctx P)
  with signature wf_gctx_eq ==> eq ==> iff as gctxeq_wf_ctx_morphism.
Proof.
  intros; split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} : (@wf_ctx_subtyp P)
  with signature wf_gctx_eq ==> eq ==> eq ==> iff as gctxeq_wf_ctx_subtyp_morphism.
Proof.
  intros; split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} : (@wf_ctx_eq P)
  with signature wf_gctx_eq ==> eq ==> eq ==> iff as gctxeq_wf_ctx_eq_morphism.
Proof.
  intros; split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} : (@wf_exp P)
    with signature wf_gctx_eq ==> eq ==> eq ==> eq ==> iff as gctxeq_wf_exp_morphism.
Proof.
  intros; split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} : (@wf_exp_eq P)
    with signature wf_gctx_eq ==> eq ==> eq ==> eq ==> eq ==> iff as gctxeq_wf_exp_eq_morphism.
Proof.
  intros; split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} : (@wf_typ P)
    with signature wf_gctx_eq ==> eq ==> eq ==> iff as gctxeq_wf_typ_morphism.
Proof.
  intros; split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} : (@wf_typ_eq P)
    with signature wf_gctx_eq ==> eq ==> eq ==> eq ==> iff as gctxeq_wf_typ_eq_morphism.
Proof.
  intros; split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} : (@wf_typ_subtyp P)
    with signature wf_gctx_eq ==> eq ==> eq ==> eq ==> iff as gctxeq_wf_typ_subtyp_morphism.
Proof.
  intros; split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} : (@wf_sub P)
  with signature wf_gctx_eq ==> eq ==> eq ==> eq ==> iff as gctxeq_wf_sub_morphism.
Proof.
  intros; split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} : (@wf_sub_eq P)
  with signature wf_gctx_eq ==> eq ==> eq ==> eq ==> eq ==> iff as gctxeq_wf_sub_eq_morphism.
Proof.
  intros; split; mauto 3.
Qed.



(** * Stability of judgments under local context equality *)
#[local]
Ltac solve_ctxeq :=
  intros; assert {{ Δ ⊢ Γ' ⊆ Γ }} as -> by mauto 3; eassumption.

Lemma ctxeq_wf_exp {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' A M}, {{ Δ ⊢ Γ ≈ Γ' }} -> {{ Δ ; Γ ⊢ M : A }} -> {{ Δ ; Γ' ⊢ M : A }}.
Proof. solve_ctxeq. Qed.

Lemma ctxeq_wf_exp_eq {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' A M M'}, {{ Δ ⊢ Γ ≈ Γ' }} -> {{ Δ ; Γ ⊢ M ≈ M' : A }} -> {{ Δ ; Γ' ⊢ M ≈ M' : A }}.
Proof. solve_ctxeq. Qed.

Lemma ctxeq_wf_typ {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' A}, {{ Δ ⊢ Γ ≈ Γ' }} -> {{ Δ ; Γ ⊢ A }} -> {{ Δ ; Γ' ⊢ A }}.
Proof. solve_ctxeq. Qed.

Lemma ctxeq_wf_typ_eq {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' A A'}, {{ Δ ⊢ Γ ≈ Γ' }} -> {{ Δ ; Γ ⊢ A ≈ A' }} -> {{ Δ ; Γ' ⊢ A ≈ A' }}.
Proof. solve_ctxeq. Qed.

Lemma ctxeq_wf_typ_subtyp {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' A A'}, {{ Δ ⊢ Γ ≈ Γ' }} -> {{ Δ ; Γ ⊢ A ⊆ A' }} -> {{ Δ ; Γ' ⊢ A ⊆ A' }}.
Proof. solve_ctxeq. Qed.

Lemma ctxeq_wf_sub {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' Γ'' σ}, {{ Δ ⊢ Γ ≈ Γ' }} -> {{ Δ ; Γ ⊢s σ : Γ'' }} -> {{ Δ ; Γ' ⊢s σ : Γ'' }}.
Proof. solve_ctxeq. Qed.

Lemma ctxeq_wf_sub_eq {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' Γ'' σ σ'}, {{ Δ ⊢ Γ ≈ Γ' }} -> {{ Δ ; Γ ⊢s σ ≈ σ' : Γ'' }} -> {{ Δ ; Γ' ⊢s σ ≈ σ' : Γ'' }}.
Proof. solve_ctxeq. Qed.

#[export]
Hint Resolve ctxeq_wf_exp ctxeq_wf_exp_eq ctxeq_wf_typ ctxeq_wf_typ_eq ctxeq_wf_typ_subtyp ctxeq_wf_sub ctxeq_wf_sub_eq : mcpts.


Lemma wf_ctx_eq_trans {P : PtsSig} : forall {Δ : gctx P} {Γ0 Γ1 Γ2}, {{ Δ ⊢ Γ0 ≈ Γ1 }} -> {{ Δ ⊢ Γ1 ≈ Γ2 }} -> {{ Δ ⊢ Γ0 ≈ Γ2 }}.
Proof with mautosolve.
  intros * HΓ01.
  gen Γ2.
  induction HΓ01; mauto.
  intros.
  inversion_clear H5.
  assert {{ Δ ⊢ Γ ≈ Γ'0 }} by mauto 2.
  econstructor; mauto 3.
  etransitivity; mauto 2.
  eapply ctxeq_wf_typ_eq; mauto 2.
Qed.

#[export]
Hint Resolve wf_ctx_eq_trans : mcpts.

#[export]
Instance wf_ctx_eq_PER {P : PtsSig} {Δ : gctx P} : PER (wf_ctx_eq Δ).
Proof.
  split.
  - eauto using wf_ctx_eq_sym.
  - eauto using wf_ctx_eq_trans.
Qed.


(** ** Rewrite rules based on context equality *)
Add Parametric Morphism {P : PtsSig} {Δ : gctx P} : (wf_exp Δ)
  with signature wf_ctx_eq Δ ==> eq ==> eq ==> iff as ctxeq_wf_exp_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P : PtsSig} {Δ : gctx P} : (wf_exp_eq Δ)
  with signature wf_ctx_eq Δ ==> eq ==> eq ==> eq ==> iff as ctxeq_wf_exp_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P} {Δ : gctx P} : (wf_typ Δ)
  with signature wf_ctx_eq Δ ==> eq ==> iff as ctxeq_wf_typ_morphism.
Proof.
  intros. split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} {Δ : gctx P} : (wf_typ_eq Δ)
  with signature wf_ctx_eq Δ ==> eq ==> eq ==> iff as ctxeq_wf_typ_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} {Δ : gctx P} : (wf_typ_subtyp Δ)
  with signature wf_ctx_eq Δ ==> eq ==> eq ==> iff as ctxeq_wf_typ_subtyp_morphism.
Proof.
  intros. split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} {Δ : gctx P} : (wf_sub Δ)
  with signature wf_ctx_eq Δ ==> eq ==> eq ==> iff as ctxeq_wf_sub_morphism.
Proof.
  intros. split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} {Δ : gctx P} : (wf_sub_eq Δ)
  with signature wf_ctx_eq Δ ==> eq ==> eq ==> eq ==> iff as ctxeq_wf_sub_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.
