From McPTS Require Import LibTactics PtsSignature Base.
From McPTS.Core.Syntactic Require Export System CtxSub.
Import Syntax_Notations.

(** * Stability of judgments under local context equality *)
Lemma wf_ctx_eq_ctx_subtyp {P} : forall {Γ : ctx P} {Γ'},
    {{ ⊢ Γ ≈ Γ' }} ->
    {{ ⊢ Γ' ⊆ Γ }}.
Proof.
  intros.
  symmetry in H.
  mauto 3.
Qed.

#[local]
Ltac solve_ctxeq :=
  intros; assert {{ ⊢ Γ' ⊆ Γ }} as -> by (eapply wf_ctx_eq_ctx_subtyp; mauto 2); eassumption.

Lemma ctxeq_wf_exp {P : PtsSig} : forall {Γ : ctx P} {Γ' A M}, {{ ⊢ Γ ≈ Γ' }} -> {{ Γ ⊢ M : A }} -> {{ Γ' ⊢ M : A }}.
Proof. solve_ctxeq. Qed.

Lemma ctxeq_wf_exp_eq {P : PtsSig} : forall {Γ : ctx P} {Γ' A M M'}, {{ ⊢ Γ ≈ Γ' }} -> {{ Γ ⊢ M ≈ M' : A }} -> {{ Γ' ⊢ M ≈ M' : A }}.
Proof. solve_ctxeq. Qed.

Lemma ctxeq_wf_typ {P : PtsSig} : forall {Γ : ctx P} {Γ' A}, {{ ⊢ Γ ≈ Γ' }} -> {{ Γ ⊢ A }} -> {{ Γ' ⊢ A }}.
Proof. solve_ctxeq. Qed.

Lemma ctxeq_wf_typ_eq {P : PtsSig} : forall {Γ : ctx P} {Γ' A A'}, {{ ⊢ Γ ≈ Γ' }} -> {{ Γ ⊢ A ≈ A' }} -> {{ Γ' ⊢ A ≈ A' }}.
Proof. solve_ctxeq. Qed.

Lemma ctxeq_wf_typ_subtyp {P : PtsSig} : forall {Γ : ctx P} {Γ' A A'}, {{ ⊢ Γ ≈ Γ' }} -> {{ Γ ⊢ A ⊆ A' }} -> {{ Γ' ⊢ A ⊆ A' }}.
Proof. solve_ctxeq. Qed.

Lemma ctxeq_wf_sub {P : PtsSig} : forall {Γ : ctx P} {Γ' Γ'' σ}, {{ ⊢ Γ ≈ Γ' }} -> {{ Γ ⊢s σ : Γ'' }} -> {{ Γ' ⊢s σ : Γ'' }}.
Proof. solve_ctxeq. Qed.

Lemma ctxeq_wf_sub_eq {P : PtsSig} : forall {Γ : ctx P} {Γ' Γ'' σ σ'}, {{ ⊢Γ ≈ Γ' }} -> {{ Γ ⊢s σ ≈ σ' : Γ'' }} -> {{ Γ' ⊢s σ ≈ σ' : Γ'' }}.
Proof. solve_ctxeq. Qed.

#[export]
Hint Resolve ctxeq_wf_exp ctxeq_wf_exp_eq ctxeq_wf_typ ctxeq_wf_typ_eq ctxeq_wf_typ_subtyp ctxeq_wf_sub ctxeq_wf_sub_eq : mcpts.

Lemma wf_ctx_eq_sym {P : PtsSig} : forall {Γ : ctx P} {Γ'},
    {{ ⊢ Γ ≈ Γ' }} ->
    {{ ⊢ Γ' ≈ Γ }}.
Proof. intros; symmetry; eauto. Qed.
  
Lemma wf_ctx_eq_trans {P : PtsSig} : forall {Γ0 : ctx P} {Γ1 Γ2}, {{ ⊢ Γ0 ≈ Γ1 }} -> {{ ⊢ Γ1 ≈ Γ2 }} -> {{ ⊢ Γ0 ≈ Γ2 }}.
Proof with mautosolve.
  intros * HΓ01.
  gen Γ2.
  induction HΓ01; mauto.
  intros.
  inversion_clear H5.
  assert {{ ⊢ Γ ≈ Γ'0 }} by mauto 2.
  econstructor; mauto 3.
  etransitivity; mauto 2.
  eapply ctxeq_wf_typ_eq; mauto 3.
Qed.

#[export]
Hint Resolve wf_ctx_eq_sym wf_ctx_eq_trans : mcpts.

#[export]
Instance wf_ctx_eq_PER {P : PtsSig} : PER (@wf_ctx_eq P).
Proof.
  split; eauto using wf_ctx_eq_sym, wf_ctx_eq_trans.
Qed.

(** ** Rewrite rules based on context equality *)
Add Parametric Morphism {P : PtsSig} : (@wf_exp P)
  with signature wf_ctx_eq ==> eq ==> eq ==> iff as ctxeq_wf_exp_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P : PtsSig} : (@wf_exp_eq P)
  with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as ctxeq_wf_exp_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P} : (@wf_typ P)
  with signature wf_ctx_eq ==> eq ==> iff as ctxeq_wf_typ_morphism.
Proof.
  intros. split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} : (@wf_typ_eq P)
  with signature wf_ctx_eq ==> eq ==> eq ==> iff as ctxeq_wf_typ_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} : (@wf_typ_subtyp P)
  with signature wf_ctx_eq ==> eq ==> eq ==> iff as ctxeq_wf_typ_subtyp_morphism.
Proof.
  intros. split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} : (@wf_sub P)
  with signature wf_ctx_eq ==> eq ==> eq ==> iff as ctxeq_wf_sub_morphism.
Proof.
  intros. split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} : (@wf_sub_eq P)
  with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as ctxeq_wf_sub_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.
