From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Soundness Require Import
  ContextCases
  FunctionCases
  SubstitutionCases
  TermStructureCases
  NatCases
  SortCases.
From McPTS.Core.Soundness Require Export LogicalRelation.
From McPTS.Core.Soundness.Extension Require Import SystemAnnotated.
Import Domain_Notations.

Section soundness_fundamental.
  Theorem soundness_fundamental {P} (pred_P : PredicativeSig P) :
    (forall anns Γ, {{ ⊫ Γ with anns }} -> {{ ⟪ pred_P ⟫ ⊩ Γ with anns }}) /\
      (forall anns Γ A s M, {{ Γ with anns ⊫ M : A @ s }} -> {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A @ s }}) /\
      (forall anns Γ A s, {{ Γ with anns ⊫ A @ s }} -> {{ ⟪ pred_P ⟫ Γ with anns ⊩u A @ s }}) /\
      (forall anns anns' Γ Δ σ, {{ Γ with anns ⊫s σ : Δ with anns' }} -> {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }}).
  Proof.
    eapply syntactic_wf_ann_mut_ind; mauto.
    - intros.
      assert {{ ⊢ Γ }} by mauto 3 using wf_ctx_ann_implies_wf_ctx.
      assert {{ #x : A ∈ Γ}} by (eapply ann_lookup_implies_lookup; mauto 2).
      eapply glu_rel_exp_vlookup; mauto 3.
  Qed.

  #[local]
  Ltac solve_it pred_P := pose proof soundness_fundamental pred_P; firstorder.

  Corollary soundness_fundamental_ctx_ann {P} (pred_P : PredicativeSig P) :
    forall anns Γ, {{ ⊫ Γ with anns }} -> {{ ⟪ pred_P ⟫ ⊩ Γ with anns }}.
  Proof. solve_it pred_P. Qed.

  Corollary soundness_fundamental_exp_ann {P} (pred_P : PredicativeSig P) :
    forall anns Γ A so M, {{ Γ with anns ⊫ M : A @ so }} -> {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A @ so }}.
  Proof. solve_it pred_P. Qed.

  Corollary soundness_fundamental_typ_ann {P} (pred_P : PredicativeSig P) :
    forall anns Γ A so, {{ Γ with anns ⊫ A @ so }} -> {{ ⟪ pred_P ⟫ Γ with anns ⊩u A @ so }}.
  Proof. solve_it pred_P. Qed.

  Corollary soundness_fundamental_sub_ann {P} (pred_P : PredicativeSig P) :
    forall anns anns' Γ Δ σ, {{ Γ with anns ⊫s σ : Δ with anns' }} -> {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }}.
  Proof. solve_it pred_P. Qed.


  Theorem soundness_fundamental_ctx {P} (pred_P : PredicativeSig P) :
    forall Γ, {{ ⊢ Γ }} -> exists anns, {{ ⟪ pred_P ⟫ ⊩ Γ with anns }}.
  Proof.
    intros.
    assert (exists anns, {{ ⊫ Γ with anns }}) as [anns] by mauto 2.
    eexists.
    eapply soundness_fundamental_ctx_ann; mauto 2.
  Qed.

  Theorem soundness_fundamental_exp {P} (pred_P : PredicativeSig P) :
    forall anns Γ M A, {{ Γ ⊢ M : A }} -> {{ ⊫ Γ with anns }} -> exists so, {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A @ so }}.
  Proof.
    intros.
    assert (exists so, {{ Γ with anns ⊫ M : A @ so }}) as [so] by mauto 2.
    eexists.
    eapply soundness_fundamental_exp_ann; mauto 2.
  Qed.

  Theorem soundness_fundamental_typ {P} (pred_P : PredicativeSig P) :
    forall anns Γ A, {{ Γ ⊢ A }} -> {{ ⊫ Γ with anns }} -> exists so, {{ ⟪ pred_P ⟫ Γ with anns ⊩u A @ so }}.
  Proof.
    intros.
    assert (exists so, {{ Γ with anns ⊫ A @ so }}) as [so] by mauto 2.
    eexists.
    eapply soundness_fundamental_typ_ann; mauto 2.
  Qed.

  Theorem soundness_fundamental_sub {P} (pred_P : PredicativeSig P):
    forall anns Γ σ Δ, {{ Γ ⊢s σ : Δ }} -> {{ ⊫ Γ with anns }} -> exists anns', {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }}.
  Proof.
    intros.
    assert (exists anns', {{ Γ with anns ⊫s σ : Δ with anns' }}) as [anns'] by mauto 2.
    eexists.
    eapply soundness_fundamental_sub_ann; mauto 2.
  Qed.
End soundness_fundamental.
