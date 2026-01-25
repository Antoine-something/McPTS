From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Soundness Require Import
  ContextCases
  FunctionCases
  SubstitutionCases
  TermStructureCases
  SortCases.
From McPTS.Core.Soundness Require Export LogicalRelation.
From McPTS.Core.Soundness.Extension Require Import SystemAnnotated.
Import Domain_Notations.

Section soundness_fundamental.
  #[local]
  Ltac gen_soundness_IH P pred_P full_P soundness_ctx soundness_exp soundness_typ soundness_sub H :=
  match type of H with
  | {{ ⊢ ^?Γ }} =>
      let HΓ := fresh "HΓ" in
      pose proof soundness_ctx P pred_P full_P Γ H as HΓ
  | {{ ^?Γ ⊫ ^?M : ^?A > ^?s }} =>
      let HM := fresh "HM" in
      pose proof soundness_exp P pred_P full_P Γ A s M H as HM
  | {{ ^?Γ ⊫ ^?A > ^?s }} =>
      let HA := fresh "HA" in
      pose proof soundness_typ P pred_P full_P Γ A s H as HA
  | {{ ^?Γ ⊢s ^?σ : ^?Δ }} =>
      let Hσ := fresh "Hσ" in
      pose proof soundness_sub P pred_P full_P Γ Δ σ H as Hσ
  end.
   
  Theorem soundness_fundamental_ctx_ann {P} (pred_P : PredicativeSig P) (full_P : FullSig P) :
    forall Γ, {{ ⊢ Γ }} -> {{ ⟪ pred_P ⟫ ⊩ Γ }}
  with soundness_fundamental_exp_ann {P} (pred_P : PredicativeSig P) (full_P : FullSig P) :
    forall Γ A s M, {{ Γ ⊫ M : A > s }} -> {{ ⟪ pred_P ⟫ Γ ⊩ M : A > s }}
  with soundness_fundamental_typ_ann {P} (pred_P : PredicativeSig P) (full_P : FullSig P) :
    forall Γ A s, {{ Γ ⊫ A > s }} -> {{ ⟪ pred_P ⟫ Γ ⊩ A > s }}
  with soundness_fundamental_sub_ann {P} (pred_P : PredicativeSig P) (full_P : FullSig P) :
    forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }}.
  Proof.
    all: inversion_clear 1;
      (on_all_hyp: gen_soundness_IH P pred_P full_P soundness_fundamental_ctx_ann soundness_fundamental_exp_ann soundness_fundamental_typ_ann soundness_fundamental_sub_ann);
      clear soundness_fundamental_ctx_ann soundness_fundamental_exp_ann soundness_fundamental_typ_ann soundness_fundamental_sub_ann;
      mauto 2.

    - (* Context extensions. Need to define proper annotations {{ ⊫ Γ }} *)
      admit.
    - (* wf_typ_sort *)
      assert (exists s', Ax P s s') as [s'] by (eapply full_P).
      assert {{ ⟪ pred_P ⟫ Γ ⊩ Sort@s0 : Sort@s > s' }} by mauto 2.
      destruct H2 as [SbΓ []].
      econstructor; split; mauto 2.
      intros.
      destruct_glu_rel_exp_with_sub.
      simplify_evals.
      invert_glu_sort_elem H7.
      unfold sort_glu_exp_pred' in *.
      unfold glu_sort_typ_rec in *.
      eapply H6 in H8.
      destruct_conjs.      
      econstructor; mauto 2.      
      
    - (* wf_typ_exp *)
      destruct HM as [SbΓ []].
      eexists; split; mauto 2.
      intros.
      destruct_glu_rel_exp_with_sub.
      simplify_evals.
      invert_glu_sort_elem H5.
      unfold sort_glu_exp_pred' in *.
      unfold glu_sort_typ_rec in *.
      eapply H5 in H6.
      destruct_conjs.      
      econstructor; mauto 2.
    - (* Substitution extensions (need to properly define annotated judgments {{ Γ ⊫s σ : Δ }} *)
      admit.
    - (* Conversion for substitutions (need another lemma) *)
      admit.
      
  Admitted.
  

  Theorem soundness_fundamental_ctx {P} (pred_P : PredicativeSig P) (full_P : FullSig P) :
    forall Γ, {{ ⊢ Γ }} -> exists sts, {{ ⟪ pred_P ⟫ ⊩ Γ : sts }}.
  Proof.
    intros.
    assert (exists sts, {{ ⊫ Γ > sts }}) as [sts] by (eapply wf_ctx_implies_wf_ctx_ann; mauto 2).
    eexists.
    eapply soundness_fundamental_ctx_ann; mauto 2.
  Qed.

  Theorem soundness_fundamental_exp {P} (pred_P : PredicativeSig P) (full_P : FullSig P) :
    forall Γ M A, {{ Γ ⊢ M : A }} -> exists sts s, {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A : s }}.
  Proof.
    intros.
    assert (exists sts s, {{ Γ : sts ⊫ M : A > s }}) as [sts [s]] by (eapply wf_exp_implies_wf_exp_ann; mauto 2).
    do 2 eexists.
    eapply soundness_fundamental_exp_ann; mauto 2.
  Qed.

  Theorem soundness_fundamental_sub {P} (pred_P : PredicativeSig P) (full_P : FullSig P) :
    forall Γ σ Δ, {{ Γ ⊢s σ : Δ }} -> exists sts sts', {{ ⟪ pred_P ⟫ Γ : sts ⊩s σ : Δ : sts' }}.
  Proof.
    intros.
    assert (exists sts sts', {{ Γ : sts ⊫s σ : Δ > sts' }}) as [sts [sts']] by (eapply wf_sub_implies_wf_sub_ann; mauto 2).
    do 2 eexists.
    eapply soundness_fundamental_sub_ann; mauto 2.
  Qed.      
End soundness_fundamental.
