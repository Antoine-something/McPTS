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
  Ltac gen_soundness_IH P pred_P full_P soundness_ctx soundness_exp soundness_sub H :=
  match type of H with
  | {{ ⊫ ^?Γ > ?sts }} =>
      let HΓ := fresh "HΓ" in
      pose proof soundness_ctx P pred_P full_P Γ sts H as HΓ
  | {{ ^?Γ : ?sts ⊫ ^?M : ^?A > ?s }} =>
      let HM := fresh "HM" in
      pose proof soundness_exp P pred_P full_P Γ sts A s M H as HM
  | {{ ^?Γ : ?stsΓ ⊫s ^?σ : ^?Δ > ?stsΔ }} =>
      let Hσ := fresh "Hσ" in
      pose proof soundness_sub P pred_P full_P Γ stsΓ Δ stsΔ σ H as Hσ
  end.
   
  Theorem soundness_fundamental_ctx_ann {P} (pred_P : PredicativeSig P) (full_P : FullSig P) :
    forall Γ sts, {{ ⊫ Γ > sts }} -> {{ ⟪ pred_P ⟫ ⊩ Γ : sts }}
  with soundness_fundamental_exp_ann {P} (pred_P : PredicativeSig P) (full_P : FullSig P) :
    forall Γ sts A s M, {{ Γ : sts ⊫ M : A > s }} -> {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A : s }}
  with soundness_fundamental_sub_ann {P} (pred_P : PredicativeSig P) (full_P : FullSig P) :
    forall Γ stsΓ Δ stsΔ σ, {{ Γ : stsΓ ⊫s σ : Δ > stsΔ }} -> {{ ⟪ pred_P ⟫ Γ : stsΓ ⊩s σ : Δ : stsΔ }}.
  Proof.
    all: inversion_clear 1;
      (on_all_hyp: gen_soundness_IH P pred_P full_P soundness_fundamental_ctx_ann soundness_fundamental_exp_ann soundness_fundamental_sub_ann);
      clear soundness_fundamental_ctx_ann soundness_fundamental_exp_ann soundness_fundamental_sub_ann;
      mauto 2.

    - (* assert (exists Γ' A', (Γ = {{{ Γ', A' }}})) as [Γ' [A' ->]]. *)
      (* { *)
      (*   destruct H1; do 2 eexists; mauto 2. *)
      (* } *)
      (* destruct HM as [SbΓ' []]. *)
      (* eexists; split; eauto. *)
      (* invert_glu_ctx_env H.       *)
      (* intros. *)
      (* destruct_glu_rel_exp_with_sub.       *)
      (* simplify_evals. *)
      (* rewrite H2 in H7. *)
      (* inversion_clear H7. *)
      (* inversion H14. *)
      (* subst. *)
      (* rename a into a'. *)
      (* rename m into a. *)
      (* econstructor; mauto 3. *)
      (* + econstructor; mauto 3. *)
        
      admit.

    (* Cases for naturals ignored since they will be removed in FSCD *)
    - admit.
    - admit.
    - admit.
    - admit.

    (* Cases for conversion rules, hard *)
    - enough {{ Γ ⊢ A0 ≈ A : Sort@s }} by (eapply glu_rel_exp_conv'; mauto 2).
      admit.
    - admit.
    - admit.
    - admit.
      
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
