From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Soundness Require Import
  ContextCases
  FunctionCases
  SubstitutionCases
  TermStructureCases
  SortCases.
From McPTS.Core.Soundness Require Export LogicalRelation.
Import Domain_Notations.

Section soundness_fundamental.
  Theorem soundness_fundamental {P} (pred_P : PredicativeSig P) (full_P : FullSig P) :
    (forall Γ, {{ ⊢ Γ }} -> exists sts, {{ ⟪ pred_P ⟫ ⊩ Γ : sts }}) /\
      (forall Γ A M, {{ Γ ⊢ M : A }} -> exists sts s, {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A : s }}) /\
      (forall Γ A, {{ Γ ⊢ A }} -> exists sts s s', {{ ⟪ pred_P ⟫ Γ : sts ⊩ A : Sort@s : s' }}) /\
      (forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> exists stsΓ stsΔ, {{ ⟪ pred_P ⟫ Γ : stsΓ ⊩s σ : Δ : stsΔ }}).
  Proof.
    apply syntactic_wf_mut_ind'; mauto 3.
    - intros.
      destruct H0 as [sts [s']].
      assert {{ ⟪ pred_P ⟫ ⊩ Γ : sts }} by mauto 2.
      eexists.
      eapply glu_rel_ctx_extend; mauto 3.

    - intros.
      destruct_conjs.
      eexists.
      eapply glu_rel_exp_typ; mauto 2.

    - intros.
      destruct H0 as [sts [s2']].
      assert {{ ⟪ pred_P ⟫ ⊩ Γ, A : sts }} by mauto 2.
      assert (exists sts' s1', sts = (s1' :: sts')) as [sts' [s1']].
      {
        destruct H1 as [SbΓA].
        invert_glu_ctx_env H1.
        do 2 eexists; reflexivity.
      }
      subst.
      assert {{ ⟪ pred_P ⟫ Γ : sts' ⊩ A : Sort@s1 : s1' }}.
      {
        destruct H1 as [SbΓA].
        invert_glu_ctx_env H1.
        eexists; split; mauto 2.
        intros.
        destruct_glu_rel_typ_with_sub.
        econstructor; mauto 3.
      }
      destruct H as [sts [s [SbΓ []]]].
      destruct H0 as [sts' [s' [SbΓA []]]].
      assert (exists s3', Ax P s3 s3') by (eapply full_P).
      eexists.
      eapply glu_rel_exp_pi; mauto 2.
      do 2 eexists.
      
      do 3 eexists; split; mauto 2.
      intros.
      destruct_glu_rel_exp_with_sub.
  Qed.
  

  #[local]
  Ltac solve_it := pose proof soundness_fundamental; firstorder.

  Theorem soundness_fundamental_ctx : forall Γ, {{ ⊢ Γ }} -> {{ ⊩ Γ }}.
  Proof. solve_it. Qed.

  Theorem soundness_fundamental_exp : forall Γ M A, {{ Γ ⊢ M : A }} -> {{ Γ ⊩ M : A }}.
  Proof. solve_it. Qed.

  Theorem soundness_fundamental_sub : forall Γ σ Δ, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊩s σ : Δ }}.
  Proof. solve_it. Qed.
End soundness_fundamental.
