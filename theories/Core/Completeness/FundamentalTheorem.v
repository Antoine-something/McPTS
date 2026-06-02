From McPTS Require Import Base LibTactics PtsSignature.
From McPTS.Core.Completeness Require Import
  ContextCases
  FunctionCases
  SubstitutionCases
  TermStructureCases
  SubtypingCases
  SortCases
  NatCases
  VariableCases.
From McPTS.Core.Completeness Require Export LogicalRelation.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations.

Section completeness_fundamental.
  Variable (P : PtsSig)
    (pred_P : PredicativeSig P).

  Theorem completeness_fundamental :
    (forall Γ, {{ ⊢ Γ }} -> {{ ⟪ pred_P ⟫ ⊨ Γ }}) /\
      (forall Γ Γ', {{ ⊢ Γ ⊆ Γ' }} -> {{ ⟪ pred_P ⟫ SubE Γ <: Γ' }}) /\
      (forall Γ Δ, {{ ⊢ Γ ≈ Δ }} -> {{ ⟪ pred_P ⟫ ⊨ Γ ≈ Δ }}) /\
      (forall Γ A M, {{ Γ ⊢ M : A }} -> {{ ⟪ pred_P ⟫ Γ ⊨u M : A }}) /\
      (forall Γ A M M', {{ Γ ⊢ M ≈ M' : A }} -> {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A }}) /\
      (forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }}) /\
      (forall Γ Δ σ σ', {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⟪ pred_P ⟫ Γ ⊨s σ ≈ σ' : Δ }}) /\
      (forall Γ A A', {{ Γ ⊢ A ⊆ A' }} -> {{ ⟪ pred_P ⟫ Γ ⊨ A ⊆ A' }}) /\
      (forall Γ A, {{ Γ ⊢ A }} -> {{ ⟪ pred_P ⟫ Γ ⊨ A }}) /\
      (forall Γ A A', {{ Γ ⊢ A ≈ A' }} -> {{ ⟪ pred_P ⟫ Γ ⊨ A ≈ A' }}).
  Proof using Type.
    apply syntactic_wf_mut_ind;
      mauto 3.

    - intros.
      eapply @valid_exp_var; mauto.
Qed.

  #[local]
  Ltac solve_it := pose proof completeness_fundamental; firstorder.


  Theorem completeness_fundamental_ctx : forall Γ, {{ ⊢ Γ }} -> {{ ⟪ pred_P ⟫ ⊨ Γ }}.
  Proof using Type. solve_it. Qed.

  Theorem completeness_fundamental_ctx_eq : forall Γ Γ', {{ ⊢ Γ ≈ Γ' }} -> {{ ⟪ pred_P ⟫ ⊨ Γ ≈ Γ' }}.
  Proof using Type. solve_it. Qed.

  Theorem completeness_fundamental_exp : forall Γ M A, {{ Γ ⊢ M : A }} -> {{ ⟪ pred_P ⟫ Γ ⊨u M : A }}.
  Proof using Type. solve_it. Qed.

  Theorem completeness_fundamental_exp_eq : forall Γ A M M', {{ Γ ⊢ M ≈ M' : A }} -> {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A }}.
  Proof using Type. solve_it. Qed.

  Theorem completeness_fundamental_sub : forall Γ σ Δ, {{ Γ ⊢s σ : Δ }} -> {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }}.
  Proof using Type. solve_it. Qed.

  Theorem completeness_fundamental_sub_eq : forall Γ Δ σ σ', {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⟪ pred_P ⟫ Γ ⊨s σ ≈ σ' : Δ }}.
  Proof using Type. solve_it. Qed.

  Theorem completeness_fundamental_typ : forall Γ A, {{ Γ ⊢ A }} -> {{ ⟪ pred_P ⟫ Γ ⊨ A }}.
  Proof using Type.
    intros.
    inversion_clear H.
    - assert {{ ⟪ pred_P ⟫ ⊨ Γ }} by solve_it.
      mauto 2.
    - assert {{ ⟪ pred_P ⟫ Γ ⊨u A : Sort@s }} by solve_it.
      destruct H as [relΓ []].
      eexists; split; mauto 2.
      intros.
      specialize (H1 ρ ρ' equiv_ρ_ρ') as [elem_rel []].
      destruct H1.
      simplify_evals.
      assert (per_typ_elem pred_P (per_sort pred_P s) d{{{ Sort@s }}} d{{{ Sort@s }}}) by (econstructor; reflexivity).
      handle_per_typ_elem_irrel.
      destruct H2.
      destruct H4 as [R].
      eexists; econstructor; mauto 2.
    - assert {{ ⟪ pred_P ⟫ Δ ⊨ A0 }} by solve_it.
      assert {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} by solve_it.
      assert {{ Γ ⊢ A0[σ] }} by mauto 3.
      mauto 3.
  Qed.

  Theorem completeness_fundamental_typ_eq : forall Γ A A', {{ Γ ⊢ A ≈ A' }} -> {{ ⟪ pred_P ⟫ Γ ⊨ A ≈ A' }}.
  Proof using Type.
    intros.
    induction H; mauto 3.
    - assert {{ ⟪ pred_P ⟫ Γ ⊨ A }} by (eapply completeness_fundamental_typ; mauto 2).
      mauto 2.
    - assert {{ ⟪ pred_P ⟫ Γ ⊨u A ≈ B : Sort@s }} by solve_it.
      destruct H0 as [relΓ []].
      eexists; split; mauto 2.
      intros.
      specialize (H1 ρ ρ' equiv_ρ_ρ') as [elem_rel []].
      destruct H1.
      simplify_evals.
      assert (per_typ_elem pred_P (per_sort pred_P s) d{{{ Sort@s }}} d{{{ Sort@s }}}) by (econstructor; reflexivity).
      handle_per_typ_elem_irrel.
      destruct H2.
      destruct H4 as [R].
      eexists; econstructor; mauto 2.
    - assert {{ ⟪ pred_P ⟫ Γ ⊨ A }} by solve_it.
      mauto 2.
    - assert {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} by solve_it.
      mauto 2.
    - assert {{ ⟪ pred_P ⟫ Δ ⊨ A ≈ A' }} by solve_it.
      assert {{ ⟪ pred_P ⟫ Γ ⊨s σ ≈ σ' : Δ }} by solve_it.
      mauto 2.
    - assert {{ ⟪ pred_P ⟫ Γ ⊨s τ : Γ' }} by solve_it.
      assert {{ ⟪ pred_P ⟫ Γ' ⊨s σ : Γ'' }} by solve_it.
      assert {{ ⟪ pred_P ⟫ Γ'' ⊨ A }} by solve_it.
      mauto 2.
  Qed.
End completeness_fundamental.
