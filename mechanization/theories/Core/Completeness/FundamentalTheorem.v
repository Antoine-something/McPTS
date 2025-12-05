From McPTS Require Import Base LibTactics PtsSignature.
From McPTS.Core.Completeness Require Import
  ContextCases
  FunctionCases
  SubstitutionCases
  TermStructureCases
  SortCases
  VariableCases
  NatCases.
From McPTS.Core.Completeness Require Export LogicalRelation.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations.

Section completeness_fundamental.
  Variable (P : PtsSig)
    (pred_P : PredicativeSig P).
  
  Theorem completeness_fundamental :
    (forall Γ, {{ ⊢ Γ }} -> {{ ⟪ pred_P ⟫ ⊨ Γ }}) /\
      (forall Γ Δ, {{ ⊢ Γ ≈ Δ }} -> {{ ⟪ pred_P ⟫ ⊨ Γ ≈ Δ }}) /\
      (forall Γ A M, {{ Γ ⊢ M : A }} -> {{ ⟪ pred_P ⟫ Γ ⊨u M : A }}) /\
      (forall Γ A M M', {{ Γ ⊢ M ≈ M' : A }} -> {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A }}) /\
      (forall Γ A, {{ Γ ⊢ A }} -> {{ ⟪ pred_P ⟫ Γ ⊨ A }}) /\
      (forall Γ A A', {{ Γ ⊢ A ≈ A' }} -> {{ ⟪ pred_P ⟫ Γ ⊨ A ≈ A' }}) /\
      (forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }}) /\
      (forall Γ Δ σ σ', {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⟪ pred_P ⟫ Γ ⊨s σ ≈ σ' : Δ }}).      
  Proof using Type.
    apply syntactic_wf_mut_ind;
      mauto 3.

    - intros.
      eapply (@rel_exp_unsorted_natrec_cong _ _ _ _ _ _ _ _ _ _ _ _ _ r); eauto.
      destruct H.
      econstructor.
      destruct_conjs.
      split; eauto.
      intros.
      assert (exists elem_rel : relation (domain P),
                 rel_typ_unsorted pred_P {{{ Sort@s' }}} ρ {{{ Sort@s' }}} ρ' elem_rel /\
                   rel_exp A ρ A ρ' elem_rel) by mauto 2.
      destruct_conjs.
      destruct H3.
      simplify_evals.
      assert (per_typ_elem pred_P (per_sort pred_P s') d{{{ Sort@s' }}} d{{{ Sort@s' }}}) by (eapply per_typ_sort; reflexivity).
      handle_per_typ_elem_irrel.
      destruct H4.
      destruct H5.
      eexists.
      econstructor; mauto.
      
    - intros.
      eapply valid_exp_var;
        mauto.
  Qed.

  #[local]
  Ltac solve_it := pose proof completeness_fundamental; firstorder.


  Theorem completeness_fundamental_ctx : forall Γ, {{ ⊢ Γ }} -> {{ ⟪ pred_P ⟫ ⊨ Γ }}.
  Proof using Type. solve_it. Qed.

  Theorem completeness_fundamental_ctx_subtyp : forall Γ Γ', {{ ⊢ Γ ≈ Γ' }} -> {{ ⟪ pred_P ⟫ ⊨ Γ ≈ Γ' }}.
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
  Proof using Type. solve_it. Qed.
    
  Theorem completeness_fundamental_typ_eq : forall Γ A A', {{ Γ ⊢ A ≈ A' }} -> {{ ⟪ pred_P ⟫ Γ ⊨ A ≈ A' }}.
  Proof using Type. solve_it. Qed.
End completeness_fundamental.
