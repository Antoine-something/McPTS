From Coq Require Import Relations.
From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Export PER.
Import Domain_Notations.

Inductive rel_exp {P : PtsSig} M ρ M' ρ' (R : relation (domain P)) : Prop :=
| mk_rel_exp : forall m m', {{ ⟦ M ⟧ ρ ↘ m }} -> {{ ⟦ M' ⟧ ρ' ↘ m' }} -> {{ Dom m ≈ m' ∈ R }} -> rel_exp M ρ M' ρ' R.
#[global]
Arguments mk_rel_exp {_ _ _ _ _ _}.
#[export]
Hint Constructors rel_exp : mcpts.

Definition rel_exp_under_ctx {P : PtsSig} (pred_P : PredicativeSig P) (Γ : ctx P) A M M' :=
  exists env_rel,
    {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} /\
      exists s,
      forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      exists (elem_rel : relation (domain P)),
        rel_typ pred_P s A ρ A ρ' elem_rel /\ rel_exp M ρ M' ρ' elem_rel.

Definition valid_exp_under_ctx {P : PtsSig} (pred_P : PredicativeSig P) Γ A M := rel_exp_under_ctx pred_P Γ A M M.
#[global]
Arguments valid_exp_under_ctx {_} _ _ _ _ /.
#[export]
Hint Transparent valid_exp_under_ctx : mcpts.
#[export]
Hint Unfold valid_exp_under_ctx : mcpts.


Definition rel_exp_under_ctx_unsorted {P} (pred_P : PredicativeSig P) (Γ : ctx P) A M M' :=
  exists env_rel,
    {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} /\
      forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      exists (elem_rel : relation (domain P)),
        rel_typ_unsorted pred_P A ρ A ρ' elem_rel /\ rel_exp M ρ M' ρ' elem_rel.

Definition valid_exp_under_ctx_unsorted {P : PtsSig} (pred_P : PredicativeSig P) Γ A M := rel_exp_under_ctx_unsorted pred_P Γ A M M.
#[global]
Arguments valid_exp_under_ctx_unsorted {_} _ _ _ _ /.
#[export]
Hint Transparent valid_exp_under_ctx_unsorted : mcpts.
#[export]
Hint Unfold valid_exp_under_ctx_unsorted : mcpts.


Definition rel_typ_under_ctx {P} (pred_P : PredicativeSig P) (Γ : ctx P) A A' :=
  exists env_rel,
    {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} /\
      forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      exists (elem_rel : relation (domain P)),
        rel_typ_unsorted pred_P A ρ A' ρ' elem_rel.

Definition valid_typ_under_ctx {P} {pred_P : PredicativeSig P} Γ A := rel_typ_under_ctx pred_P Γ A A.
#[global]
Arguments valid_typ_under_ctx {_} _ _ _ /.
#[export]
Hint Transparent valid_typ_under_ctx : mcpts.
#[export]
Hint Unfold valid_typ_under_ctx : mcpts.


Inductive rel_sub {P : PtsSig} σ ρ σ' ρ' (R : relation (env P)) : Prop :=
| mk_rel_sub : forall ρσ ρ'σ', {{ ⟦ σ ⟧s ρ ↘ ρσ }} -> {{ ⟦ σ' ⟧s ρ' ↘ ρ'σ' }} -> {{ Dom ρσ ≈ ρ'σ' ∈ R }} -> rel_sub σ ρ σ' ρ' R.
#[global]
Arguments mk_rel_sub {_ _ _ _ _ _ _}.
#[export]
Hint Constructors rel_sub : mcpts.

Definition rel_sub_under_ctx {P : PtsSig} (pred_P : PredicativeSig P) Γ Δ σ σ' :=
  exists env_rel,
    {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} /\
      exists env_rel',
        {{ EF Δ ≈ Δ ∈ per_ctx_env pred_P ↘ env_rel' }} /\
          (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
              rel_sub σ ρ σ' ρ' env_rel').

Definition valid_sub_under_ctx {P : PtsSig} (pred_P : PredicativeSig P) Γ Δ σ := rel_sub_under_ctx pred_P Γ Δ σ σ.
#[global]
Arguments valid_sub_under_ctx {_} _ _ _ _ /.
#[export]
Hint Transparent valid_sub_under_ctx : mcpts.
#[export]
Hint Unfold valid_sub_under_ctx : mcpts.

Notation "⟪ pred_P ⟫ ⊨ Γ ≈ Γ'" := (per_ctx pred_P Γ Γ')  (in custom judg at level 80, pred_P constr at level 0, Γ custom exp, Γ' custom exp).
Notation "⟪ pred_P ⟫ ⊨ Γ" := (valid_ctx pred_P Γ) (in custom judg at level 80, pred_P constr at level 0, Γ custom exp).
Notation "⟪ pred_P ⟫ Γ ⊨ M ≈ M' : A" := (rel_exp_under_ctx pred_P Γ A M M') (in custom judg at level 80, pred_P constr at level 0, Γ custom exp, M custom exp, M' custom exp, A custom exp).
Notation "⟪ pred_P ⟫ Γ ⊨ M : A" := (valid_exp_under_ctx pred_P Γ A M) (in custom judg at level 80, pred_P constr at level 0, Γ custom exp, M custom exp, A custom exp).
Notation "⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A" := (rel_exp_under_ctx_unsorted pred_P Γ A M M') (in custom judg at level 80, pred_P constr at level 0, Γ custom exp, M custom exp, M' custom exp, A custom exp).
Notation "⟪ pred_P ⟫ Γ ⊨u M : A" := (valid_exp_under_ctx_unsorted pred_P Γ A M) (in custom judg at level 80, pred_P constr at level 0, Γ custom exp, M custom exp, A custom exp).
Notation "⟪ pred_P ⟫ Γ ⊨ A ≈ A'" := (rel_typ_under_ctx pred_P Γ A A') (in custom judg at level 80, pred_P constr at level 0, Γ custom exp, A custom exp, A' custom exp).
Notation "⟪ pred_P ⟫ Γ ⊨ A" := (valid_typ_under_ctx pred_P Γ A) (in custom judg at level 80, pred_P constr at level 0, Γ custom exp, A custom exp).
Notation "⟪ pred_P ⟫ Γ ⊨s σ ≈ σ' : Δ" := (rel_sub_under_ctx pred_P Γ Δ σ σ') (in custom judg at level 80, pred_P constr at level 0, Γ custom exp, σ custom exp, σ' custom exp, Δ custom exp).
Notation "⟪ pred_P ⟫ Γ ⊨s σ : Δ" := (valid_sub_under_ctx pred_P Γ Δ σ) (in custom judg at level 80, pred_P constr at level 0, Γ custom exp, σ custom exp, Δ custom exp).
