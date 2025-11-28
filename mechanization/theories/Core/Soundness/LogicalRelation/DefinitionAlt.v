From Coq Require Import Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Export PER.
From McPTS.Core.Soundness.Weakening Require Export Definitions.

Import Domain_Notations.
Global Open Scope predicate_scope.

Generalizable All Variables.

Notation "'glu_typ_pred_args' P" := (Tcons (ctx P) (Tcons (typ P) (Tcons (relation (domain P)) Tnil))) (at level 80, P constr at level 0).
Notation "'glu_typ_pred' P" := (predicate (glu_typ_pred_args P)) (at level 80, P constr at level 0).
Notation "'glu_typ_pred_equivalence' P" := (@predicate_equivalence (glu_typ_pred_args P)) (at level 80, P constr at level 0).
Notation "Γ ⊢ A ∈ R ® GT" := (GT Γ A R) (in custom judg at level 80, Γ custom exp, A custom exp, R constr, GT constr).

Notation "'glu_exp_pred_args' P" := (Tcons (ctx P) (Tcons (typ P) (Tcons (exp P) (Tcons (domain P) (Tcons (relation (domain P)) Tnil))))) (at level 80, P constr at level 0).
Notation "'glu_exp_pred' P" := (predicate (glu_exp_pred_args P)) (at level 80, P constr at level 0).
Notation "'glu_exp_pred_equivalence' P" := (@predicate_equivalence (glu_exp_pred_args P)) (at level 80, P constr at level 0, only parsing).
Notation "Γ ⊢ M : A ® m ∈ R ⋈ GE" := (GE Γ A M m R) (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp, m custom domain, R constr, GE constr).


Variant neut_glu_typ_pred {P} (pred_P : PredicativeSig P) a s : glu_typ_pred P :=
| mk_neut_glu_typ_pred :
  `{ {{ Γ ⊢ A : Sort@s }} ->
     {{ Dom a ≈ a ∈ (@per_bot P) }} ->
     (forall Δ σ, {{ Δ ⊢w σ : Γ }} -> {{ Rne a in length Δ ↘ A' }} ->  {{ Δ ⊢ A[σ] ≈ A' : Sort@s }}) ->
     {{ Γ ⊢ A ∈ per_sort pred_P s ® neut_glu_typ_pred pred_P a s }} }.
     
  
Variant neut_glu_exp_pred {P} a s : glu_exp_pred P :=
| mk_neut_glu_exp_pred :
  `{ {{ Γ ⊢ A ∈ per_sort pred_P s ® neut_glu_typ_pred pred_P a s }} ->
     {{ Γ ⊢ M : A }} ->
     {{ DF ⇑ Sort@s a ≈ ⇑ Sort@s a ∈ per_sort_elem pred_P s ↘ R }} ->
     {{ Dom m ≈ m ∈ R }} ->
     (forall Δ σ, {{ Δ ⊢w σ : Γ }} -> {{ Rnf ⇓ (⇑ Sort@s e) m in length Δ ↘ M' }} -> {{ Δ ⊢ M[σ] ≈ M' : A[σ] }}) ->
     {{ Γ ⊢ M : A ® m ∈ R ⋈ neut_glu_exp_pred a s }} }.







   
Inductive glu_exp_model {P} (pred_P : PredicativeSig P) : ctx P -> exp P -> typ P -> domain P -> relation (domain P) -> Prop :=
| glu_exp_neut :
  `{ {{ Γ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ M : A }} ->
     {{ Dom e ≈ e ∈ per_bot }} ->
     {{ DF ⇑ Sort@s e ≈ ⇑ Sort@s e ∈ per_typ_elem pred_P ↘ R }} ->
     {{ Dom m ≈ m ∈ R }} ->
     (forall Δ σ, {{ Δ ⊢w σ : Γ }} -> {{ Rne e in length Δ ↘ E }} ->  {{ Δ ⊢ A[σ] ≈ E : Sort@s }}) ->
     (forall Δ σ, {{ Δ ⊢w σ : Γ }} -> {{ Rnf ⇓ (⇑ Sort@s e) m in length Δ ↘ W }} -> {{ Δ ⊢ M[σ] ≈ W : A[σ] }}) ->
     {{ ⟪ pred_P ⟫ Γ ⊢ M : A ⋈ m ∈ R }} }

| glu_exp_sort_neut :
  `{ {{ Γ ⊢ A ≈ Sort@s }} ->
     {{ Γ ⊢ M : A }} ->
     {{ Dom e ≈ e ∈ per_bot }} ->
     (forall Δ σ, {{ Δ ⊢w σ : Γ }} -> {{ Rne e in length Δ ↘ E }} -> {{ Δ ⊢ M[σ] ≈ E : Sort@s }}) ->
     {{ ⟪ pred_P ⟫ Γ ⊢ M : A ⋈ (⇑ Sort@s e) ∈ (per_sort pred_P s) }} }

| glu_exp_sort_sort :
  `{ {{ Γ ⊢ A ≈ Sort@s }} ->
     {{ Γ ⊢ M : A }} ->
     {{ Dom Sort@s' ≈ Sort@s' ∈ per_sort pred_P s }} ->
     (forall Δ σ, {{ Δ ⊢w σ : Γ }} -> {{ Δ ⊢ M[σ] ≈ Sort@s' : Sort@s }}) ->
     {{ ⟪ pred_P ⟫ Γ ⊢ M : A ⋈ Sort@s' ∈ per_sort pred_P s }} }

| glu_exp_sort_pi :
  `{ forall {r : Ru P s1 s2 s },
        {{ Γ ⊢ A ≈ Sort@s }} ->
        {{ Γ ⊢ M ≈ Π r A' B : A }} ->
        {{ DF a ≈ a ∈ per_sort_elem pred_P s1 ↘ Rin }} ->
        {{ Dom Π r a ρ B ≈ Π r a ρ B ∈ per_sort pred_P s }} ->
        {{ ⟪ pred_P ⟫ Γ ⊢ A' : Sort@s1 ⋈ a ∈ per_sort pred_P s1 }} ->
        (forall Δ σ N n, {{ Δ ⊢w σ : Γ }} -> {{ ⟪ pred_P ⟫ Δ ⊢ N : A'[σ] ⋈ n ∈ Rin }} -> {{ ⟦ B ⟧(ρ ↦ n) ↘ b }} -> {{ ⟪ pred_P ⟫ Δ ⊢ B[σ,,N] : Sort@s2 ⋈ b ∈ per_sort pred_P s2 }}) ->
        {{ ⟪ pred_P ⟫ Γ ⊢ M : A ⋈ Π r a ρ B ∈ per_sort pred_P s }} }
     
where "⟪ pred_P ⟫ Γ ⊢ M : A ⋈ m ∈ R" := (glu_exp_model pred_P Γ M A m R) (in custom judg) : type_scope.
