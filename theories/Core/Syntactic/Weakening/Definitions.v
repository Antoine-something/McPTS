From McPTS Require Import PtsSignature Base.
From McPTS.Core.Syntactic.System Require Import Definitions.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

Generalizable All Variables.

Reserved Notation "Γ ⊢w σ : Γ'" (in custom judg at level 80, Γ custom exp, σ custom exp, Γ' custom exp).

Inductive weakening {P} : ctx P -> sub P -> ctx P -> Prop :=
| wk_id :
  `( {{ Γ ⊢s σ ≈ Id : Γ' }} ->
     {{ Γ ⊢w σ : Γ' }} )
| wk_p :
  `( {{ Γ ⊢w τ : Γ', A }} ->
     {{ ⊢ Γ' ⊆ Γ'' }} ->
     {{ Γ ⊢s σ ≈ Wk ∘ τ : Γ'' }} ->
     {{ Γ ⊢w σ : Γ'' }} )
where "Γ ⊢w σ : Γ'" := (weakening Γ σ Γ') (in custom judg) : type_scope.

#[export]
Hint Constructors weakening : mcpts.
