From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic.System Require Import Definitions.
(* From McPTS.Core.Syntactic Require Export SystemOpt. *)
Import Syntax_Notations.

Generalizable All Variables.

Reserved Notation "▶w Δ < Δ'" (in custom judg at level 80, Δ custom exp, Δ' custom exp).
Reserved Notation "Δ ▶ Γ ⊢w σ : Γ'" (in custom judg at level 80, Δ custom exp, Γ custom exp, σ custom exp, Γ' custom exp).

Inductive gctx_weakening {P} : gctx P -> gctx P -> Prop :=
| gctx_wk_empty : {{ ▶w ⋅ < ⋅ }}
| gctx_wk_extend_right :
  `{ {{ ▶w Δ < Δ' }} ->
     {{ `#x ∉ Δ' }} ->
     {{ Δ' ▶ ⋅ ⊢ A }} ->
     {{ ▶w Δ < Δ', x:A }} }
| gctx_wk_extend_both :
  `{ {{ ▶w Δ < Δ' }} ->
     {{ `#x ∉ Δ' }} ->
     {{ Δ ▶ ⋅ ⊢ A }} ->
     {{ Δ' ▶ ⋅ ⊢ A }} ->
     {{ ▶w Δ, x:A < Δ', x:A }} }
where "▶w Δ < Δ'" := (gctx_weakening Δ Δ') (in custom judg) : type_scope.

#[export]
Hint Constructors gctx_weakening : mcpts.

Inductive weakening {P} : gctx P -> ctx P -> sub P -> ctx P -> Prop :=
| wk_id :
  `( {{ Δ ▶ Γ ⊢s σ ≈ Id : Γ' }} ->
     {{ Δ ▶ Γ ⊢w σ : Γ' }} )
| wk_p :
  `( {{ Δ ▶ Γ ⊢w τ : Γ', A }} ->
     {{ Δ ▶ Γ' ⊆ Γ'' }} ->
     {{ Δ ▶ Γ ⊢s σ ≈ Wk ∘ τ : Γ'' }} ->
     {{ Δ ▶ Γ ⊢w σ : Γ'' }} )
where "Δ ▶ Γ ⊢w σ : Γ'" := (weakening Δ Γ σ Γ') (in custom judg) : type_scope.

#[export]
Hint Constructors weakening : mcpts.
