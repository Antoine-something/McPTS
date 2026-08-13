From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import System.
From McPTS.Core.Semantic Require Export Domain.
Import Domain_Notations.

Reserved Notation "Δ ▶ '⟦' M '⟧' ρ '↘' r" (in custom judg at level 80, M custom exp at level 99, Δ custom exp, ρ custom domain at level 99, r custom domain at level 99).
Reserved Notation "Δ ▶ '$|' m '&' n '|↘' r" (in custom judg at level 80, Δ custom exp, m custom domain at level 99, n custom domain at level 99, r custom domain at level 99).
Reserved Notation "Δ ▶ 'rec' m '⟦return' A | 'zero' -> MZ | 'succ' -> MS 'end⟧' ρ '↘' r" (in custom judg at level 80, m custom domain at level 99, A custom exp at level 99, MZ custom exp at level 99, MS custom exp at level 99, Δ custom exp, ρ custom domain at level 99, r custom domain at level 99).
Reserved Notation "Δ ▶ '⟦' σ '⟧s' ρ '↘' ρσ" (in custom judg at level 80, σ custom exp at level 99, Δ custom exp, ρ custom domain at level 99, ρσ custom domain at level 99).
Reserved Notation "'#|' ρ '[' n ']' '|↘' m" (in custom judg at level 80, ρ custom domain, n constr at level 0, m custom domain at level 99).


Generalizable All Variables.

Inductive env_lookup {P : PtsSig} : env P -> nat -> domain P -> Prop :=
| el_here : `({{ #| (ρ ↦ m)[0] |↘ m }})
| el_there : `({{ #| ρ[i] |↘ m }} ->
               {{ #| (ρ ↦ n)[S i] |↘ m }})
where "'#|' ρ '[' n ']' '|↘' m" := (env_lookup ρ n m) (in custom judg).

#[export]
Hint Constructors env_lookup : mcpts.

Inductive eval_exp {P : PtsSig} : gctx P -> exp P -> env P -> domain P -> Prop :=
| eval_exp_typ :
  `( {{ Δ ▶ ⟦ Sort@s ⟧ ρ ↘ Sort@s }} )
| eval_exp_var :
  `( {{ #| ρ[x] |↘ m }} ->
     {{ Δ ▶ ⟦ #x ⟧ ρ ↘ m }} )
| eval_exp_gvar :
  `( {{ `#x : A ∈ Δ }} ->
     {{ Δ ▶ ⟦ A ⟧ ⋅ ↘ a }} ->
     {{ Δ ▶ ⟦ `#x ⟧ ρ ↘ ⇑`! a x }} )
| eval_exp_pi :
  `( forall r : Ru_pi P s1 s2 s3,
        {{ Δ ▶ ⟦ A ⟧ ρ ↘ a }} ->
        {{ Δ ▶ ⟦ Π r A B ⟧ ρ ↘ Π r a ρ B }} )
| eval_exp_fn :
  `( forall r : Ru_pi P s1 s2 s3,
      {{ Δ ▶ ⟦ λ r A B M ⟧ ρ ↘ λ r ρ M }} )
| eval_exp_app :
  `( {{ Δ ▶ ⟦ M ⟧ ρ ↘ m }} ->
     {{ Δ ▶ ⟦ N ⟧ ρ ↘ n }} ->
     {{ Δ ▶ $| m & n |↘ m' }} ->
     {{ Δ ▶ ⟦ M N ⟧ ρ ↘ m' }} )
(** Naturals *)
| eval_exp_nat :
  `( {{ Δ ▶ ⟦ ℕ ⟧ ρ ↘ ℕ }} )
| eval_exp_zero :
  `( {{ Δ ▶ ⟦ zero ⟧ ρ ↘ zero }} )
| eval_exp_succ :
  `( {{ Δ ▶ ⟦ M ⟧ ρ ↘ m }} ->
     {{ Δ ▶ ⟦ succ M ⟧ ρ ↘ succ m }} )
| eval_exp_natrec :
  `( {{ Δ ▶ ⟦ M ⟧ ρ ↘ m }} ->
     {{ Δ ▶ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} ->
     {{ Δ ▶ ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ ρ ↘ r }} )
| eval_exp_sub :
  `( {{ Δ ▶ ⟦ σ ⟧s ρ ↘ ρ' }} ->
     {{ Δ ▶ ⟦ M ⟧ ρ' ↘ m }} ->
     {{ Δ ▶ ⟦ M[σ] ⟧ ρ ↘ m }} )
where "Δ ▶ '⟦' M '⟧' ρ '↘' m" := (eval_exp Δ M ρ m) (in custom judg)
                                                                  
with eval_app {P : PtsSig} : gctx P -> domain P -> domain P -> domain P -> Prop :=
| eval_app_fn :
  `( forall r : Ru_pi P s1 s2 s3,
      {{ Δ ▶ ⟦ M ⟧ ρ ↦ n ↘ m }} ->
      {{ Δ ▶ $| λ r ρ M & n |↘ m }} )
| eval_app_neut :
  `( forall r : Ru_pi P s1 s2 s3,
      {{ Δ ▶ ⟦ B ⟧ ρ ↦ n ↘ b }} ->
      {{ Δ ▶ $| ⇑ (Π r a ρ B) m & n |↘ ⇑ b (m (⇓ a n)) }} )
where "Δ ▶ '$|' m '&' n '|↘' m'" := (eval_app Δ m n m') (in custom judg)
with eval_natrec {P : PtsSig} : gctx P -> exp P -> exp P -> exp P -> domain P -> env P -> domain P -> Prop :=
| eval_natrec_zero :
  `( {{ Δ ▶ ⟦ MZ ⟧ ρ ↘ mz }} ->
     {{ Δ ▶ rec zero ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ mz }} )
| eval_natrec_succ :
  `( {{ Δ ▶ rec b ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} ->
     {{ Δ ▶ ⟦ MS ⟧ (ρ ↦ b) ↦ r ↘ ms }} ->
     {{ Δ ▶ rec succ b ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ ms }} )
| eval_natrec_neut :
  `( {{ Δ ▶ ⟦ MZ ⟧ ρ ↘ mz }} ->
     {{ Δ ▶ ⟦ A ⟧ ρ ↦ ⇑ b m ↘ a }} ->
     {{ Δ ▶ rec ⇑ b m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ ⇑ a (rec m under ρ return A | zero -> mz | succ -> MS end) }} )
where "Δ ▶ 'rec' m '⟦return' A | 'zero' -> MZ | 'succ' -> MS 'end⟧' ρ '↘' r" := (eval_natrec Δ A MZ MS m ρ r) (in custom judg)
with eval_sub {P : PtsSig} : gctx P -> sub P -> env P -> env P -> Prop :=
| eval_sub_id :
  `( {{ Δ ▶ ⟦ Id ⟧s ρ ↘ ρ }} )
| eval_sub_weaken :
  `( {{ Δ ▶ ⟦ Wk ⟧s ρ ↘ ρ ↯ }} )
| eval_sub_extend :
  `( {{ Δ ▶ ⟦ σ ⟧s ρ ↘ ρσ }} ->
     {{ Δ ▶ ⟦ M ⟧ ρ ↘ m }} ->
     {{ Δ ▶ ⟦ σ ,, M ⟧s ρ ↘ ρσ ↦ m }} )
| eval_sub_compose :
  `( {{ Δ ▶ ⟦ τ ⟧s ρ ↘ ρτ }} ->
     {{ Δ ▶ ⟦ σ ⟧s ρτ ↘ ρτσ }} ->
     {{ Δ ▶ ⟦ σ ∘ τ ⟧s ρ ↘ ρτσ }} )
where "Δ ▶ '⟦' σ '⟧s' ρ '↘' ρσ" := (eval_sub Δ σ ρ ρσ) (in custom judg)
.

Scheme eval_exp_mut_ind := Induction for eval_exp Sort Prop
with eval_app_mut_ind := Induction for eval_app Sort Prop
with eval_natrec_mut_ind := Induction for eval_natrec Sort Prop
with eval_sub_mut_ind := Induction for eval_sub Sort Prop.
Combined Scheme eval_mut_ind from
  eval_exp_mut_ind,
  eval_app_mut_ind,
  eval_natrec_mut_ind,
  eval_sub_mut_ind.

#[export]
Hint Constructors eval_exp eval_app eval_natrec eval_sub : mcpts.
