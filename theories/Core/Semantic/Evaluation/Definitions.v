From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import System.
From McPTS.Core.Semantic Require Export Domain.
Import Domain_Notations.

Reserved Notation "'⟦' M '⟧' '(' Δ ';' ρ ')' '↘' r" (in custom judg at level 80, M custom exp at level 99, Δ custom exp at level 99, ρ custom domain at level 99, r custom domain at level 99).
Reserved Notation "'$|' m '&' n '|↘' r" (in custom judg at level 80, m custom domain at level 99, n custom domain at level 99, r custom domain at level 99).
Reserved Notation "'rec' m '⟦return' A | 'zero' -> MZ | 'succ' -> MS 'end⟧' '(' Δ ';' ρ ')' '↘' r" (in custom judg at level 80, m custom domain at level 99, A custom exp at level 99, MZ custom exp at level 99, MS custom exp at level 99, Δ custom exp at level 99, ρ custom domain at level 99, r custom domain at level 99).
Reserved Notation "'⟦' σ '⟧s' '(' Δ ';' ρ ')' '↘' ρσ" (in custom judg at level 80, σ custom exp at level 99, Δ custom exp at level 99, ρ custom domain at level 99, ρσ custom domain at level 99).
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
  `( {{ ⟦ Sort@s ⟧ (Δ ; ρ) ↘ Sort@s }} )
| eval_exp_var :
  `( {{ #| ρ[x] |↘ m }} ->
     {{ ⟦ #x ⟧ (Δ ; ρ) ↘ m }} )
| eval_exp_gvar :
  `( {{ `#x : A ∈ Δ }} ->
     {{ ⟦ A ⟧ (Δ ; ⋅) ↘ a }} ->
     {{ ⟦ `#x ⟧ (Δ ; ρ) ↘ ⇑`! a x }} )
| eval_exp_pi :
  `( forall r : Ru_pi P s1 s2 s3,
        {{ ⟦ A ⟧ (Δ ; ρ) ↘ a }} ->
        {{ ⟦ Π r A B ⟧ (Δ ; ρ) ↘ Π r a (Δ ; ρ) B }} )
| eval_exp_fn :
  `( forall r : Ru_pi P s1 s2 s3,
      {{ ⟦ λ r A B M ⟧ (Δ ; ρ) ↘ λ r (Δ ; ρ) M }} )
| eval_exp_app :
  `( {{ ⟦ M ⟧ (Δ ; ρ) ↘ m }} ->
     {{ ⟦ N ⟧ (Δ ; ρ) ↘ n }} ->
     {{ $| m & n |↘ m' }} ->
     {{ ⟦ M N ⟧ (Δ ; ρ) ↘ m' }} )
(** Naturals *)
| eval_exp_nat :
  `( {{ ⟦ ℕ ⟧ (Δ ; ρ) ↘ ℕ }} )
| eval_exp_zero :
  `( {{ ⟦ zero ⟧ (Δ ; ρ) ↘ zero }} )
| eval_exp_succ :
  `( {{ ⟦ M ⟧ (Δ ; ρ) ↘ m }} ->
     {{ ⟦ succ M ⟧ (Δ ; ρ) ↘ succ m }} )
| eval_exp_natrec :
  `( {{ ⟦ M ⟧ (Δ ; ρ) ↘ m }} ->
     {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ (Δ ; ρ) ↘ r }} ->
     {{ ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ (Δ ; ρ) ↘ r }} )
| eval_exp_sub :
  `( {{ ⟦ σ ⟧s (Δ ; ρ) ↘ ρ' }} ->
     {{ ⟦ M ⟧ (Δ ; ρ') ↘ m }} ->
     {{ ⟦ M[σ] ⟧ (Δ ; ρ) ↘ m }} )
where "'⟦' M '⟧' '(' Δ ';' ρ ')' '↘' m" := (eval_exp Δ M ρ m) (in custom judg)
with eval_app {P : PtsSig} : domain P -> domain P -> domain P -> Prop :=
| eval_app_fn :
  `( forall r : Ru_pi P s1 s2 s3,
      {{ ⟦ M ⟧ (Δ ; ρ ↦ n) ↘ m }} ->
      {{ $| λ r (Δ ; ρ) M & n |↘ m }} )
| eval_app_neut :
  `( forall r : Ru_pi P s1 s2 s3,
      {{ ⟦ B ⟧ (Δ ; ρ ↦ n) ↘ b }} ->
      {{ $| ⇑ (Π r a (Δ ; ρ) B) m & n |↘ ⇑ b (m (⇓ a n)) }} )
where "'$|' m '&' n '|↘' m'" := (eval_app m n m') (in custom judg)
with eval_natrec {P : PtsSig} : exp P -> exp P -> exp P -> domain P -> gctx P -> env P -> domain P -> Prop :=
| eval_natrec_zero :
  `( {{ ⟦ MZ ⟧ (Δ ; ρ) ↘ mz }} ->
     {{ rec zero ⟦return A | zero -> MZ | succ -> MS end⟧ (Δ ; ρ) ↘ mz }} )
| eval_natrec_succ :
  `( {{ rec b ⟦return A | zero -> MZ | succ -> MS end⟧ (Δ ; ρ) ↘ r }} ->
     {{ ⟦ MS ⟧ (Δ ; (ρ ↦ b) ↦ r) ↘ ms }} ->
     {{ rec succ b ⟦return A | zero -> MZ | succ -> MS end⟧ (Δ ; ρ) ↘ ms }} )
| eval_natrec_neut :
  `( {{ ⟦ MZ ⟧ (Δ ; ρ) ↘ mz }} ->
     {{ ⟦ A ⟧ (Δ ; ρ ↦ ⇑ b m) ↘ a }} ->
     {{ rec ⇑ b m ⟦return A | zero -> MZ | succ -> MS end⟧ (Δ ; ρ) ↘ ⇑ a (rec m under (Δ ; ρ) return A | zero -> mz | succ -> MS end) }} )
where "'rec' m '⟦return' A | 'zero' -> MZ | 'succ' -> MS 'end⟧' '(' Δ ';' ρ ')' '↘' r" := (eval_natrec A MZ MS m Δ ρ r) (in custom judg)
with eval_sub {P : PtsSig} : gctx P -> sub P -> env P -> env P -> Prop :=
| eval_sub_id :
  `( {{ ⟦ Id ⟧s (Δ ; ρ) ↘ ρ }} )
| eval_sub_weaken :
  `( {{ ⟦ Wk ⟧s (Δ ; ρ) ↘ ρ ↯ }} )
| eval_sub_extend :
  `( {{ ⟦ σ ⟧s (Δ ; ρ) ↘ ρσ }} ->
     {{ ⟦ M ⟧ (Δ ; ρ) ↘ m }} ->
     {{ ⟦ σ ,, M ⟧s (Δ ; ρ) ↘ ρσ ↦ m }} )
| eval_sub_compose :
  `( {{ ⟦ τ ⟧s (Δ ; ρ) ↘ ρτ }} ->
     {{ ⟦ σ ⟧s (Δ ; ρτ) ↘ ρτσ }} ->
     {{ ⟦ σ ∘ τ ⟧s (Δ ; ρ) ↘ ρτσ }} )
where "'⟦' σ '⟧s' '(' Δ ';' ρ ')' '↘' ρσ" := (eval_sub Δ σ ρ ρσ) (in custom judg)
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
