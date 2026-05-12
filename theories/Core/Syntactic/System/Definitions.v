From Coq Require Import List Classes.RelationClasses Setoid Morphisms.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.


Reserved Notation "⊢ Γ" (in custom judg at level 80, Γ custom exp).
Reserved Notation "⊢ Γ ≈ Γ'" (in custom judg at level 80, Γ custom exp, Γ' custom exp).
Reserved Notation "Γ ⊢ M : A" (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp).
Reserved Notation "Γ ⊢ M ≈ M' : A" (in custom judg at level 80, Γ custom exp, M custom exp, M' custom exp, A custom exp).
Reserved Notation "Γ ⊢ A" (in custom judg at level 80, Γ custom exp, A custom exp).
Reserved Notation "Γ ⊢ A ≈ A'" (in custom judg at level 80, Γ custom exp, A custom exp, A' custom exp).
Reserved Notation "Γ ⊢s σ : Δ" (in custom judg at level 80, Γ custom exp, σ custom exp, Δ custom exp).
Reserved Notation "Γ ⊢s σ ≈ σ' : Δ" (in custom judg at level 80, Γ custom exp, σ custom exp, σ' custom exp, Δ custom exp).
Reserved Notation "⊢ Γ ⊆ Γ'" (in custom judg at level 80, Γ custom exp, Γ' custom exp).
Reserved Notation "Γ ⊢ A ⊆ A' @ s" (in custom judg at level 80, Γ custom exp, A custom exp, A' custom exp, s custom exp).
Reserved Notation "Γ ⊢ A ⊆ A'" (in custom judg at level 80, Γ custom exp, A custom exp, A' custom exp).
Reserved Notation "'#' x : A @ s ∈ Γ" (in custom judg at level 80, x constr at level 0, A custom exp, s custom exp, Γ custom exp at level 50).

Generalizable All Variables.

Inductive ctx_lookup {P : PtsSig} : nat -> typ P -> P -> ctx P -> Prop :=
  | here : `({{ #0 : A[Wk]@s ∈ Γ, A@s }})
  | there : `({{ #n : A@s ∈ Γ }} -> {{ #(S n) : A[Wk]@s ∈ Γ, B@s' }})
where "'#' x : A @ K ∈ Γ" := (ctx_lookup x A K Γ) (in custom judg) : type_scope.

Inductive wf_ctx {P : PtsSig} : ctx P -> Prop :=
| wf_ctx_empty : {{ ⊢ ⋅ }}
| wf_ctx_extend :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ A : Sort@s }} ->
     {{ ⊢ Γ, A@s }} )
where "⊢ Γ" := (wf_ctx Γ) (in custom judg) : type_scope

with wf_ctx_sub {P : PtsSig} : ctx P -> ctx P -> Prop :=
| wf_ctx_sub_empty : {{ ⊢ ⋅ ⊆ ⋅ }}
| wf_ctx_sub_extend :
  `( {{ ⊢ Γ ⊆ Δ }} ->
     {{ Γ ⊢ A : Sort@s }} ->
     {{ Δ ⊢ A' : Sort@s }} ->
     {{ Γ ⊢ A ⊆ A' @ s }} ->
     {{ ⊢ Γ, A@s ⊆ Δ, A'@s }} )
where "⊢ Γ ⊆ Γ'" := (wf_ctx_sub Γ Γ') (in custom judg) : type_scope
                                                           
with wf_exp {P : PtsSig} : ctx P -> typ P -> exp P -> Prop :=
(** Sorts *)
| wf_st :
  `( Ax P s1 s2 -> {{ ⊢ Γ }} ->
     {{ Γ ⊢ Sort@s1 : Sort@s2 }} )

(** Functions *)
| wf_pi :
  `( forall (r : Ru P s1 s2 s3),
      {{ Γ ⊢ A : Sort@s1 }} ->
      {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
      {{ Γ ⊢ Π r A B : Sort@s3 }} )
| wf_fn :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
        {{ Γ, A@s1 ⊢ M : B }} ->
        {{ Γ ⊢ λ r A M : Π r A B }} )
| wf_app :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
        {{ Γ ⊢ M : Π r A B }} ->
        {{ Γ ⊢ N : A }} ->
        {{ Γ ⊢ M N : B[Id,,N] }} )

| wf_vlookup :
  `( {{ ⊢ Γ }} ->
     (** This premise is redundant, but helpful for soundness *)
     {{ Γ ⊢ A : Sort@s }} ->
     {{ #x : A@s ∈ Γ }} ->
     {{ Γ ⊢ #x : A }} )

(** Naturals **)
| wf_nat :
  `( forall (r : Ru_nat P s),
        {{ ⊢ Γ }} ->
        {{ Γ ⊢ ℕ: Sort@s }} )
| wf_zero :
  `(forall (r : Ru_nat P s),
        {{ ⊢ Γ }} ->
        {{ Γ ⊢ zero : ℕ}} )
| wf_succ :
  `( forall (r : Ru_nat P s),
        {{ Γ ⊢ M : ℕ}} ->
        {{ Γ ⊢ succ M : ℕ}} )
| wf_natrec :
  `( forall (r : Ru_nat P s),
        {{ Γ, ℕ@s ⊢ A : Sort@s' }} ->
        {{ Γ ⊢ MZ : A[Id,,zero] }} ->
        {{ Γ, ℕ@s, A@s' ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
        {{ Γ ⊢ M : ℕ}} ->
        {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }} )

(** This rule needs to be duplicated to handle top sorts *)
| wf_exp_sub_typ :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ M : A }} ->
     {{ Δ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ M[σ] : A[σ] }} )
| wf_exp_sub_sort :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ A[σ] : Sort@s }} )
| wf_exp_conv :
  `( {{ Γ ⊢ M : A }} ->
     (** We have these extra argument for soundness. *)
     {{ Γ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ A' : Sort@s }} ->
     {{ Γ ⊢ A ⊆ A' @ s }} ->
     {{ Γ ⊢ M : A' }} )
where "Γ ⊢ M : A" := (wf_exp Γ A M) (in custom judg) : type_scope

with wf_sub {P : PtsSig} : ctx P -> ctx P -> sub P -> Prop :=
| wf_sub_id :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢s Id : Γ }} )
| wf_sub_weaken :
  `( {{ ⊢ Γ, A@s }} ->
     {{ Γ, A@s ⊢s Wk : Γ }} )
| wf_sub_compose :
  `( {{ Γ1 ⊢s σ2 : Γ2 }} ->
     {{ Γ2 ⊢s σ1 : Γ3 }} ->
     {{ Γ1 ⊢s σ1∘σ2 : Γ3 }} )
| wf_sub_extend :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ M : A[σ] }} ->
     {{ Γ ⊢s σ,,M : Δ, A@s }} )
| wf_sub_conv :
  `( {{ Γ ⊢s σ : Δ }} ->
     (** As in [wf_exp_conv], we need this extra argument for soundness *)
     {{ ⊢ Δ' }} ->
     {{ ⊢ Δ ⊆ Δ' }} ->
     {{ Γ ⊢s σ : Δ' }} )
where "Γ ⊢s σ : Δ" := (wf_sub Γ Δ σ) (in custom judg) : type_scope

with wf_ctx_eq {P : PtsSig} : ctx P -> ctx P -> Prop :=
| wf_ctx_eq_empty : {{ ⊢ ⋅ ≈ ⋅ }}
| wf_ctx_eq_extend :
  `( {{ ⊢ Γ ≈ Δ }} ->
     {{ Γ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ A' : Sort@s }} ->
     {{ Δ ⊢ A : Sort@s }} ->
     {{ Δ ⊢ A' : Sort@s }} ->
     {{ Γ ⊢ A ≈ A' : Sort@s }} ->
     {{ Δ ⊢ A ≈ A' : Sort@s }} ->
     {{ ⊢ Γ, A@s ≈ Δ, A'@s }} )
where "⊢ Γ ≈ Γ'" := (wf_ctx_eq Γ Γ') (in custom judg) : type_scope

with wf_exp_eq {P : PtsSig} : ctx P -> typ P -> exp P -> exp P -> Prop :=
| wf_exp_eq_typ_sub :
  `( Ax P s1 s2 ->
     {{ Γ ⊢s σ : Δ }} ->
     {{ Γ ⊢ Sort@s1[σ] ≈ Sort@s1 : Sort@s2 }} )

| wf_exp_eq_pi_sub :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢s σ : Δ }} ->
        {{ Δ ⊢ A : Sort@s1 }} ->
        {{ Δ, A@s1 ⊢ B : Sort@s2 }} ->
        {{ Γ ⊢ (Π r A B)[σ] ≈ Π r A[σ] B[q σ] : Sort@s3 }} )
| wf_exp_eq_pi_cong :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
        {{ Γ, A@s1 ⊢ B ≈ B' : Sort@s2 }} ->
        {{ Γ ⊢ Π r A B ≈ Π r A' B' : Sort@s3 }} )
| wf_exp_eq_fn_cong :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
        {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
        {{ Γ, A@s1 ⊢ M ≈ M' : B }} ->
        {{ Γ ⊢ λ r A M ≈ λ r A' M' : Π r A B }} )
| wf_exp_eq_fn_sub :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢s σ : Δ }} ->
        {{ Δ ⊢ A : Sort@s1 }} ->
        {{ Δ, A@s1 ⊢ B : Sort@s2 }} ->
        {{ Δ, A@s1 ⊢ M : B }} ->
        {{ Γ ⊢ (λ r A M)[σ] ≈ λ r A[σ] M[q σ] : (Π r A B)[σ] }} )
| wf_exp_eq_app_cong :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
        {{ Γ ⊢ M ≈ M' : Π r A B }} ->
        {{ Γ ⊢ N ≈ N' : A }} ->
        {{ Γ ⊢ M N ≈ M' N' : B[Id,,N] }} )
| wf_exp_eq_app_sub :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢s σ : Δ }} ->
        {{ Δ ⊢ A : Sort@s1 }} ->
        {{ Δ, A@s1 ⊢ B : Sort@s2 }} ->
        {{ Δ ⊢ M : Π r A B }} ->
        {{ Δ ⊢ N : A }} ->
        {{ Γ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }} )
| wf_exp_eq_pi_beta :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
        {{ Γ, A@s1 ⊢ M : B }} ->
        {{ Γ ⊢ N : A }} ->
        {{ Γ ⊢ (λ r A M) N ≈ M[Id,,N] : B[Id,,N] }} )
| wf_exp_eq_pi_eta :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
        {{ Γ ⊢ M : Π r A B }} ->
        {{ Γ ⊢ M ≈ λ r A (M[Wk] #0) : Π r A B }} )

(** Naturals **)
| wf_exp_eq_nat_sub :
  `( forall (r : Ru_nat P s),
        {{ Γ ⊢s σ : Δ }} ->
        {{ Γ ⊢ (ℕ)[σ] ≈ ℕ : Sort@s }} )
| wf_exp_eq_zero_sub :
  `( forall (r : Ru_nat P s),
        {{ Γ ⊢s σ : Δ }} ->
        {{ Γ ⊢ zero[σ] ≈ zero : ℕ}} )
| wf_exp_eq_succ_sub :
  `( forall (r : Ru_nat P s),
        {{ Γ ⊢s σ : Δ }} ->
        {{ Δ ⊢ M : ℕ}} ->
        {{ Γ ⊢ (succ M)[σ] ≈ succ (M[σ]) : ℕ}} )
| wf_exp_eq_succ_cong :
  `( forall (r : Ru_nat P s),
        {{ Γ ⊢ M ≈ M' : ℕ}} ->
        {{ Γ ⊢ succ M ≈ succ M' : ℕ}} )
| wf_exp_eq_natrec_cong :
  `( forall (r : Ru_nat P s),
        {{ Γ, ℕ@s ⊢ A : Sort@s' }} ->
        {{ Γ, ℕ@s ⊢ A' : Sort@s' }} ->
        {{ Γ, ℕ@s ⊢ A ≈ A' : Sort@s' }} ->
        {{ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] }} ->
        {{ Γ, ℕ@s, A@s' ⊢ MS ≈ MS' : A[Wk∘Wk,,succ #1] }} ->
        {{ Γ ⊢ M ≈ M' : ℕ}} ->
        {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }} )
| wf_exp_eq_natrec_sub :
  `( forall (r : Ru_nat P s),
        {{ Γ ⊢s σ : Δ }} ->
        {{ Δ, ℕ@s ⊢ A : Sort@s' }} ->
        {{ Δ ⊢ MZ : A[Id,,zero] }} ->
        {{ Δ, ℕ@s, A@s' ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
        {{ Δ ⊢ M : ℕ}} ->
        {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }} )
| wf_exp_eq_nat_beta_zero :
  `( forall (r : Ru_nat P s),
        {{ Γ, ℕ@s ⊢ A : Sort@s' }} ->
        {{ Γ ⊢ MZ : A[Id,,zero] }} ->
        {{ Γ, ℕ@s, A@s' ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
        {{ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }} )
| wf_exp_eq_nat_beta_succ :
  `( forall (r : Ru_nat P s),
        {{ Γ, ℕ@s ⊢ A : Sort@s' }} ->
        {{ Γ ⊢ MZ : A[Id,,zero] }} ->
        {{ Γ, ℕ@s, A@s' ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
        {{ Γ ⊢ M : ℕ}} ->
        {{ Γ ⊢ rec succ M return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }} )

| wf_exp_eq_var :
  `( {{ ⊢ Γ }} ->
     {{ #x : A@s ∈ Γ }} ->
     {{ Γ ⊢ #x ≈ #x : A }} )
| wf_exp_eq_var_0_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ M : A[σ] }} ->
     {{ Γ ⊢ #0[σ,,M] ≈ M : A[σ] }} )
| wf_exp_eq_var_S_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ M : A[σ] }} ->
     {{ #x : B@s' ∈ Δ }} ->
     {{ Γ ⊢ #(S x)[σ,,M] ≈ #x[σ] : B[σ] }} )
| wf_exp_eq_var_weaken :
  `( {{ ⊢ Γ, B@s' }} ->
     {{ #x : A@s ∈ Γ }} ->
     {{ Γ, B@s' ⊢ #x[Wk] ≈ #(S x) : A[Wk] }} )
(** This rule needs to be duplicated to handle top sorts *)
| wf_exp_eq_sub_cong_typ :
  `( {{ Δ ⊢ A : Sort@s }} ->
     {{ Δ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Γ ⊢ M[σ] ≈ M'[σ'] : A[σ] }} )
| wf_exp_eq_sub_cong_sort :
  `( {{ Δ ⊢ A ≈ A' : Sort@s }} ->
     {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Γ ⊢ A[σ] ≈ A'[σ'] : Sort@s }} )
| wf_exp_eq_sub_id :
  `( {{ Γ ⊢ M : A }} ->
     {{ Γ ⊢ M[Id] ≈ M : A }} )
(** This rule needs to be duplicated to handle top sorts *)
| wf_exp_eq_sub_compose_typ :
  `( {{ Γ ⊢s τ : Γ' }} ->
     {{ Γ' ⊢s σ : Γ'' }} ->
     {{ Γ'' ⊢ M : A }} ->
     {{ Γ'' ⊢ A : Sort@s }} ->
     {{ Γ ⊢ M[σ∘τ] ≈ M[σ][τ] : A[σ∘τ] }} )
| wf_exp_eq_sub_compose_sort :
  `( {{ Γ ⊢s τ : Γ' }} ->
     {{ Γ' ⊢s σ : Γ'' }} ->
     {{ Γ'' ⊢ A : Sort@s }} ->
     {{ Γ ⊢ A[σ∘τ] ≈ A[σ][τ] : Sort@s }} )
| wf_exp_eq_conv :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ A' : Sort@s }} ->
     {{ Γ ⊢ A ⊆ A' @ s }} ->
     {{ Γ ⊢ M ≈ M' : A' }} )
| wf_exp_eq_sym :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ M' ≈ M : A }} )
| wf_exp_eq_trans :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ M' ≈ M'' : A }} ->
     {{ Γ ⊢ M ≈ M'' : A }} )
where "Γ ⊢ M ≈ M' : A" := (wf_exp_eq Γ A M M') (in custom judg) : type_scope

with wf_sub_eq {P : PtsSig} : ctx P -> ctx P -> sub P -> sub P -> Prop :=
| wf_sub_eq_id :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢s Id ≈ Id : Γ }} )
| wf_sub_eq_weaken :
  `( {{ ⊢ Γ, A@s }} ->
     {{ Γ, A@s ⊢s Wk ≈ Wk : Γ }} )
| wf_sub_eq_compose_cong :
  `( {{ Γ ⊢s τ ≈ τ' : Γ' }} ->
     {{ Γ' ⊢s σ ≈ σ' : Γ'' }} ->
     {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Γ'' }} )
| wf_sub_eq_extend_cong :
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Δ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ M ≈ M' : A[σ] }} ->
     {{ Γ ⊢s σ,,M ≈ σ',,M' : Δ, A@s }} )
| wf_sub_eq_id_compose_right :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Γ ⊢s Id∘σ ≈ σ : Δ }} )
| wf_sub_eq_id_compose_left :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Γ ⊢s σ∘Id ≈ σ : Δ }} )
| wf_sub_eq_compose_assoc :
  `( {{ Γ' ⊢s σ : Γ }} ->
     {{ Γ'' ⊢s σ' : Γ' }} ->
     {{ Γ''' ⊢s σ'' : Γ'' }} ->
     {{ Γ''' ⊢s (σ∘σ')∘σ'' ≈ σ∘(σ'∘σ'') : Γ }} )
| wf_sub_eq_extend_compose :
  `( {{ Γ' ⊢s σ : Γ'' }} ->
     {{ Γ'' ⊢ A : Sort@s }} ->
     {{ Γ' ⊢ M : A[σ] }} ->
     {{ Γ ⊢s τ : Γ' }} ->
     {{ Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', A@s }} )
| wf_sub_eq_p_extend :
  `( {{ Γ' ⊢s σ : Γ }} ->
     {{ Γ ⊢ A : Sort@s }} ->
     {{ Γ' ⊢ M : A[σ] }} ->
     {{ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }} )
| wf_sub_eq_extend :
  `( {{ Γ' ⊢s σ : Γ, A@s }} ->
     {{ Γ' ⊢s σ ≈ (Wk∘σ),,#0[σ] : Γ, A@s }} )
| wf_sub_eq_sym :
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Γ ⊢s σ' ≈ σ : Δ }} )
| wf_sub_eq_trans :
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Γ ⊢s σ' ≈ σ'' : Δ }} ->
     {{ Γ ⊢s σ ≈ σ'' : Δ }} )
| wf_sub_eq_conv :
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ ⊢ Δ' }} ->
     {{ ⊢ Δ ⊆ Δ' }} ->
     {{ Γ ⊢s σ ≈ σ' : Δ' }} )
where "Γ ⊢s σ ≈ σ' : Δ" := (wf_sub_eq Γ Δ σ σ') (in custom judg) : type_scope

with wf_subtyp {P : PtsSig} : ctx P -> P -> typ P -> typ P -> Prop :=
| wf_subtyp_refl_typ :
  (** We need this extra argument in order to prove the lemmas
      in CtxSub.v independently. We can prove those and
      presupposition lemmas mutually dependently, but that would
      be more messy.

      The main point of this assumption gives presupposition for
      RHS directly so that we can remove the extra arguments in
      type checking rules immediately.
   *)
  `( {{ Γ ⊢ A' : Sort@s }} ->
     {{ Γ ⊢ A ≈ A' : Sort@s }} ->
     {{ Γ ⊢ A ⊆ A' @ s }} )
| wf_subtyp_trans :
  `( {{ Γ ⊢ A ⊆ A' @ s }} ->
     {{ Γ ⊢ A' ⊆ A'' @ s }} ->
     {{ Γ ⊢ A ⊆ A'' @ s }} )
| wf_subtyp_sort_sub :
  `( {{ ⊢ Γ }} ->
     Ru_sub P s1 s2 ->
     Ax P s2 s3 ->
     {{ Γ ⊢ Sort@s1 ⊆ Sort@s2 @ s3 }} )
| wf_subtyp_pi :
  `( forall {r : Ru P s1 s2 s3},
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ ⊢ A' : Sort@s1 }} ->
        {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
        {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
        {{ Γ, A'@s1 ⊢ B' : Sort@s2 }} ->
        {{ Γ, A'@s1 ⊢ B ⊆ B' @ s2 }} ->
        {{ Γ ⊢ Π r A B ⊆ Π r A' B' @ s3 }} )
where "Γ ⊢ A ⊆ A' @ s" := (wf_subtyp Γ s A A') (in custom judg) : type_scope.

(** Unsorted judgments for types *)
Inductive wf_typ {P : PtsSig} : ctx P -> typ P -> Prop :=
| wf_typ_st :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ Sort@s }})
| wf_typ_exp :
  `( {{ Γ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ A }})
where "Γ ⊢ A" := (wf_typ Γ A) (in custom judg) : type_scope.

Inductive wf_typ_eq {P : PtsSig} : ctx P -> typ P -> typ P -> Prop :=
| wf_typ_eq_refl :
  `( {{ Γ ⊢ A }} ->
     {{ Γ ⊢ A ≈ A }} )
| wf_typ_eq_sorted :
  `( {{ Γ ⊢ A ≈ B : Sort@s }} ->
     {{ Γ ⊢ A ≈ B }} )
| wf_tp_eq_trans_sorted :
  `( {{ Γ ⊢ A ≈ B }} ->
     {{ Γ ⊢ B ≈ C : Sort@s }} ->
     {{ Γ ⊢ A ≈ C }} )
where "Γ ⊢ A ≈ A'" := (wf_typ_eq Γ A A') (in custom judg) : type_scope.

Inductive wf_typ_subtyp {P} : ctx P -> typ P -> typ P -> Prop :=
| wf_typ_subtyp_refl :
  `( {{ Γ ⊢ A ≈ B }} ->
     {{ Γ ⊢ A ⊆ B }} )
| wf_typ_subtyp_subtyp :
  `( {{ Γ ⊢ A ⊆ A' @ s}} ->
     {{ Γ ⊢ A ⊆ A' }} )
| wf_typ_subtyp_trans :
  `( {{ Γ ⊢ A ⊆ B }} ->
     {{ Γ ⊢ B ⊆ C @ s }} ->
     {{ Γ ⊢ A ⊆ C }} )
where "Γ ⊢ A ⊆ A'" := (wf_typ_subtyp Γ A A') (in custom judg) : type_scope.

Scheme wf_ctx_mut_ind := Induction for wf_ctx Sort Prop
with wf_ctx_sub_mut_ind := Induction for wf_ctx_sub Sort Prop
with wf_ctx_eq_mut_ind := Induction for wf_ctx_eq Sort Prop
with wf_exp_mut_ind := Induction for wf_exp Sort Prop
with wf_exp_eq_mut_ind := Induction for wf_exp_eq Sort Prop
with wf_sub_mut_ind := Induction for wf_sub Sort Prop
with wf_sub_eq_mut_ind := Induction for wf_sub_eq Sort Prop
with wf_subtyp_mut_ind := Induction for wf_subtyp Sort Prop.
Combined Scheme syntactic_wf_mut_ind from
  wf_ctx_mut_ind,
  wf_ctx_sub_mut_ind,
  wf_ctx_eq_mut_ind,
  wf_exp_mut_ind,
  wf_exp_eq_mut_ind,
  wf_sub_mut_ind,
  wf_sub_eq_mut_ind,
  wf_subtyp_mut_ind.

Scheme wf_ctx_mut_ind' := Induction for wf_ctx Sort Prop
with wf_exp_mut_ind' := Induction for wf_exp Sort Prop
with wf_sub_mut_ind' := Induction for wf_sub Sort Prop.
Combined Scheme syntactic_wf_mut_ind' from
  wf_ctx_mut_ind',
  wf_exp_mut_ind',
  wf_sub_mut_ind'.


#[export]
Hint Constructors wf_ctx wf_ctx_sub wf_ctx_eq wf_exp wf_typ wf_sub wf_exp_eq wf_typ_eq wf_sub_eq wf_subtyp wf_typ_subtyp ctx_lookup : mcpts.

#[export]
Instance wf_exp_eq_PER {P : PtsSig} (Γ : ctx P) A : PER (wf_exp_eq Γ A).
Proof.
  split.
  - eauto using wf_exp_eq_sym.
  - eauto using wf_exp_eq_trans.
Qed.


#[export]
Instance wf_sub_eq_PER {P : PtsSig} (Γ : ctx P) Δ : PER (wf_sub_eq Γ Δ).
Proof.
  split.
  - eauto using wf_sub_eq_sym.
  - eauto using wf_sub_eq_trans.
Qed.


Lemma wf_typ_eq_trans {P} : forall {Γ : ctx P} {A B C},
    {{ Γ ⊢ A ≈ B }} ->
    {{ Γ ⊢ B ≈ C }} ->
    {{ Γ ⊢ A ≈ C }}.
Proof.
  intros * HAB HBC.
  gen A.
  induction HBC; intros; mauto 2.
  - assert {{ Γ ⊢ A0 ≈ B }} by mauto 2.
    mauto 2.
Qed.

Lemma wf_typ_eq_sym {P} : forall {Γ : ctx P} {A B},
    {{ Γ ⊢ A ≈ B }} ->
    {{ Γ ⊢ B ≈ A }}.
Proof.
  induction 1; mauto 2.
  - symmetry in H.
    mauto 2.
  - symmetry in H0.
    assert {{ Γ ⊢ C ≈ B }} by mauto 2.
    eapply wf_typ_eq_trans; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_eq_sym wf_typ_eq_trans : mcpts.

#[export]
Instance wf_typ_eq_PER {P : PtsSig} (Γ : ctx P) : PER (wf_typ_eq Γ).
Proof.
  split.
  - eauto using wf_typ_eq_sym.
  - eauto using wf_typ_eq_trans.
Qed.

Instance wf_ctx_eq_Symmetric {P : PtsSig} : Symmetric (@wf_ctx_eq P).
Proof.
  induction 1; mauto.
Qed.

#[export]
Instance wf_subtyp_Transitive {P : PtsSig} Γ s : Transitive (@wf_subtyp P Γ s).
Proof.
  hnf; mauto.
Qed.


(** Immediate & Independent Presuppositions *)
Lemma presup_ctx_sub {P} : forall {Γ Δ : ctx P}, {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

#[export]
Hint Resolve presup_ctx_sub : mcpts.

Lemma presup_ctx_sub_left {P} : forall {Γ Δ : ctx P}, {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_ctx_sub...
Qed.

#[export]
Hint Resolve presup_ctx_sub_left : mcpts.

Lemma presup_ctx_sub_right {P} : forall {Γ Δ : ctx P}, {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_ctx_sub...
Qed.

#[export]
Hint Resolve presup_ctx_sub_right : mcpts.

Lemma presup_wf_ctx_eq {P : PtsSig} : forall {Γ Δ : ctx P}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

#[export]
Hint Resolve presup_wf_ctx_eq : mcpts.

Lemma presup_wf_ctx_eq_left {P : PtsSig} : forall {Γ Δ : ctx P}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_wf_ctx_eq...
Qed.

#[export]
Hint Resolve presup_wf_ctx_eq_left : mcpts.

Lemma presup_wf_ctx_eq_right {P : PtsSig} : forall {Γ Δ : ctx P}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_wf_ctx_eq...
Qed.

#[export]
Hint Resolve presup_wf_ctx_eq_right : mcpts.

Lemma presup_subtyp_right {P} : forall {Γ : ctx P} {A B s}, {{ Γ ⊢ A ⊆ B @ s }} -> {{ Γ ⊢ B : Sort@s }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve presup_subtyp_right : mcpts.


Add Parametric Morphism {P : PtsSig} (Γ : ctx P) T : (wf_exp_eq Γ T)
    with signature wf_exp_eq Γ T ==> eq ==> iff as wf_exp_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ : ctx P) T : (wf_exp_eq Γ T)
    with signature eq ==> wf_exp_eq Γ T ==> iff as wf_exp_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ : ctx P) : (wf_typ_eq Γ)
    with signature wf_typ_eq Γ ==> eq ==> iff as wf_typ_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ : ctx P) : (wf_typ_eq Γ)
    with signature eq ==> wf_typ_eq Γ ==> iff as wf_typ_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P} (Γ : ctx P) s : (wf_typ_eq Γ)
  with signature eq ==> wf_exp_eq Γ {{{ Sort@s }}} ==> iff as wf_typ_eq_morphism_iff3.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P} (Γ : ctx P) s : (wf_typ_eq Γ)
  with signature wf_exp_eq Γ {{{ Sort@s }}} ==> eq ==> iff as wf_typ_eq_morphism_iff4.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ : ctx P) Δ : (wf_sub_eq Γ Δ)
    with signature wf_sub_eq Γ Δ ==> eq ==> iff as wf_sub_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ : ctx P) Δ : (wf_sub_eq Γ Δ)
    with signature eq ==> wf_sub_eq Γ Δ ==> iff as wf_sub_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.

#[export]
Hint Rewrite -> @wf_exp_eq_typ_sub using mauto 3 : mcpts.

#[export]
Hint Rewrite -> @wf_sub_eq_id_compose_right @wf_sub_eq_id_compose_left
                  @wf_sub_eq_compose_assoc (* prefer right association *)
                  @wf_sub_eq_p_extend using mauto 4 : mcpts.

#[export]
  Hint Rewrite -> @wf_exp_eq_sub_id @wf_exp_eq_pi_sub using mauto 4 : mcpts.

#[export]
Hint Rewrite -> @wf_exp_eq_typ_sub using mauto 3 : mcpts.


#[export]
Instance wf_exp_eq_per_elem {P : PtsSig} (Γ : ctx P) T : PERElem _ (wf_exp Γ T) (wf_exp_eq Γ T).
Proof.
  intros a Ha. mauto.
Qed.


#[export]
Instance wf_sub_eq_per_elem {P : PtsSig} (Γ : ctx P) Δ : PERElem _ (wf_sub Γ Δ) (wf_sub_eq Γ Δ).
Proof.
  intros a Ha. mauto.
Qed.
