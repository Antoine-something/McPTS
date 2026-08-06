From Coq Require Import List Classes.RelationClasses Setoid Morphisms String.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

(** Context lookups *)
Reserved Notation "'`#' x ∉ Δ" (in custom judg at level 80, x constr at level 0, Δ custom exp at level 50).
Reserved Notation "'`#' x : A ∈ Δ" (in custom judg at level 80, x constr at level 0, A custom exp, Δ custom exp at level 50).
Reserved Notation "'#' x : A ∈ Γ" (in custom judg at level 80, x constr at level 0, A custom exp, Γ custom exp at level 50).
(** Judgments for global contexts *)
Reserved Notation "⊢ Δ" (in custom judg at level 80, Δ custom exp).
Reserved Notation "⊢ Δ ≈ Δ'" (in custom judg at level 80, Δ custom exp, Δ' custom exp).
Reserved Notation "⊢ Δ ⊆ Δ'" (in custom judg at level 80, Δ custom exp, Δ' custom exp).
(** Judgments for local contexts *)
Reserved Notation "Δ ⊢ Γ" (in custom judg at level 80, Δ custom exp, Γ custom exp).
Reserved Notation "Δ ⊢ Γ ≈ Γ'" (in custom judg at level 80, Δ custom exp, Γ custom exp, Γ' custom exp).
Reserved Notation "Δ ⊢ Γ ⊆ Γ'" (in custom judg at level 80, Δ custom exp, Γ custom exp, Γ' custom exp).
(** Judgments for expressions *)
Reserved Notation "Δ ; Γ ⊢ M : A" (in custom judg at level 80, Δ custom exp, Γ custom exp, M custom exp, A custom exp).
Reserved Notation "Δ ; Γ ⊢ M ≈ M' : A" (in custom judg at level 80, Δ custom exp, Γ custom exp, M custom exp, M' custom exp, A custom exp).
(** Judgments for types *)
Reserved Notation "Δ ; Γ ⊢ A" (in custom judg at level 80, Δ custom exp, Γ custom exp, A custom exp).
Reserved Notation "Δ ; Γ ⊢ A ≈ A'" (in custom judg at level 80, Δ custom exp, Γ custom exp, A custom exp, A' custom exp).
Reserved Notation "Δ ; Γ ⊢ A ⊆ A'" (in custom judg at level 80, Δ custom exp, Γ custom exp, A custom exp, A' custom exp).
(** Judgments for substitutions *)
Reserved Notation "Δ ; Γ ⊢s σ : Γ'" (in custom judg at level 80, Δ custom exp, Γ custom exp, σ custom exp, Γ' custom exp).
Reserved Notation "Δ ; Γ ⊢s σ ≈ σ' : Γ'" (in custom judg at level 80, Δ custom exp, Γ custom exp, σ custom exp, σ' custom exp, Γ' custom exp).


Generalizable All Variables.

(** * Judgments definition *)
(** Fresh names *)
Inductive gctx_fresh {P} : string -> gctx P -> Prop :=
| fresh_nil : `( {{ `#x ∉ ⋅ }} )
| fresh_extend : `( {{ `#x ∉ Δ }} -> x <> y ->
                    {{ `#x ∉ Δ, y : A }} )
where "'`#' x ∉ Δ" := (gctx_fresh x Δ) (in custom judg) : type_scope.

#[export]
Hint Constructors gctx_fresh : mcpts.

(** Lookup in global contexts *)
Inductive gctx_lookup {P} : string -> typ P -> gctx P -> Prop :=
| ghere : `({{ `#x : A ∈ Δ, x : A }})
| gthere : `({{ `#x : A ∈ Δ }} ->
             x <> y ->
             {{ `#x : A ∈ Δ, y : B }})
where "'`#' x : A ∈ Δ" := (gctx_lookup x A Δ) (in custom judg) : type_scope.

#[export]
Hint Constructors gctx_lookup : mcpts.

(** Lookup in local contexts *)
Inductive ctx_lookup {P : PtsSig} : nat -> typ P -> ctx P -> Prop :=
| here : `({{ #0 : A[Wk] ∈ Γ, A }})
| there : `({{ #n : A ∈ Γ }} -> {{ #(S n) : A[Wk] ∈ Γ, B }})
where "'#' x : A ∈ Γ" := (ctx_lookup x A Γ) (in custom judg) : type_scope.

#[export]
Hint Constructors ctx_lookup : mcpts.

(** Well-formedness for global contexts *)
Inductive wf_gctx {P : PtsSig} : gctx P -> Prop :=
| wf_gctx_empty : {{ ⊢ ⋅ }}
| wf_gctx_extend :
  `( {{ ⊢ Δ }} ->
     {{ Δ ; ⋅ ⊢ A }} ->
     {{ `#x ∉ Δ }} ->
     {{ ⊢ Δ, x : A }} )
where "⊢ Δ" := (wf_gctx Δ) (in custom judg) : type_scope


(** Well-formedness for local contexts *)
with wf_ctx {P : PtsSig} : gctx P -> ctx P -> Prop :=
| wf_ctx_empty :
  `( {{ ⊢ Δ }} ->
     {{ Δ ⊢ ⋅ }} )
| wf_ctx_extend :
  `( {{ Δ ⊢ Γ }} ->
     {{ Δ ; Γ ⊢ A }} ->
     {{ Δ ⊢ Γ, A }} )
where "Δ ⊢ Γ" := (wf_ctx Δ Γ) (in custom judg) : type_scope


(** subtyping for local contexts *)                        
with wf_ctx_subtyp {P : PtsSig} : gctx P -> ctx P -> ctx P -> Prop :=
| wf_ctx_sub_empty :
  `( {{ ⊢ Δ }} ->
     {{ Δ ⊢ ⋅ ⊆ ⋅ }} )
| wf_ctx_sub_extend :
  `( {{ Δ ⊢ Γ ⊆ Γ' }} ->
     {{ Δ ; Γ ⊢ A }} ->
     {{ Δ ; Γ' ⊢ A' }} ->
     {{ Δ ; Γ ⊢ A ⊆ A' }} ->
     {{ Δ ⊢ Γ, A ⊆ Γ', A' }} )
where "Δ ⊢ Γ ⊆ Γ'" := (wf_ctx_subtyp Δ Γ Γ') (in custom judg) : type_scope

(** Well-formedness for expressions (i.e. typing) *)
with wf_exp {P : PtsSig} : gctx P -> ctx P -> typ P -> exp P -> Prop :=
(** Sorts *)
| wf_st :
  `( Ax_typ P s1 s2 ->
     {{ Δ ⊢ Γ }} ->
     {{ Δ ; Γ ⊢ Sort@s1 : Sort@s2 }} )

(** Functions *)
| wf_pi :
  `( forall (r : Ru_pi P s1 s2 s3),
      {{ Δ ; Γ ⊢ A : Sort@s1 }} ->
      {{ Δ ; Γ, A ⊢ B : Sort@s2 }} ->
      {{ Δ ; Γ ⊢ Π r A B : Sort@s3 }} )
| wf_fn :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Δ ; Γ ⊢ A : Sort@s1 }} ->
        {{ Δ ; Γ, A ⊢ B : Sort@s2 }} ->
        {{ Δ ; Γ, A ⊢ M : B }} ->
        {{ Δ ; Γ ⊢ λ r A B M : Π r A B }} )
| wf_app :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Δ ; Γ ⊢ A : Sort@s1 }} ->
        {{ Δ ; Γ, A ⊢ B : Sort@s2 }} ->
        {{ Δ ; Γ ⊢ M : Π r A B }} ->
        {{ Δ ; Γ ⊢ N : A }} ->
        {{ Δ ; Γ ⊢ M N : B[Id,,N] }} )

(** Variables *)
| wf_vlookup :
  `( {{ Δ ⊢ Γ }} ->
     (** This premise is redundant, but helpful for soundness *)
     (* {{ Γ ⊢ A }} -> *)
     {{ #x : A ∈ Γ }} ->
     {{ Δ ; Γ ⊢ #x : A }} )
(* NOTE: This rule might very well be wrong (no substitution?) *)
| wf_gvlookup :
  `( {{ Δ ; Γ ⊢s σ : ⋅ }} ->
     {{ `#x : A ∈ Δ }} ->
     {{ Δ ; Γ ⊢ `#x : A[σ] }} )
  
(** Naturals **)
| wf_nat :
  `( forall (r : Ru_nat P s),
        {{ Δ ⊢ Γ }} ->
        {{ Δ ; Γ ⊢ ℕ: Sort@s }} )
| wf_zero :
  `(forall (r : Ru_nat P s),
        {{ Δ ⊢ Γ }} ->
        {{ Δ ; Γ ⊢ zero : ℕ}} )
| wf_succ :
  `( forall (r : Ru_nat P s),
        {{ Δ ; Γ ⊢ M : ℕ}} ->
        {{ Δ ; Γ ⊢ succ M : ℕ}} )
| wf_natrec :
  `( forall (r : Ru_nat P s),
        {{ Δ ; Γ, ℕ ⊢ A }} ->
        {{ Δ ; Γ ⊢ MZ : A[Id,,zero] }} ->
        {{ Δ ; Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
        {{ Δ ; Γ ⊢ M : ℕ}} ->
        {{ Δ ; Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }} )

| wf_exp_sub :
  `( {{ Δ ; Γ ⊢s σ : Γ' }} ->
     {{ Δ ; Γ' ⊢ M : A }} ->
     {{ Δ ; Γ' ⊢ A }} ->
     {{ Δ ; Γ ⊢ M[σ] : A[σ] }} )

| wf_exp_conv :
  `( {{ Δ ; Γ ⊢ M : A }} ->
     (* We have these extra argument for soundness. *)
     {{ Δ ; Γ ⊢ A }} ->
     {{ Δ ; Γ ⊢ A' }} ->
     {{ Δ ; Γ ⊢ A ⊆ A' }} ->
     {{ Δ ; Γ ⊢ M : A' }} )
where "Δ ; Γ ⊢ M : A" := (wf_exp Δ Γ A M) (in custom judg) : type_scope

(** Equality for expressions *)
with wf_exp_eq {P : PtsSig} : gctx P -> ctx P -> typ P -> exp P -> exp P -> Prop :=
| wf_exp_eq_typ_sub :
  `( {{ Δ ; Γ ⊢ Sort@s1 : Sort@s2 }} ->
     {{ Δ ; Γ' ⊢ Sort@s1 : Sort@s2 }} ->
     {{ Δ ; Γ ⊢s σ : Γ' }} ->
     {{ Δ ; Γ ⊢ Sort@s1[σ] ≈ Sort@s1 : Sort@s2 }} )

| wf_exp_eq_pi_sub :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Δ ; Γ ⊢s σ : Γ' }} ->
        {{ Δ ; Γ' ⊢ A : Sort@s1 }} ->
        {{ Δ ; Γ', A ⊢ B : Sort@s2 }} ->
        {{ Δ ; Γ ⊢ (Π r A B)[σ] ≈ Π r A[σ] B[q σ] : Sort@s3 }} )
| wf_exp_eq_pi_cong :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Δ ; Γ ⊢ A : Sort@s1 }} ->
        {{ Δ ; Γ ⊢ A ≈ A' : Sort@s1 }} ->
        {{ Δ ; Γ, A ⊢ B ≈ B' : Sort@s2 }} ->
        {{ Δ ; Γ ⊢ Π r A B ≈ Π r A' B' : Sort@s3 }} )
| wf_exp_eq_fn_cong :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Δ ; Γ ⊢ A : Sort@s1 }} ->
        {{ Δ ; Γ ⊢ A ≈ A' : Sort@s1 }} ->
        {{ Δ ; Γ, A ⊢ B : Sort@s2 }} ->
        {{ Δ ; Γ, A ⊢ B ≈ B' : Sort@s2 }} ->
        {{ Δ ; Γ, A ⊢ M ≈ M' : B }} ->
        {{ Δ ; Γ ⊢ λ r A B M ≈ λ r A' B' M' : Π r A B }} )
| wf_exp_eq_fn_sub :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Δ ; Γ ⊢s σ : Γ' }} ->
        {{ Δ ; Γ' ⊢ A : Sort@s1 }} ->
        {{ Δ ; Γ', A ⊢ B : Sort@s2 }} ->
        {{ Δ ; Γ', A ⊢ M : B }} ->
        {{ Δ ; Γ ⊢ (λ r A B M)[σ] ≈ λ r A[σ] B[q σ] M[q σ] : (Π r A B)[σ] }} )
| wf_exp_eq_app_cong :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Δ ; Γ ⊢ A : Sort@s1 }} ->
        {{ Δ ; Γ, A ⊢ B : Sort@s2 }} ->
        {{ Δ ; Γ ⊢ M ≈ M' : Π r A B }} ->
        {{ Δ ; Γ ⊢ N ≈ N' : A }} ->
        {{ Δ ; Γ ⊢ M N ≈ M' N' : B[Id,,N] }} )
| wf_exp_eq_app_sub :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Δ ; Γ ⊢s σ : Γ' }} ->
        {{ Δ ; Γ' ⊢ A : Sort@s1 }} ->
        {{ Δ ; Γ', A ⊢ B : Sort@s2 }} ->
        {{ Δ ; Γ' ⊢ M : Π r A B }} ->
        {{ Δ ; Γ' ⊢ N : A }} ->
        {{ Δ ; Γ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }} )
| wf_exp_eq_pi_beta :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Δ ; Γ ⊢ A : Sort@s1 }} ->
        {{ Δ ; Γ, A ⊢ B : Sort@s2 }} ->
        {{ Δ ; Γ, A ⊢ M : B }} ->
        {{ Δ ; Γ ⊢ N : A }} ->
        {{ Δ ; Γ ⊢ (λ r A B M) N ≈ M[Id,,N] : B[Id,,N] }} )
| wf_exp_eq_pi_eta :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Δ ; Γ ⊢ A : Sort@s1 }} ->
        {{ Δ ; Γ, A ⊢ B : Sort@s2 }} ->
        {{ Δ ; Γ ⊢ M : Π r A B }} ->
        {{ Δ ; Γ ⊢ M ≈ λ r A B (M[Wk] #0) : Π r A B }} )

(** Naturals **)
| wf_exp_eq_nat_sub :
  `( forall (r : Ru_nat P s),
        {{ Δ ; Γ ⊢s σ : Γ' }} ->
        {{ Δ ; Γ ⊢ (ℕ)[σ] ≈ ℕ : Sort@s }} )
| wf_exp_eq_zero_sub :
  `( forall (r : Ru_nat P s),
        {{ Δ ; Γ ⊢s σ : Γ' }} ->
        {{ Δ ; Γ ⊢ zero[σ] ≈ zero : ℕ}} )
| wf_exp_eq_succ_sub :
  `( forall (r : Ru_nat P s),
        {{ Δ ; Γ ⊢s σ : Γ' }} ->
        {{ Δ ; Γ' ⊢ M : ℕ}} ->
        {{ Δ ; Γ ⊢ (succ M)[σ] ≈ succ (M[σ]) : ℕ}} )
| wf_exp_eq_succ_cong :
  `( forall (r : Ru_nat P s),
        {{ Δ ; Γ ⊢ M ≈ M' : ℕ}} ->
        {{ Δ ; Γ ⊢ succ M ≈ succ M' : ℕ}} )
| wf_exp_eq_natrec_cong :
  `( forall (r : Ru_nat P s),
        {{ Δ ; Γ, ℕ ⊢ A }} ->
        {{ Δ ; Γ, ℕ ⊢ A' }} ->
        {{ Δ ; Γ, ℕ ⊢ A ≈ A' }} ->
        {{ Δ ; Γ ⊢ MZ ≈ MZ' : A[Id,,zero] }} ->
        {{ Δ ; Γ, ℕ, A ⊢ MS ≈ MS' : A[Wk∘Wk,,succ #1] }} ->
        {{ Δ ; Γ ⊢ M ≈ M' : ℕ}} ->
        {{ Δ ; Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }} )
| wf_exp_eq_natrec_sub :
  `( forall (r : Ru_nat P s),
        {{ Δ ; Γ ⊢s σ : Γ' }} ->
        {{ Δ ; Γ', ℕ ⊢ A }} ->
        {{ Δ ; Γ' ⊢ MZ : A[Id,,zero] }} ->
        {{ Δ ; Γ', ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
        {{ Δ ; Γ' ⊢ M : ℕ}} ->
        {{ Δ ; Γ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }} )
| wf_exp_eq_nat_beta_zero :
  `( forall (r : Ru_nat P s),
        {{ Δ ; Γ, ℕ ⊢ A }} ->
        {{ Δ ; Γ ⊢ MZ : A[Id,,zero] }} ->
        {{ Δ ; Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
        {{ Δ ; Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }} )
| wf_exp_eq_nat_beta_succ :
  `( forall (r : Ru_nat P s),
        {{ Δ ; Γ, ℕ ⊢ A }} ->
        {{ Δ ; Γ ⊢ MZ : A[Id,,zero] }} ->
        {{ Δ ; Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
        {{ Δ ; Γ ⊢ M : ℕ}} ->
        {{ Δ ; Γ ⊢ rec succ M return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }} )

(** Local variables *)
| wf_exp_eq_var :
  `( {{ Δ ⊢ Γ }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Δ ; Γ ⊢ #x ≈ #x : A }} )
| wf_exp_eq_var_0_sub :
  `( {{ Δ ; Γ ⊢s σ : Γ' }} ->
     {{ Δ ; Γ' ⊢ A }} ->
     {{ Δ ; Γ ⊢ M : A[σ] }} ->
     {{ Δ ; Γ ⊢ #0[σ,,M] ≈ M : A[σ] }} )
| wf_exp_eq_var_S_sub :
  `( {{ Δ ; Γ ⊢s σ : Γ' }} ->
     {{ Δ ; Γ' ⊢ A }} ->
     {{ Δ ; Γ ⊢ M : A[σ] }} ->
     {{ #x : B ∈ Γ' }} ->
     {{ Δ ; Γ ⊢ #(S x)[σ,,M] ≈ #x[σ] : B[σ] }} )
| wf_exp_eq_var_weaken :
  `( {{ Δ ⊢ Γ, B }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Δ ; Γ, B ⊢ #x[Wk] ≈ #(S x) : A[Wk] }} )

(** Global variables *)
(* NOTE: First attempt at equality rules for gvar, may need adjustments *)
(* | wf_exp_eq_gvar_refl : *)
(*   `( {{ Δ ; Γ ⊢s σ : ⋅ }} -> *)
(*      {{ `#x : A ∈ Δ }} -> *)
(*      {{ Δ ; Γ ⊢ `#x ≈ `#x : A }} ) *)
| wf_exp_eq_gvar_sub :
  `( {{ Δ ; Γ ⊢s σ : ⋅ }} ->
     {{ `#x : A ∈ Δ }} ->
     {{ Δ ; Γ ⊢ `#x[σ] ≈ `#x : A[σ] }} )

(** Substitution propagation *)
| wf_exp_eq_sub_cong :
  `( {{ Δ ; Γ' ⊢ A }} ->
     {{ Δ ; Γ' ⊢ M ≈ M' : A }} ->
     {{ Δ ; Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ Δ ; Γ ⊢ M[σ] ≈ M'[σ'] : A[σ] }} )
| wf_exp_eq_sub_id :
  `( {{ Δ ; Γ ⊢ M : A }} ->
     {{ Δ ; Γ ⊢ M[Id] ≈ M : A }} )
| wf_exp_eq_sub_compose :
  `( {{ Δ ; Γ ⊢s τ : Γ' }} ->
     {{ Δ ; Γ' ⊢s σ : Γ'' }} ->
     {{ Δ ; Γ'' ⊢ M : A }} ->
     {{ Δ ; Γ'' ⊢ A }} ->
     {{ Δ ; Γ ⊢ M[σ∘τ] ≈ M[σ][τ] : A[σ∘τ] }} )

   
| wf_exp_eq_conv :
  `( {{ Δ ; Γ ⊢ M ≈ M' : A }} ->
     {{ Δ ; Γ ⊢ A' }} ->
     {{ Δ ; Γ ⊢ A ⊆ A' }} ->
     {{ Δ ; Γ ⊢ M ≈ M' : A' }} )
| wf_exp_eq_sym :
  `( {{ Δ ; Γ ⊢ M ≈ M' : A }} ->
     {{ Δ ; Γ ⊢ M' ≈ M : A }} )
| wf_exp_eq_trans :
  `( {{ Δ ; Γ ⊢ M ≈ M' : A }} ->
     {{ Δ ; Γ ⊢ M' ≈ M'' : A }} ->
     {{ Δ ; Γ ⊢ M ≈ M'' : A }} )
where "Δ ; Γ ⊢ M ≈ M' : A" := (wf_exp_eq Δ Γ A M M') (in custom judg) : type_scope

(** Well-formedness for types *)
with wf_typ {P : PtsSig} : gctx P -> ctx P -> typ P -> Prop :=
| wf_typ_st :
  `( {{ Δ ⊢ Γ }} ->
     {{ Δ ; Γ ⊢ Sort@s }})
| wf_typ_exp :
  `( {{ Δ ; Γ ⊢ A : Sort@s }} ->
     {{ Δ ; Γ ⊢ A }})
| wf_typ_sub_sort :
  `( {{ Δ ; Γ ⊢s σ : Γ' }} ->
     {{ Δ ; Γ' ⊢ A }} ->
     {{ Δ ; Γ ⊢ A[σ] }} )
where "Δ ; Γ ⊢ A" := (wf_typ Δ Γ A) (in custom judg) : type_scope

(** Equality for types *)
with wf_typ_eq {P : PtsSig} : gctx P -> ctx P -> typ P -> typ P -> Prop :=
| wf_typ_eq_sorted :
  `( {{ Δ ; Γ ⊢ A ≈ B : Sort@s }} ->
     {{ Δ ; Γ ⊢ A ≈ B }} )
| wf_typ_eq_sub_sort :
  `( {{ Δ ; Γ ⊢s σ : Γ' }} ->
     {{ Δ ; Γ ⊢ Sort@s1[σ] ≈ Sort@s1 }} )
| wf_typ_eq_sub_cong :
  `( {{ Δ ; Γ' ⊢ A ≈ A' }} ->
     {{ Δ ; Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ Δ ; Γ ⊢ A[σ] ≈ A'[σ'] }} )
| wf_typ_eq_sub_compose :
  `( {{ Δ ; Γ ⊢s τ : Γ' }} ->
     {{ Δ ; Γ' ⊢s σ : Γ'' }} ->
     {{ Δ ; Γ'' ⊢ A  }} ->
     {{ Δ ; Γ ⊢ A[σ∘τ] ≈ A[σ][τ] }} )   
| wf_typ_eq_sym :
  `( {{ Δ ; Γ ⊢ A ≈ B }} ->
     {{ Δ ; Γ ⊢ B ≈ A }} )
| wf_typ_eq_trans :
  `( {{ Δ ; Γ ⊢ A ≈ B }} ->
     {{ Δ ; Γ ⊢ B ≈ C }} ->
     {{ Δ ; Γ ⊢ A ≈ C }} )
where "Δ ; Γ ⊢ A ≈ A'" := (wf_typ_eq Δ Γ A A') (in custom judg) : type_scope

(** Subtyping for types *)
with wf_typ_subtyp {P : PtsSig} : gctx P -> ctx P -> typ P -> typ P -> Prop :=
| wf_typ_subtyp_refl :
  `( {{ Δ ; Γ ⊢ A ≈ B }} ->
     {{ Δ ; Γ ⊢ B }} ->
     {{ Δ ; Γ ⊢ A ⊆ B }} )
| wf_typ_subtyp_trans :
  `( {{ Δ ; Γ ⊢ A ⊆ B }} ->
     {{ Δ ; Γ ⊢ B ⊆ C }} ->
     {{ Δ ; Γ ⊢ A ⊆ C }} )
| wf_typ_subtyp_sort_ax_sub :
  `( Ax_sub P s1 s2 ->
     {{ Δ ⊢ Γ }} ->
     {{ Δ ; Γ ⊢ Sort@s1 ⊆ Sort@s2 }} )   
| wf_typ_subtyp_pi :
  `( forall {r : Ru_pi P s1 s2 s3},
        {{ Δ ; Γ ⊢ A : Sort@s1 }} ->
        {{ Δ ; Γ ⊢ A' : Sort@s1 }} ->
        {{ Δ ; Γ ⊢ A ≈ A' : Sort@s1 }} ->
        {{ Δ ; Γ, A ⊢ B : Sort@s2 }} ->
        {{ Δ ; Γ, A' ⊢ B' : Sort@s2 }} ->
        {{ Δ ; Γ, A' ⊢ B ⊆ B' }} ->
        {{ Δ ; Γ ⊢ Π r A B ⊆ Π r A' B' }} )
where "Δ ; Γ ⊢ A ⊆ A'" := (wf_typ_subtyp Δ Γ A A') (in custom judg) : type_scope

(** Well-formedness for substitutions *)                                                              
with wf_sub {P : PtsSig} : gctx P -> ctx P -> ctx P -> sub P -> Prop :=
| wf_sub_id :
  `( {{ Δ ⊢ Γ }} ->
     {{ Δ ; Γ ⊢s Id : Γ }} )
| wf_sub_weaken :
  `( {{ Δ ⊢ Γ, A }} ->
     {{ Δ ; Γ, A ⊢s Wk : Γ }} )
| wf_sub_compose :
  `( {{ Δ ; Γ1 ⊢s σ2 : Γ2 }} ->
     {{ Δ ; Γ2 ⊢s σ1 : Γ3 }} ->
     {{ Δ ; Γ1 ⊢s σ1∘σ2 : Γ3 }} )
| wf_sub_extend :
  `( {{ Δ ; Γ ⊢s σ : Γ' }} ->
     {{ Δ ; Γ' ⊢ A }} ->
     {{ Δ ; Γ ⊢ M : A[σ] }} ->
     {{ Δ ; Γ ⊢s σ,,M : Γ', A }} )
| wf_sub_conv :
  `( {{ Δ ; Γ ⊢s σ : Γ' }} ->
     (** As in [wf_exp_conv], we need this extra argument for soundness *)
     {{ Δ ⊢ Γ'' }} ->
     {{ Δ ⊢ Γ' ⊆ Γ'' }} ->
     {{ Δ ; Γ ⊢s σ : Γ'' }} )
where "Δ ; Γ ⊢s σ : Γ'" := (wf_sub Δ Γ Γ' σ) (in custom judg) : type_scope

(** Equality of substitutions *)
with wf_sub_eq {P : PtsSig} : gctx P -> ctx P -> ctx P -> sub P -> sub P -> Prop :=
| wf_sub_eq_id :
  `( {{ Δ ⊢ Γ }} ->
     {{ Δ ; Γ ⊢s Id ≈ Id : Γ }} )
| wf_sub_eq_weaken :
  `( {{ Δ ⊢ Γ, A }} ->
     {{ Δ ; Γ, A ⊢s Wk ≈ Wk : Γ }} )
| wf_sub_eq_compose_cong :
  `( {{ Δ ; Γ ⊢s τ ≈ τ' : Γ' }} ->
     {{ Δ ; Γ' ⊢s σ ≈ σ' : Γ'' }} ->
     {{ Δ ; Γ ⊢s σ∘τ ≈ σ'∘τ' : Γ'' }} )
| wf_sub_eq_extend_cong :
  `( {{ Δ ; Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ Δ ; Γ' ⊢ A }} ->
     {{ Δ ; Γ ⊢ M ≈ M' : A[σ] }} ->
     {{ Δ ; Γ ⊢s σ,,M ≈ σ',,M' : Γ', A }} )
| wf_sub_eq_id_compose_right :
  `( {{ Δ ; Γ ⊢s σ : Γ' }} ->
     {{ Δ ; Γ ⊢s Id∘σ ≈ σ : Γ' }} )
| wf_sub_eq_id_compose_left :
  `( {{ Δ ; Γ ⊢s σ : Γ' }} ->
     {{ Δ ; Γ ⊢s σ∘Id ≈ σ : Γ' }} )
| wf_sub_eq_compose_assoc :
  `( {{ Δ ; Γ' ⊢s σ : Γ }} ->
     {{ Δ ; Γ'' ⊢s σ' : Γ' }} ->
     {{ Δ ; Γ''' ⊢s σ'' : Γ'' }} ->
     {{ Δ ; Γ''' ⊢s (σ∘σ')∘σ'' ≈ σ∘(σ'∘σ'') : Γ }} )
| wf_sub_eq_extend_compose :
  `( {{ Δ ; Γ' ⊢s σ : Γ'' }} ->
     {{ Δ ; Γ'' ⊢ A }} ->
     {{ Δ ; Γ' ⊢ M : A[σ] }} ->
     {{ Δ ; Γ ⊢s τ : Γ' }} ->
     {{ Δ ; Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', A }} )
| wf_sub_eq_p_extend :
  `( {{ Δ ; Γ' ⊢s σ : Γ }} ->
     {{ Δ ; Γ ⊢ A }} ->
     {{ Δ ; Γ' ⊢ M : A[σ] }} ->
     {{ Δ ; Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }} )
| wf_sub_eq_extend :
  `( {{ Δ ; Γ' ⊢s σ : Γ, A }} ->
     {{ Δ ; Γ' ⊢s σ ≈ (Wk∘σ),,#0[σ] : Γ, A }} )
| wf_sub_eq_sym :
  `( {{ Δ ; Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ Δ ; Γ ⊢s σ' ≈ σ : Γ' }} )
| wf_sub_eq_trans :
  `( {{ Δ ; Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ Δ ; Γ ⊢s σ' ≈ σ'' : Γ' }} ->
     {{ Δ ; Γ ⊢s σ ≈ σ'' : Γ' }} )
| wf_sub_eq_conv :
  `( {{ Δ ; Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ Δ ⊢ Γ'' }} ->
     {{ Δ ⊢ Γ' ⊆ Γ'' }} ->
     {{ Δ ; Γ ⊢s σ ≈ σ' : Γ'' }} )
where "Δ ; Γ ⊢s σ ≈ σ' : Γ'" := (wf_sub_eq Δ Γ Γ' σ σ') (in custom judg) : type_scope.

#[export]
Hint Constructors wf_gctx wf_ctx wf_ctx_subtyp wf_exp wf_exp_eq wf_typ wf_typ_eq wf_typ_subtyp wf_sub wf_sub_eq : mcpts.

Scheme wf_gctx_mut_ind := Induction for wf_gctx Sort Prop
with wf_ctx_mut_ind := Induction for wf_ctx Sort Prop
with wf_ctx_subtyp_mut_ind := Induction for wf_ctx_subtyp Sort Prop
with wf_exp_mut_ind := Induction for wf_exp Sort Prop
with wf_exp_eq_mut_ind := Induction for wf_exp_eq Sort Prop
with wf_typ_mut_ind := Induction for wf_typ Sort Prop
with wf_typ_eq_mut_ind := Induction for wf_typ_eq Sort Prop
with wf_typ_subtyp_mut_ind := Induction for wf_typ_subtyp Sort Prop     
with wf_sub_mut_ind := Induction for wf_sub Sort Prop
with wf_sub_eq_mut_ind := Induction for wf_sub_eq Sort Prop.
Combined Scheme syntactic_wf_mut_ind from
  wf_gctx_mut_ind,
  wf_ctx_mut_ind,
  wf_ctx_subtyp_mut_ind,
  wf_exp_mut_ind,
  wf_exp_eq_mut_ind,
  wf_typ_mut_ind,
  wf_typ_eq_mut_ind,
  wf_typ_subtyp_mut_ind,
  wf_sub_mut_ind,
  wf_sub_eq_mut_ind.  

Scheme wf_ctx_local_mut_ind := Induction for wf_ctx Sort Prop
with wf_ctx_subtyp_local_mut_ind := Induction for wf_ctx_subtyp Sort Prop
with wf_exp_local_mut_ind := Induction for wf_exp Sort Prop
with wf_exp_eq_local_mut_ind := Induction for wf_exp_eq Sort Prop
with wf_typ_local_mut_ind := Induction for wf_typ Sort Prop
with wf_typ_eq_local_mut_ind := Induction for wf_typ_eq Sort Prop
with wf_typ_subtyp_local_mut_ind := Induction for wf_typ_subtyp Sort Prop     
with wf_sub_local_mut_ind := Induction for wf_sub Sort Prop
with wf_sub_eq_local_mut_ind := Induction for wf_sub_eq Sort Prop.
Combined Scheme syntactic_wf_local_mut_ind from
  wf_ctx_local_mut_ind,
  wf_ctx_subtyp_local_mut_ind,
  wf_exp_local_mut_ind,
  wf_exp_eq_local_mut_ind,
  wf_typ_local_mut_ind,
  wf_typ_eq_local_mut_ind,
  wf_typ_subtyp_local_mut_ind,
  wf_sub_local_mut_ind,
  wf_sub_eq_local_mut_ind.  

Scheme wf_exp_no_ctx_mut_ind := Induction for wf_exp Sort Prop
with wf_exp_eq_no_ctx_mut_ind := Induction for wf_exp_eq Sort Prop
with wf_typ_no_ctx_mut_ind := Induction for wf_typ Sort Prop
with wf_typ_eq_no_ctx_mut_ind := Induction for wf_typ_eq Sort Prop
with wf_typ_subtyp_no_ctx_mut_ind := Induction for wf_typ_subtyp Sort Prop     
with wf_sub_no_ctx_mut_ind := Induction for wf_sub Sort Prop
with wf_sub_eq_no_ctx_mut_ind := Induction for wf_sub_eq Sort Prop.
Combined Scheme syntactic_wf_no_ctx_mut_ind from
  wf_exp_no_ctx_mut_ind,
  wf_exp_eq_no_ctx_mut_ind,
  wf_typ_no_ctx_mut_ind,
  wf_typ_eq_no_ctx_mut_ind,
  wf_typ_subtyp_no_ctx_mut_ind,
  wf_sub_no_ctx_mut_ind,
  wf_sub_eq_no_ctx_mut_ind.  

Scheme wf_gctx_mut_ind' := Induction for wf_gctx Sort Prop
with wf_ctx_mut_ind' := Induction for wf_ctx Sort Prop
with wf_exp_mut_ind' := Induction for wf_exp Sort Prop
with wf_typ_mut_ind' := Induction for wf_typ Sort Prop
with wf_sub_mut_ind' := Induction for wf_sub Sort Prop.
Combined Scheme syntactic_wf_mut_ind' from
  wf_ctx_mut_ind',
  wf_exp_mut_ind',
  wf_typ_mut_ind',
  wf_sub_mut_ind'.


(** Equality for global contexts *)
Inductive wf_gctx_eq {P : PtsSig} : gctx P -> gctx P -> Prop :=
| wf_gctx_eq_empty : {{ ⊢ ⋅ ≈ ⋅ }}
| wf_gctx_eq_extend :
  `( {{ ⊢ Δ ≈ Δ' }} ->
     {{ Δ ; ⋅ ⊢ A }} ->
     {{ Δ ; ⋅ ⊢ A' }} ->
     {{ Δ' ; ⋅ ⊢ A }} ->
     {{ Δ' ; ⋅ ⊢ A' }} ->
     {{ Δ ; ⋅ ⊢ A ≈ A' }} ->
     {{ Δ' ; ⋅ ⊢ A ≈ A' }} ->
     {{ `#x ∉ Δ }} ->
     {{ `#x ∉ Δ' }} ->
     {{ ⊢ Δ, x : A ≈ Δ', x : A' }} )
where "⊢ Δ ≈ Δ'" := (wf_gctx_eq Δ Δ') (in custom judg) : type_scope.

#[export]
Hint Constructors wf_gctx_eq : mcpts.

(** Subtyping for global contexts *)
Inductive wf_gctx_subtyp {P : PtsSig} :  gctx P -> gctx P -> Prop :=
| wf_gctx_subtyp_empty : {{ ⊢ ⋅ ⊆ ⋅ }}
| wf_gctx_subtyp_extend :
  `( {{ ⊢ Δ ⊆ Δ' }} ->
     {{ Δ ; ⋅ ⊢ A }} ->
     {{ Δ' ; ⋅ ⊢ A' }} ->
     {{ Δ ; ⋅ ⊢ A ⊆ A' }} ->
     {{ `#x ∉ Δ }} ->
     {{ `#x ∉ Δ' }} ->
     {{ ⊢ Δ, x : A ⊆ Δ', x : A' }} )
where "⊢ Δ ⊆ Δ'" := (wf_gctx_subtyp Δ Δ') (in custom judg) : type_scope.

#[export]
Hint Constructors wf_gctx_subtyp : mcpts.

(** Equality for local contexts *)
Inductive wf_ctx_eq {P : PtsSig} : gctx P -> ctx P -> ctx P -> Prop :=
| wf_ctx_eq_empty :
  `( {{ ⊢ Δ }} ->
     {{ Δ ⊢ ⋅ ≈ ⋅ }} )
| wf_ctx_eq_extend :
  `( {{ Δ ⊢ Γ ≈ Γ' }} ->
     {{ Δ ; Γ ⊢ A }} ->
     {{ Δ ; Γ ⊢ A' }} ->
     {{ Δ ; Γ' ⊢ A }} ->
     {{ Δ ; Γ' ⊢ A' }} ->
     {{ Δ ; Γ ⊢ A ≈ A' }} ->
     {{ Δ ; Γ' ⊢ A ≈ A' }} ->
     {{ Δ ⊢ Γ, A ≈ Γ', A' }} )
where "Δ ⊢ Γ ≈ Γ'" := (wf_ctx_eq Δ Γ Γ') (in custom judg) : type_scope.

#[export]
Hint Constructors wf_ctx_eq : mcpts.


(** * Equality judgments are equivalences *)
(** For wf_exp_eq *)
#[export]
Instance wf_exp_eq_PER {P : PtsSig} (Δ : gctx P) (Γ : ctx P) (A : typ P) : PER (wf_exp_eq Δ Γ A).
Proof.
  split.
  - eauto using wf_exp_eq_sym.
  - eauto using wf_exp_eq_trans.
Qed.

#[export]
Instance wf_exp_eq_per_elem {P : PtsSig} (Δ : gctx P) (Γ : ctx P) (A : typ P) : PERElem _ (wf_exp Δ Γ A) (wf_exp_eq Δ Γ A).
Proof.
  intros a Ha. mauto.
Qed.

(** For wf_sub_eq *)
#[export]
Instance wf_sub_eq_PER {P : PtsSig} (Δ : gctx P) (Γ Γ' : ctx P) : PER (wf_sub_eq Δ Γ Γ').
Proof.
  split.
  - eauto using wf_sub_eq_sym.
  - eauto using wf_sub_eq_trans.
Qed.

#[export]
Instance wf_sub_eq_per_elem {P : PtsSig} (Δ : gctx P) (Γ Γ' : ctx P) : PERElem _ (wf_sub Δ Γ Γ') (wf_sub_eq Δ Γ Γ').
Proof.
  intros a Ha. mauto.
Qed.

(** For wf_typ_eq *) 
#[export]
Instance wf_typ_eq_PER {P : PtsSig} (Δ : gctx P) (Γ : ctx P) : PER (wf_typ_eq Δ Γ).
Proof.
  split.
  - eauto using wf_typ_eq_sym.
  - eauto using wf_typ_eq_trans.
Qed.

#[export]
Instance wf_typ_eq_per_elem {P : PtsSig} (Δ : gctx P) (Γ : ctx P) : PERElem _ (wf_typ Δ Γ) (wf_typ_eq Δ Γ).
Proof.
  induction 1.
  - transitivity {{{ Sort@s[Id] }}}; mauto.
  - enough {{ Δ; Γ ⊢ A ≈ A : Sort@s }}; mauto.
  - enough {{ Δ; Γ ⊢s σ ≈ σ : Γ' }}; mauto.
Qed.


(** For global contexts *)
(* NOTE:
 * For contexts (global and local), we cannot establish transitivity at this point since it requires showing that rewrite rules using context equality are admissible in typing/type well-formedness judgments 
* Instead, we show only reflexivity and symmetry now
*)
#[export]
Instance wf_gctx_eq_Symmetric {P : PtsSig} : Symmetric (@wf_gctx_eq P).
Proof.
  induction 1; mauto.
Qed.

#[export]
Instance wf_gctx_eq_per_elem {P : PtsSig} : PERElem _ (@wf_gctx P) (@wf_gctx_eq P).
Proof.
  induction 1; mauto;
    econstructor; mauto;
      apply wf_typ_eq_per_elem;
      eassumption.
Qed.

(** For local contexts *)
#[export]
Instance wf_ctx_eq_Symmetric {P : PtsSig} (Δ : gctx P) : Symmetric (wf_ctx_eq Δ).
Proof.
  induction 1; mauto.
Qed.

#[export]
Instance wf_ctx_eq_per_elem {P : PtsSig} (Δ : gctx P) : PERElem _ (wf_ctx Δ) (wf_ctx_eq Δ).
Proof.
  induction 1; mauto.
  econstructor; mauto;
      apply wf_typ_eq_per_elem;
      eassumption.
Qed.


(** * Subtyping relations are orders *)
(* NOTE:
 * Ultimately, we would like to know that the subtyping judgments are partial orders, but it does not seem that antisymmetry can be established through stricly syntactic methods
 * Instead, we settle for pre-orders
 *)
(** For types *)
#[export]
Instance wf_typ_subtyp_per_elem {P : PtsSig} (Δ : gctx P) (Γ : ctx P) : PERElem _ (wf_typ Δ Γ) (wf_typ_subtyp Δ Γ).
Proof.
  intros A HA.
  enough {{ Δ; Γ ⊢ A ≈ A }} by mauto.
  apply wf_typ_eq_per_elem; mauto.
Qed.

#[export]
Instance wf_typ_subtyp_Transitive {P : PtsSig} (Δ : gctx P) (Γ : ctx P) : Transitive (wf_typ_subtyp Δ Γ).
Proof.
  hnf; mauto.
Qed.  

(** For global contexts *)
(* NOTE:
 * For (local and global) contexts, we cannot establish transitivity at this point, for similar reason as in the equality case
 *)
#[export]
Instance wf_gctx_subtyp_per_elem {P : PtsSig} : PERElem _ (@wf_gctx P) (@wf_gctx_subtyp P).
Proof.
  induction 1; mauto;
    econstructor; mauto;
    apply wf_typ_subtyp_per_elem; mauto.
Qed.

(** For local contexts *)
#[export]
Instance wf_ctx_subtyp_per_elem {P : PtsSig} (Δ : gctx P) : PERElem _ (wf_ctx Δ) (wf_ctx_subtyp Δ).
Proof.
  induction 1; mauto;
    econstructor; mauto;
    apply wf_typ_subtyp_per_elem; mauto.
Qed.


(** ** Basic rewriting rules *)
(** For wf_exp_eq *)
Add Parametric Morphism {P : PtsSig} (Δ : gctx P) (Γ : ctx P) (A : typ P) : (wf_exp_eq Δ Γ A)
    with signature wf_exp_eq Δ Γ A ==> eq ==> iff as wf_exp_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Δ : gctx P) (Γ : ctx P) (A : typ P) : (wf_exp_eq Δ Γ A)
    with signature eq ==> wf_exp_eq Δ Γ A ==> iff as wf_exp_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.

(** For wf_typ_eq *)
Add Parametric Morphism {P : PtsSig} (Δ : gctx P) (Γ : ctx P) : (wf_typ_eq Δ Γ)
    with signature wf_typ_eq Δ Γ ==> eq ==> iff as wf_typ_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Δ : gctx P) (Γ : ctx P) : (wf_typ_eq Δ Γ)
    with signature eq ==> wf_typ_eq Δ Γ ==> iff as wf_typ_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P} (Δ : gctx P) (Γ : ctx P) (s : P) : (wf_typ_eq Δ Γ)
  with signature eq ==> wf_exp_eq Δ Γ {{{ Sort@s }}} ==> iff as wf_typ_eq_morphism_iff3.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P} (Δ : gctx P) (Γ : ctx P) (s : P) : (wf_typ_eq Δ Γ)
  with signature wf_exp_eq Δ Γ {{{ Sort@s }}} ==> eq ==> iff as wf_typ_eq_morphism_iff4.
Proof.
  split; mauto.
Qed.

(** For wf_sub_eq *)
Add Parametric Morphism {P : PtsSig} (Δ : gctx P) (Γ Γ' : ctx P) : (wf_sub_eq Δ Γ Γ')
    with signature wf_sub_eq Δ Γ Γ' ==> eq ==> iff as wf_sub_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Δ : gctx P) (Γ Γ' : ctx P) : (wf_sub_eq Δ Γ Γ')
    with signature eq ==> wf_sub_eq Δ Γ Γ' ==> iff as wf_sub_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.

(** Rewrite using specific constructors of equality judgments *)
#[export]
Hint Rewrite -> @wf_exp_eq_typ_sub using mauto 3 : mcpts.

#[export]
Hint Rewrite -> @wf_exp_eq_sub_id
                 @wf_exp_eq_pi_sub using mauto 4 : mcpts.

#[export]
Hint Rewrite -> @wf_exp_eq_typ_sub using mauto 3 : mcpts.

#[export]
Hint Rewrite -> @wf_sub_eq_id_compose_right
                 @wf_sub_eq_id_compose_left
                 @wf_sub_eq_compose_assoc (* prefer right association *)
                 @wf_sub_eq_p_extend using mauto 4 : mcpts.


(** * Immediately admissible rules *)
(** All equality judgments are reflexive on well-formed objects *)
Lemma exp_eq_refl {P : PtsSig} : forall {Δ : gctx P} {Γ M A},
    {{ Δ ; Γ ⊢ M : A }} ->
    {{ Δ ; Γ ⊢ M ≈ M : A }}.
Proof. mauto. Qed.

#[export]
Hint Resolve exp_eq_refl : mcpts.

Lemma wf_typ_eq_refl {P : PtsSig} : forall (Δ : gctx P) (Γ : ctx P) (A : typ P),
    {{ Δ ; Γ ⊢ A }} ->
    {{ Δ ; Γ ⊢ A ≈ A }}.
Proof.
  intros.
  apply wf_typ_eq_per_elem; eassumption.
Qed.

#[export]
Hint Resolve wf_typ_eq_refl : mcpts.

Lemma sub_eq_refl {P : PtsSig} : forall {Δ : gctx P} {σ Γ Γ'},
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ; Γ ⊢s σ ≈ σ : Γ' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve sub_eq_refl : mcpts.

Lemma gctx_eq_refl {P : PtsSig} : forall {Δ : gctx P},
    {{ ⊢ Δ }} ->
    {{ ⊢ Δ ≈ Δ }}.
Proof.
  induction 1; mauto 2.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve gctx_eq_refl : mcpts.

Lemma ctx_eq_refl {P : PtsSig} : forall {Δ : gctx P} {Γ},
    {{ Δ ⊢ Γ }} ->
    {{ Δ ⊢ Γ ≈ Γ }}.
Proof.
  induction 1; mauto 4.
Qed.

#[export]
Hint Resolve ctx_eq_refl : mcpts.

(** Equality of local and global contexts is symmetric (follows trivially from PER instances) *)
Lemma wf_gctx_eq_sym {P : PtsSig} : forall {Δ Δ' : gctx P}, {{ ⊢ Δ ≈ Δ' }} -> {{ ⊢ Δ' ≈ Δ }}.
Proof. intros; symmetry; eauto. Qed.

Lemma wf_ctx_eq_sym {P : PtsSig} : forall {Δ : gctx P} {Γ Γ'}, {{ Δ ⊢ Γ ≈ Γ' }} -> {{ Δ ⊢ Γ' ≈ Γ }}.
Proof. intros; symmetry; eauto. Qed.

#[export]
Hint Resolve wf_gctx_eq_sym wf_ctx_eq_sym : mcpts.
 
(** Admissible subtyping rules *)
Lemma wf_typ_subtyp_sort_st_subtyp {P : PtsSig} : forall (Δ : gctx P) (Γ : ctx P) (s1 s2 : P),
    {{ Δ ⊢ Γ }} ->
    st_subtyp s1 s2 ->
    {{ Δ ; Γ ⊢ Sort@s1 ⊆ Sort@s2 }}.
Proof.
  intros.
  induction H0.
  - enough {{ Δ; Γ ⊢ Sort@s ≈ Sort@s }} by mauto 3.
    enough {{ Δ; Γ ⊢ Sort@s }}; mauto 2.
  - transitivity {{{ Sort@s2 }}}; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_subtyp_sort_st_subtyp : mcpts.

Lemma wf_exp_eq_sort_subtyp {P : PtsSig} : forall {Δ : gctx P} {Γ A B s},
    {{ Δ ; Γ ⊢ A ≈ B : Sort@s }} ->
    {{ Δ ; Γ ⊢ B }} ->
    {{ Δ ; Γ ⊢ A ⊆ B }}.
Proof.
  intros.
  assert {{ Δ ; Γ ⊢ A ≈ B }} by mauto 2.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_sort_subtyp : mcpts.
