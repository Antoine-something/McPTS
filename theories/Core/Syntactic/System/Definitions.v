From Coq Require Import List Classes.RelationClasses Setoid Morphisms String.

From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

(** Context lookups *)
Reserved Notation "'#' x : A ∈ Γ" (in custom judg at level 80, x constr at level 0, A custom exp, Γ custom exp at level 50).
(** Judgments for global contexts *)
(** Judgments for local contexts *)
Reserved Notation "⊢ Γ" (in custom judg at level 80, Γ custom exp).
Reserved Notation "⊢ Γ ≈ Γ'" (in custom judg at level 80, Γ custom exp, Γ' custom exp).
Reserved Notation "⊢ Γ ⊆ Γ'" (in custom judg at level 80, Γ custom exp, Γ' custom exp).
(** Judgments for expressions *)
Reserved Notation "Γ ⊢ M : A" (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp).
Reserved Notation "Γ ⊢ M ≈ M' : A" (in custom judg at level 80, Γ custom exp, M custom exp, M' custom exp, A custom exp).
(** Judgments for types *)
Reserved Notation "Γ ⊢ A" (in custom judg at level 80, Γ custom exp, A custom exp).
Reserved Notation "Γ ⊢ A ≈ A'" (in custom judg at level 80, Γ custom exp, A custom exp, A' custom exp).
Reserved Notation "Γ ⊢ A ⊆ A'" (in custom judg at level 80, Γ custom exp, A custom exp, A' custom exp).
(** Judgments for substitutions *)
Reserved Notation "Γ ⊢s σ : Γ'" (in custom judg at level 80, Γ custom exp, σ custom exp, Γ' custom exp).
Reserved Notation "Γ ⊢s σ ≈ σ' : Γ'" (in custom judg at level 80, Γ custom exp, σ custom exp, σ' custom exp, Γ' custom exp).


Generalizable All Variables.

(** * Judgments definition *)
(** Lookup in local contexts *)
Inductive ctx_lookup {P : PtsSig} : nat -> typ P -> ctx P -> Prop :=
| here : `({{ #0 : A[Wk] ∈ Γ, A }})
| there : `({{ #n : A ∈ Γ }} -> {{ #(S n) : A[Wk] ∈ Γ, B }})
where "'#' x : A ∈ Γ" := (ctx_lookup x A Γ) (in custom judg) : type_scope.

#[export]
Hint Constructors ctx_lookup : mcpts.

(** Well-formedness for local contexts *)
Inductive wf_ctx {P : PtsSig} :  ctx P -> Prop :=
| wf_ctx_empty :
  {{ ⊢ ⋅ }}
| wf_ctx_extend :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ A }} ->
     {{ ⊢ Γ, A }} )
where "⊢ Γ" := (wf_ctx Γ) (in custom judg) : type_scope


(** subtyping for local contexts *)                        
with wf_ctx_subtyp {P : PtsSig} : ctx P -> ctx P -> Prop :=
| wf_ctx_subtyp_empty :
  {{ ⊢ ⋅ ⊆ ⋅ }}
| wf_ctx_subtyp_extend :
  `( {{ ⊢ Γ ⊆ Γ' }} ->
     {{ Γ ⊢ A }} ->
     {{ Γ' ⊢ A' }} ->
     {{ Γ ⊢ A ⊆ A' }} ->
     {{ ⊢ Γ, A ⊆ Γ', A' }} )
where "⊢ Γ ⊆ Γ'" := (wf_ctx_subtyp Γ Γ') (in custom judg) : type_scope

(** Well-formedness for expressions (i.e. typing) *)
with wf_exp {P : PtsSig} : ctx P -> typ P -> exp P -> Prop :=
(** Sorts *)
| wf_exp_st :
  `( Ax_typ P s1 s2 ->
     {{ ⊢ Γ }} ->
     {{ Γ ⊢ Sort@s1 : Sort@s2 }} )

(** Functions *)
| wf_exp_pi :
  `( forall (r : Ru_pi P s1 s2 s3),
      {{ Γ ⊢ A : Sort@s1 }} ->
      {{ Γ, A ⊢ B : Sort@s2 }} ->
      {{ Γ ⊢ Π r A B : Sort@s3 }} )
| wf_exp_fn :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ, A ⊢ B : Sort@s2 }} ->
        {{ Γ, A ⊢ M : B }} ->
        {{ Γ ⊢ λ r A B M : Π r A B }} )
| wf_exp_app :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ, A ⊢ B : Sort@s2 }} ->
        {{ Γ ⊢ M : Π r A B }} ->
        {{ Γ ⊢ N : A }} ->
        {{ Γ ⊢ M N : B[Id,,N] }} )

(** Variables *)
| wf_exp_vlookup :
  `( {{ ⊢ Γ }} ->
     (** This premise is redundant, but helpful for soundness *)
     (* {{ Γ ⊢ A }} -> *)
     {{ #x : A ∈ Γ }} ->
     {{ Γ ⊢ #x : A }} )
  
(** Naturals **)
| wf_exp_nat :
  `( forall (r : Ru_nat P s),
        {{ ⊢ Γ }} ->
        {{ Γ ⊢ ℕ: Sort@s }} )
| wf_exp_zero :
  `(forall (r : Ru_nat P s),
        {{ ⊢ Γ }} ->
        {{ Γ ⊢ zero : ℕ}} )
| wf_exp_succ :
  `( forall (r : Ru_nat P s),
        {{ Γ ⊢ M : ℕ}} ->
        {{ Γ ⊢ succ M : ℕ}} )
| wf_exp_natrec :
  `( forall (r : Ru_nat P s),
        {{ Γ, ℕ ⊢ A }} ->
        {{ Γ ⊢ MZ : A[Id,,zero] }} ->
        {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
        {{ Γ ⊢ M : ℕ}} ->
        {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }} )

| wf_exp_sub :
  `( {{ Γ ⊢s σ : Γ' }} ->
     {{ Γ' ⊢ M : A }} ->
     {{ Γ' ⊢ A }} ->
     {{ Γ ⊢ M[σ] : A[σ] }} )

| wf_exp_conv :
  `( {{ Γ ⊢ M : A }} ->
     (* We have these extra argument for soundness. *)
     {{ Γ ⊢ A }} ->
     {{ Γ ⊢ A' }} ->
     {{ Γ ⊢ A ⊆ A' }} ->
     {{ Γ ⊢ M : A' }} )
where "Γ ⊢ M : A" := (wf_exp Γ A M) (in custom judg) : type_scope

(** Equality for expressions *)
with wf_exp_eq {P : PtsSig} : ctx P -> typ P -> exp P -> exp P -> Prop :=
| wf_exp_eq_typ_sub :
  `( {{ Γ ⊢ Sort@s1 : Sort@s2 }} ->
     {{ Γ' ⊢ Sort@s1 : Sort@s2 }} ->
     {{ Γ ⊢s σ : Γ' }} ->
     {{ Γ ⊢ Sort@s1[σ] ≈ Sort@s1 : Sort@s2 }} )

| wf_exp_eq_pi_sub :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ ⊢s σ : Γ' }} ->
        {{ Γ' ⊢ A : Sort@s1 }} ->
        {{ Γ', A ⊢ B : Sort@s2 }} ->
        {{ Γ ⊢ (Π r A B)[σ] ≈ Π r A[σ] B[q σ] : Sort@s3 }} )
| wf_exp_eq_pi_cong :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
        {{ Γ, A ⊢ B ≈ B' : Sort@s2 }} ->
        {{ Γ ⊢ Π r A B ≈ Π r A' B' : Sort@s3 }} )
| wf_exp_eq_fn_cong :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
        {{ Γ, A ⊢ B : Sort@s2 }} ->
        {{ Γ, A ⊢ B ≈ B' : Sort@s2 }} ->
        {{ Γ, A ⊢ M ≈ M' : B }} ->
        {{ Γ ⊢ λ r A B M ≈ λ r A' B' M' : Π r A B }} )
| wf_exp_eq_fn_sub :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ ⊢s σ : Γ' }} ->
        {{ Γ' ⊢ A : Sort@s1 }} ->
        {{ Γ', A ⊢ B : Sort@s2 }} ->
        {{ Γ', A ⊢ M : B }} ->
        {{ Γ ⊢ (λ r A B M)[σ] ≈ λ r A[σ] B[q σ] M[q σ] : (Π r A B)[σ] }} )
| wf_exp_eq_app_cong :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ, A ⊢ B : Sort@s2 }} ->
        {{ Γ ⊢ M ≈ M' : Π r A B }} ->
        {{ Γ ⊢ N ≈ N' : A }} ->
        {{ Γ ⊢ M N ≈ M' N' : B[Id,,N] }} )
| wf_exp_eq_app_sub :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ ⊢s σ : Γ' }} ->
        {{ Γ' ⊢ A : Sort@s1 }} ->
        {{ Γ', A ⊢ B : Sort@s2 }} ->
        {{ Γ' ⊢ M : Π r A B }} ->
        {{ Γ' ⊢ N : A }} ->
        {{ Γ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }} )
| wf_exp_eq_pi_beta :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ, A ⊢ B : Sort@s2 }} ->
        {{ Γ, A ⊢ M : B }} ->
        {{ Γ ⊢ N : A }} ->
        {{ Γ ⊢ (λ r A B M) N ≈ M[Id,,N] : B[Id,,N] }} )
| wf_exp_eq_pi_eta :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ, A ⊢ B : Sort@s2 }} ->
        {{ Γ ⊢ M : Π r A B }} ->
        {{ Γ ⊢ M ≈ λ r A B (M[Wk] #0) : Π r A B }} )

(** Naturals **)
| wf_exp_eq_nat_sub :
  `( forall (r : Ru_nat P s),
        {{ Γ ⊢s σ : Γ' }} ->
        {{ Γ ⊢ (ℕ)[σ] ≈ ℕ : Sort@s }} )
| wf_exp_eq_zero_sub :
  `( forall (r : Ru_nat P s),
        {{ Γ ⊢s σ : Γ' }} ->
        {{ Γ ⊢ zero[σ] ≈ zero : ℕ}} )
| wf_exp_eq_succ_sub :
  `( forall (r : Ru_nat P s),
        {{ Γ ⊢s σ : Γ' }} ->
        {{ Γ' ⊢ M : ℕ}} ->
        {{ Γ ⊢ (succ M)[σ] ≈ succ (M[σ]) : ℕ}} )
| wf_exp_eq_succ_cong :
  `( forall (r : Ru_nat P s),
        {{ Γ ⊢ M ≈ M' : ℕ}} ->
        {{ Γ ⊢ succ M ≈ succ M' : ℕ}} )
| wf_exp_eq_natrec_cong :
  `( forall (r : Ru_nat P s),
        {{ Γ, ℕ ⊢ A }} ->
        {{ Γ, ℕ ⊢ A' }} ->
        {{ Γ, ℕ ⊢ A ≈ A' }} ->
        {{ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] }} ->
        {{ Γ, ℕ, A ⊢ MS ≈ MS' : A[Wk∘Wk,,succ #1] }} ->
        {{ Γ ⊢ M ≈ M' : ℕ}} ->
        {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }} )
| wf_exp_eq_natrec_sub :
  `( forall (r : Ru_nat P s),
        {{ Γ ⊢s σ : Γ' }} ->
        {{ Γ', ℕ ⊢ A }} ->
        {{ Γ' ⊢ MZ : A[Id,,zero] }} ->
        {{ Γ', ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
        {{ Γ' ⊢ M : ℕ}} ->
        {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }} )
| wf_exp_eq_nat_beta_zero :
  `( forall (r : Ru_nat P s),
        {{ Γ, ℕ ⊢ A }} ->
        {{ Γ ⊢ MZ : A[Id,,zero] }} ->
        {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
        {{ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }} )
| wf_exp_eq_nat_beta_succ :
  `( forall (r : Ru_nat P s),
        {{ Γ, ℕ ⊢ A }} ->
        {{ Γ ⊢ MZ : A[Id,,zero] }} ->
        {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
        {{ Γ ⊢ M : ℕ}} ->
        {{ Γ ⊢ rec succ M return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }} )

(** Local variables *)
| wf_exp_eq_var :
  `( {{ ⊢ Γ }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Γ ⊢ #x ≈ #x : A }} )
| wf_exp_eq_var_0_sub :
  `( {{ Γ ⊢s σ : Γ' }} ->
     {{ Γ' ⊢ A }} ->
     {{ Γ ⊢ M : A[σ] }} ->
     {{ Γ ⊢ #0[σ,,M] ≈ M : A[σ] }} )
| wf_exp_eq_var_S_sub :
  `( {{ Γ ⊢s σ : Γ' }} ->
     {{ Γ' ⊢ A }} ->
     {{ Γ ⊢ M : A[σ] }} ->
     {{ #x : B ∈ Γ' }} ->
     {{ Γ ⊢ #(S x)[σ,,M] ≈ #x[σ] : B[σ] }} )
| wf_exp_eq_var_weaken :
  `( {{ ⊢ Γ, B }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Γ, B ⊢ #x[Wk] ≈ #(S x) : A[Wk] }} )

(** Substitution propagation *)
| wf_exp_eq_sub_cong :
  `( {{ Γ' ⊢ A }} ->
     {{ Γ' ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ Γ ⊢ M[σ] ≈ M'[σ'] : A[σ] }} )
| wf_exp_eq_sub_id :
  `( {{ Γ ⊢ M : A }} ->
     {{ Γ ⊢ M[Id] ≈ M : A }} )
| wf_exp_eq_sub_compose :
  `( {{ Γ ⊢s τ : Γ' }} ->
     {{ Γ' ⊢s σ : Γ'' }} ->
     {{ Γ'' ⊢ M : A }} ->
     {{ Γ'' ⊢ A }} ->
     {{ Γ ⊢ M[σ∘τ] ≈ M[σ][τ] : A[σ∘τ] }} )
   
(** Rules not related to specific term constructors *) 
| wf_exp_eq_conv :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ A' }} ->
     {{ Γ ⊢ A ⊆ A' }} ->
     {{ Γ ⊢ M ≈ M' : A' }} )
| wf_exp_eq_sym :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ M' ≈ M : A }} )
| wf_exp_eq_trans :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ M' ≈ M'' : A }} ->
     {{ Γ ⊢ M ≈ M'' : A }} )
where "Γ ⊢ M ≈ M' : A" := (wf_exp_eq Γ A M M') (in custom judg) : type_scope

(** Well-formedness for types *)
with wf_typ {P : PtsSig} : ctx P -> typ P -> Prop :=
| wf_typ_st :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ Sort@s }})
| wf_typ_exp :
  `( {{ Γ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ A }})
| wf_typ_sub :
  `( {{ Γ ⊢s σ : Γ' }} ->
     {{ Γ' ⊢ A }} ->
     {{ Γ ⊢ A[σ] }} )
where "Γ ⊢ A" := (wf_typ Γ A) (in custom judg) : type_scope

(** Equality for types *)
with wf_typ_eq {P : PtsSig} : ctx P -> typ P -> typ P -> Prop :=
| wf_typ_eq_sorted :
  `( {{ Γ ⊢ A ≈ B : Sort@s }} ->
     {{ Γ ⊢ A ≈ B }} )
| wf_typ_eq_sub_sort :
  `( {{ Γ ⊢s σ : Γ' }} ->
     {{ Γ ⊢ Sort@s1[σ] ≈ Sort@s1 }} )
| wf_typ_eq_sub_cong :
  `( {{ Γ' ⊢ A ≈ A' }} ->
     {{ Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ Γ ⊢ A[σ] ≈ A'[σ'] }} )
| wf_typ_eq_sub_compose :
  `( {{ Γ ⊢s τ : Γ' }} ->
     {{ Γ' ⊢s σ : Γ'' }} ->
     {{ Γ'' ⊢ A  }} ->
     {{ Γ ⊢ A[σ∘τ] ≈ A[σ][τ] }} )   
| wf_typ_eq_sym :
  `( {{ Γ ⊢ A ≈ B }} ->
     {{ Γ ⊢ B ≈ A }} )
| wf_typ_eq_trans :
  `( {{ Γ ⊢ A ≈ B }} ->
     {{ Γ ⊢ B ≈ C }} ->
     {{ Γ ⊢ A ≈ C }} )
where "Γ ⊢ A ≈ A'" := (wf_typ_eq Γ A A') (in custom judg) : type_scope

(** Subtyping for types *)
with wf_typ_subtyp {P : PtsSig} : ctx P -> typ P -> typ P -> Prop :=
| wf_typ_subtyp_refl :
  `( {{ Γ ⊢ A ≈ B }} ->
     {{ Γ ⊢ B }} ->
     {{ Γ ⊢ A ⊆ B }} )
| wf_typ_subtyp_trans :
  `( {{ Γ ⊢ A ⊆ B }} ->
     {{ Γ ⊢ B ⊆ C }} ->
     {{ Γ ⊢ A ⊆ C }} )
| wf_typ_subtyp_sort_ax_sub :
  `( Ax_sub P s1 s2 ->
     {{ ⊢ Γ }} ->
     {{ Γ ⊢ Sort@s1 ⊆ Sort@s2 }} )   
| wf_typ_subtyp_pi :
  `( forall {r : Ru_pi P s1 s2 s3},
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ ⊢ A' : Sort@s1 }} ->
        {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
        {{ Γ, A ⊢ B : Sort@s2 }} ->
        {{ Γ, A' ⊢ B' : Sort@s2 }} ->
        {{ Γ, A' ⊢ B ⊆ B' }} ->
        {{ Γ ⊢ Π r A B ⊆ Π r A' B' }} )
where "Γ ⊢ A ⊆ A'" := (wf_typ_subtyp Γ A A') (in custom judg) : type_scope

(** Well-formedness for substitutions *)                                                              
with wf_sub {P : PtsSig} : ctx P -> ctx P -> sub P -> Prop :=
| wf_sub_id :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢s Id : Γ }} )
| wf_sub_weaken :
  `( {{ ⊢ Γ, A }} ->
     {{ Γ, A ⊢s Wk : Γ }} )
| wf_sub_compose :
  `( {{ Γ1 ⊢s σ2 : Γ2 }} ->
     {{ Γ2 ⊢s σ1 : Γ3 }} ->
     {{ Γ1 ⊢s σ1∘σ2 : Γ3 }} )
| wf_sub_extend :
  `( {{ Γ ⊢s σ : Γ' }} ->
     {{ Γ' ⊢ A }} ->
     {{ Γ ⊢ M : A[σ] }} ->
     {{ Γ ⊢s σ,,M : Γ', A }} )
| wf_sub_conv :
  `( {{ Γ ⊢s σ : Γ' }} ->
     (** As in [wf_exp_conv], we need this extra argument for soundness *)
     {{ ⊢ Γ'' }} ->
     {{ ⊢ Γ' ⊆ Γ'' }} ->
     {{ Γ ⊢s σ : Γ'' }} )
where "Γ ⊢s σ : Γ'" := (wf_sub Γ Γ' σ) (in custom judg) : type_scope

(** Equality of substitutions *)
with wf_sub_eq {P : PtsSig} : ctx P -> ctx P -> sub P -> sub P -> Prop :=
| wf_sub_eq_id :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢s Id ≈ Id : Γ }} )
| wf_sub_eq_weaken :
  `( {{ ⊢ Γ, A }} ->
     {{ Γ, A ⊢s Wk ≈ Wk : Γ }} )
| wf_sub_eq_compose_cong :
  `( {{ Γ ⊢s τ ≈ τ' : Γ' }} ->
     {{ Γ' ⊢s σ ≈ σ' : Γ'' }} ->
     {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Γ'' }} )
| wf_sub_eq_extend_cong :
  `( {{ Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ Γ' ⊢ A }} ->
     {{ Γ ⊢ M ≈ M' : A[σ] }} ->
     {{ Γ ⊢s σ,,M ≈ σ',,M' : Γ', A }} )
| wf_sub_eq_id_compose_right :
  `( {{ Γ ⊢s σ : Γ' }} ->
     {{ Γ ⊢s Id∘σ ≈ σ : Γ' }} )
| wf_sub_eq_id_compose_left :
  `( {{ Γ ⊢s σ : Γ' }} ->
     {{ Γ ⊢s σ∘Id ≈ σ : Γ' }} )
| wf_sub_eq_compose_assoc :
  `( {{ Γ' ⊢s σ : Γ }} ->
     {{ Γ'' ⊢s σ' : Γ' }} ->
     {{ Γ''' ⊢s σ'' : Γ'' }} ->
     {{ Γ''' ⊢s (σ∘σ')∘σ'' ≈ σ∘(σ'∘σ'') : Γ }} )
| wf_sub_eq_extend_compose :
  `( {{ Γ' ⊢s σ : Γ'' }} ->
     {{ Γ'' ⊢ A }} ->
     {{ Γ' ⊢ M : A[σ] }} ->
     {{ Γ ⊢s τ : Γ' }} ->
     {{ Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', A }} )
| wf_sub_eq_p_extend :
  `( {{ Γ' ⊢s σ : Γ }} ->
     {{ Γ ⊢ A }} ->
     {{ Γ' ⊢ M : A[σ] }} ->
     {{ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }} )
| wf_sub_eq_extend :
  `( {{ Γ' ⊢s σ : Γ, A }} ->
     {{ Γ' ⊢s σ ≈ (Wk∘σ),,#0[σ] : Γ, A }} )
| wf_sub_eq_sym :
  `( {{ Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ Γ ⊢s σ' ≈ σ : Γ' }} )
| wf_sub_eq_trans :
  `( {{ Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ Γ ⊢s σ' ≈ σ'' : Γ' }} ->
     {{ Γ ⊢s σ ≈ σ'' : Γ' }} )
| wf_sub_eq_conv :
  `( {{ Γ ⊢s σ ≈ σ' : Γ' }} ->
     {{ ⊢ Γ'' }} ->
     {{ ⊢ Γ' ⊆ Γ'' }} ->
     {{ Γ ⊢s σ ≈ σ' : Γ'' }} )
where "Γ ⊢s σ ≈ σ' : Γ'" := (wf_sub_eq Γ Γ' σ σ') (in custom judg) : type_scope.

#[export]
Hint Constructors wf_ctx wf_ctx_subtyp wf_exp wf_exp_eq wf_typ wf_typ_eq wf_typ_subtyp wf_sub wf_sub_eq : mcpts.

Scheme wf_ctx_mut_ind := Induction for wf_ctx Sort Prop
with wf_ctx_subtyp_mut_ind := Induction for wf_ctx_subtyp Sort Prop
with wf_exp_mut_ind := Induction for wf_exp Sort Prop
with wf_exp_eq_mut_ind := Induction for wf_exp_eq Sort Prop
with wf_typ_mut_ind := Induction for wf_typ Sort Prop
with wf_typ_eq_mut_ind := Induction for wf_typ_eq Sort Prop
with wf_typ_subtyp_mut_ind := Induction for wf_typ_subtyp Sort Prop     
with wf_sub_mut_ind := Induction for wf_sub Sort Prop
with wf_sub_eq_mut_ind := Induction for wf_sub_eq Sort Prop.
Combined Scheme syntactic_wf_mut_ind from
  wf_ctx_mut_ind,
  wf_ctx_subtyp_mut_ind,
  wf_exp_mut_ind,
  wf_exp_eq_mut_ind,
  wf_typ_mut_ind,
  wf_typ_eq_mut_ind,
  wf_typ_subtyp_mut_ind,
  wf_sub_mut_ind,
  wf_sub_eq_mut_ind.  

(* Scheme wf_ctx_local_mut_ind := Induction for wf_ctx Sort Prop *)
(* with wf_ctx_subtyp_local_mut_ind := Induction for wf_ctx_subtyp Sort Prop *)
(* with wf_exp_local_mut_ind := Induction for wf_exp Sort Prop *)
(* with wf_exp_eq_local_mut_ind := Induction for wf_exp_eq Sort Prop *)
(* with wf_typ_local_mut_ind := Induction for wf_typ Sort Prop *)
(* with wf_typ_eq_local_mut_ind := Induction for wf_typ_eq Sort Prop *)
(* with wf_typ_subtyp_local_mut_ind := Induction for wf_typ_subtyp Sort Prop      *)
(* with wf_sub_local_mut_ind := Induction for wf_sub Sort Prop *)
(* with wf_sub_eq_local_mut_ind := Induction for wf_sub_eq Sort Prop. *)
(* Combined Scheme syntactic_wf_local_mut_ind from *)
(*   wf_ctx_local_mut_ind, *)
(*   wf_ctx_subtyp_local_mut_ind, *)
(*   wf_exp_local_mut_ind, *)
(*   wf_exp_eq_local_mut_ind, *)
(*   wf_typ_local_mut_ind, *)
(*   wf_typ_eq_local_mut_ind, *)
(*   wf_typ_subtyp_local_mut_ind, *)
(*   wf_sub_local_mut_ind, *)
(*   wf_sub_eq_local_mut_ind.   *)

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

Scheme wf_ctx_mut_ind' := Induction for wf_ctx Sort Prop
with wf_exp_mut_ind' := Induction for wf_exp Sort Prop
with wf_typ_mut_ind' := Induction for wf_typ Sort Prop
with wf_sub_mut_ind' := Induction for wf_sub Sort Prop.
Combined Scheme syntactic_wf_mut_ind' from
  wf_ctx_mut_ind',
  wf_exp_mut_ind',
  wf_typ_mut_ind',
  wf_sub_mut_ind'.


(** Equality for local contexts *)
Inductive wf_ctx_eq {P : PtsSig} : ctx P -> ctx P -> Prop :=
| wf_ctx_eq_empty :
  {{ ⊢ ⋅ ≈ ⋅ }}
| wf_ctx_eq_extend :
  `( {{ ⊢ Γ ≈ Γ' }} ->
     {{ Γ ⊢ A }} ->
     {{ Γ ⊢ A' }} ->
     {{ Γ' ⊢ A }} ->
     {{ Γ' ⊢ A' }} ->
     {{ Γ ⊢ A ≈ A' }} ->
     {{ Γ' ⊢ A ≈ A' }} ->
     {{ ⊢ Γ, A ≈ Γ', A' }} )
where "⊢ Γ ≈ Γ'" := (wf_ctx_eq Γ Γ') (in custom judg) : type_scope.

#[export]
Hint Constructors wf_ctx_eq : mcpts.
