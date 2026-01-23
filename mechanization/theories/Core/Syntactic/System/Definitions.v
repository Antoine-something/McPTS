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
Reserved Notation "'#' x : A ∈ Γ" (in custom judg at level 80, x constr at level 0, A custom exp, Γ custom exp at level 50).

Generalizable All Variables.

Inductive ctx_lookup {P : PtsSig} : nat -> typ P -> ctx P -> Prop :=
  | here : `({{ #0 : A[Wk] ∈ Γ, A }})
  | there : `({{ #n : A ∈ Γ }} -> {{ #(S n) : A[Wk] ∈ Γ, B }})
where "'#' x : A ∈ Γ" := (ctx_lookup x A Γ) (in custom judg) : type_scope.

Inductive wf_ctx {P : PtsSig} : ctx P -> Prop :=
| wf_ctx_empty : {{ ⊢ ⋅ }}
| wf_ctx_extend :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ A : Sort@s }} ->
     {{ ⊢ Γ, A }} )
where "⊢ Γ" := (wf_ctx Γ) (in custom judg) : type_scope

with wf_exp {P : PtsSig} : ctx P -> typ P -> exp P -> Prop :=
(** Sorts *)
| wf_st :
  `( Ax P s1 s2 -> {{ ⊢ Γ }} ->
     {{ Γ ⊢ Sort@s1 : Sort@s2 }} )

(** Functions *)
| wf_pi :
  `( Ru P s1 s2 s3 ->
     {{ Γ ⊢ A : Sort@s1 }} ->
     {{ Γ, A ⊢ B : Sort@s2 }} ->
     {{ Γ ⊢ Π A B : Sort@s3 }} )
| wf_fn :
  `( Ru P s1 s2 s3 ->
     {{ Γ ⊢ A : Sort@s1 }} ->
     {{ Γ, A ⊢ B : Sort@s2 }} ->
     {{ Γ, A ⊢ M : B }} ->
     {{ Γ ⊢ λ A M : Π A B }} )
| wf_app :
  `( Ru P s1 s2 s3 ->
     {{ Γ ⊢ A : Sort@s1 }} ->
     {{ Γ, A ⊢ B : Sort@s2 }} ->
     {{ Γ ⊢ M : Π A B }} ->
     {{ Γ ⊢ N : A }} ->
     {{ Γ ⊢ M N : B[Id,,N] }} )

| wf_vlookup :
  `( {{ ⊢ Γ }} ->
     (** This premise is redundant, but helpful for soundness *)
     {{ Γ ⊢ A : Sort@s }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Γ ⊢ #x : A }} )

(** Naturals **)
(* | wf_nat : *)
(*   `( forall (r : Ru_nat P s), *)
(*         {{ ⊢ Γ }} -> *)
(*         {{ Γ ⊢ ℕ: Sort@s }} ) *)
(* | wf_zero : *)
(*   `(forall (r : Ru_nat P s), *)
(*       {{ ⊢ Γ }} -> *)
(*       {{ Γ ⊢ zero : ℕ}} ) *)
(* | wf_succ : *)
(*   `( forall (r : Ru_nat P s), *)
(*         {{ Γ ⊢ M : ℕ}} -> *)
(*         {{ Γ ⊢ succ M : ℕ}} ) *)
(* | wf_natrec : *)
(*   `( forall (r : Ru_nat P s), *)
(*         {{ Γ, ℕ ⊢ A : Sort@s' }} -> *)
(*         {{ Γ ⊢ MZ : A[Id,,zero] }} -> *)
(*         {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} -> *)
(*         {{ Γ ⊢ M : ℕ}} -> *)
(*         {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }} ) *)


| wf_exp_sub :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ M : A }} ->
     {{ Γ ⊢ M[σ] : A[σ] }} )
| wf_exp_conv :
  `( {{ Γ ⊢ M : A }} ->
     (** We have this extra argument for soundness.
         Note that we need to keep it asymmetric:
         only [A'] is checked. If we check A as well,
         we cannot even construct something like
         [{{ Γ ⊢ Type@0[Wk] : Type@1 }}] with the current
         rules. Under the symmetric rule, the example requires
         [{{ Γ ⊢ Type@1[Wk] : Type@2 }}] to apply [wf_exp_sub],
         which requires [{{ Γ ⊢ Type@2[Wk] : Type@3 }}], and so on.
      *)
     {{ Γ ⊢ A' }} ->
     {{ Γ ⊢ A ≈ A' }} ->
     {{ Γ ⊢ M : A' }} )
where "Γ ⊢ M : A" := (wf_exp Γ A M) (in custom judg) : type_scope

with wf_typ {P : PtsSig} : ctx P -> typ P -> Prop :=
| wf_typ_st :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ Sort@s }})
| wf_typ_exp :
  `( {{ Γ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ A }})
| wf_typ_clo :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A }} ->
     {{ Γ ⊢ A[σ] }})
where "Γ ⊢ A" := (wf_typ Γ A) (in custom judg) : type_scope
                                                         
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
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ M : A[σ] }} ->
     {{ Γ ⊢s σ,,M : Δ, A }} )
| wf_sub_conv :
  `( {{ Γ ⊢s σ : Δ }} ->
     (** As in [wf_exp_subtyp], this extra argument is
         for soundness. We don't need to keep it asymmetric,
         but do so to match with [wf_exp_subtyp].
      *)
     {{ ⊢ Δ' }} ->
     {{ ⊢ Δ ≈ Δ' }} ->
     {{ Γ ⊢s σ : Δ' }} )
where "Γ ⊢s σ : Δ" := (wf_sub Γ Δ σ) (in custom judg) : type_scope

with wf_ctx_eq {P : PtsSig} : ctx P -> ctx P -> Prop :=
| wf_ctx_eq_empty : {{ ⊢ ⋅ ≈ ⋅ }}
| wf_ctx_eq_extend :
  `( {{ ⊢ Γ ≈ Δ }} ->
     {{ Γ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ A' : Sort@s' }} ->
     {{ Δ ⊢ A : Sort@s }} ->
     {{ Δ ⊢ A' : Sort@s' }} ->
     {{ Γ ⊢ A ≈ A' }} ->
     {{ Δ ⊢ A ≈ A' }} ->
     {{ ⊢ Γ, A ≈ Δ, A' }} )
where "⊢ Γ ≈ Γ'" := (wf_ctx_eq Γ Γ') (in custom judg) : type_scope
                                                          
with wf_exp_eq {P : PtsSig} : ctx P -> typ P -> exp P -> exp P -> Prop :=
| wf_exp_eq_typ_sub :
  `( Ax P s1 s2 ->
     {{ Γ ⊢s σ : Δ }} ->
     {{ Γ ⊢ Sort@s1[σ] ≈ Sort@s1 : Sort@s2 }} )

| wf_exp_eq_pi_sub :
  `( Ru P s1 s2 s3 ->
     {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A : Sort@s1 }} ->
     {{ Δ, A ⊢ B : Sort@s2 }} ->
     {{ Γ ⊢ (Π A B)[σ] ≈ Π A[σ] B[q σ] : Sort@s3 }} )
| wf_exp_eq_pi_cong :
  `( Ru P s1 s2 s3 ->
     {{ Γ ⊢ A : Sort@s1 }} ->
     {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
     {{ Γ, A ⊢ B ≈ B' : Sort@s2 }} ->
     {{ Γ ⊢ Π A B ≈ Π A' B' : Sort@s3 }} )
| wf_exp_eq_fn_cong :
  `( Ru P s1 s2 s3 ->
     {{ Γ ⊢ A : Sort@s1 }} ->
     {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
     {{ Γ, A ⊢ B : Sort@s2 }} -> 
     {{ Γ, A ⊢ M ≈ M' : B }} ->
     {{ Γ ⊢ λ A M ≈ λ A' M' : Π A B }} )
| wf_exp_eq_fn_sub :
  `( Ru P s1 s2 s3 ->
     {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A : Sort@s1 }} ->
     {{ Δ, A ⊢ B : Sort@s2 }} ->
     {{ Δ, A ⊢ M : B }} ->
     {{ Γ ⊢ (λ A M)[σ] ≈ λ A[σ] M[q σ] : (Π A B)[σ] }} )
| wf_exp_eq_app_cong :
  `( Ru P s1 s2 s3 ->
     {{ Γ ⊢ A : Sort@s1 }} ->
     {{ Γ, A ⊢ B : Sort@s2 }} ->
     {{ Γ ⊢ M ≈ M' : Π A B }} ->
     {{ Γ ⊢ N ≈ N' : A }} ->
     {{ Γ ⊢ M N ≈ M' N' : B[Id,,N] }} )
| wf_exp_eq_app_sub :
  `( Ru P s1 s2 s3 ->
     {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A : Sort@s1 }} ->
     {{ Δ, A ⊢ B : Sort@s2 }} ->
     {{ Δ ⊢ M : Π A B }} ->
     {{ Δ ⊢ N : A }} ->
     {{ Γ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }} )
| wf_exp_eq_pi_beta :
  `( Ru P s1 s2 s3 ->
     {{ Γ ⊢ A : Sort@s1 }} ->
     {{ Γ, A ⊢ B : Sort@s2 }} ->
     {{ Γ, A ⊢ M : B }} ->
     {{ Γ ⊢ N : A }} ->
     {{ Γ ⊢ (λ A M) N ≈ M[Id,,N] : B[Id,,N] }} )
| wf_exp_eq_pi_eta :
  `( Ru P s1 s2 s3 ->
     {{ Γ ⊢ A : Sort@s1 }} ->
     {{ Γ, A ⊢ B : Sort@s2 }} ->
     {{ Γ ⊢ M : Π A B }} ->
     {{ Γ ⊢ M ≈ λ A (M[Wk] #0) : Π A B }} )
(** Naturals **)
(* | wf_exp_eq_nat_sub : *)
(*   `( forall (r : Ru_nat P s), *)
(*         {{ Γ ⊢s σ : Δ }} -> *)
(*         {{ Γ ⊢ (ℕ)[σ] ≈ ℕ : Sort@s }} ) *)
(* | wf_exp_eq_zero_sub : *)
(*   `( forall (r : Ru_nat P s), *)
(*         {{ Γ ⊢s σ : Δ }} -> *)
(*         {{ Γ ⊢ zero[σ] ≈ zero : ℕ}} ) *)
(* | wf_exp_eq_succ_sub : *)
(*   `( forall (r : Ru_nat P s), *)
(*         {{ Γ ⊢s σ : Δ }} -> *)
(*         {{ Δ ⊢ M : ℕ}} -> *)
(*         {{ Γ ⊢ (succ M)[σ] ≈ succ (M[σ]) : ℕ}} ) *)
(* | wf_exp_eq_succ_cong : *)
(*   `( forall (r : Ru_nat P s), *)
(*         {{ Γ ⊢ M ≈ M' : ℕ}} -> *)
(*         {{ Γ ⊢ succ M ≈ succ M' : ℕ}} ) *)
(* | wf_exp_eq_natrec_cong : *)
(*   `( forall (r : Ru_nat P s), *)
(*         {{ Γ, ℕ ⊢ A : Sort@s' }} -> *)
(*         {{ Γ, ℕ ⊢ A' : Sort@s' }} ->  *)
(*         {{ Γ, ℕ ⊢ A ≈ A' }} -> *)
(*         {{ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] }} -> *)
(*         {{ Γ, ℕ, A ⊢ MS ≈ MS' : A[Wk∘Wk,,succ #1] }} -> *)
(*         {{ Γ ⊢ M ≈ M' : ℕ}} -> *)
(*         {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }} ) *)
(* | wf_exp_eq_natrec_sub : *)
(*   `( forall (r : Ru_nat P s), *)
(*        {{ Γ ⊢s σ : Δ }} -> *)
(*        {{ Δ, ℕ ⊢ A : Sort@s' }} -> *)
(*        {{ Δ ⊢ MZ : A[Id,,zero] }} -> *)
(*        {{ Δ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} -> *)
(*        {{ Δ ⊢ M : ℕ}} -> *)
(*        {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }} ) *)
(* | wf_exp_eq_nat_beta_zero : *)
(*   `( forall (r : Ru_nat P s), *)
(*         {{ Γ, ℕ ⊢ A : Sort@s' }} -> *)
(*         {{ Γ ⊢ MZ : A[Id,,zero] }} -> *)
(*         {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} -> *)
(*         {{ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }} ) *)
(* | wf_exp_eq_nat_beta_succ : *)
(*   `( forall (r : Ru_nat P s), *)
(*         {{ Γ, ℕ ⊢ A : Sort@s' }} -> *)
(*         {{ Γ ⊢ MZ : A[Id,,zero] }} -> *)
(*         {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} -> *)
(*         {{ Γ ⊢ M : ℕ}} -> *)
(*         {{ Γ ⊢ rec succ M return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }} ) *)

| wf_exp_eq_var :
  `( {{ ⊢ Γ }} ->
     {{ #x : A ∈ Γ }} ->
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
     {{ #x : B ∈ Δ }} ->
     {{ Γ ⊢ #(S x)[σ,,M] ≈ #x[σ] : B[σ] }} )
| wf_exp_eq_var_weaken :
  `( {{ ⊢ Γ, B }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Γ, B ⊢ #x[Wk] ≈ #(S x) : A[Wk] }} )
| wf_exp_eq_sub_cong :
  `( {{ Δ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Γ ⊢ M[σ] ≈ M'[σ'] : A[σ] }} )
| wf_exp_eq_sub_id :
  `( {{ Γ ⊢ M : A }} ->
     {{ Γ ⊢ M[Id] ≈ M : A }} )
| wf_exp_eq_sub_compose :
  `( {{ Γ ⊢s τ : Γ' }} ->
     {{ Γ' ⊢s σ : Γ'' }} ->
     {{ Γ'' ⊢ M : A }} ->
     {{ Γ ⊢ M[σ∘τ] ≈ M[σ][τ] : A[σ∘τ] }} )
| wf_exp_eq_conv :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ A' }} ->
     (** This extra argument is here to be consistent with
         [wf_exp_conv].
      *)
     {{ Γ ⊢ A ≈ A' }} ->
     {{ Γ ⊢ M ≈ M' : A' }} )
| wf_exp_eq_sym :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ M' ≈ M : A }} )
| wf_exp_eq_trans :
  `( {{ Γ ⊢ M ≈ M' : A }} ->
     {{ Γ ⊢ M' ≈ M'' : A }} ->
     {{ Γ ⊢ M ≈ M'' : A }} )
where "Γ ⊢ M ≈ M' : A" := (wf_exp_eq Γ A M M') (in custom judg) : type_scope

with wf_typ_eq {P : PtsSig} : ctx P -> typ P -> typ P -> Prop :=
| wf_typ_eq_st :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ Sort@s ≈ Sort@s }})
| wf_typ_eq_sub_st :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Γ ⊢ Sort@s[σ] ≈ Sort@s}})
| wf_typ_eq_exp :
  `( {{ Γ ⊢ A ≈ A' : Sort@s }} ->
     {{ Γ ⊢ A ≈ A' }})
| wf_typ_eq_sub_cong :
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Δ ⊢ A ≈ A' }} ->
     {{ Γ ⊢ A[σ] ≈ A'[σ'] }})
| wf_typ_eq_sub_compose :
  `( {{ Γ ⊢s τ : Γ' }} ->
     {{ Γ' ⊢s σ : Γ'' }} ->
     {{ Γ'' ⊢ A }} ->
     {{ Γ ⊢ A[σ∘τ] ≈ A[σ][τ] }} )
| wf_typ_eq_sub_id :
  `( {{ Γ ⊢ A }} ->
     {{ Γ ⊢ A[Id] ≈ A }} )
| wf_typ_eq_refl : `({{ Γ ⊢ A }} ->
                  {{ Γ ⊢ A ≈ A }})
| wf_typ_eq_sym : `({{ Γ ⊢ A ≈ B }} ->
                 {{ Γ ⊢ B ≈ A }})
| wf_typ_eq_trans : `({{ Γ ⊢ A1 ≈ A2 }} -> {{ Γ ⊢ A2 ≈ A3 }} ->
                   {{ Γ ⊢ A1 ≈ A3 }})
where "Γ ⊢ A ≈ A'" := (wf_typ_eq Γ A A') (in custom judg) : type_scope
                                                                    
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
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Δ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ M ≈ M' : A[σ] }} ->
     {{ Γ ⊢s σ,,M ≈ σ',,M' : Δ, A }} )
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
     {{ Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', A }} )
| wf_sub_eq_p_extend :
  `( {{ Γ' ⊢s σ : Γ }} ->
     {{ Γ ⊢ A : Sort@s }} ->
     {{ Γ' ⊢ M : A[σ] }} ->
     {{ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }} )
| wf_sub_eq_extend :
  `( {{ Γ' ⊢s σ : Γ, A }} ->
     {{ Γ' ⊢s σ ≈ (Wk∘σ),,#0[σ] : Γ, A }} )
| wf_sub_eq_sym :
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Γ ⊢s σ' ≈ σ : Δ }} )
| wf_sub_eq_trans :
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Γ ⊢s σ' ≈ σ'' : Δ }} ->
     {{ Γ ⊢s σ ≈ σ'' : Δ }} )
| wf_sub_eq_conv :
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     (** This extra argument is here to be consistent with
         [wf_sub_subtyp].
      *)
     {{ ⊢ Δ' }} ->
     {{ ⊢ Δ ≈ Δ' }} ->
     {{ Γ ⊢s σ ≈ σ' : Δ' }} )
where "Γ ⊢s σ ≈ σ' : Δ" := (wf_sub_eq Γ Δ σ σ') (in custom judg) : type_scope.

Scheme wf_ctx_mut_ind := Induction for wf_ctx Sort Prop
with wf_ctx_eq_mut_ind := Induction for wf_ctx_eq Sort Prop
with wf_exp_mut_ind := Induction for wf_exp Sort Prop
with wf_exp_eq_mut_ind := Induction for wf_exp_eq Sort Prop
with wf_typ_mut_ind := Induction for wf_typ Sort Prop
with wf_typ_eq_mut_ind := Induction for wf_typ_eq Sort Prop
with wf_sub_mut_ind := Induction for wf_sub Sort Prop
with wf_sub_eq_mut_ind := Induction for wf_sub_eq Sort Prop.
Combined Scheme syntactic_wf_mut_ind from
  wf_ctx_mut_ind,
  wf_ctx_eq_mut_ind,
  wf_exp_mut_ind,
  wf_exp_eq_mut_ind,
  wf_typ_mut_ind,
  wf_typ_eq_mut_ind,
  wf_sub_mut_ind,
  wf_sub_eq_mut_ind.

Scheme wf_ctx_mut_ind' := Induction for wf_ctx Sort Prop
with wf_exp_mut_ind' := Induction for wf_exp Sort Prop
(* with wf_typ_mut_ind' := Induction for wf_typ Sort Prop *)
with wf_sub_mut_ind' := Induction for wf_sub Sort Prop.
Combined Scheme syntactic_wf_mut_ind' from
  wf_ctx_mut_ind',
  wf_exp_mut_ind',
  (* wf_typ_mut_ind', *)
  wf_sub_mut_ind'.


#[export]
Hint Constructors wf_ctx wf_ctx_eq wf_exp wf_typ wf_sub wf_exp_eq wf_typ_eq wf_sub_eq ctx_lookup : mcpts.

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

(** Immediate & Independent Presuppositions *)

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
