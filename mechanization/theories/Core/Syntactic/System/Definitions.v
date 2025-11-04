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
Reserved Notation "'#' x : A :: K ∈ Γ" (in custom judg at level 80, x constr at level 0, A custom exp, K custom exp, Γ custom exp at level 50).

Generalizable All Variables.

Inductive ctx_lookup {P : PtsSig} : nat -> typ P -> knd P -> ctx P -> Prop :=
  | here : `({{ #0 : A[Wk] :: K ∈ Γ, A :: K }})
  | there : `({{ #n : A :: K ∈ Γ }} -> {{ #(S n) : A[Wk] :: K ∈ Γ, B :: L }})
where "'#' x : A :: K ∈ Γ" := (ctx_lookup x A K Γ) (in custom judg) : type_scope.

Inductive wf_ctx {P : PtsSig} : ctx P -> Prop :=
| wf_ctx_empty : {{ ⊢ ⋅ }}
| wf_ctx_extend :
  `( {{ ⊢ Γ }} ->
     {{ Γ ⊢ A : Sort@s }} ->
     {{ ⊢ Γ, A::Sort@s }} )
where "⊢ Γ" := (wf_ctx Γ) (in custom judg) : type_scope

with wf_exp {P : PtsSig} : ctx P -> typ P -> exp P -> Prop :=
(** Sorts *)
| wf_st :
  `( Ax P s1 s2 -> {{ ⊢ Γ }} ->
     {{ Γ ⊢ Sort@s1 : Sort@s2 }} )

(** Functions *)
| wf_pi :
  `( forall (r : Ru P s1 s2 s3),
      {{ Γ ⊢ A : Sort@s1 }} ->
      {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
      {{ Γ ⊢ Π r A B : Sort@s3 }} )
| wf_fn :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
        {{ Γ, A :: Sort@s1 ⊢ M : B }} ->
        {{ Γ ⊢ λ r A M : Π r A B }} )
| wf_app :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
        {{ Γ ⊢ M : Π r A B }} ->
        {{ Γ ⊢ N : A }} ->
        {{ Γ ⊢ M N : B[Id,,N] }} )

| wf_vlookup :
  `( {{ ⊢ Γ }} ->
     {{ #x : A :: Sort@s ∈ Γ }} ->
     {{ Γ ⊢ #x : A }} )

(** Naturals **)
| wf_nat :
  `( forall (r : Ru_nat P s),
        {{ ⊢ Γ }} ->
        {{ Γ ⊢ ℕ r: Sort@s }} )
   
| wf_zero :
  `(forall (r : Ru_nat P s),
      {{ ⊢ Γ }} ->
      {{ Γ ⊢ zero : ℕ r}} )
| wf_succ :
  `( forall (r : Ru_nat P s),
        {{ Γ ⊢ M : ℕ r}} ->
        {{ Γ ⊢ succ M : ℕ r}} )
(* | wf_natrec : *)
(*   `( {{ Γ, ℕ ⊢ A : Type@i }} -> *)
(*      {{ Γ ⊢ MZ : A[Id,,zero] }} -> *)
(*      {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} -> *)
(*      {{ Γ ⊢ M : ℕ }} -> *)
(*      {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }} ) *)


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
  `( {{ ⊢ Γ, A::Sort@s }} ->
     {{ Γ, A::Sort@s ⊢s Wk : Γ }} )
| wf_sub_compose :
  `( {{ Γ1 ⊢s σ2 : Γ2 }} ->
     {{ Γ2 ⊢s σ1 : Γ3 }} ->
     {{ Γ1 ⊢s σ1∘σ2 : Γ3 }} )
| wf_sub_extend :
  `( {{ Γ ⊢s σ : Δ }} ->
     {{ Δ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ M : A[σ] }} ->
     {{ Γ ⊢s σ,,M : Δ, A::Sort@s }} )
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
     {{ Γ ⊢ A' : Sort@s }} ->
     {{ Δ ⊢ A : Sort@s }} ->
     {{ Δ ⊢ A' : Sort@s }} ->
     {{ Γ ⊢ A ≈ A' : Sort@s }} ->
     {{ Δ ⊢ A ≈ A' : Sort@s }} ->
     {{ ⊢ Γ, A::Sort@s ≈ Δ, A'::Sort@s }} )
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
        {{ Δ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
        {{ Γ ⊢ (Π r A B)[σ] ≈ Π r A[σ] B[q σ] : Sort@s3 }} )
| wf_exp_eq_pi_cong :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
        {{ Γ, A::Sort@s1 ⊢ B ≈ B' : Sort@s2 }} ->
        {{ Γ ⊢ Π r A B ≈ Π r A' B' : Sort@s3 }} )
| wf_exp_eq_fn_cong :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
        {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} -> 
        {{ Γ, A::Sort@s1 ⊢ M ≈ M' : B }} ->
        {{ Γ ⊢ λ r A M ≈ λ r A' M' : Π r A B }} )
| wf_exp_eq_fn_sub :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢s σ : Δ }} ->
        {{ Δ ⊢ A : Sort@s1 }} ->
        {{ Δ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
        {{ Δ, A::Sort@s1 ⊢ M : B }} ->
        {{ Γ ⊢ (λ r A M)[σ] ≈ λ r A[σ] M[q σ] : (Π r A B)[σ] }} )
| wf_exp_eq_app_cong :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
        {{ Γ ⊢ M ≈ M' : Π r A B }} ->
        {{ Γ ⊢ N ≈ N' : A }} ->
        {{ Γ ⊢ M N ≈ M' N' : B[Id,,N] }} )
| wf_exp_eq_app_sub :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢s σ : Δ }} ->
        {{ Δ ⊢ A : Sort@s1 }} ->
        {{ Δ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
        {{ Δ ⊢ M : Π r A B }} ->
        {{ Δ ⊢ N : A }} ->
        {{ Γ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }} )
| wf_exp_eq_pi_beta :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
        {{ Γ, A::Sort@s1 ⊢ M : B }} ->
        {{ Γ ⊢ N : A }} ->
        {{ Γ ⊢ (λ r A M) N ≈ M[Id,,N] : B[Id,,N] }} )
| wf_exp_eq_pi_eta :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊢ A : Sort@s1 }} ->
        {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
        {{ Γ ⊢ M : Π r A B }} ->
        {{ Γ ⊢ M ≈ λ r A (M[Wk] #0) : Π r A B }} )

| wf_exp_eq_var :
  `( {{ ⊢ Γ }} ->
     {{ #x : A :: Sort@s ∈ Γ }} ->
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
     {{ #x : B :: Sort@s' ∈ Δ }} ->
     {{ Γ ⊢ #(S x)[σ,,M] ≈ #x[σ] : B[σ] }} )
| wf_exp_eq_var_weaken :
  `( {{ ⊢ Γ, B::Sort@s }} ->
     {{ #x : A::Sort@s' ∈ Γ }} ->
     {{ Γ, B::Sort@s ⊢ #x[Wk] ≈ #(S x) : A[Wk] }} )
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
         [wf_exp_subtyp].
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
  `( {{ ⊢ Γ, A::Sort@s }} ->
     {{ Γ, A::Sort@s ⊢s Wk ≈ Wk : Γ }} )
| wf_sub_eq_compose_cong :
  `( {{ Γ ⊢s τ ≈ τ' : Γ' }} ->
     {{ Γ' ⊢s σ ≈ σ' : Γ'' }} ->
     {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Γ'' }} )
| wf_sub_eq_extend_cong :
  `( {{ Γ ⊢s σ ≈ σ' : Δ }} ->
     {{ Δ ⊢ A : Sort@s }} ->
     {{ Γ ⊢ M ≈ M' : A[σ] }} ->
     {{ Γ ⊢s σ,,M ≈ σ',,M' : Δ, A::Sort@s }} )
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
     {{ Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', A::Sort@s }} )
| wf_sub_eq_p_extend :
  `( {{ Γ' ⊢s σ : Γ }} ->
     {{ Γ ⊢ A : Sort@s }} ->
     {{ Γ' ⊢ M : A[σ] }} ->
     {{ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }} )
| wf_sub_eq_extend :
  `( {{ Γ' ⊢s σ : Γ, A::Sort@s }} ->
     {{ Γ' ⊢s σ ≈ (Wk∘σ),,#0[σ] : Γ, A::Sort@s }} )
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
with wf_typ_eq_mut_ind' := Induction for wf_typ_eq Sort Prop.
Combined Scheme syntactic_wf_mut_ind' from
  wf_ctx_mut_ind',
  wf_exp_mut_ind',
  wf_typ_eq_mut_ind'.


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
Instance wf_typ_eq_PER {P : PtsSig} (Γ : ctx P) : PER (wf_typ_eq Γ).
Proof.
  split.
  - eauto using wf_typ_eq_sym.
  - eauto using wf_typ_eq_trans.
Qed.

#[export]
Instance wf_sub_eq_PER {P : PtsSig} (Γ : ctx P) Δ : PER (wf_sub_eq Γ Δ).
Proof.
  split.
  - eauto using wf_sub_eq_sym.
  - eauto using wf_sub_eq_trans.
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
Instance wf_exp_eq_per_elem {P : PtsSig} (Γ : ctx P) T : PERElem _ (wf_exp Γ T) (wf_exp_eq Γ T).
Proof.
  intros a Ha. mauto.
Qed.


#[export]
Instance wf_sub_eq_per_elem {P : PtsSig} (Γ : ctx P) Δ : PERElem _ (wf_sub Γ Δ) (wf_sub_eq Γ Δ).
Proof.
  intros a Ha. mauto.
Qed.
