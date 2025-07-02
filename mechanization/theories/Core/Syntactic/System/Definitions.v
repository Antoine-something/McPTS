From Coq Require Import List Classes.RelationClasses Setoid Morphisms.

From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export Syntax.

Reserved Notation "⊢ Γ" (in custom judg at level 80, Γ custom Exp).
Reserved Notation "⊢ Γ ≡ Δ" (in custom judg at level 80, Γ custom Exp, Δ custom Exp).
Reserved Notation "Γ ⊢ M : A :: K" (in custom judg at level 80, Γ custom Exp, M custom Exp, A custom Exp, K custom Exp).
Reserved Notation "Γ ⊢ M ≡ N : A :: K" (in custom judg at level 80, Γ custom Exp, M custom Exp, N custom Exp, A custom Exp, K custom Exp).
Reserved Notation "Γ ⊢ A :: K" (in custom judg at level 80, Γ custom Exp, A custom Exp, K custom Exp).
Reserved Notation "Γ ⊢ A ≡ B :: K" (in custom judg at level 80, Γ custom Exp, A custom Exp, B custom Exp, K custom Exp).
Reserved Notation "Γ ⊢s σ : Δ" (in custom judg at level 80, Γ custom Exp, σ custom Exp, Δ custom Exp).
Reserved Notation "Γ ⊢s σ ≡ τ : Δ" (in custom judg at level 80, Γ custom Exp, σ custom Exp, τ custom Exp, Δ custom Exp).
Reserved Notation "'#' x : A :: K ∈ Γ" (in custom judg at level 80, x constr at level 0, A custom Exp, K custom Exp, Γ custom Exp).

Generalizable All Variables.

(* Context lookup: #x : A :: Sort@s ∈ Γ *)
Inductive ctx_lookup {P : PtsSig} : nat -> Typ P -> Knd P -> Ctx P -> Prop :=
| here : `({{ #0 : [Wk]A :: Sort@s ∈ Γ, A :: Sort@s }})
| there : `({{ #i : A :: Sort@s ∈ Γ }} ->
            {{ #(S i) : [Wk]A :: Sort@s ∈ Γ, B :: Sort@s'}})
where "'#' x : A :: K ∈ Γ" := (ctx_lookup x A K Γ) (in custom judg) : type_scope.

(* Context formation: ⊢ Γ *)
Inductive wf_ctx {P : PtsSig} : Ctx P -> Prop :=
| wf_ctx_empty : {{ ⊢ ⋅ }}
| wf_ctx_extend : `({{ ⊢ Γ }} -> {{ Γ ⊢ A :: Sort@s }} ->
                    {{ ⊢ Γ, A :: Sort@s}})
where "⊢ Γ" := (wf_ctx Γ) (in custom judg) : type_scope

(* Typing for expressions: Γ ⊢ M : A *)
with wf_exp {P : PtsSig} : Ctx P -> Exp P -> Typ P -> Knd P -> Prop :=
| wf_exp_st : `(Ax P s1 s2 -> {{ ⊢ Γ }} -> 
                {{ Γ ⊢ Sort@s1 : Sort@s2 :: Type}})
| wf_exp_var : `({{ ⊢ Γ }} -> {{ #i : A :: Sort@s ∈ Γ }} ->
                 {{ Γ ⊢ #i : A :: Sort@s}})
| wf_exp_pi : `(forall r : Ru P s1 s2 s3,
                    {{ Γ ⊢ A : Sort@s1 :: Type }} -> {{ Γ, A :: Sort@s1 ⊢ B : Sort@s2 :: Type }} ->
                    {{ Γ ⊢ Π r A B : Sort@s3 :: Type}})
| wf_exp_lam : `(forall r : Ru P s1 s2 s3,
                     {{ Γ ⊢ Π r A B : Sort@s3 :: Type}} -> {{ Γ, A :: Sort@s ⊢ M : B :: Sort@s2 }} ->
                     {{ Γ ⊢ λM : Π r A B :: Sort@s3}})
| wf_exp_app : `(forall r : Ru P s1 s2 s3,
                     {{ Γ ⊢ Π r A B : Sort@s3 :: Type }} -> {{ Γ ⊢ M : Π r A B :: Sort@s3 }} -> {{ Γ ⊢ N : A :: Sort@s1 }} ->
                     {{ Γ ⊢ M N : [Id,,N]B :: Sort@s2 }})
| wf_exp_clo : `({{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ M : A :: K }} ->
                 {{ Γ ⊢ [σ]M : [σ]A :: K }})
| wf_exp_conv : `({{ Γ ⊢ M : A :: K }} -> {{ Γ ⊢ A ≡ B : K :: L }} ->
                  {{ Γ ⊢ M : B :: K }})
where "Γ ⊢ M : A :: K" := (wf_exp Γ M A K) (in custom judg) : type_scope

(* Type well-formedness: Γ ⊢ A :: K *)
with wf_typ {P : PtsSig} : Ctx P -> Typ P -> Knd P -> Prop :=
| wf_typ_st : `({{ ⊢ Γ }} ->
                {{ Γ ⊢ Sort@s :: Type }})
| wf_typ_exp : `({{ Γ ⊢ A : Sort@s :: K }} ->
                 {{ Γ ⊢ A :: Sort@s }})
where "Γ ⊢ A :: K" := (wf_typ Γ A K) (in custom judg) : type_scope

(* Typing for substitutions: Γ ⊢s σ : Δ *)
with wf_sub {P : PtsSig} : Ctx P -> Sub P -> Ctx P -> Prop :=
| wf_sub_id : `({{ ⊢ Γ }} ->
                {{ Γ ⊢s Id : Γ }})
| wf_sub_wk : `({{ ⊢ Γ, A :: Sort@s }} ->
                {{ Γ, A :: Sort@s ⊢s Wk : Γ }})
| wf_sub_ext : `({{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A : Sort@s :: Type }} -> {{ Γ ⊢ M : [σ]A :: Sort@s }} ->
                 {{ Γ ⊢s σ,,M : Δ, A :: Sort@s }})
| wf_sub_comp : `({{ Γ1 ⊢s σ : Γ2 }} -> {{ Γ2 ⊢s τ :Γ3 }} ->
                  {{ Γ1 ⊢s σ ∘ τ : Γ3 }})
| wf_sub_conv : `({{ Γ ⊢s σ : Δ }} -> {{ ⊢ Δ ≡ Δ' }} ->
                  {{ Γ ⊢s σ : Δ' }})
where "Γ ⊢s σ : Δ" := (wf_sub Γ σ Δ) (in custom judg) : type_scope

(* Context equality: ⊢ Γ ≡ Δ *)
with eq_ctx {P : PtsSig} : Ctx P -> Ctx P -> Prop :=
| eq_ctx_nil : {{ ⊢ ⋅ ≡ ⋅ }}
| eq_ctx_cons : `({{ ⊢ Γ ≡ Δ }} ->
                  {{ Γ ⊢ A :: Sort@s }} -> {{ Γ ⊢ B :: Sort@s }} ->
                  {{ Δ ⊢ A :: Sort@s }} -> {{ Δ ⊢ B :: Sort@s }} ->
                  {{ Γ ⊢ A ≡ B :: Sort@s }} ->
                  {{ Δ ⊢ A ≡ B :: Sort@s }} ->
                  {{ ⊢ Γ, A :: Sort@s ≡ Δ, B :: Sort@s }})
where "⊢ Γ ≡ Δ" := (eq_ctx Γ Δ) (in custom judg) : type_scope

(* Expressions equality: Γ ⊢ M ≡ N : A *)
with eq_exp {P : PtsSig} : Ctx P -> Exp P -> Exp P -> Typ P -> Knd P -> Prop :=
(* β-reduction and η-expansion *)
| eq_exp_beta : `(forall r : Ru P s1 s2 s3,
                      {{ Γ ⊢ Π r A B : Sort@s3 :: K }} -> {{ Γ, A :: Sort@s1 ⊢ M : B :: Sort@s2 }} -> {{ Γ ⊢ N : A :: Sort@s1 }} ->
                      {{ Γ ⊢ M N ≡ [Id,,N]M : [Id,,N]B :: Sort@s2 }})
| eq_exp_eta : `(forall r : Ru P s1 s2 s3,
                     {{ Γ ⊢ Π r A B : Sort@s3 :: K }} -> {{ Γ ⊢ M : Π r A B :: Sort@s3 }} ->
                     {{ Γ ⊢ M ≡ λ([Wk]M #0) : Π r A B :: Sort@s3 }})
(* Substitution propagation *)
| eq_exp_prop_sort : `(Ax P s1 s2 -> {{ Γ ⊢s σ : Δ }} ->
                       {{ Γ ⊢ [σ]Sort@s1 ≡ Sort@s1 : Sort@s2 :: Type }})
| eq_exp_prop_var_ze : `({{ Γ ⊢s σ,,M : Δ, A :: Sort@s }} ->
                         {{ Γ ⊢ [σ,,M]#0 ≡ M : [σ]A :: Sort@s }})
| eq_exp_prop_var_su : `({{ Γ ⊢s σ,,M : Δ, A :: Sort@s1 }} -> {{ #i : B :: Sort@s2 ∈ Δ }} ->
                         {{ Γ ⊢ [σ,,M]#(S i) ≡ [σ]#i : [σ]B :: Sort@s2 }})
| eq_exp_prop_pi : `(forall r : Ru P s1 s2 s3,
                         {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ Π r A B : Sort@s3 :: K }} ->
                         {{ Γ ⊢ [σ](Π r A B) ≡ Π r ([σ] A) ([(Wk ∘ σ),,#0]B) : Sort@s3 :: K }})
| eq_exp_prop_lam : `(forall r : Ru P s1 s2 s3,
                          {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ Π r A B : Sort@s3 :: K }} -> {{ Δ, A :: Sort@s1 ⊢ M : B :: Sort@s2 }} ->
                          {{ Γ ⊢ [σ](λM) ≡ λ([(Wk∘σ),,#0]M) : [σ](Π r A B) :: Sort@s3 }})
| eq_exp_prop_app : `(forall r : Ru P s1 s2 s3,
                          {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ Π r A B : Sort@s3 :: K }} -> {{ Δ ⊢ M : Π r A B:: Sort@s3 }} -> {{ Δ ⊢ N : A :: Sort@s1 }} ->
                          {{ Γ ⊢ [σ](M N) ≡ [σ]M [σ]N : [σ,,[σ]N]B :: Sort@s2 }})
| eq_exp_prop_id : `({{ Γ ⊢ M : A :: Sort@s }} ->
                     {{ Γ ⊢ [Id]M ≡ M : A :: Sort@s }})
| eq_exp_prop_comp : `({{ Γ1 ⊢s σ1 : Γ2 }} -> {{ Γ2 ⊢s σ2 : Γ3 }} -> {{ Γ3 ⊢ M : A :: Sort@s }} ->
                       {{ Γ1 ⊢ [σ1 ∘ σ2]M ≡ [σ1][σ2]M : [σ1 ∘ σ2]A :: Sort@s }})
(* Congruence rules *)
| eq_exp_cong_pi : `(forall r : Ru P s1 s2 s3,
                         {{ Γ ⊢ A1 ≡ A2 : Sort@s1 :: K }} -> {{ Γ, A1 :: Sort@s1 ⊢ B1 ≡ B2 : Sort@s2 :: K }} ->
                         {{ Γ ⊢ Π r A1 B1 ≡ Π r A2 B2 : Sort@s3 :: K }})
| eq_exp_cong_lam : `(forall r : Ru P s1 s2 s3,
                          {{ Γ ⊢ Π r A B : Sort@s3 :: K }} -> {{ Γ, A :: Sort@s1 ⊢ M1 ≡ M2 : B :: Sort@s2 }} ->
                          {{ Γ ⊢ λM1 ≡ λM2 : Π r A B :: Sort@s3 }})
| eq_exp_cong_app : `(forall r : Ru P s1 s2 s3,
                          {{ Γ ⊢ Π r A B : Sort@s3 :: K }} -> {{ Γ ⊢ M1 ≡ M2 : Π r A B :: Sort@s3 }} -> {{ Γ ⊢ N1 ≡ N2 : A :: Sort@s1 }} ->
                          {{ Γ ⊢ M1 N1 ≡ M2 N2 : [Id,,N1]B :: Sort@s2 }})
| eq_exp_cong_clo : `({{ Γ ⊢s σ1 ≡ σ2 : Δ }} -> {{ Δ ⊢ M1 ≡ M2 : A :: Sort@s }} ->
                      {{ Γ ⊢ [σ1]M1 ≡ [σ2]M2 : [σ1]A :: Sort@s }})
(* Equivalence relation rules *)
| eq_exp_refl : `({{ Γ ⊢ M : A :: K }} ->
                  {{ Γ ⊢ M ≡ M : A :: K }})
| eq_exp_sym : `({{ Γ ⊢ M1 ≡ M2 : A :: K }} ->
                 {{ Γ ⊢ M2 ≡ M1 : A :: K }})
| eq_exp_trans : `({{ Γ ⊢ M1 ≡ M2 : A :: K }} -> {{ Γ ⊢ M2 ≡ M3 : A :: K }} ->
                   {{ Γ ⊢ M1 ≡ M3 : A :: K }})
(* Conversion rule *)
| eq_exp_conv : `({{ Γ ⊢ M1 ≡ M2 : A :: K }} -> {{ Γ ⊢ A ≡ B : K :: L }} ->
                  {{ Γ ⊢ M1 ≡ M2 : B :: K }})
where "Γ ⊢ M ≡ N : A :: K" := (eq_exp Γ M N A K) (in custom judg) : type_scope

(* Type equality: Γ ⊢ A ≡ B *)
with eq_typ {P : PtsSig} : Ctx P -> Typ P -> Typ P -> Knd P -> Prop :=
| eq_typ_st : `({{ ⊢ Γ }} ->
                {{ Γ ⊢ Sort@s ≡ Sort@s :: Type }})
| eq_typ_exp : `({{ Γ ⊢ A ≡ B : Sort@s :: K }} ->
                 {{ Γ ⊢ A ≡ B :: Sort@s }})
where "Γ ⊢ A ≡ B :: K" := (eq_typ Γ A B K) (in custom judg) : type_scope

(* Substitution equality: Γ ⊢s σ ≡ τ : Δ *)
with eq_sub {P : PtsSig} : Ctx P -> Ctx P -> Sub P -> Sub P -> Prop :=
(* β-reduction and η-expansion *)
| eq_sub_beta_nil : `({{ ⋅ ⊢s Id ≡ .. : ⋅ }})
| eq_sub_beta_cons : `({{ ⊢ Γ, A :: Sort@s }} ->
                       {{ Γ, A :: Sort@s ⊢s Id ≡ (Wk ∘ Id),,#0 : Γ, A :: Sort@s }})
| eq_sub_eta : `({{ Γ ⊢s σ : Δ, A :: Sort@s }} ->
                 {{ Γ ⊢s σ ≡ (σ ∘ Wk),,[σ]#0 : Δ, A :: Sort@s }})
(* Substitution propagation *)
| eq_sub_prop_id_left : `({{ Γ ⊢s σ : Δ }} ->
                          {{ Γ ⊢s Id ∘ σ ≡ σ : Δ }})
| eq_sub_prop_id_right : `({{ Γ ⊢s σ : Δ }} ->
                           {{ Γ ⊢s σ ∘ Id ≡ σ : Δ }})
| eq_sub_prop_assoc : `({{ Γ1 ⊢s σ1 : Γ2 }} -> {{ Γ2 ⊢s σ2 : Γ3 }} -> {{ Γ3 ⊢s σ3 : Γ4 }} ->
                        {{ Γ1 ⊢s (σ1 ∘ σ2) ∘ σ3 ≡ σ1 ∘ (σ2 ∘ σ3) : Γ4 }})
| eq_sub_prop_ext_left : `({{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A : K :: L }} -> {{ Γ ⊢ M : [σ]A :: K }} ->
                           {{ Γ ⊢s (σ,,M) ∘ Wk ≡ σ : Δ }})
| eq_sub_prop_ext_right : `({{ Γ1 ⊢s σ1 : Γ2 }} -> {{ Γ2 ⊢s σ2 : Γ3 }} -> {{ Γ3 ⊢ A : Sort@s :: K }} -> {{ Γ2 ⊢ M : [σ2]A :: Sort@s }} ->
                            {{ Γ1 ⊢s σ1 ∘ (σ2,,M) ≡ (σ1 ∘ σ2),,[σ1]M : Γ3, A :: Sort@s }})
(* Congruence rules *)
| eq_sub_cong_ext : `({{ Γ ⊢s σ1 ≡ σ2 : Δ }} -> {{ Δ ⊢ A : Sort@s :: K }} -> {{ Γ ⊢ M1 ≡ M2 : [σ]A :: Sort@s }} ->
                      {{ Γ ⊢s σ1,,M1 ≡ σ2,,M2 : Δ, A :: Sort@s }})
| eq_sub_cong_comp : `({{ Γ1 ⊢s σ1 ≡ σ2 : Γ2 }} -> {{ Γ2 ⊢s τ1 ≡ τ2 : Γ3 }} ->
                       {{ Γ1 ⊢s σ1 ∘ τ1 ≡ σ2 ∘ τ2 : Γ3 }})
(* Equivalence relation rules *)
| eq_sub_refl : `({{ Γ ⊢s σ : Δ }} ->
                  {{ Γ ⊢s σ ≡ σ : Δ }})
| eq_sub_sym : `({{ Γ ⊢s σ1 ≡ σ2 : Δ }} ->
                 {{ Γ ⊢s σ2 ≡ σ1 : Δ }})
| eq_sub_trans : `({{ Γ ⊢s σ1 ≡ σ2 : Δ }} -> {{ Γ ⊢s σ2 ≡ σ3 : Δ }} ->
                   {{ Γ ⊢s σ1 ≡ σ3 : Δ }})
(* Conversion rule *)
| eq_sub_conv : `({{ Γ ⊢s σ1 ≡ σ2 : Δ1 }} -> {{ ⊢ Δ1 ≡ Δ2 }} ->
                  {{ Γ ⊢s σ1 ≡ σ2 : Δ2 }})
where "Γ ⊢s σ ≡ τ : Δ" := (eq_sub Γ Δ σ τ) (in custom judg) : type_scope.
