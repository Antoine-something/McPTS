From McPTS.Core Require Import Base.
From McPTS.Core.PTSSignature Require Import Signature.
From McPTS.Core.Syntactic Require Import Syntax.

Module SystemFunctor (P : PtsSig).
  Module Syn := SyntaxFunctor P.
  Import P.
  Import Syn.
  
  Reserved Notation "⊢ Γ" (in custom judg at level 80, Γ custom Exp).
  Reserved Notation "⊢ Γ ≡ Δ" (in custom judg at level 80, Γ custom Exp, Δ custom Exp).
  Reserved Notation "Γ ⊢ M : A" (in custom judg at level 80, Γ custom Exp, M custom Exp, A custom Exp).
  Reserved Notation "Γ ⊢ M ≡ N : A" (in custom judg at level 80, Γ custom Exp, M custom Exp, N custom Exp, A custom Exp).
  Reserved Notation "Γ ⊢ A" (in custom judg at level 80, Γ custom Exp, A custom Exp).
  Reserved Notation "Γ ⊢ A ≡ B" (in custom judg at level 80, Γ custom Exp, A custom Exp, B custom Exp).
  Reserved Notation "Γ ⊢s σ : Δ" (in custom judg at level 80, Γ custom Exp, σ custom Exp, Δ custom Exp).
  Reserved Notation "Γ ⊢s σ ≡ τ : Δ" (in custom judg at level 80, Γ custom Exp, σ custom Exp, τ custom Exp, Δ custom Exp).
  Reserved Notation "'#' x : A : s ∈ Γ" (in custom judg at level 80, x constr at level 0, A custom Exp, s custom Exp, Γ custom Exp).

  Generalizable All Variables.
  
  Inductive ctx_lookup : nat -> Typ -> St -> Ctx -> Prop :=
  | here : `({{ #0 : [Wk]A : s ∈ Γ, A : s }})
  | there : `({{ #i : A : s ∈ Γ }} ->
              {{ #(S i) : [Wk]A : s ∈ Γ, B : s}})
  where "'#' x : A : s ∈ Γ" := (ctx_lookup x A s Γ) (in custom judg) : type_scope.

  (* Context formation: ⊢ Γ *)
  Inductive wf_ctx : Ctx -> Prop :=
  | wf_ctx_empty : {{ ⊢ ⋅ }}
  | wf_ctx_extend : `({{ ⊢ Γ }} -> {{ Γ ⊢ A : Sort@s}} ->
                      {{ ⊢ Γ, A:s}})
  where "⊢ Γ" := (wf_ctx Γ) (in custom judg) : type_scope

  (* Typing for expressions: Γ ⊢ M : A *)
  with wf_exp : Ctx -> Exp -> Typ -> Prop :=
  | wf_exp_st : `(Ax s1 s2 -> {{ ⊢ Γ }} -> 
                  {{ Γ ⊢ Sort@s1 : Sort@s2 }})
  | wf_exp_var : `({{ ⊢ Γ }} -> {{ #i : A : s ∈ Γ }} ->
                   {{ Γ ⊢ #i : A}})
  | wf_exp_pi : `(forall r : Ru s1 s2 s3,
                      {{ Γ ⊢ A : Sort@s1 }} -> {{ Γ, A:s1 ⊢ B : Sort@s2 }} ->
                      {{ Γ ⊢ Π r A B : Sort@s3 }})
  | wf_exp_lam : `(forall r : Ru s1 s2 s3,
                       {{ Γ ⊢ Π r A B : Sort@s3 }} -> {{ Γ, A:s ⊢ M : B }} ->
                       {{ Γ ⊢ λM : Π r A B }})
  | wf_exp_app : `(forall r : Ru s1 s2 s3,
                       {{ Γ ⊢ Π r A B : Sort@s3 }} -> {{ Γ ⊢ M : Π r A B }} -> {{ Γ ⊢ N : A }} ->
                       {{ Γ ⊢ M N : [Id,,N]B }})
  | wf_exp_clo : `({{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ M : A }} ->
                   {{ Γ ⊢ [σ]M : [σ]A }})
  | wf_exp_conv : `({{ Γ ⊢ M : A }} -> {{ Γ ⊢ A ≡ B }} ->
                    {{ Γ ⊢ M : B }})
  where "Γ ⊢ M : A" := (wf_exp Γ M A) (in custom judg) : type_scope

  (* Type well-formedness: Γ ⊢ A *)
  with wf_typ : Ctx -> Typ -> Prop :=
  | wf_typ_st : `({{ ⊢ Γ }} ->
                  {{ Γ ⊢ Sort@s }})
  | wf_typ_exp : `({{ Γ ⊢ A : Sort@s }} ->
                   {{ Γ ⊢ A }})
  where "Γ ⊢ A" := (wf_typ Γ A) (in custom judg) : type_scope

  (* Typing for substitutions: Γ ⊢s σ : Δ *)
  with wf_sub : Ctx -> Sub -> Ctx -> Prop :=
  | wf_sub_id : `({{ ⊢ Γ }} ->
                  {{ Γ ⊢s Id : Γ }})
  | wf_sub_wk : `({{ ⊢ Γ, A:s }} ->
                  {{ Γ, A:s ⊢s Wk : Γ }})
  | wf_sub_ext : `({{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A : Sort@s }} -> {{ Γ ⊢ M : [σ]A }} ->
                   {{ Γ ⊢s σ,,M : Δ, A:s }})
  | wf_sub_comp : `({{ Γ1 ⊢s σ : Γ2 }} -> {{ Γ2 ⊢s τ :Γ3 }} ->
                    {{ Γ1 ⊢s σ ∘ τ : Γ3 }})
  | wf_sub_conv : `({{ Γ ⊢s σ : Δ }} -> {{ ⊢ Δ ≡ Δ' }} ->
                    {{ Γ ⊢s σ : Δ' }})
  where "Γ ⊢s σ : Δ" := (wf_sub Γ σ Δ) (in custom judg) : type_scope

  (* Context equality: ⊢ Γ ≡ Δ *)
  with eq_ctx : Ctx -> Ctx -> Prop :=
  | eq_ctx_nil : {{ ⊢ ⋅ ≡ ⋅ }}
  | eq_ctx_cons : `({{ ⊢ Γ ≡ Δ }} -> {{ Γ ⊢ A ≡ B : Sort@s }} ->
                    {{ ⊢ Γ, A:s ≡ Δ, B:s }})
  where "⊢ Γ ≡ Δ" := (eq_ctx Γ Δ) (in custom judg) : type_scope

  (* Expressions equality: Γ ⊢ M ≡ N : A *)
  with eq_exp : Ctx -> Exp -> Exp -> Typ -> Prop :=
  (* β-reduction and η-expansion *)
  | eq_exp_beta : `(forall r : Ru s1 s2 s3,
                        {{ Γ ⊢ Π r A B : Sort@s3 }} -> {{ Γ, A:s1 ⊢ M : B }} -> {{ Γ ⊢ N : A }} ->
                        {{ Γ ⊢ M N ≡ [Id,,N]M : [Id,,N]B }})
  | eq_exp_eta : `(forall r : Ru s1 s2 s3,
                       {{ Γ ⊢ Π r A B : Sort@s3 }} -> {{ Γ ⊢ M : Π r A B }} ->
                       {{ Γ ⊢ M ≡ λ([Wk]M #0) : Π r A B }})
  (* Substitution propagation *)
  | eq_exp_prop_sort : `(Ax s1 s2 -> {{ Γ ⊢s σ : Δ }} ->
                         {{ Γ ⊢ [σ]Sort@s1 ≡ Sort@s1 : Sort@s2 }})
  | eq_exp_prop_var_ze : `({{ Γ ⊢s σ,,M : Δ, A:s }} ->
                           {{ Γ ⊢ [σ,,M]#0 ≡ M : [σ]A }})
  | eq_exp_prop_var_su : `({{ Γ ⊢s σ,,M : Δ, A:s1 }} -> {{ #i:B:s2 ∈ Δ }} ->
                           {{ Γ ⊢ [σ,,M]#(S i) ≡ [σ]#i : [σ]B }})
  | eq_exp_prop_pi : `(forall r : Ru s1 s2 s3,
                           {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ Π r A B : Sort@s3 }} ->
                           {{ Γ ⊢ [σ](Π r A B) ≡ Π r ([σ] A) ([(Wk ∘ σ),,#0]B) : Sort@s3 }})
  | eq_exp_prop_lam : `(forall r : Ru s1 s2 s3,
                            {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ Π r A B : Sort@s3 }} -> {{ Δ, A:s1 ⊢ M : B }} ->
                            {{ Γ ⊢ [σ](λM) ≡ λ([(Wk∘σ),,#0]M) : [σ](Π r A B) }})
  | eq_exp_prop_app : `(forall r : Ru s1 s2 s3,
                            {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ Π r A B : Sort@s3 }} -> {{ Δ ⊢ M : Π r A B }} -> {{ Δ ⊢ N : A }} ->
                            {{ Γ ⊢ [σ](M N) ≡ [σ]M [σ]N : [σ,,[σ]N]B }})
  | eq_exp_prop_id : `({{ Γ ⊢ M : A }} ->
                       {{ Γ ⊢ [Id]M ≡ M : A }})
  | eq_exp_prop_comp : `({{ Γ1 ⊢s σ1 : Γ2 }} -> {{ Γ2 ⊢s σ2 : Γ3 }} -> {{ Γ3 ⊢ M : A }} ->
                         {{ Γ1 ⊢ [σ1 ∘ σ2]M ≡ [σ1][σ2]M : [σ1 ∘ σ2]A }})
  (* Congruence rules *)
  | eq_exp_cong_pi : `(forall r : Ru s1 s2 s3,
                           {{ Γ ⊢ A1 ≡ A2 : Sort@s1 }} -> {{ Γ, A1:s1 ⊢ B1 ≡ B2 : Sort@s2 }} ->
                           {{ Γ ⊢ Π r A1 B1 ≡ Π r A2 B2 : Sort@s3 }})
  | eq_exp_cong_lam : `(forall r : Ru s1 s2 s3,
                            {{ Γ ⊢ Π r A B : Sort@s3 }} -> {{ Γ, A:s1 ⊢ M1 ≡ M2 : B }} ->
                            {{ Γ ⊢ λM1 ≡ λM2 : Π r A B }})
  | eq_exp_cong_app : `(forall r : Ru s1 s2 s3,
                            {{ Γ ⊢ Π r A B : Sort@s3 }} -> {{ Γ ⊢ M1 ≡ M2 : Π r A B }} -> {{ Γ ⊢ N1 ≡ N2 : A }} ->
                            {{ Γ ⊢ M1 N1 ≡ M2 N2 : [Id,,N1]B }})
  | eq_exp_cong_clo : `({{ Γ ⊢s σ1 ≡ σ2 : Δ }} -> {{ Δ ⊢ M1 ≡ M2 : A }} ->
                        {{ Γ ⊢ [σ1]M1 ≡ [σ2]M2 : [σ1]A }})
  (* Equivalence relation rules *)
  | eq_exp_refl : `({{ Γ ⊢ M : A }} ->
                    {{ Γ ⊢ M ≡ M : A }})
  | eq_exp_sym : `({{ Γ ⊢ M1 ≡ M2 : A }} ->
                   {{ Γ ⊢ M2 ≡ M1 : A }})
  | eq_exp_trans : `({{ Γ ⊢ M1 ≡ M2 : A }} -> {{ Γ ⊢ M2 ≡ M3 : A }} ->
                     {{ Γ ⊢ M1 ≡ M3 : A }})
  (* Conversion rule *)
  | eq_exp_conv : `({{ Γ ⊢ M1 ≡ M2 : A }} -> {{ Γ ⊢ A ≡ B }} ->
                    {{ Γ ⊢ M1 ≡ M2 : B }})
  where "Γ ⊢ M ≡ N : A" := (eq_exp Γ M N A) (in custom judg) : type_scope

  (* Type equality: Γ ⊢ A ≡ B *)
  with eq_typ : Ctx -> Typ -> Typ -> Prop :=
  | eq_typ_st : `({{ ⊢ Γ }} ->
                  {{ Γ ⊢ Sort@s ≡ Sort@s }})
  | eq_typ_exp : `({{ Γ ⊢ A ≡ B : Sort@s }} ->
                   {{ Γ ⊢ A ≡ B }})
  where "Γ ⊢ A ≡ B" := (eq_typ Γ A B) (in custom judg) : type_scope

  (* Substitution equality: Γ ⊢s σ ≡ τ : Δ *)
  with eq_sub : Ctx -> Sub -> Sub -> Ctx -> Prop :=
  (* β-reduction and η-expansion *)
  | eq_sub_beta_nil : `({{ ⋅ ⊢s Id ≡ .. : ⋅ }})
  | eq_sub_beta_cons : `({{ ⊢ Γ, A:s }} ->
                         {{ Γ, A:s ⊢s Id ≡ (Wk ∘ Id),,#0 : Γ, A:s }})
  | eq_sub_eta : `({{ Γ ⊢s σ : Δ, A:s }} ->
                   {{ Γ ⊢s σ ≡ (σ ∘ Wk),,[σ]#0 : Δ, A:s }})
  (* Substitution propagation *)
  | eq_sub_prop_id_left : `({{ Γ ⊢s σ : Δ }} ->
                            {{ Γ ⊢s Id ∘ σ ≡ σ : Δ }})
  | eq_sub_prop_id_right : `({{ Γ ⊢s σ : Δ }} ->
                             {{ Γ ⊢s σ ∘ Id ≡ σ : Δ }})
  | eq_sub_prop_assoc : `({{ Γ1 ⊢s σ1 : Γ2 }} -> {{ Γ2 ⊢s σ2 : Γ3 }} -> {{ Γ3 ⊢s σ3 : Γ4 }} ->
                          {{ Γ1 ⊢s (σ1 ∘ σ2) ∘ σ3 ≡ σ1 ∘ (σ2 ∘ σ3) : Γ4 }})
  | eq_sub_prop_ext_left : `({{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A }} -> {{ Γ ⊢ M : [σ]A }} ->
                             {{ Γ ⊢s (σ,,M) ∘ Wk ≡ σ : Δ }})
  | eq_sub_prop_ext_right : `({{ Γ1 ⊢s σ1 : Γ2 }} -> {{ Γ2 ⊢s σ2 : Γ3 }} -> {{ Γ3 ⊢ A : Sort@s }} -> {{ Γ2 ⊢ M : [σ2]A }} ->
                              {{ Γ1 ⊢s σ1 ∘ (σ2,,M) ≡ (σ1 ∘ σ2),,[σ1]M : Γ3, A:s }})
  (* Congruence rules *)
  | eq_sub_cong_ext : `({{ Γ ⊢s σ1 ≡ σ2 : Δ }} -> {{ Δ ⊢ A : Sort@s }} -> {{ Γ ⊢ M1 ≡ M2 : [σ]A }} ->
                        {{ Γ ⊢s σ1,,M1 ≡ σ2,,M2 : Δ, A:s }})
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
  where "Γ ⊢s σ ≡ τ : Δ" := (eq_sub Γ σ τ Δ) (in custom judg) : type_scope.  
End SystemFunctor.
