From Coq Require Import List Classes.RelationClasses Setoid Morphisms.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export Syntax.
Import Syntax_Notations.

Reserved Notation "⊢ Γ" (in custom judg at level 80, Γ custom Exp).
Reserved Notation "⊢ Γ ≈ Δ" (in custom judg at level 80, Γ custom Exp, Δ custom Exp).
Reserved Notation "Γ ⊢ M : A" (in custom judg at level 80, Γ custom Exp, M custom Exp, A custom Exp).
Reserved Notation "Γ ⊢ M ≈ N : A" (in custom judg at level 80, Γ custom Exp, M custom Exp, N custom Exp, A custom Exp).
Reserved Notation "Γ ⊢ A" (in custom judg at level 80, Γ custom Exp, A custom Exp).
Reserved Notation "Γ ⊢ A ≈ B" (in custom judg at level 80, Γ custom Exp, A custom Exp, B custom Exp).
Reserved Notation "Γ ⊢s σ : Δ" (in custom judg at level 80, Γ custom Exp, σ custom Exp, Δ custom Exp).
Reserved Notation "Γ ⊢s σ ≈ τ : Δ" (in custom judg at level 80, Γ custom Exp, σ custom Exp, τ custom Exp, Δ custom Exp).
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
| wf_ctx_extend : `({{ ⊢ Γ }} -> {{ Γ ⊢ A : Sort@s }} ->
                    {{ ⊢ Γ, A :: Sort@s }})
where "⊢ Γ" := (wf_ctx Γ) (in custom judg) : type_scope

(* Typing for expressions: Γ ⊢ M : A *)
with wf_exp {P : PtsSig} : Ctx P -> Typ P -> Exp P -> Prop :=
| wf_exp_st : `(Ax P s1 s2 -> {{ ⊢ Γ }} -> 
                {{ Γ ⊢ Sort@s1 : Sort@s2 }})
| wf_exp_var : `({{ ⊢ Γ }} -> {{ #i : A :: Sort@s ∈ Γ }} ->
                 {{ Γ ⊢ #i : A}})
| wf_exp_pi : `(forall r : Ru P s1 s2 s3,
                    {{ Γ ⊢ A : Sort@s1 }} -> {{ Γ, A :: Sort@s1 ⊢ B : Sort@s2 }} ->
                    {{ Γ ⊢ Π r A B : Sort@s3 }})
| wf_exp_lam : `(forall r : Ru P s1 s2 s3,
                     {{ Γ ⊢ A : Sort@s1 }} -> {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} -> {{ Γ, A :: Sort@s1 ⊢ M : B }} ->
                     {{ Γ ⊢ λ r A M : Π r A B }})
| wf_exp_app : `(forall r : Ru P s1 s2 s3,
                     {{ Γ ⊢ A : Sort@s1 }} -> {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} -> {{ Γ ⊢ M : Π r A B }} -> {{ Γ ⊢ N : A }} ->
                     {{ Γ ⊢ M N : [Id,,N]B }})
| wf_exp_clo : `({{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ M : A }} ->
                 {{ Γ ⊢ [σ]M : [σ]A }})
| wf_exp_conv : `({{ Γ ⊢ M : A }} -> {{ Γ ⊢ B }} -> {{ Γ ⊢ A ≈ B }} ->
                  {{ Γ ⊢ M : B }})
where "Γ ⊢ M : A" := (wf_exp Γ A M) (in custom judg) : type_scope

(* Type well-formedness: Γ ⊢ A *)
with wf_typ {P : PtsSig} : Ctx P -> Typ P -> Prop :=
| wf_typ_st : `({{ ⊢ Γ }} ->
                {{ Γ ⊢ Sort@s }})
| wf_typ_clo : `({{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A }} ->
                    {{ Γ ⊢ [σ]A }})
| wf_typ_exp : `({{ Γ ⊢ A : Sort@s }} ->
                 {{ Γ ⊢ A }})
where "Γ ⊢ A" := (wf_typ Γ A) (in custom judg) : type_scope

(* Typing for substitutions: Γ ⊢s σ : Δ *)
with wf_sub {P : PtsSig} : Ctx P -> Ctx P -> Sub P -> Prop :=
| wf_sub_id : `({{ ⊢ Γ }} ->
                {{ Γ ⊢s Id : Γ }})
| wf_sub_wk : `({{ ⊢ Γ, A :: Sort@s }} ->
                {{ Γ, A :: Sort@s ⊢s Wk : Γ }})
| wf_sub_ext : `({{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A : Sort@s }} -> {{ Γ ⊢ M : [σ]A }} ->
                 {{ Γ ⊢s σ,,M : Δ, A :: Sort@s }})
| wf_sub_comp : `({{ Γ1 ⊢s σ : Γ2 }} -> {{ Γ2 ⊢s τ :Γ3 }} ->
                  {{ Γ1 ⊢s σ ∘ τ : Γ3 }})
| wf_sub_conv : `({{ Γ ⊢s σ : Δ }} -> {{ ⊢ Δ ≈ Δ' }} ->
                  {{ Γ ⊢s σ : Δ' }})
where "Γ ⊢s σ : Δ" := (wf_sub Γ Δ σ) (in custom judg) : type_scope

(* Context equality: ⊢ Γ ≈ Δ *)
with eq_ctx {P : PtsSig} : Ctx P -> Ctx P -> Prop :=
| eq_ctx_nil : {{ ⊢ ⋅ ≈ ⋅ }}
| eq_ctx_cons : `({{ ⊢ Γ ≈ Δ }} ->
                  {{ Γ ⊢ A : Sort@s }} -> {{ Γ ⊢ B : Sort@s }} ->
                  {{ Δ ⊢ A : Sort@s }} -> {{ Δ ⊢ B : Sort@s }} ->
                  {{ Γ ⊢ A ≈ B : Sort@s }} -> {{ Δ ⊢ A ≈ B : Sort@s }} ->
                  {{ ⊢ Γ, A :: Sort@s ≈ Δ, B :: Sort@s }})
where "⊢ Γ ≈ Δ" := (eq_ctx Γ Δ) (in custom judg) : type_scope

(* Expressions equality: Γ ⊢ M ≈ N : A *)
with eq_exp {P : PtsSig} : Ctx P -> Typ P -> Exp P -> Exp P -> Prop :=
(* β-reduction and η-expansion *)
| eq_exp_beta : `(forall r : Ru P s1 s2 s3,
                      {{ Γ ⊢ A : Sort@s1 }} -> {{ Γ, A :: Sort@s1 ⊢ M : B }} -> {{ Γ ⊢ N : A }} ->
                      {{ Γ ⊢ (λ r A M) N ≈ [Id,,N]M : [Id,,N]B }})
| eq_exp_eta : `(forall r : Ru P s1 s2 s3,
                     {{ Γ ⊢ Π r A B : Sort@s3 }} -> {{ Γ ⊢ M : Π r A B }} ->
                     {{ Γ ⊢ M ≈ λ r A ([Wk]M #0) : Π r A B }})
(* Substitution propagation *)
| eq_exp_prop_sort : `(Ax P s1 s2 -> {{ Γ ⊢s σ : Δ }} ->
                       {{ Γ ⊢ [σ]Sort@s1 ≈ Sort@s1 : Sort@s2 }})
| eq_exp_prop_var_ze : `({{ Γ ⊢s σ,,M : Δ, A :: Sort@s }} ->
                         {{ Γ ⊢ [σ,,M]#0 ≈ M : [σ]A }})
| eq_exp_prop_var_su : `({{ Γ ⊢s σ,,M : Δ, A :: Sort@s1 }} -> {{ #i : B :: Sort@s2 ∈ Δ }} ->
                         {{ Γ ⊢ [σ,,M]#(S i) ≈ [σ]#i : [σ]B }})
| eq_exp_prop_pi : `(forall r : Ru P s1 s2 s3,
                         {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ Π r A B : Sort@s3 }} ->
                         {{ Γ ⊢ [σ](Π r A B) ≈ Π r ([σ] A) ([(Wk ∘ σ),,#0]B) : Sort@s3 }})
| eq_exp_prop_lam : `(forall r : Ru P s1 s2 s3,
                          {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ Π r A B : Sort@s3 }} -> {{ Δ, A :: Sort@s1 ⊢ M : B }} ->
                          {{ Γ ⊢ [σ](λ r A M) ≈ λ r [σ]A ([(Wk∘σ),,#0]M) : [σ](Π r A B) }})
| eq_exp_prop_app : `(forall r : Ru P s1 s2 s3,
                          {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ Π r A B : Sort@s3 }} -> {{ Δ ⊢ M : Π r A B }} -> {{ Δ ⊢ N : A }} ->
                          {{ Γ ⊢ [σ](M N) ≈ [σ]M [σ]N : [σ,,[σ]N]B }})
| eq_exp_prop_id : `({{ Γ ⊢ M : A }} ->
                     {{ Γ ⊢ [Id]M ≈ M : A }})
| eq_exp_prop_comp : `({{ Γ1 ⊢s σ1 : Γ2 }} -> {{ Γ2 ⊢s σ2 : Γ3 }} -> {{ Γ3 ⊢ M : A }} ->
                       {{ Γ1 ⊢ [σ1 ∘ σ2]M ≈ [σ1][σ2]M : [σ1 ∘ σ2]A }})
(* Congruence rules *)
| eq_exp_cong_pi : `(forall r : Ru P s1 s2 s3,
                         {{ Γ ⊢ A1 : Sort@s1 }} -> {{ Γ ⊢ A1 ≈ A2 : Sort@s1 }} -> {{ Γ, A1 :: Sort@s1 ⊢ B1 ≈ B2 : Sort@s2 }} ->
                         {{ Γ ⊢ Π r A1 B1 ≈ Π r A2 B2 : Sort@s3 }})
| eq_exp_cong_lam : `(forall r : Ru P s1 s2 s3,
                          {{ Γ ⊢ A1 : Sort@s1 }} -> {{ Γ ⊢ A1 ≈ A2 : Sort@s1 }} -> {{ Γ, A1 :: Sort@s1 ⊢ M1 ≈ M2 : B }} ->
                          {{ Γ ⊢ λ r A1 M1 ≈ λ r A2 M2 : Π r A B }})
| eq_exp_cong_app : `(forall r : Ru P s1 s2 s3,
                          {{ Γ ⊢ Π r A B : Sort@s3 }} -> {{ Γ ⊢ M1 ≈ M2 : Π r A B }} -> {{ Γ ⊢ N1 ≈ N2 : A }} ->
                          {{ Γ ⊢ M1 N1 ≈ M2 N2 : [Id,,N1]B }})
| eq_exp_cong_clo : `({{ Γ ⊢s σ1 ≈ σ2 : Δ }} -> {{ Δ ⊢ M1 ≈ M2 : A }} ->
                      {{ Γ ⊢ [σ1]M1 ≈ [σ2]M2 : [σ1]A }})
(* Equivalence relation rules *)
| eq_exp_refl : `({{ Γ ⊢ M : A }} ->
                  {{ Γ ⊢ M ≈ M : A }})
| eq_exp_sym : `({{ Γ ⊢ M1 ≈ M2 : A }} ->
                 {{ Γ ⊢ M2 ≈ M1 : A }})
| eq_exp_trans : `({{ Γ ⊢ M1 ≈ M2 : A }} -> {{ Γ ⊢ M2 ≈ M3 : A }} ->
                   {{ Γ ⊢ M1 ≈ M3 : A }})
(* Conversion rule *)
| eq_exp_conv : `({{ Γ ⊢ M1 ≈ M2 : A }} -> {{ Γ ⊢ A ≈ B }} ->
                  {{ Γ ⊢ M1 ≈ M2 : B }})
where "Γ ⊢ M ≈ N : A" := (eq_exp Γ A M N) (in custom judg) : type_scope

(* Type equality: Γ ⊢ A ≈ B *)
(* 
 * This judgment is probably missing some rules.
 * In particular, we cannot properly propagate substitutions into (maximal) sorts
*)
with eq_typ {P : PtsSig} : Ctx P -> Typ P -> Typ P -> Prop :=
| eq_typ_st : `({{ ⊢ Γ }} ->
                {{ Γ ⊢ Sort@s ≈ Sort@s }})
| eq_typ_clo_st : `({{ Γ ⊢s σ : Δ }} ->
                    {{ Γ ⊢ [σ]Sort@s ≈ Sort@s }})
| eq_typ_clo_cong : `({{ Γ ⊢s σ ≈ τ : Δ }} -> {{ Δ ⊢ A ≈ B }} ->
                      {{ Γ ⊢ [σ]A ≈ [τ]B }})
| eq_typ_prop_comp : `({{ Γ1 ⊢s σ : Γ2 }} -> {{ Γ2 ⊢s τ : Γ3 }} -> {{ Γ3 ⊢ A ≈ B }} ->
                       {{ Γ1 ⊢ [σ∘τ]A ≈ [σ][τ]B }})
| eq_typ_exp : `({{ Γ ⊢ A ≈ B : Sort@s }} ->
                 {{ Γ ⊢ A ≈ B }})
| eq_typ_refl : `({{ Γ ⊢ A }} ->
                  {{ Γ ⊢ A ≈ A }})
| eq_typ_sym : `({{ Γ ⊢ A ≈ B }} ->
                 {{ Γ ⊢ B ≈ A }})
| eq_typ_trans : `({{ Γ ⊢ A1 ≈ A2 }} -> {{ Γ ⊢ A2 ≈ A3 }} ->
                   {{ Γ ⊢ A1 ≈ A3 }})
where "Γ ⊢ A ≈ B" := (eq_typ Γ A B) (in custom judg) : type_scope

(* Substitution equality: Γ ⊢s σ ≈ τ : Δ *)
with eq_sub {P : PtsSig} : Ctx P -> Ctx P -> Sub P -> Sub P -> Prop :=
(* β-reduction and η-expansion *)
| eq_sub_beta_nil : `({{ ⋅ ⊢s Id ≈ .. : ⋅ }})
| eq_sub_beta_cons : `({{ ⊢ Γ, A :: Sort@s }} ->
                       {{ Γ, A :: Sort@s ⊢s Id ≈ (Wk ∘ Id),,#0 : Γ, A :: Sort@s }})
| eq_sub_eta : `({{ Γ ⊢s σ : Δ, A :: Sort@s }} ->
                 {{ Γ ⊢s σ ≈ (σ ∘ Wk),,[σ]#0 : Δ, A :: Sort@s }})
(* Substitution propagation *)
| eq_sub_prop_id_left : `({{ Γ ⊢s σ : Δ }} ->
                          {{ Γ ⊢s Id ∘ σ ≈ σ : Δ }})
| eq_sub_prop_id_right : `({{ Γ ⊢s σ : Δ }} ->
                           {{ Γ ⊢s σ ∘ Id ≈ σ : Δ }})
| eq_sub_prop_assoc : `({{ Γ1 ⊢s σ1 : Γ2 }} -> {{ Γ2 ⊢s σ2 : Γ3 }} -> {{ Γ3 ⊢s σ3 : Γ4 }} ->
                        {{ Γ1 ⊢s (σ1 ∘ σ2) ∘ σ3 ≈ σ1 ∘ (σ2 ∘ σ3) : Γ4 }})
| eq_sub_prop_ext_left : `({{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A }} -> {{ Γ ⊢ M : [σ]A }} ->
                           {{ Γ ⊢s (σ,,M) ∘ Wk ≈ σ : Δ }})
| eq_sub_prop_ext_right : `({{ Γ1 ⊢s σ1 : Γ2 }} -> {{ Γ2 ⊢s σ2 : Γ3 }} -> {{ Γ3 ⊢ A : Sort@s }} -> {{ Γ2 ⊢ M : [σ2]A }} ->
                            {{ Γ1 ⊢s σ1 ∘ (σ2,,M) ≈ (σ1 ∘ σ2),,[σ1]M : Γ3, A :: Sort@s }})
(* Congruence rules *)
| eq_sub_cong_ext : `({{ Γ ⊢s σ1 ≈ σ2 : Δ }} -> {{ Δ ⊢ A : Sort@s }} -> {{ Γ ⊢ M1 ≈ M2 : [σ]A }} ->
                      {{ Γ ⊢s σ1,,M1 ≈ σ2,,M2 : Δ, A :: Sort@s }})
| eq_sub_cong_comp : `({{ Γ1 ⊢s σ1 ≈ σ2 : Γ2 }} -> {{ Γ2 ⊢s τ1 ≈ τ2 : Γ3 }} ->
                       {{ Γ1 ⊢s σ1 ∘ τ1 ≈ σ2 ∘ τ2 : Γ3 }})
(* Equivalence relation rules *)
| eq_sub_refl : `({{ Γ ⊢s σ : Δ }} ->
                  {{ Γ ⊢s σ ≈ σ : Δ }})
| eq_sub_sym : `({{ Γ ⊢s σ1 ≈ σ2 : Δ }} ->
                 {{ Γ ⊢s σ2 ≈ σ1 : Δ }})
| eq_sub_trans : `({{ Γ ⊢s σ1 ≈ σ2 : Δ }} -> {{ Γ ⊢s σ2 ≈ σ3 : Δ }} ->
                   {{ Γ ⊢s σ1 ≈ σ3 : Δ }})
(* Conversion rule *)
| eq_sub_conv : `({{ Γ ⊢s σ1 ≈ σ2 : Δ1 }} -> {{ ⊢ Δ1 ≈ Δ2 }} ->
                  {{ Γ ⊢s σ1 ≈ σ2 : Δ2 }})
where "Γ ⊢s σ ≈ τ : Δ" := (eq_sub Γ Δ σ τ) (in custom judg) : type_scope.


Scheme wf_ctx_mut_ind := Induction for wf_ctx Sort Prop
with wf_exp_mut_ind := Induction for wf_exp Sort Prop
with wf_typ_mut_ind := Induction for wf_typ Sort Prop                                     
with wf_sub_mut_ind := Induction for wf_sub Sort Prop
with eq_ctx_mut_ind := Induction for eq_ctx Sort Prop
with eq_exp_mut_ind := Induction for eq_exp Sort Prop
with eq_typ_mut_ind := Induction for eq_typ Sort Prop
with eq_sub_mut_ind := Induction for eq_sub Sort Prop.
Combined Scheme syntactic_wf_mut_ind from
  wf_ctx_mut_ind,
  wf_exp_mut_ind,
  wf_typ_mut_ind,
  wf_sub_mut_ind,
  eq_ctx_mut_ind,
  eq_exp_mut_ind,
  eq_typ_mut_ind,
  eq_sub_mut_ind.


Scheme wf_ctx_mut_ind' := Induction for wf_ctx Sort Prop
with wf_exp_mut_ind' := Induction for wf_exp Sort Prop
with wf_sub_mut_ind' := Induction for wf_sub Sort Prop.
Combined Scheme syntactic_wf_mut_ind' from
  wf_ctx_mut_ind',
  wf_exp_mut_ind',
  wf_sub_mut_ind'.


#[export]
Hint Constructors wf_ctx eq_ctx wf_exp eq_exp wf_typ eq_typ wf_sub eq_sub ctx_lookup : mcpts.


#[export]
Instance eq_exp_PER {P : PtsSig} (Γ : Ctx P) A : PER (eq_exp Γ A).
Proof.
  split.
  - eauto using eq_exp_sym.
  - eauto using eq_exp_trans.
Qed.

#[export]
  Instance eq_typ_PER {P : PtsSig} (Γ : Ctx P) : PER (eq_typ Γ).
Proof.
  split.
  - eauto using eq_typ_sym.
  - eauto using eq_typ_trans.
Qed.

#[export]
Instance eq_sub_PER {P : PtsSig} (Γ Δ : Ctx P) : PER (eq_sub Γ Δ).
Proof.
  split.
  - eauto using eq_sub_sym.
  - eauto using eq_sub_trans.
Qed.

#[export]
Instance eq_ctx_Symmetric {P : PtsSig} : Symmetric (@eq_ctx P).
Proof.  
  induction 1; econstructor; mauto; apply eq_exp_PER; mauto.
Qed.


Add Parametric Morphism {P : PtsSig} (Γ : Ctx P) T : (eq_exp Γ T)
    with signature eq_exp Γ T ==> eq ==> iff as eq_exp_morphism_iff1.
Proof.
  split; mauto; intros; eapply eq_exp_trans; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ : Ctx P) T : (eq_exp Γ T)
    with signature eq ==> eq_exp Γ T ==> iff as eq_exp_morphism_iff2.
Proof.
  split; mauto; intros; eapply eq_exp_trans; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ Δ : Ctx P) : (eq_sub Γ Δ)
    with signature eq_sub Γ Δ ==> eq ==> iff as eq_sub_morphism_iff1.
Proof.
  split; mauto; intros; eapply eq_sub_trans; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ Δ : Ctx P) : (eq_sub Γ Δ)
    with signature eq ==> eq_sub Γ Δ ==> iff as eq_sub_morphism_iff2.
Proof.
  split; mauto; intros; eapply eq_sub_trans; mauto.
Qed.


#[export]
Hint Rewrite -> @eq_exp_prop_sort using mauto 3 : mcpts.

#[export]
Hint Rewrite -> @eq_sub_prop_id_right @eq_sub_prop_id_left
                  @eq_sub_prop_assoc (* prefer right association *)
                  @eq_sub_prop_ext_left using mauto 4 : mcpts.

#[export]
Hint Rewrite -> @eq_exp_prop_id @eq_exp_prop_pi using mauto 4 : mcpts.

#[export]
Instance wf_exp_eq_per_elem {P : PtsSig} (Γ : Ctx P) T : PERElem _ (wf_exp Γ T) (eq_exp Γ T).
Proof.
  intros a Ha; econstructor; mauto.
Qed.


#[export]
Instance wf_sub_eq_per_elem {P : PtsSig} (Γ Δ : Ctx P) : PERElem _ (wf_sub Γ Δ) (eq_sub Γ Δ).
Proof.
  intros a Ha; econstructor; mauto.
Qed.
