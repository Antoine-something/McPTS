From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Export NbE.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

Reserved Notation "Γ ⊢a A ⊆ A'" (in custom judg at level 80, Γ custom exp, A custom exp, A' custom exp).
Reserved Notation "⊢anf A ⊆ A'" (in custom judg at level 80, A custom nf, A' custom nf).

Reserved Notation "⊢a Γ ⊆ Γ'" (in custom judg at level 80, Γ custom exp, Γ' custom exp).

Definition not_sort_pi {P} (A : nf P) : Prop :=
  match A with
  | nf_st _ | nf_pi _ _ _  => False
  | _ => True
  end.

Inductive alg_subtyping_nf {P} : nf P -> nf P -> Prop :=
| asnf_refl : forall A A',
    not_sort_pi A ->
    A = A' ->
    {{ ⊢anf A ⊆ A' }}
| asnf_sort : forall s s',
    st_subtyp s s' ->
    {{ ⊢anf Sort@s ⊆ Sort@s' }}
| asnf_pi : forall A B A' B' s1 s2 s3 (r : Ru_pi P s1 s2 s3 ),
    A = A' ->
    {{ ⊢anf B ⊆ B' }} ->
    {{ ⊢anf Π r A B ⊆ Π r A' B' }}
where "⊢anf A ⊆ A'" := (alg_subtyping_nf A A') (in custom judg) : type_scope.

Inductive alg_subtyping {P} : ctx P -> typ P -> typ P -> Prop :=
| alg_subtyp_run : forall Γ A B A' B',
    nbe_ty Γ A A' ->
    nbe_ty Γ B B' ->
    {{ ⊢anf A' ⊆ B' }} ->
    {{ Γ ⊢a A ⊆ B }}
where "Γ ⊢a A ⊆ B" := (alg_subtyping Γ A B) (in custom judg) : type_scope.

Inductive alg_subtyping_ctx {P} : ctx P -> ctx P -> Prop :=
| asc_nil : {{ ⊢a ⋅ ⊆ ⋅ }}
| asc_cons : forall Γ Γ' A A' s,
    {{ ⊢a Γ ⊆ Γ' }} ->
    {{ Γ ⊢a A ⊆ A' }} ->
    {{ ⊢a Γ, A@s ⊆ Γ', A'@s }}
where "⊢a Γ ⊆ Γ'" := (alg_subtyping_ctx Γ Γ') (in custom judg) : type_scope.

#[export]
Hint Constructors alg_subtyping_nf alg_subtyping alg_subtyping_ctx : mcpts.
