From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Export NbE.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

Reserved Notation "Γ ⊢a A ⊆ A'" (in custom judg at level 80, Γ custom exp, A custom exp, A' custom exp).
Reserved Notation "⊢anf A ⊆ A'" (in custom judg at level 80, A custom nf, A' custom nf).

Definition not_sort_pi {P} (A : nf P) : Prop :=
  match A with
  | nf_st _ | nf_pi _ _ _  => False
  | _ => True
  end.

Record ConvertibleSig (P : PtsSig) : Prop :=
  mkConvertibleSig {
      Convert : ctx P -> typ P -> typ P -> Prop;
      CorrectConv : forall Γ A B, Convert Γ A B <-> {{ Γ ⊢ A ≈ B }};
      DecidableConv : forall Γ A B, (Convert Γ A B) \/ ~(Convert Γ A B);
    }.

Inductive alg_subtyping {P} (conv_P : ConvertibleSig P) : ctx P -> nf P -> typ P -> Prop :=
| alg_subtyp_refl : forall A B,
    not_sort_pi A ->
    Convert conv_P Γ A B ->
    {{ Γ ⊢a A ⊆ B }}.

Inductive alg_subtyping_nf : nf P -> nf P -> Prop :=
| asnf_refl : forall A A',
    not_univ_pi_sigma A ->
    A = A' ->
    {{ ⊢anf A ⊆ A' }}
| asnf_univ : forall i j,
    i <= j ->
    {{ ⊢anf Type@i ⊆ Type@j }}
| asnf_pi : forall A B A' B',
    A = A' ->
    {{ ⊢anf B ⊆ B' }} ->
    {{ ⊢anf Π A B ⊆ Π A' B' }}
| asnf_sigma : forall A B A' B',
    A = A' ->
    {{ ⊢anf B ⊆ B' }} ->
    {{ ⊢anf Σ A B ⊆ Σ A' B' }}
where "⊢anf A ⊆ A'" := (alg_subtyping_nf A A') (in custom judg) : type_scope.

Inductive alg_subtyping : ctx -> typ -> typ -> Prop :=
| alg_subtyp_run : forall Γ A B A' B',
    nbe_ty Γ A A' ->
    nbe_ty Γ B B' ->
    {{ ⊢anf A' ⊆ B' }} ->
    {{ Γ ⊢a A ⊆ B }}
where "Γ ⊢a A ⊆ B" := (alg_subtyping Γ A B) (in custom judg) : type_scope.

#[export]
Hint Constructors alg_subtyping_nf alg_subtyping: mcpts.
