From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Export NbE.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.


Reserved Notation "⟪ conv_P ⟫ Γ '⊢a' M ⟹ A" (in custom judg at level 80, conv_P constr, Γ custom exp, M custom exp, A custom exp).
Reserved Notation "⟪ conv_P ⟫ Γ '⊢a' M ⟸ A" (in custom judg at level 80, conv_P constr, Γ custom exp, M custom exp, A custom exp).

Generalizable All Variables.


Record ConvertibleSig (P : PtsSig) : Type :=
  mkConvertibleSig {
      Convert : ctx P -> typ P -> typ P -> Prop;
      CorrectConv : forall Γ A B, Convert Γ A B <-> {{ Γ ⊢ A ⊆ B }};
      DecidableConv : forall Γ A B, (Convert Γ A B) \/ ~(Convert Γ A B);
    }.
Arguments Convert {_}.
Arguments CorrectConv {_}.
Arguments DecidableConv {_}.

Inductive alg_type_check {P} (conv_P : ConvertibleSig P) : ctx P -> typ P -> exp P -> Prop :=             
(** Conversion *)
| atc_conv : `( {{ ⟪ conv_P ⟫ Γ ⊢a M ⟹ A }} ->
                Convert conv_P Γ A B ->
                {{ ⟪ conv_P ⟫ Γ ⊢a M ⟸ B }} )
              
where "⟪ conv_P ⟫ Γ '⊢a' M ⟸ A" := (alg_type_check conv_P Γ A M) (in custom judg) : type_scope

with alg_type_infer {P} (conv_P : ConvertibleSig P) : ctx P -> typ P -> exp P -> Prop :=
(** Variables *)
| ati_var : `( {{ #x : A @ s ∈ Γ }} ->
               {{ ⟪ conv_P ⟫ Γ ⊢a #x ⟹ A }} )

(** Sorts *)
| ati_st : `( Ax_typ P s1 s2 ->
              {{ ⟪ conv_P ⟫  Γ ⊢a Sort@s1 ⟹ Sort@s2 }} )
             
(** Functions *)
| atc_pi : `( forall {r : Ru_pi P s1 s2 s3},
                 {{ ⟪ conv_P ⟫  Γ ⊢a A ⟸ Sort@s1 }} ->
                 {{ ⟪ conv_P ⟫  Γ, A@s1 ⊢a B ⟸ Sort@s2 }} ->
                 {{ ⟪ conv_P ⟫  Γ ⊢a Π r A B ⟹ Sort@s3 }} )

| ati_lam : `( forall {r : Ru_pi P s1 s2 s3},
                  {{ ⟪ conv_P ⟫ Γ ⊢a A ⟸ Sort@s1 }} ->
                  {{ ⟪ conv_P ⟫ Γ, A@s1 ⊢a B ⟸ Sort@s2 }} ->
                  {{ ⟪ conv_P ⟫ Γ, A@s1 ⊢a M ⟹ B }} ->
                  {{ ⟪ conv_P ⟫ Γ ⊢a λ r A M ⟹ Π r A B }} )
             
| ati_app : `( forall {r : Ru_pi P s1 s2 s3},
                  {{ ⟪ conv_P ⟫ Γ ⊢a M ⟹ Π r A B }} ->
                  {{ ⟪ conv_P ⟫ Γ ⊢a N ⟸ A }} ->
                  {{ ⟪ conv_P ⟫ Γ ⊢a M N ⟹ B[Id,,N] }} )
                  
(** Naturals *)
| ati_nat : `( Ru_nat P s ->
               {{ ⟪ conv_P ⟫ Γ ⊢a ℕ ⟹ Sort@s }} )
| ati_zero : `( Ru_nat P s ->
                {{ ⟪ conv_P ⟫ Γ ⊢a zero ⟹ ℕ }} )
| ati_succ : `( Ru_nat P s ->
                {{ ⟪ conv_P ⟫ Γ ⊢a M ⟹ ℕ }} ->
                {{ ⟪ conv_P ⟫ Γ ⊢a succ M ⟹ ℕ }} )
| ati_rec : `( Ru_nat P s ->
               {{ ⟪ conv_P ⟫ Γ, ℕ@s ⊢a A ⟸ Sort@s' }} ->
               {{ ⟪ conv_P ⟫ Γ ⊢a MZ ⟸ A[Id,,zero] }} ->
               {{ ⟪ conv_P ⟫ Γ, ℕ@s, A@s' ⊢a MS ⟸ A[Wk∘Wk,,succ #1] }} ->
               {{ ⟪ conv_P ⟫ Γ ⊢a N ⟹ ℕ }} ->
               {{ ⟪ conv_P ⟫ Γ ⊢a rec N return A | zero -> MZ | succ -> MS end ⟹ A[Id,,N] }} )
where "⟪ conv_P ⟫ Γ '⊢a' M ⟹ A" := (alg_type_infer conv_P Γ A M) (in custom judg) : type_scope.


#[export]
Hint Constructors alg_type_check alg_type_infer : mcpts.

Scheme alg_type_check_mut_ind := Induction for alg_type_check Sort Prop
with alg_type_infer_mut_ind := Induction for alg_type_infer Sort Prop.
Combined Scheme alg_type_mut_ind from
  alg_type_check_mut_ind,
  alg_type_infer_mut_ind.
