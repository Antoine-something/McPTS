From McPTS Require Import PtsSignature.
From McPTS.Algorithmic.Subtyping Require Export Definitions.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Export NbE.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.


Reserved Notation "⟪ pred_P ⟫ Γ '⊢a' M ⟹ A" (in custom judg at level 80, pred_P constr, Γ custom exp, M custom exp, A custom nf).
Reserved Notation "⟪ pred_P ⟫ Γ '⊢a' M ⟸ A" (in custom judg at level 80, pred_P constr, Γ custom exp, M custom exp, A custom exp).

Generalizable All Variables.

(* Record ConvertibleSig (P : PtsSig) : Type := *)
(*   mkConvertibleSig { *)
(*       Convert : ctx P -> typ P -> typ P -> Prop; *)
(*       CorrectConv : forall Γ A B, Convert Γ A B <-> {{ Γ ⊢ A ⊆ B }}; *)
(*       DecidableConv : forall Γ A B, (Convert Γ A B) \/ ~(Convert Γ A B); *)
(*     }. *)
(* Arguments Convert {_}. *)
(* Arguments CorrectConv {_}. *)
(* Arguments DecidableConv {_}. *)

Inductive alg_type_check {P} (pred_P : PredicativeSig P) : ctx P -> typ P -> exp P -> Prop :=             
(** Conversion *)
| atc_conv : `( {{ ⟪ pred_P ⟫ Γ ⊢a M ⟹ A }} ->
                {{ Γ ⊢a A ⊆ B }} ->
                {{ ⟪ pred_P ⟫ Γ ⊢a M ⟸ B }} )
              
where "⟪ pred_P ⟫ Γ '⊢a' M ⟸ A" := (alg_type_check pred_P Γ A M) (in custom judg) : type_scope

with alg_type_infer {P} (pred_P : PredicativeSig P) : ctx P -> nf P -> exp P -> Prop :=
(** Variables *)
| ati_var : `( {{ #x : A @ s ∈ Γ }} ->
               nbe_ty Γ A B ->
               {{ ⟪ pred_P ⟫ Γ ⊢a #x ⟹ B }} )

(** Sorts *)
| ati_st : `( Ax_typ P s1 s2 ->
              {{ ⟪ pred_P ⟫  Γ ⊢a Sort@s1 ⟹ Sort@s2 }} )
             
(** Functions *)
| atc_pi : `( forall {r : Ru_pi P s1 s2 s3},
                 {{ ⟪ pred_P ⟫  Γ ⊢a A ⟸ Sort@s1 }} ->
                 {{ ⟪ pred_P ⟫  Γ, A@s1 ⊢a B ⟸ Sort@s2 }} ->
                 {{ ⟪ pred_P ⟫  Γ ⊢a Π r A B ⟹ Sort@s3 }} )

| ati_lam : `( forall {r : Ru_pi P s1 s2 s3},
                  {{ ⟪ pred_P ⟫ Γ ⊢a A ⟸ Sort@s1 }} ->
                  {{ ⟪ pred_P ⟫ Γ, A@s1 ⊢a B ⟸ Sort@s2 }} ->
                  {{ ⟪ pred_P ⟫ Γ, A@s1 ⊢a M ⟹ D }} ->
                  nbe {{{ Γ, A@s1 }}} B {{{ Sort@s2 }}} D ->
                  nbe Γ A {{{ Sort@s1 }}} C ->
                  {{ ⟪ pred_P ⟫ Γ ⊢a λ r A M ⟹ Π r C D }} )
             
| ati_app : `( forall {r : Ru_pi P s1 s2 s3},
                  {{ ⟪ pred_P ⟫ Γ ⊢a M ⟹ Π r A B }} ->
                  {{ ⟪ pred_P ⟫ Γ ⊢a N ⟸ A }} ->
                  nbe_ty Γ {{{ B[Id,,N] }}} C ->
                  {{ ⟪ pred_P ⟫ Γ ⊢a M N ⟹ C }} )
                  
(** Naturals *)
| ati_nat : `( Ru_nat P s ->
               {{ ⟪ pred_P ⟫ Γ ⊢a ℕ ⟹ Sort@s }} )
| ati_zero : `( Ru_nat P s ->
                {{ ⟪ pred_P ⟫ Γ ⊢a zero ⟹ ℕ }} )
| ati_succ : `( Ru_nat P s ->
                {{ ⟪ pred_P ⟫ Γ ⊢a M ⟸ ℕ }} ->
                {{ ⟪ pred_P ⟫ Γ ⊢a succ M ⟹ ℕ }} )
| ati_rec : `( Ru_nat P s ->
               {{ ⟪ pred_P ⟫ Γ, ℕ@s ⊢a A ⟹ Sort@s' }} ->
               {{ ⟪ pred_P ⟫ Γ ⊢a MZ ⟸ A[Id,,zero] }} ->
               {{ ⟪ pred_P ⟫ Γ, ℕ@s, A@s' ⊢a MS ⟸ A[Wk∘Wk,,succ #1] }} ->
               {{ ⟪ pred_P ⟫ Γ ⊢a N ⟸ ℕ }} ->
               nbe_ty Γ {{{ A[Id,,N] }}} B ->
               {{ ⟪ pred_P ⟫ Γ ⊢a rec N return A | zero -> MZ | succ -> MS end ⟹ B }} )
where "⟪ pred_P ⟫ Γ '⊢a' M ⟹ A" := (alg_type_infer pred_P Γ A M) (in custom judg) : type_scope.


#[export]
Hint Constructors alg_type_check alg_type_infer : mcpts.

Scheme alg_type_check_mut_ind := Induction for alg_type_check Sort Prop
with alg_type_infer_mut_ind := Induction for alg_type_infer Sort Prop.
Combined Scheme alg_type_mut_ind from
  alg_type_check_mut_ind,
  alg_type_infer_mut_ind.
