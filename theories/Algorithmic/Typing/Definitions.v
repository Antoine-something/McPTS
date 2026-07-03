From McPTS Require Import PtsSignature.
From McPTS.Algorithmic.Subtyping Require Export Definitions.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Export NbE.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

Reserved Notation "Γ '⊢a' M ⟹ A" (in custom judg at level 80, Γ custom exp, M custom exp, A custom nf).
Reserved Notation "Γ '⊢a' M ⟸ A" (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp).
Reserved Notation "Γ '⊢aty' A" (in custom judg at level 80, Γ custom exp, A custom nf).

Generalizable All Variables.

Inductive alg_type_check {P} : ctx P -> typ P -> exp P -> Prop :=             
(** Conversion *)
| atc_conv : `( {{ Γ ⊢a M ⟹ A }} ->
                {{ Γ ⊢a A ⊆ B }} ->
                {{ Γ ⊢a M ⟸ B }} )
              
where "Γ '⊢a' M ⟸ A" := (alg_type_check Γ A M) (in custom judg) : type_scope

with alg_type_infer {P} : ctx P -> nf P -> exp P -> Prop :=
(** Variables *)
| ati_var : `( {{ #x : A @ s ∈ Γ }} ->
               nbe_ty Γ A B ->
               {{ Γ ⊢a #x ⟹ B }} )

(** Sorts *)
| ati_st : `( Ax_typ P s1 s2 ->
              {{  Γ ⊢a Sort@s1 ⟹ Sort@s2 }} )
             
(** Functions *)
| atc_pi : `( forall {r : Ru_pi P s1 s2 s3},
                 {{  Γ ⊢a A ⟸ Sort@s1 }} ->
                 {{  Γ, A@s1 ⊢a B ⟸ Sort@s2 }} ->
                 {{  Γ ⊢a Π r A B ⟹ Sort@s3 }} )

| ati_lam : `( forall {r : Ru_pi P s1 s2 s3},
                  {{ Γ ⊢a A ⟸ Sort@s1 }} ->
                  {{ Γ, A@s1 ⊢a B ⟸ Sort@s2 }} ->
                  {{ Γ, A@s1 ⊢a M ⟸ B }} ->
                  nbe {{{ Γ, A@s1 }}} B {{{ Sort@s2 }}} D ->
                  nbe Γ A {{{ Sort@s1 }}} C ->
                  {{ Γ ⊢a λ r A B M ⟹ Π r C D }} )
             
| ati_app : `( forall {r : Ru_pi P s1 s2 s3},
                  {{ Γ ⊢a M ⟹ Π r A B }} ->
                  {{ Γ ⊢a N ⟸ A }} ->
                  nbe_ty Γ {{{ B[Id,,N] }}} C ->
                  {{ Γ ⊢a M N ⟹ C }} )
                  
(** Naturals *)
| ati_nat : `( Ru_nat P s ->
               {{ Γ ⊢a ℕ ⟹ Sort@s }} )
| ati_zero : `( Ru_nat P s ->
                {{ Γ ⊢a zero ⟹ ℕ }} )
| ati_succ : `( Ru_nat P s ->
                {{ Γ ⊢a M ⟸ ℕ }} ->
                {{ Γ ⊢a succ M ⟹ ℕ }} )
| ati_rec : `( Ru_nat P s ->
               {{ Γ, ℕ@s ⊢a A ⟹ Sort@s' }} ->
               st_subtyp s' s'' ->
               {{ Γ ⊢a MZ ⟸ A[Id,,zero] }} ->
               {{ Γ, ℕ@s, A@s'' ⊢a MS ⟸ A[Wk∘Wk,,succ #1] }} ->
               {{ Γ ⊢a N ⟸ ℕ }} ->
               nbe_ty Γ {{{ A[Id,,N] }}} B ->
               {{ Γ ⊢a rec N return A | zero -> MZ | succ -> MS end ⟹ B }} )
where "Γ '⊢a' M ⟹ A" := (alg_type_infer Γ A M) (in custom judg) : type_scope.

#[export]
Hint Constructors alg_type_check alg_type_infer : mcpts.

Inductive alg_wf_type {P} : ctx P -> typ P -> Prop :=
| awt_sort : `( {{ Γ ⊢aty Sort@s }} )
| awt_sorted : `( {{ Γ ⊢a A ⟹ Sort@s }} ->
                  {{ Γ ⊢aty A }} )
where "Γ '⊢aty' A" := (alg_wf_type Γ A) (in custom judg) : type_scope.



Scheme alg_type_check_mut_ind := Induction for alg_type_check Sort Prop
with alg_type_infer_mut_ind := Induction for alg_type_infer Sort Prop.
Combined Scheme alg_type_mut_ind from
  alg_type_check_mut_ind,
  alg_type_infer_mut_ind.
