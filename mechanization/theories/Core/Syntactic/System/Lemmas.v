From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic.System Require Import Definitions.

(** ** Basic Context Properties *)

Lemma ctx_lookup_lt {P : PtsSig} : forall {Γ : Ctx P} {A x s},
    {{ #x : A :: Sort@s ∈ Γ }} ->
    x < length Γ.
Proof.
  induction 1; simpl; lia.
Qed.
#[export]
Hint Resolve ctx_lookup_lt : mctt.

Lemma functional_ctx_lookup_typ {P : PtsSig} : forall {Γ : Ctx P} {A A' x s s'},
    {{ #x : A :: Sort@s ∈ Γ }} ->
    {{ #x : A' :: Sort@s' ∈ Γ }} ->
    A = A'.
Proof with mautosolve.
  intros * Hx Hx'; gen s' A'.
  induction Hx as [|* ? IHHx]; intros; inversion_clear Hx';
    f_equal;
    intuition.
Qed.


Lemma functional_ctx_lookup_st {P : PtsSig} : forall {Γ : Ctx P} {A A' x s s'},
    {{ #x : A :: Sort@s ∈ Γ }} ->
    {{ #x : A' :: Sort@s' ∈ Γ }} ->
    s = s'.
Proof with mautosolve.
  intros * Hx Hx'; gen s' A'.
  induction Hx as [|* ? IHHx]; intros; inversion_clear Hx'.
  - admit.
  - eapply IHHx; mauto.
Admitted.


Lemma functional_ctx_lookup {P : PtsSig} : forall {Γ : Ctx P} {A A' x s s'},
    {{ #x : A :: Sort@s ∈ Γ }} ->
    {{ #x : A' :: Sort@s' ∈ Γ }} ->
    A = A' /\ s = s'.
Proof.
  intros; split.
  - eapply functional_ctx_lookup_typ; mauto.
  - eapply functional_ctx_lookup_st; mauto.
Qed.



Lemma ctx_decomp {P : PtsSig} : forall {Γ : Ctx P} {A s}, {{ ⊢ Γ, A :: Sort@s }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ A : Sort@s }}.
Proof with now eauto.
  inversion 1...
Qed.

#[export]
Hint Resolve ctx_decomp : mctt.

Corollary ctx_decomp_left {P : PtsSig} : forall {Γ : Ctx P} {A s}, {{ ⊢ Γ , A :: Sort@s }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

Corollary ctx_decomp_right {P : PtsSig} : forall {Γ : Ctx P} {A s}, {{ ⊢ Γ, A :: Sort@s }} -> {{ Γ ⊢ A : Sort@s }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

#[export]
Hint Resolve ctx_decomp_left ctx_decomp_right : mctt.



(** ** Core Presuppositions *)

(** *** Context Presuppositions *)

Lemma presup_ctx_eq {P : PtsSig} : forall {Γ Δ : Ctx P}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_ctx_eq_left : forall {Γ Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_ctx_eq...
Qed.

Corollary presup_ctx_eq_right : forall {Γ Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_ctx_eq...
Qed.

#[export]
Hint Resolve presup_ctx_eq presup_ctx_eq_left presup_ctx_eq_right : mctt.
