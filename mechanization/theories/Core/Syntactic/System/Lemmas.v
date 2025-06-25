From McPTS Require Import LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.PTSSignature Require Import Signature.
From McPTS.Core.Syntactic.System Require Import Definitions.

(* Basic properties of contexts *)
Lemma ctx_lookup_lt {P : PtsSig} : forall {Γ : Ctx P} {x : nat} {A : Typ P} {s : St P},
      {{ #x : A : s ∈ Γ }} ->
      x < length Γ.
Proof.
  induction 1; simpl; lia.
Qed.
#[export]
  Hint Resolve ctx_lookup_lt : mcpts.


Lemma functional_ctx_lookup {P : PtsSig} : forall {Γ : Ctx P} {x A A' s},
    {{ #x : A : s ∈ Γ }} ->
    {{ #x : A' : s ∈ Γ }} ->
    A = A'.
Proof with mautosolve.
  intros * Hx Hx'; gen A'.
  induction Hx as [|* ? IHHx]; intros; inversion_clear Hx';
    f_equal;
    intuition.
Qed.


Lemma ctx_decomp {P : PtsSig} : forall {Γ : Ctx P} {A s},
    {{ ⊢ Γ, A : s}} -> {{ ⊢ Γ }} /\ exists i, {{ Γ ⊢ A : Sort@i }}.
Proof with now eauto.
  inversion 1...
Qed.

#[export]
  Hint Resolve ctx_decomp : mcpts.

Corollary ctx_decomp_left {P : PtsSig} : forall {Γ : Ctx P} {A s}, {{ ⊢ Γ , A : s}} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

Corollary ctx_decomp_right {P : PtsSig} : forall {Γ : Ctx P} {A s}, {{ ⊢ Γ, A : s }} -> exists i, {{ Γ ⊢ A : Sort@i }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

#[export]
Hint Resolve ctx_decomp_left ctx_decomp_right : mcpts.


(** ** Core Presuppositions *)

(** *** Context Presuppositions *)

Lemma presup_ctx_eq {P : PtsSig} : forall {Γ Δ : Ctx P}, {{ ⊢ Γ ≡ Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; split; econstructor; destruct_pairs; assumption.
Qed.

Corollary presup_ctx_eq_left {P : PtsSig} : forall {Γ Δ : Ctx P}, {{ ⊢ Γ ≡ Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_ctx_eq...
Qed.

Corollary presup_ctx_eq_right {P : PtsSig} : forall {Γ Δ : Ctx P}, {{ ⊢ Γ ≡ Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_ctx_eq...
Qed.

#[export]
Hint Resolve presup_ctx_eq presup_ctx_eq_left presup_ctx_eq_right : mcpts.

Lemma presup_sub {P : PtsSig}: forall {Γ Δ : Ctx P} {σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; split; mauto; destruct_pairs; mauto; econstructor; assumption.
Qed.

Corollary presup_sub_left {P : PtsSig} : forall {Γ Δ : Ctx P} {σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_sub...
Qed.

Corollary presup_sub_right {P : PtsSig} : forall {Γ Δ : Ctx P} {σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_sub...
Qed.

#[export]
Hint Resolve presup_sub presup_sub_left presup_sub_right : mcpts.

(** With [presup_sub], we can prove similar for [exp]. *)

Lemma presup_exp_ctx {P : PtsSig} : forall {Γ : Ctx P} {M A}, {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve presup_exp_ctx : mcpts.

(** and other presuppositions about context well-formedness. *)

Lemma presup_sub_eq_ctx {P : PtsSig} : forall {Γ Δ : Ctx P} {σ σ'}, {{ Γ ⊢s σ ≡ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; split; mauto; try econstructor; mauto; destruct_pairs; mauto.
Qed.

Corollary presup_sub_eq_ctx_left {P : PtsSig} : forall {Γ Δ : Ctx P} {σ σ'}, {{ Γ ⊢s σ ≡ σ' : Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_sub_eq_ctx...
Qed.

Corollary presup_sub_eq_ctx_right {P : PtsSig} : forall {Γ Δ : Ctx P} {σ σ'}, {{ Γ ⊢s σ ≡ σ' : Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_sub_eq_ctx...
Qed.

#[export]
Hint Resolve presup_sub_eq_ctx presup_sub_eq_ctx_left presup_sub_eq_ctx_right : mcpts.

Lemma presup_exp_eq_ctx {P : PtsSig} : forall {Γ : Ctx P} {M M' A}, {{ Γ ⊢ M ≡ M' : A }} -> {{ ⊢ Γ }}.
Proof with mautosolve 2.
  induction 1...
Qed.

#[export]
Hint Resolve presup_exp_eq_ctx : mcpts.

(** *** Immediate Results of Context Presuppositions *)

Lemma wf_conv {P : PtsSig} : forall (Γ : Ctx P) M A i A',
    {{ Γ ⊢ M : A }} ->
    (** The next argument will be removed in SystemOpt *)
    {{ Γ ⊢ A' : Sort@i }} ->
    {{ Γ ⊢ A ≡ A' : Sort@i }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
  intros.
  econstructor; mauto.
  econstructor; mauto.  
Qed.

#[export]
Hint Resolve wf_conv : mcpts.

Lemma wf_sub_conv {P : PtsSig} : forall (Γ : Ctx P) σ Δ Δ',
  {{ Γ ⊢s σ : Δ }} ->
  {{ ⊢ Δ ≡ Δ' }} ->
  {{ Γ ⊢s σ : Δ' }}.
Proof.
  intros.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_sub_conv : mcpts.
