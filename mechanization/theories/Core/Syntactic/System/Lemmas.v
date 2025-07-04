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
  intros * Hx Hx'; gen s' A'. dependent induction Hx; intros.
  - inversion_clear Hx'. auto. 
  - inversion_clear Hx'; auto.
    eapply IHHx; mauto.
Qed.

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

Lemma wf_exp_eq_conv {P : PtsSig} : forall (Γ : Ctx P) M M' A A' i,
   {{ Γ ⊢ M ≡ M' : A }} ->
   (** The next argument will be removed in SystemOpt *)
   {{ Γ ⊢ A' : Sort@i }} ->
   {{ Γ ⊢ A ≡ A' : Sort@i }} ->
   {{ Γ ⊢ M ≡ M' : A' }}.
Proof. 
  intros.
  eapply eq_exp_conv; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_conv : mcpts.

Lemma wf_sub_eq_conv {P : PtsSig} : forall (Γ : Ctx P) σ σ' Δ Δ',
    {{ Γ ⊢s σ ≡ σ' : Δ }} ->
    {{ ⊢ Δ ≡ Δ' }} ->
    {{ Γ ⊢s σ ≡ σ' : Δ' }}.
Proof.
  intros.
  eapply eq_sub_conv; mauto.
Qed.

#[export]
Hint Resolve wf_sub_eq_conv : mcpts.

Add Parametric Morphism {P : PtsSig} (Γ : Ctx P) : (fun Δ σ τ => eq_sub Γ σ τ Δ)
    with signature eq_ctx ==> eq ==> eq ==> iff as wf_sub_eq_morphism_iff3.
Proof.
  admit.
Admitted.

Lemma ctx_eq_refl {P : PtsSig} : forall {Γ : Ctx P},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ ≡ Γ }}.
Proof.
  induction 1; econstructor; mauto 4.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve ctx_eq_refl : mcpts.


(** *** Lemmas for [exp] of [{{{ Type@i }}}] *)

Lemma exp_sub_typ {P : PtsSig} : forall {Δ Γ : Ctx P} {A σ s},
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ [σ]A : Sort@s }}.
Proof with mautosolve 3.
  intros.
  econstructor; mauto 3.
  econstructor...
  (* We are missing a rule here.
   * The problem is that the rule for sorts does not apply, so there is no other choice but to find a s' such that (s : s') ∈ Ax, but that might not be the case
   *)
  admit.
Admitted.

#[export]
Hint Resolve exp_sub_typ : mcpts.

Lemma presup_ctx_lookup_typ {P : PtsSig} : forall {Γ : Ctx P} {A x s},
    {{ ⊢ Γ }} ->
    {{ #x : A : s ∈ Γ }} ->
    {{ Γ ⊢ A : Sort@s }}.
Proof with mautosolve 4.
  intros * HΓ.  
  induction 1; inversion_clear HΓ; eapply exp_sub_typ; mauto; econstructor; econstructor; assumption.
Qed.

#[export]
Hint Resolve presup_ctx_lookup_typ : mcpts.


Lemma exp_eq_sub_cong_typ1 {P : PtsSig} : forall {Δ Γ : Ctx P} {A A' σ s},
    {{ Δ ⊢ A ≡ A' : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ [σ]A ≡ [σ]A' : Sort@s }}.
Proof with mautosolve 3.
  intros.
  (* Same problem as before: we cannot just apply conversion because it gives [σ]Sort@s *)
Admitted.

Lemma exp_eq_sub_cong_typ2' {P : PtsSig} : forall {Δ Γ : Ctx P} {A σ τ s},
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≡ τ : Δ }} ->
    {{ Γ ⊢ [σ]A ≡ [τ]A : Sort@s }}.
Proof with mautosolve 3.
  (* Same problem as before *)
Admitted.

Lemma exp_eq_sub_compose_typ {P : PtsSig} : forall {Ψ Δ Γ : Ctx P} {A σ τ s},
    {{ Ψ ⊢ A : Sort@s }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ [σ][τ]A ≡ [σ∘τ]A : Sort@s }}.
Proof with mautosolve 3.
  (* Same problem *)
Admitted.

#[export]
Hint Resolve exp_eq_sub_cong_typ1 exp_eq_sub_cong_typ2' exp_eq_sub_compose_typ : mcpts.

Lemma exp_eq_sub_compose_weaken_extend_typ {P : PtsSig} : forall {Γ : Ctx P} {σ Δ s1 A s2 B M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ Δ ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ M : [σ]B }} ->
    {{ Γ ⊢ [Wk][σ,,M]A ≡ [σ]A : Sort@s1 }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ, B : s2 ⊢s Wk : Δ }}.
  {
    econstructor; mauto.
    econstructor; mauto.
  }
  (* Same problem *)
Admitted.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_extend_typ : mcpts.
