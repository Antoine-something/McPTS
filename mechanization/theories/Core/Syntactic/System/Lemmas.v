From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic.System Require Import Definitions.

(* Basic properties of contexts *)
Lemma ctx_lookup_lt {P : PtsSig} : forall {Γ : Ctx P} {x : nat} {A : Typ P} {s : St P},
      {{ #x : A :: Sort@s ∈ Γ }} ->
      x < length Γ.
Proof.
  induction 1; simpl; lia.
Qed.
#[export]
  Hint Resolve ctx_lookup_lt : mcpts.


Lemma functional_ctx_lookup {P : PtsSig} : forall {Γ : Ctx P} {x A A' s},
    {{ #x : A :: Sort@s ∈ Γ }} ->
    {{ #x : A' :: Sort@s ∈ Γ }} ->
    A = A'.
Proof with mautosolve.
  intros * Hx Hx'; gen A'.
  induction Hx as [|* ? IHHx]; intros; inversion_clear Hx';
    f_equal;
    intuition.
Qed.


Lemma ctx_decomp {P : PtsSig} : forall {Γ : Ctx P} {A s},
    {{ ⊢ Γ, A :: Sort@s}} -> {{ ⊢ Γ }} /\ exists s, {{ Γ ⊢ A :: Sort@s }}.
Proof with now eauto.
  inversion 1...
Qed.

#[export]
  Hint Resolve ctx_decomp : mcpts.

Corollary ctx_decomp_left {P : PtsSig} : forall {Γ : Ctx P} {A s}, {{ ⊢ Γ , A :: Sort@s}} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

Corollary ctx_decomp_right {P : PtsSig} : forall {Γ : Ctx P} {A s}, {{ ⊢ Γ, A :: Sort@s }} -> exists s, {{ Γ ⊢ A :: Sort@s }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

#[export]
Hint Resolve ctx_decomp_left ctx_decomp_right : mcpts.


(** ** Core Presuppositions *)

(** *** Context Presuppositions *)

Lemma presup_ctx_eq {P : PtsSig} : forall {Γ Δ : Ctx P}, {{ ⊢ Γ ≡ Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; split; econstructor; destruct_pairs; mauto; econstructor; mauto.
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
  induction 1; split; mauto; destruct_pairs; mauto; econstructor; mauto; econstructor; mauto.
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

Lemma presup_exp_ctx {P : PtsSig} : forall {Γ : Ctx P} {M A K}, {{ Γ ⊢ M : A :: K }} -> {{ ⊢ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve presup_exp_ctx : mcpts.

(** and other presuppositions about context well-formedness. *)

Lemma presup_sub_eq_ctx {P : PtsSig} : forall {Γ Δ : Ctx P} {σ σ'}, {{ Γ ⊢s σ ≡ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; split; mauto; try econstructor; mauto; destruct_pairs; mauto; econstructor; mauto.
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

Lemma presup_exp_eq_ctx {P : PtsSig} : forall {Γ : Ctx P} {M M' A K}, {{ Γ ⊢ M ≡ M' : A :: K }} -> {{ ⊢ Γ }}.
Proof with mautosolve 2.
  induction 1...
Qed.

#[export]
Hint Resolve presup_exp_eq_ctx : mcpts.

(** *** Immediate Results of Context Presuppositions *)

Lemma wf_conv {P : PtsSig} : forall (Γ : Ctx P) M A A' K L,
    {{ Γ ⊢ M : A :: K }} ->
    (** The next argument will be removed in SystemOpt *)
    {{ Γ ⊢ A' : K :: L }} ->
    {{ Γ ⊢ A ≡ A' : K :: L }} ->
    {{ Γ ⊢ M : A' :: K }}.
Proof.
  intros.
  eapply wf_exp_conv; mauto.
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

Lemma wf_exp_eq_conv {P : PtsSig} : forall (Γ : Ctx P) M M' A A' K L,
   {{ Γ ⊢ M ≡ M' : A :: K }} ->
   (** The next argument will be removed in SystemOpt *)
   {{ Γ ⊢ A' : K :: L }} ->
   {{ Γ ⊢ A ≡ A' : K :: L }} ->
   {{ Γ ⊢ M ≡ M' : A' :: K }}.
Proof. 
  intros.
  eapply eq_exp_conv; mauto.
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


Lemma eq_ctx_sym {P : PtsSig} : forall {Γ Δ : Ctx P},
    {{ ⊢ Γ ≡ Δ }} ->
    {{ ⊢ Δ ≡ Γ }}
.
Proof with mautosolve.
  intros *; induction 1; econstructor; mauto.
Qed.

    
Add Parametric Morphism {P : PtsSig} (Γ : Ctx P) : (eq_sub Γ)
    with signature eq_ctx ==> eq ==> eq ==> iff as wf_sub_eq_morphism_iff3.
Proof.
  intros Δ1 Δ2 H σ τ.
  split; intros; eapply eq_sub_conv; mauto.
  apply eq_ctx_sym; mauto.
Qed.


Lemma ctx_eq_refl {P : PtsSig} : forall {Γ : Ctx P},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ ≡ Γ }}.
Proof.
  induction 1; econstructor; mauto.
  
  econstructor; mauto 4; econstructor; mauto; econstructor; mauto.
Qed.

#[export]
Hint Resolve ctx_eq_refl : mcpts.


(** *** Lemmas for [exp] of [{{{ Type@i }}}] *)


    
Lemma exp_sub_typ {P : PtsSig} : forall {Δ Γ : Ctx P} {A σ s K},
    {{ Δ ⊢ A : Sort@s :: K }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ [σ]A : Sort@s :: K}}.
Proof with mautosolve 3.  
  intros.  
  econstructor; mauto 3.
  eapply wf_exp_conv; mauto.
  eapply wf_exp_clo; mauto.
  econstructor; mauto.
  
  
  (* We are missing a rule here.
   * The problem is that the rule for sorts does not apply, so there is no other choice but to find a s' such that (s : s') ∈ Ax, but that might not be the case
   *)
  admit.
Admitted.

#[export]
Hint Resolve exp_sub_typ : mcpts.

Lemma presup_ctx_lookup_typ {P : PtsSig} : forall {Γ : Ctx P} {A x s},
    {{ ⊢ Γ }} ->
    {{ #x : A :: Sort@s ∈ Γ }} ->
    {{ Γ ⊢ A :: Sort@s }}.
Proof with mautosolve 4.
  intros * HΓ.
  induction 1; inversion_clear HΓ; eapply exp_sub_typ; mauto; econstructor; mauto; econstructor; mauto.
Qed.

#[export]
Hint Resolve presup_ctx_lookup_typ : mcpts.


Lemma exp_eq_sub_cong_typ1 {P : PtsSig} : forall {Δ Γ : Ctx P} {A A' σ s K},
    {{ Δ ⊢ A ≡ A' : Sort@s :: K }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ [σ]A ≡ [σ]A' : Sort@s :: K }}.
Proof with mautosolve 3.
  intros.
  (* Same problem as before: we cannot just apply conversion because it gives [σ]Sort@s *)
Admitted.

Lemma exp_eq_sub_cong_typ2' {P : PtsSig} : forall {Δ Γ : Ctx P} {A σ τ s K},
    {{ Δ ⊢ A : Sort@s :: K }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≡ τ : Δ }} ->
    {{ Γ ⊢ [σ]A ≡ [τ]A : Sort@s :: K }}.
Proof with mautosolve 3.
  (* Same problem as before *)
Admitted.

Lemma exp_eq_sub_compose_typ {P : PtsSig} : forall {Ψ Δ Γ : Ctx P} {A σ τ s K},
    {{ Ψ ⊢ A : Sort@s :: K }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ [σ][τ]A ≡ [σ∘τ]A : Sort@s :: K }}.
Proof with mautosolve 3.
  (* Same problem *)
Admitted.

#[export]
Hint Resolve exp_eq_sub_cong_typ1 exp_eq_sub_cong_typ2' exp_eq_sub_compose_typ : mcpts.

Lemma exp_eq_sub_compose_weaken_extend_typ {P : PtsSig} : forall {Γ : Ctx P} {σ Δ s1 A s2 B M K1 K2},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 :: K1 }} ->
    {{ Δ ⊢ B : Sort@s2 :: K2 }} ->
    {{ Γ ⊢ M : [σ]B :: Sort@s2}} ->
    {{ Γ ⊢ [Wk][σ,,M]A ≡ [σ]A : Sort@s1 :: K1 }}.
Proof with mautosolve 3.
  (* Same problem *)
Admitted.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_extend_typ : mcpts.


Lemma exp_eq_sub_compose_weaken_id_extend_typ {P : PtsSig} : forall {Γ : Ctx P} {s1 A s2 B M K1 K2},
    {{ Γ ⊢ A : Sort@s1 :: K1 }} ->
    {{ Γ ⊢ B : Sort@s2 :: K2 }} ->
    {{ Γ ⊢ M : B :: Sort@s2 }} ->
    {{ Γ ⊢ [Wk][Id,,M]A ≡ A : Sort@s1 :: K1 }}.
Proof with mautosolve 4.
  intros.  
  assert {{ Γ ⊢ [Id]B : Sort@s2 :: K2 }}.
  {
    eapply wf_exp_conv.
    eapply wf_exp_clo; mauto.
    econstructor.
    mauto.
    eapply wf_typ_exp.
  }
  by mauto 4.
  assert {{ Γ ⊢ B ⊆ B[Id] }} by mauto 4.
  assert {{ Γ ⊢ M : B[Id] }} by mauto 2.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_id_extend_typ : mcpts.
