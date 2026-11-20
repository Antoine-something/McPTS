From Coq Require Import Setoid Nat.
From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

(** ** Identity does nothing *)
Lemma wf_sub_invert_compose_id {P : PtsSig} : forall {Γ : ctx P} {Γ' σ},
    {{ Γ ⊢s σ∘Id : Γ' }} ->
    {{ Γ ⊢s σ : Γ' }}.
Proof.
  intros * [? []]%wf_sub_compose_inversion.
  mauto 4.
Qed.

#[export]
Hint Resolve wf_sub_invert_compose_id : mcpts.

Add Parametric Morphism {P : PtsSig} (Γ1 : ctx P) Γ2 Γ3 : a_compose
    with signature wf_sub_eq Γ2 Γ3 ==> wf_sub_eq Γ1 Γ2 ==> wf_sub_eq Γ1 Γ3 as sub_compose_cong.
Proof. mauto. Qed.

(** ** Derived equality rules *)
Lemma wf_sub_eq_q_cong {P : PtsSig} : forall {Γ' : ctx P} {A Γ σ σ'},
    {{ Γ' ⊢ A }} ->
    {{ Γ ⊢s σ ≈ σ' : Γ' }} ->
    {{ Γ, A[σ] ⊢s q σ ≈ q σ' : Γ', A }}.
Proof.
  intros. gen_presup H0.
  econstructor; mauto 3.
  - econstructor; mauto 4.
  - assert {{ #0 : A[σ][Wk] ∈ Γ, A[σ] }} by mauto.
    assert {{ Γ, A[σ] ⊢ #0 ≈ #0 : A[σ][Wk] }} by mauto.
    assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 3.    
    eapply wf_exp_eq_conv_typ_eq'; mauto 3.
Qed.

#[export]
Hint Resolve wf_sub_eq_q_cong : mcpts.

Lemma sub_decompose_q {P : PtsSig} : forall {Γ : ctx P} {Γ' Γ'' A σ τ M},
  {{ Γ ⊢ A }} ->
  {{ Γ' ⊢s σ : Γ }} ->
  {{ Γ'' ⊢s τ : Γ' }} ->
  {{ Γ'' ⊢ M : A[σ][τ] }} ->
  {{ Γ'' ⊢s (q σ)∘(τ,,M) ≈ σ∘τ,,M : Γ, A }}.
Proof.
  intros. gen_presups.
  simpl.
  assert {{ ⊢ Γ', A[σ] }} by mauto 3.
  assert {{ Γ', A[σ] ⊢s Wk : Γ' }} by mauto 3.
  assert {{ Γ', A[σ] ⊢s σ∘Wk : Γ }} by mauto 3.
  rewrite wf_sub_eq_extend_compose; mauto 3.

  assert {{ Γ'' ⊢s τ,,M : Γ', A[σ] }} by mauto 3.
  assert {{ Γ'' ⊢s (σ∘Wk)∘(τ,,M) ≈ σ∘(Wk∘(τ,,M)) : Γ }} by mauto 3.
  assert {{ Γ'' ⊢s Wk∘(τ,,M) ≈ τ : Γ' }} by mauto 3.
  assert {{ Γ'' ⊢s σ∘(Wk∘(τ,,M)) ≈ σ∘τ : Γ }} by mauto 3.
  assert {{ Γ'' ⊢s (σ∘Wk)∘(τ,,M) ≈ σ∘τ : Γ}} by (etransitivity; mauto 2).
  assert {{ Γ'' ⊢ #0[τ,,M] ≈ M : A[σ][τ] }} by mauto 3.
  assert {{ Γ ⊢ A ≈ A }} by mauto 2.
  assert {{ Γ'' ⊢ A[σ][τ] ≈ A[σ∘τ] }} by mauto 2.
  assert {{ Γ'' ⊢ A[σ∘τ] ≈ A[(σ∘Wk)∘(τ,,M)] }} by mauto 3.
  assert {{ Γ'' ⊢ A[σ][τ] ≈ A[(σ∘Wk)∘(τ,,M)]  }} by (etransitivity; mauto 2).
  mauto 3.  
Qed.

#[export]
Hint Resolve sub_decompose_q : mcpts.
#[local]
Hint Rewrite -> @sub_decompose_q using mauto : mcpts.

Lemma wf_sub_eq_p_q_sigma_compose_tau_extend {P : PtsSig} : forall {Γ'' : ctx P} {τ Γ' M A σ Γ},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ'' ⊢s τ : Γ' }} ->
    {{ Γ ⊢ A }} ->
    {{ Γ'' ⊢ M : A[σ][τ] }} ->
    {{ Γ'' ⊢s Wk∘(q σ∘(τ,,M)) ≈ σ∘τ : Γ }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ', A[σ] ⊢s q σ : Γ, A }} by mauto 2.
  assert {{ Γ'' ⊢s τ,,M : Γ', A[σ] }} by mauto 3.
  transitivity {{{ Wk∘((σ∘τ),,M) }}}; [| autorewrite with mcpts; mauto 3].
  eapply wf_sub_eq_compose_cong; [| mauto 2].
  autorewrite with mcpts.
  econstructor; mauto 3.
  assert {{ Γ'' ⊢ A[σ∘τ] ≈ A[σ][τ] }} by mauto.
  eapply wf_exp_eq_conv; mauto 4.
Qed.

#[export]
Hint Resolve wf_sub_eq_p_q_sigma_compose_tau_extend : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_p_q_sigma_compose_tau_extend using mauto 4 : mcpts.

Lemma wf_sub_eq_q_compose {P : PtsSig} : forall {Γ : ctx P} {Γ' Γ'' σ τ A},
  {{ Γ ⊢ A }} ->
  {{ Γ' ⊢s σ : Γ }} ->
  {{ Γ'' ⊢s τ : Γ' }} ->
  {{ Γ'', A[σ∘τ] ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, A }}.
Proof.
  intros.
  assert {{ ⊢ Γ'' }} by mauto 2.
  assert {{ Γ'' ⊢ A[σ∘τ] ≈ A[σ][τ] }} by mauto.
  assert {{ ⊢ Γ'', A[σ][τ] }} by mauto 4.
  assert {{ ⊢ Γ'', A[σ∘τ] ≈ Γ'', A[σ][τ] }} as -> by mauto.
  assert {{ ⊢Γ' }} by mauto 3.
  assert {{ ⊢ Γ', A[σ] }} by mauto 3.
  assert {{ Γ', A[σ] ⊢s Wk : Γ' }} by mauto 3.
  assert {{ Γ', A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 3.
  assert {{ Γ', A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto 3.
  assert {{ Γ'' ⊢ A[σ][τ] }} by mauto 4.
  assert {{ Γ'', A[σ][τ] ⊢s Wk : Γ'' }} by mauto 3.
  transitivity {{{ ((σ∘Wk)∘q τ),,#0[q τ] }}}; [econstructor; mauto 3 |].
  symmetry; econstructor; mauto 3; symmetry.
  - transitivity {{{ σ∘(Wk∘q τ) }}}; [mauto 4 |].
    transitivity {{{ σ∘(τ∘Wk) }}}; [| mauto 3].
    econstructor; mauto 3.
  - assert {{ Γ'', A[σ][τ] ⊢s (σ∘τ)∘Wk ≈ σ∘(τ∘Wk) : Γ }} by mauto 3.
    gen_presup H10.
    assert {{ Γ'', A[σ][τ] ⊢s τ∘Wk : Γ' }} by mauto 3.
    assert {{ Γ'', A[σ][τ] ⊢s (σ∘τ)∘Wk : Γ }} by mauto 3.
    assert {{ Γ'', A[σ][τ] ⊢ A[(σ∘τ)∘Wk] ≈ A[σ∘(τ∘Wk)] }} by mauto 3.
    assert {{ Γ'', A[σ][τ] ⊢ A[σ∘(τ∘Wk)] ≈ A[σ][τ∘Wk] }} by mauto 3.
    assert {{ Γ'', A[σ][τ] ⊢ A[(σ∘τ)∘Wk] ≈ A[σ][τ∘Wk] }} by mauto 3.
    assert {{ Γ'', A[σ][τ] ⊢ A[(σ∘τ)∘Wk] ≈ A[σ∘τ][Wk] }} by mauto.
    assert {{ Γ'', A[σ][τ] ⊢ A[σ∘τ][Wk] ≈ A[σ][τ][Wk] }} by mauto 3.
    eapply @wf_exp_eq_conv_typ_eq with (A := {{{ A[σ][τ∘Wk] }}}); mauto 3.
    eapply wf_exp_eq_var_0_sub; mauto 3.
Qed.

#[export]
Hint Resolve wf_sub_eq_q_compose : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_q_compose using mauto 4 : mcpts.
