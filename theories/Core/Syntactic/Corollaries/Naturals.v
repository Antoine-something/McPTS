From Coq Require Import Setoid Nat.
From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Export SystemOpt.
From McPTS.Core.Syntactic.Corollaries Require Import Substitutions TermStructure.
Import Syntax_Notations.

(** ** Lemmas about well-formedness *)
Lemma wf_exp_nat_sub_lhs {P} : forall {Γ Γ' σ s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ ℕ[σ] : Sort@s }}.
Proof.
  intros; gen_presups; mauto 3.
Qed.
#[export]
Hint Resolve wf_exp_nat_sub_lhs : mcpts.

Lemma wf_exp_zero_sub_lhs {P} : forall {Γ : ctx P} {Γ' σ s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ zero[σ] : ℕ }}.
Proof.
  intros; gen_presups; mauto 3.
Qed.
#[export]
Hint Resolve wf_exp_zero_sub_lhs : mcpts.

Lemma wf_exp_succ_sub_lhs {P} : forall {Γ : ctx P} {Γ' σ M s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ M : ℕ }} ->
    {{ Γ ⊢ (succ M)[σ] : ℕ }}.
Proof.
  intros; gen_presups; mauto 3.
Qed.
#[export]
Hint Resolve wf_exp_succ_sub_lhs : mpts.

Lemma wf_exp_succ_sub_rhs {P} : forall {Γ : ctx P} {Γ' σ M s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ M : ℕ }} ->
    {{ Γ ⊢ succ (M[σ]) : ℕ }}.
Proof.
  intros; gen_presups; mauto 3.
Qed.
#[export]
Hint Resolve wf_exp_succ_sub_rhs : mcpts.


(** ** Lemmas for substitutions involving naturals *)
Lemma wf_typ_eq_natrec_cong_rhs_typ {P} : forall {Γ : ctx P} {M M' A A' s} {r : Ru_nat P s},
    {{ Γ, ℕ ⊢ A ≈ A' }} ->
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢ A[Id,,M] ≈ A'[Id,,M'] }}.
Proof.
  intros.
  gen_presups.
  assert {{ Γ ⊢ ℕ[Id] ≈ ℕ : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ M ≈ M' : ℕ[Id] }} by mauto 3.
  assert {{ Γ ⊢s Id,,M ≈ Id,,M' : Γ, ℕ }} by mauto 3.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_eq_natrec_cong_rhs_typ : mcpts.

Lemma wf_sub_eq_q_compose_nat {P} : forall {Γ : ctx P} {Γ' Γ'' σ τ s} {r : Ru_nat P s},
  {{ Γ' ⊢s σ : Γ }} ->
  {{ Γ'' ⊢s τ : Γ' }} ->
  {{ Γ'', ℕ ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, ℕ }}.
Proof.
  intros.
  assert {{ Γ ⊢ ℕ : Sort@s }} by mauto 4.
  assert {{ Γ'' ⊢ ℕ[σ∘τ] ≈ ℕ : Sort@s }} by mauto 3.
  assert {{ ⊢ Γ'' }} by mauto 2.
  assert {{ Γ'' ⊢ ℕ : Sort@s }} by mauto 3.
  assert {{ Γ'' ⊢ ℕ[σ∘τ] : Sort@s }} by mauto 3.
  assert {{ ⊢ Γ'', ℕ[σ∘τ] ≈ Γ'', ℕ }} by (econstructor; mauto 4).
  mautosolve 4.
Qed.

#[export]
Hint Resolve wf_sub_eq_q_compose_nat : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_q_compose_nat using mauto 4 : mcpts.

Lemma wf_sub_eq_compose_id_zero_sigma_sigma_zero {P} : forall {Γ : ctx P} {Γ' σ},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ ⊢ ℕ }} ->
    {{ Γ' ⊢s (Id,,zero)∘σ ≈ σ,,zero : Γ, ℕ }}.
Proof.
  intros * Hσ Hℕ.
  pose proof wf_typ_nat_inversion Hℕ as [s [r Htriv]]; clear Htriv.
  assert {{ Γ' ⊢s Id∘σ ≈ σ : Γ }} by mauto 3.
  assert {{ Γ' ⊢ zero[σ] ≈ zero : ℕ }} by mauto 3.
  gen_presups.
  transitivity {{{ Id∘σ,,zero[σ] }}}; mauto 3. 
  mauto 4.
Qed.

#[export]
Hint Resolve wf_sub_eq_compose_id_zero_sigma_sigma_zero : mcpts.

Lemma wf_sub_eq_extend_id_zero_compose_sigma {P} : forall {Γ : ctx P} {Γ' σ},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ ⊢ ℕ }} ->
    {{ Γ' ⊢s (Id,,zero)∘σ ≈ σ,,zero : Γ, ℕ }}.
Proof.
  intros * Hσ Hℕ.
  pose proof wf_typ_nat_inversion Hℕ as [s [r Htriv]]; clear Htriv.
  assert {{ Γ ⊢ zero : ℕ }} by mauto 3.
  transitivity {{{ σ,,zero[σ] }}}; mauto 3.
  assert {{ Γ' ⊢ zero[σ] ≈ zero : ℕ }} by mauto 3.
  mauto 3.
Qed.

#[export]
Hint Resolve wf_sub_eq_extend_id_zero_compose_sigma : mcpts.

Lemma wf_typ_eq_nat_beta_succ_rhs_typ_gen_of_sort {P} : forall {Γ : ctx P} {Γ' σ A M N s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ', ℕ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ N : A[σ,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk,,succ #1][σ,,M,,N] ≈ A[σ,,succ M] : Sort@s }}.
Proof.
  intros.
  gen_presup H1.
  pose proof wf_typ_nat_inversion HAwf as [sn [r Htriv]]; clear Htriv.
  assert {{ ⊢ Γ' }} by mauto 3.
  assert {{ Γ', ℕ ⊢s Wk : Γ' }} by mauto 3.
  assert {{ Γ', ℕ, A ⊢s Wk : Γ', ℕ }} by mauto 4.
  assert {{ Γ', ℕ, A ⊢s Wk∘Wk : Γ' }} by mauto 3.
  assert {{ Γ', ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ', ℕ }} by mauto 4.
  assert {{ Γ ⊢s σ,,M : Γ', ℕ }} by mauto 4.
  assert {{ Γ ⊢s σ,,M,,N : Γ', ℕ, A }} by mauto 3.
  autorewrite with mcpts.
  assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M,,N) : Γ', ℕ }} by mauto 3.
  assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M,,N) ≈ ((Wk∘Wk)∘(σ,,M,,N)),,(succ #1)[σ,,M,,N] : Γ', ℕ }} by mauto.
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ Wk∘(Wk∘(σ,,M,,N)) : Γ' }} by mauto 3.
  assert {{ Γ ⊢s Wk∘(σ,,M,,N) ≈ σ,,M : Γ', ℕ }} by (unshelve autorewrite with mcpts; mauto 3).
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ Wk∘(σ,,M) : Γ' }} by (unshelve bulky_rewrite; constructor).
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ σ : Γ' }} by bulky_rewrite.
  assert {{ Γ ⊢ (succ #1)[σ,,M,,N] ≈ succ (#1[σ,,M,,N]) : ℕ }} by mauto 4.
  assert {{ Γ ⊢ (succ #1)[σ,,M,,N] ≈ succ (#0[σ,,M]) : ℕ }} by (bulky_rewrite; mauto 4).
  assert {{ Γ ⊢ (succ #1)[σ,,M,,N] ≈ succ M : ℕ }} by (bulky_rewrite; mauto 3).
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N),,(succ #1)[σ,,M,,N] ≈ σ,,succ M : Γ', ℕ }} by mauto 3.
  assert {{ Γ ⊢ A[(Wk∘Wk,,succ #1)∘(σ,,M,,N)] ≈ A[(Wk∘Wk)∘(σ,,M,,N),,(succ #1)[σ,,M,,N]] }} by mauto 3.
  assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M,,N) ≈ σ,,(succ M) : Γ', ℕ }} by mauto 3.
  transitivity {{{ A[(Wk∘Wk)∘(σ,,M,,N),,(succ #1)[σ,,M,,N]] }}}; mauto 4.
Qed.

#[export]
Hint Resolve wf_typ_eq_nat_beta_succ_rhs_typ_gen_of_sort : mcpts.


(** ** Helper lemmas to deal with recursor *)
Lemma wf_exp_eq_sub_decompose_double_q_with_id_double_extend {P : PtsSig} : forall {Γ : ctx P} {Γ' σ A B C M N L},
    {{ Γ, B, C ⊢ A }} ->
    {{ Γ, B, C ⊢ M : A }} ->
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ' ⊢ N : B[σ] }} ->
    {{ Γ' ⊢ L : C[σ,,N] }} ->
    {{ Γ' ⊢ M[σ,,N,,L] ≈ M[q (q σ)][Id,,N,,L] : A[σ,,N,,L] }}.
Proof.
  intros.
  gen_presups.
  assert {{ Γ ⊢ B }} by mauto 3.

  assert {{ Γ', B[σ] ⊢s q σ : Γ, B }} by mauto 3.
  assert {{ Γ' ⊢s Id,,N : Γ', B[σ] }} by mauto 3.
  assert {{ Γ' ⊢s q σ∘(Id,,N) ≈ σ,,N : Γ, B }} by mauto 3.
  assert {{ Γ, B ⊢ C }} by mauto 3.
  assert {{ Γ' ⊢ C[q σ][Id,,N] }} by mauto 4.  
  assert {{ Γ' ⊢ C[σ,,N] ≈ C[q σ][Id,,N] }} by mauto 4.
  assert {{ Γ' ⊢ L : C[q σ][Id,,N] }} by mauto 3.
  assert {{ Γ' ⊢ L : C[q σ∘(Id,,N)] }} by mauto 3.
  assert {{ Γ' ⊢s Id,,N,,L : Γ', B[σ], C[q σ] }} by mauto 3.
  assert {{ Γ' ⊢s q σ∘(Id,,N) ≈ σ,,N : Γ, B }} by mauto 3.
  assert {{ Γ' ⊢ C[q σ∘(Id,,N)] ≈ C[σ,,N] }} by mauto 3.
  assert {{ Γ' ⊢ C[q σ][Id,,N] ≈ C[σ,,N] }} by mauto 3.
  assert {{ Γ' ⊢s q (q σ)∘(Id,,N,,L) : Γ, B, C }} by mauto 3.
  assert {{ Γ' ⊢s q (q σ)∘(Id,,N,,L) ≈ (q σ∘(Id,,N)),,L : Γ, B, C }} by (eapply sub_decompose_q; mauto 3).
  assert {{ Γ' ⊢s q (q σ)∘(Id,,N,,L) ≈ σ,,N,,L : Γ, B, C }} by (bulky_rewrite; mauto 3).
  assert {{ Γ' ⊢ A[q (q σ)][Id,,N,,L] ≈ A[q (q σ)∘(Id,,N,,L)] }} by mauto 3.
  assert {{ Γ' ⊢s q (q σ)∘(Id,,N,,L) ≈ σ,,N,,L : Γ, B, C }} by mauto 3.
  assert {{ Γ' ⊢ A[q (q σ)∘(Id,,N,,L)] ≈ A[σ,,N,,L] }} by mauto 3.
  assert {{ Γ' ⊢ M[q (q σ)][Id,,N,,L] ≈ M[q (q σ)∘(Id,,N,,L)] : A[q (q σ)∘(Id,,N,,L)] }} by mauto 4.
  assert {{ Γ' ⊢ M[q (q σ)][Id,,N,,L] ≈ M[σ,,N,,L] : A[q (q σ)∘(Id,,N,,L)] }} by (bulky_rewrite; mauto 4).
  symmetry; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_decompose_double_q_with_id_double_extend : mcpts.

Lemma wf_typ_eq_nat_beta_succ_rhs_typ_gen {P} : forall {Γ : ctx P} {Γ' σ A M N s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ', ℕ ⊢ A }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ N : A[σ,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk,,succ #1][σ,,M,,N] ≈ A[σ,,succ M] }}.
Proof.
  intros.
  assert {{ ⊢ Γ' }} by mauto 3.
  assert {{ Γ', ℕ ⊢s Wk : Γ' }} by mauto 3.
  assert {{ Γ', ℕ, A ⊢s Wk : Γ', ℕ }} by mauto 4.
  assert {{ Γ', ℕ, A ⊢s Wk∘Wk : Γ' }} by mauto 3.
  assert {{ Γ', ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ', ℕ }} by mauto 4.
  assert {{ Γ ⊢s σ,,M : Γ', ℕ }} by mauto 4.
  assert {{ Γ ⊢s σ,,M,,N : Γ', ℕ, A }} by mauto 3.
  assert {{ Γ ⊢s σ,,M,,N : Γ', ℕ, A }} by mauto 3.
  autorewrite with mcpts.
  assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M,,N) : Γ', ℕ }} by mauto 3.
  assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M,,N) ≈ ((Wk∘Wk)∘(σ,,M,,N)),,(succ #1)[σ,,M,,N] : Γ', ℕ }} by mauto 4.
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ Wk∘(Wk∘(σ,,M,,N)) : Γ' }} by mauto 3.
  assert {{ Γ ⊢s Wk∘(σ,,M,,N) ≈ σ,,M : Γ', ℕ }} by (autorewrite with mcpts; mauto 3).
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ Wk∘(σ,,M) : Γ' }} by (unshelve bulky_rewrite; constructor).
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ σ : Γ' }} by bulky_rewrite.
  assert {{ Γ ⊢ (succ #1)[σ,,M,,N] ≈ succ (#1[σ,,M,,N]) : ℕ }} by mauto 3.
  assert {{ Γ ⊢ (succ #1)[σ,,M,,N] ≈ succ (#0[σ,,M]) : ℕ }} by (bulky_rewrite; mauto 4).
  assert {{ Γ ⊢ (succ #1)[σ,,M,,N] ≈ succ M : ℕ }} by (bulky_rewrite; mauto 3).
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N),,(succ #1)[σ,,M,,N] ≈ σ,,succ M : Γ', ℕ }} by mauto 3.
  assert {{ Γ ⊢ A[(Wk∘Wk,,succ #1)∘(σ,,M,,N)] ≈ A[(Wk∘Wk)∘(σ,,M,,N),,(succ #1)[σ,,M,,N]] }} by mauto 3.
  assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M,,N) ≈ σ,,(succ M) : Γ', ℕ }} by mauto 3.
  transitivity {{{ A[(Wk∘Wk)∘(σ,,M,,N),,(succ #1)[σ,,M,,N]] }}}; mauto 4.
Qed.
#[export]
Hint Resolve wf_typ_eq_nat_beta_succ_rhs_typ_gen : mcpts.



Lemma wf_typ_eq_q_sigma_then_weak_weak_extend_succ_var_1 {P} : forall {Γ : ctx P} {Γ' σ A s} {r : Ru_nat P s},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ, ℕ ⊢ A }} ->
    {{ Γ', ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q σ)] }}.
Proof.
  intros.
  assert {{ Γ', ℕ ⊢s q σ : Γ, ℕ }} by mauto 3.
  assert {{ Γ', ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Γ', ℕ }} by mauto 3.
  assert {{ Γ', ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[q σ∘(Wk∘Wk,,succ #1)] }} as -> by mauto 3.

  assert {{ Γ', ℕ, A[q σ] ⊢s q (q σ) : Γ, ℕ, A }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 3. 
  assert {{ Γ', ℕ, A[q σ] ⊢ A[Wk∘Wk,,succ #1][q (q σ)] ≈ A[(Wk∘Wk,,succ #1)∘q (q σ)] }} by (symmetry; mauto 3).
  transitivity {{{ A[(Wk∘Wk,,succ #1)∘q (q σ)] }}}; mauto 2.
  mauto 4.
Qed.

#[export]
Hint Resolve wf_typ_eq_q_sigma_then_weak_weak_extend_succ_var_1 : mcpts.

(** ** Derived congruences for recursor *)
Lemma wf_exp_eq_natrec_beta_zero_cong {P} : forall {Γ : ctx P} {A M MZ MS},
    {{ Γ, ℕ ⊢ A }} ->
    {{ Γ ⊢ M ≈ zero : ℕ }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,, succ #1] }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,M] }}.
Proof.
  intros.
  gen_presups.
  pose proof wf_typ_nat_inversion HA as [s [r Htriv]]; clear Htriv.
  assert {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈  rec zero return A | zero -> MZ | succ -> MS end : A[Id,,M] }} as -> by (eapply wf_exp_eq_natrec_cong; mauto 3).
  assert {{ Γ ⊢s Id,,M ≈ Id,,zero : Γ, ℕ }} as -> by mauto 3.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_beta_zero_cong : mcpts.

Lemma wf_exp_eq_natrec_beta_zero_cong_under_sub {P} : forall {Γ : ctx P} {Γ' A σ M MZ MS},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ' ⊢ M ≈ zero : ℕ }} ->
    {{ Γ, ℕ ⊢ A }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,, succ #1] }} ->
    {{ Γ' ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ MZ[σ] : A[σ,,M] }}.
Proof.
  intros.
  gen_presups.
  pose proof wf_typ_nat_inversion HA as [s [r Htriv]]; clear Htriv.
  assert {{ Γ' ⊢ ℕ[σ] ≈ ℕ }} by mauto 3.
  assert {{ Γ' ⊢s (q σ)∘(Id,,M) ≈ σ,,M : Γ, ℕ }} by mauto 4.
  assert {{ Γ' ⊢ A[σ,,M] ≈ A[q σ][Id,,M] }} as -> by mauto 4.
  assert {{ Γ', ℕ ⊢ A[q σ] }} by mauto 3.
  
  (* Proving that {{ Γ' ⊢ MZ[σ] : A[q σ][Id,,zero] }} *) 
  assert {{ Γ' ⊢s (q σ)∘(Id,,zero) ≈ σ,,zero : Γ, ℕ }} by mauto 4.
  assert {{ Γ' ⊢s (Id,,zero)∘σ ≈ Id∘σ,,zero[σ] : Γ, ℕ }} by mauto 4.
  assert {{ Γ' ⊢s Id∘σ ≈ σ : Γ }} by mauto 3.
  assert {{ Γ' ⊢ zero[σ] ≈ zero : ℕ }} by mauto 3.
  assert {{ Γ' ⊢s Id∘σ,,zero[σ] ≈ σ,,zero : Γ, ℕ }} by mauto 4.
  assert {{ Γ' ⊢s (Id,,zero)∘σ ≈ σ,,zero : Γ, ℕ }} by mauto 4.
  assert {{ Γ' ⊢s (q σ)∘(Id,,zero) ≈ (Id,,zero)∘σ : Γ,ℕ }} by mauto 4.
  assert {{ Γ' ⊢s (q σ)∘(Id,,zero) ≈ (Id,,zero)∘σ : Γ, ℕ }} by mauto 3.
  assert {{ Γ' ⊢ A[q σ][Id,,zero] ≈ A[(q σ)∘(Id,,zero)] }} by mauto 4.
  assert {{ Γ' ⊢ A[(q σ)∘(Id,,zero)] ≈ A[(Id,,zero)∘σ] }} by mauto 3.
  assert {{ Γ' ⊢ A[q σ][Id,,zero] ≈ A[(Id,,zero)∘σ] }} by mauto 3.
  assert {{ Γ' ⊢ A[(Id,,zero)∘σ] ≈ A[Id,,zero][σ] }} by mauto 3.
  assert {{ Γ' ⊢ A[q σ][Id,,zero] ≈ A[Id,,zero][σ] }} by mauto 3.
  assert {{ Γ' ⊢ MZ[σ] : A[Id,,zero][σ] }} by mauto 2.
  assert {{ Γ' ⊢ MZ[σ] : A[q σ][Id,,zero] }} by mauto 3.  

  (* Proving that {{ Γ', ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} *)
  assert {{ Γ', ℕ, A[q σ] ⊢s (q σ)∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘(q (q σ)) : Γ, ℕ }} as HqWkWk by mauto 3.
  gen_presup HqWkWk.
  assert {{ Γ', ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[(q σ)∘(Wk∘Wk,,succ #1)] }} by mauto 4.
  assert {{ Γ', ℕ, A[q σ] ⊢ A[(q σ)∘(Wk∘Wk,,succ #1)] ≈ A[(Wk∘Wk,,succ #1)∘(q (q σ))] }} by mauto 3.
  assert {{ Γ', ℕ, A[q σ] ⊢ A[(Wk∘Wk,,succ #1)∘(q (q σ))] ≈ A[Wk∘Wk,,succ #1][q (q σ)] }} by mauto 3.
  assert {{ Γ', ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q σ)] }} by mauto 3.
  assert {{ Γ', ℕ, A[q σ] ⊢ MS[q (q σ)] : A[Wk∘Wk,,succ #1][q (q σ)] }} by mauto 4.
  assert {{ Γ', ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by mauto 3.
  mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_beta_zero_cong_under_sub : mcpts.


Lemma wf_exp_eq_natrec_beta_succ_cong {P} : forall {Γ : ctx P} {A M M' MZ MS},
    {{ Γ, ℕ ⊢ A }} ->
    {{ Γ ⊢ M ≈ succ M' : ℕ }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,, succ #1] }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M',,rec M' return A | zero -> MZ | succ -> MS end] : A[Id,,M] }}.
Proof.
  intros.
  gen_presups.
  pose proof wf_typ_nat_inversion HA as [s [r Htriv]]; clear Htriv.
  pose proof wf_exp_succ_inversion HN as [].
  assert {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈  rec succ M' return A | zero -> MZ | succ -> MS end : A[Id,,M] }} as -> by (eapply wf_exp_eq_natrec_cong; mauto 3).
  assert {{ Γ ⊢s Id,,M ≈ Id,,succ M' : Γ, ℕ }} as -> by mauto 3.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_beta_succ_cong : mcpts.

Lemma wf_exp_eq_natrec_beta_succ_cong_under_sub {P} : forall {Γ : ctx P} {Γ' A σ M M' MZ MS},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ' ⊢ M ≈ succ M' : ℕ }} ->
    {{ Γ, ℕ ⊢ A }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,, succ #1] }} ->
    {{ Γ' ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ MS[q (q σ)][Id,,M',,rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end] : A[σ,,M] }}.
Proof.
  intros.
  gen_presups.
  pose proof wf_typ_nat_inversion HA as [s [r Htriv]]; clear Htriv.
  pose proof wf_exp_succ_inversion HN as [].

  assert {{ Γ' ⊢s (q σ)∘(Id,,M) ≈ σ,,M : Γ, ℕ }} as <- by mauto 4.
  assert {{ Γ' ⊢ A[(q σ)∘(Id,,M)] ≈ A[q σ][Id,,M] }} as -> by mauto 4.

  assert {{ Γ' ⊢ MZ[σ] : A[Id,,zero][σ] }} by mauto 3.
  assert {{ Γ' ⊢ ℕ[σ] ≈ ℕ }} by mauto 3.
  assert {{ Γ' ⊢s (Id,,zero)∘σ ≈ σ,,zero : Γ, ℕ }} by mauto 3.
  assert {{ Γ' ⊢s σ,, zero ≈ (q σ)∘(Id,,zero) : Γ, ℕ }} by (symmetry; eapply wf_sub_eq_q_sigma_id_extend; mauto 3).
  assert {{ Γ' ⊢s (Id,,zero)∘σ ≈ (q σ)∘(Id,,zero) : Γ, ℕ }} by (etransitivity; mauto 3).
  assert {{ Γ' ⊢ A[Id,,zero][σ] ≈ A[(Id,,zero)∘σ] }} by mauto 3.
  assert {{ Γ' ⊢ A[(Id,,zero)∘σ] ≈ A[(q σ)∘(Id,,zero)] }} by mauto 3.
  assert {{ Γ' ⊢ A[(q σ)∘(Id,,zero)] ≈ A[q σ][Id,,zero] }} by mauto 4.
  assert {{ Γ' ⊢ A[Id,,zero][σ] ≈ A[q σ][Id,,zero] }} by (do 2 etransitivity; mauto 3).  
  assert {{ Γ' ⊢ MZ[σ] : A[q σ][Id,,zero] }} by mauto 3.

  assert {{ Γ', ℕ, A[q σ] ⊢ MS[q (q σ)] : A[Wk∘Wk,,succ #1][q (q σ)] }} by mauto 4.
  assert {{ Γ', ℕ ⊢s q σ : Γ, ℕ }} by mauto 3.
  assert {{ Γ', ℕ, A[q σ] ⊢s q (q σ) : Γ, ℕ, A }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 3.
  assert {{ Γ', ℕ, A[q σ] ⊢ A[Wk∘Wk,,succ #1][q (q σ)] ≈ A[(Wk∘Wk,,succ #1)∘(q (q σ))] }} by mauto 3.
  assert {{ Γ', ℕ, A[q σ] ⊢s q σ∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘q (q σ) : Γ, ℕ }} by mauto 3.
  assert {{ Γ', ℕ, A[q σ] ⊢ A[q σ∘(Wk∘Wk,,succ #1)] ≈ A[(Wk∘Wk,,succ #1)∘q (q σ)] }} by mauto 3.
  assert {{ Γ', ℕ, A[q σ] ⊢ A[q σ∘(Wk∘Wk,,succ #1)] ≈ A[q σ][Wk∘Wk,,succ #1] }} by mauto 4.
  assert {{ Γ', ℕ, A[q σ] ⊢ A[Wk∘Wk,,succ #1][q (q σ)] ≈ A[q σ][Wk∘Wk,,succ #1] }} by (do 2 etransitivity; mauto 3).
  assert {{ Γ', ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by mauto 3.
  eapply wf_exp_eq_natrec_beta_succ_cong; mauto 3.
Qed.
  
#[export]
Hint Resolve wf_exp_eq_natrec_beta_succ_cong_under_sub : mcpts.
