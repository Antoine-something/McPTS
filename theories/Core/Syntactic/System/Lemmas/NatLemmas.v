From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic.System Require Import Definitions Lemmas.Instances Lemmas.CorePresup Lemmas.SortLemmas.
Import Syntax_Notations.

(** * Lemmas for sorts and well-sorted expressions *)
Lemma wf_typ_eq_refl_nat {P : PtsSig} : forall {Γ : ctx P} {s} {r : Ru_nat P s},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ ℕ ≈ ℕ }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_eq_refl_nat : mcpts.

(** ** Invariance of sorts under substitutions *)
Lemma wf_typ_subtyp_nat_sub_left {P} : forall {Γ : ctx P} {Γ' σ s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ ℕ[σ] ⊆ ℕ }}.
Proof.
  intros.
  econstructor; mauto 4.
Qed. 

Lemma wf_typ_subtyp_nat_sub_right {P} : forall {Γ : ctx P} {Γ' σ s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ ℕ ⊆ ℕ[σ] }}.
Proof.
  intros.  
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ' ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ ℕ[σ] }} by mauto 3.
  enough {{ Γ ⊢ ℕ ≈ ℕ[σ] }} by mauto 2.
  symmetry; mauto 3.
Qed. 

#[export]
Hint Resolve wf_typ_subtyp_nat_sub_left wf_typ_subtyp_nat_sub_right : mcpts.

Lemma wf_exp_eq_nat_sub_sub {P} : forall {Γ : ctx P} {Γ' Γ'' σ τ s} {r : Ru_nat P s},
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢ ℕ[σ][τ] ≈ ℕ : Sort@s }}.
Proof.
  intros.
  transitivity {{{ ℕ[σ∘τ] }}}; mauto 3.
  symmetry.
  mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_sub_sub : mcpts.

Corollary wf_typ_eq_nat_sub_sub {P} : forall {Γ : ctx P} {Γ' Γ'' σ τ s} {r : Ru_nat P s},
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢ ℕ[σ][τ] ≈ ℕ }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_eq_nat_sub_sub : mcpts.

Lemma wf_exp_eq_nat_sub_sub_to_nat_sub {P} : forall {Γ : ctx P} {Γ' Γ''1 Γ''2 σ τ σ' s} {r : Ru_nat P s},
    {{ Γ' ⊢s σ : Γ''1 }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢s σ' : Γ''2 }} ->
    {{ Γ ⊢ ℕ[σ][τ] ≈ ℕ[σ'] : Sort@s }}.
Proof.
  intros.
  transitivity (@a_nat P); mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_sub_sub_to_nat_sub : mcpts.

Corollary wf_typ_eq_nat_sub_sub_to_nat_sub {P} : forall {Γ : ctx P} {Γ' Γ''1 Γ''2 σ τ σ' s} {r : Ru_nat P s},
    {{ Γ' ⊢s σ : Γ''1 }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢s σ' : Γ''2 }} ->
    {{ Γ ⊢ ℕ[σ][τ] ≈ ℕ[σ'] }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_eq_nat_sub_sub_to_nat_sub : mcpts.

(** ** Expressions of type ℕ still have type ℕ under substitutions *)
Lemma wf_exp_sub_nat {P} : forall {Γ : ctx P} {Γ' M σ s} {r : Ru_nat P s},
    {{ Γ' ⊢ M : ℕ }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ M[σ] : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ' ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ M[σ] : ℕ[σ] }} by mauto 3.  
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_sub_nat : mcpts.

Lemma wf_exp_eq_sub_cong_nat1 {P} : forall {Γ : ctx P} {Γ' M M' σ s} {r : Ru_nat P s},
    {{ Γ' ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ M[σ] ≈ M'[σ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ' ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ ℕ }} by mauto 3.
  econstructor; mauto 3.
Qed.

Lemma wf_exp_eq_sub_cong_nat2 {P} : forall {Γ : ctx P} {Γ' M σ τ s} {r : Ru_nat P s},
    {{ Γ' ⊢ M : ℕ }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢s σ ≈ τ : Γ' }} ->
    {{ Γ ⊢ M[σ] ≈ M[τ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ' ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ ℕ }} by mauto 3.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_cong_nat1 wf_exp_eq_sub_cong_nat2 : mcpts.
  
Lemma wf_exp_eq_sub_compose_nat {P} : forall {Γ : ctx P} {Γ' Γ'' M σ τ s} {r : Ru_nat P s},
    {{ Γ'' ⊢ M : ℕ }} ->
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ ⊢s τ : Γ'}} ->
    {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  gen_core_presups.
  assert {{ Γ' ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ M[σ∘τ] ≈ M[σ][τ] : ℕ[σ∘τ] }} by mauto 3.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_nat : mcpts.

Lemma wf_exp_eq_sub_sub_compose_cong_nat {P} : forall {Γ : ctx P} {Γ'1 Γ'2 Γ'' σ τ σ' τ' M s} {r : Ru_nat P s},
    {{ Γ'' ⊢ M : ℕ }} ->
    {{ Γ'1 ⊢s σ : Γ'' }} ->
    {{ Γ'2 ⊢s σ' : Γ'' }} ->
    {{ Γ ⊢s τ : Γ'1 }} ->
    {{ Γ ⊢s τ' : Γ'2 }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Γ'' }} ->
    {{ Γ ⊢ M[σ][τ] ≈ M[σ'][τ'] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : ℕ }} by mauto.
  assert {{ Γ ⊢ M[σ∘τ] ≈ M[σ'∘τ'] : ℕ }} by mauto.
  enough {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : ℕ }}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_sub_compose_cong_nat : mcpts.


(** ** Optimized rules for propagating substitutions in expressions of type ℕ *)
Lemma wf_exp_eq_sub_compose_weaken_extend_nat {P} : forall {Γ : ctx P} {Γ' σ M B N s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ M : ℕ }} ->
    {{ Γ' ⊢ B }} ->
    {{ Γ ⊢ N : B[σ] }} ->
    {{ Γ ⊢ M[Wk][σ,,N] ≈ M[σ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ', B ⊢s Wk : Γ' }} by mauto 3.
  assert {{ Γ ⊢s σ,,N : Γ', B }} by mauto 2.
  transitivity {{{ M[Wk∘(σ,,N)] }}}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_weaken_extend_nat : mcpts.

Lemma wf_exp_eq_sub_compose_weaken_id_extend_nat {P} : forall {Γ : ctx P} {M B N s} {r : Ru_nat P s},
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ N : B }} ->
    {{ Γ ⊢ M[Wk][Id,,N] ≈ M : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ B ≈ B[Id] }} by mauto 4.
  assert {{ Γ ⊢ N : B[Id] }} by mauto 4.
  transitivity {{{ M[Id] }}}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_weaken_id_extend_nat : mcpts.

Lemma wf_exp_eq_sub_compose_double_weaken_double_extend_nat {P} : forall {Γ : ctx P} {Γ' σ M B N C L s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ M : ℕ }} ->
    {{ Γ' ⊢ B  }} ->
    {{ Γ ⊢ N : B[σ] }} ->
    {{ Γ', B ⊢ C }} ->
    {{ Γ ⊢ L : C[σ,,N] }} ->
    {{ Γ ⊢ M[Wk∘Wk][σ,,N,,L] ≈ M[σ] : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ', B ⊢s Wk : Γ' }} by mauto 3.
  assert {{ Γ', B, C ⊢s Wk : Γ', B }} by mauto 4.
  assert {{ Γ ⊢s σ,,N : Γ', B }} by mauto 2.
  assert {{ Γ ⊢s σ,,N,,L : Γ', B, C }} by mauto 2.
  transitivity {{{ M[Wk][Wk][σ,,N,,L] }}}; [econstructor; mautosolve 3|].
  transitivity {{{ M[Wk][σ,,N] }}}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_double_weaken_double_extend_nat : mcpts.

Lemma wf_exp_eq_sub_compose_double_weaken_id_double_extend_nat {P} : forall {Γ : ctx P} {M B N C L s } {r : Ru_nat P s},
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ N : B }} ->
    {{ Γ, B ⊢ C }} ->
    {{ Γ ⊢ L : C[Id,,N] }} ->
    {{ Γ ⊢ M[Wk∘Wk][Id,,N,,L] ≈ M : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ B ≈ B[Id] }} by mauto 4.
  assert {{ Γ ⊢ N : B[Id] }} by mauto 4.
  transitivity {{{ M[Id] }}}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_double_weaken_id_double_extend_nat : mcpts.


(** ** Lemmas for well-sorted variables *)
Lemma vlookup_0_nat {P} : forall {Γ : ctx P} {s} {r : Ru_nat P s},
    {{ ⊢ Γ }} ->
    {{ Γ, ℕ ⊢ #0 : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ ℕ }} by mauto 3.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
  eapply wf_exp_conv...
Qed.

Lemma vlookup_1_nat {P} : forall {Γ : ctx P} {A s} {r : Ru_nat P s},
    {{ Γ, ℕ ⊢ A }} ->
    {{ Γ, ℕ, A ⊢ #1 : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  assert {{ Γ ⊢ ℕ : Sort@s }} by mauto 2.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 5.
  assert {{ Γ, ℕ, A ⊢ #1 : ℕ[Wk][Wk] }} by mauto 4.
  eapply wf_exp_conv_exp_eq; mauto 3.
Qed.

#[export]
Hint Resolve vlookup_0_nat vlookup_1_nat : mcpts.

Lemma wf_exp_sub_nat_helper {P} : forall {Γ : ctx P} {Γ' σ M s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ M : ℕ[σ] }}.
Proof.
  intros.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ' ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ ℕ ⊆ ℕ[σ] }} by mauto 2.
  mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_sub_nat_helper : mcpts.

Lemma wf_exp_eq_var_0_sub_nat {P} : forall {Γ : ctx P} {Γ' σ M s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ #0[σ,,M] ≈ M : ℕ }}.
Proof with mautosolve 3.
  intros.
  gen_core_presups.
  assert {{ Γ' ⊢ ℕ }} by mauto 3.
  eapply wf_exp_eq_conv...
Qed.

Lemma wf_exp_eq_var_1_sub_nat {P} : forall {Γ : ctx P} {Γ' σ A M s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ #0 : ℕ[Wk] ∈ Γ' }} ->
    {{ Γ ⊢ #1[σ,,M] ≈ #0[σ] : ℕ }}.
Proof with mautosolve 4.
  inversion 5 as [? Γ''|]; subst.
  assert {{ Γ ⊢ #1[σ,,M] ≈ #0[σ] : ℕ[Wk][σ] }} by mauto 3.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor; mauto 4.
Qed.

#[export]
Hint Resolve wf_exp_eq_var_0_sub_nat wf_exp_eq_var_1_sub_nat : mcpts.

Lemma wf_exp_eq_var_0_weaken_nat {P} : forall {Γ : ctx P} {A s} {r : Ru_nat P s},
    {{ ⊢ Γ, A }} ->
    {{ #0 : ℕ[Wk] ∈ Γ }} ->
    {{ Γ, A ⊢ #0[Wk] ≈ #1 : ℕ }}.
Proof with mautosolve 4.
  inversion 2; subst.
  inversion 1; subst.
  assert {{ Γ0, ℕ, A ⊢ #0[Wk] ≈ #1 : ℕ[Wk][Wk] }} by mauto 3.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor; mauto 4.
Qed.

#[export]
Hint Resolve wf_exp_eq_var_0_weaken_nat : mcpts.


(** ** Lemmas about substitutions involving expressions of type ℕ *)
Lemma wf_sub_extend_nat {P} : forall {Γ : ctx P} {Γ' σ M s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢s σ,,M : Γ', ℕ }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_extend_nat : mcpts.

Lemma wf_sub_eq_extend_cong_nat {P} : forall {Γ : ctx P} {Γ' σ σ' M M' s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢s σ ≈ σ' : Γ' }} ->
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢s σ,,M ≈ σ',,M' : Γ', ℕ }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto 4.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ ℕ ≈ ℕ[σ] : Sort@s }} by mauto 3.
  assert {{ Γ' ⊢ ℕ : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ ℕ[σ] : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ ℕ ⊆ ℕ[σ] }} by mauto 2.
  eapply wf_exp_eq_conv; mauto 3.
Qed.

Lemma wf_sub_eq_extend_compose_nat {P} : forall {Γ : ctx P} {Γ' Γ'' τ σ M s} {r : Ru_nat P s},
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ' ⊢ M : ℕ }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', ℕ }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

Lemma wf_sub_eq_p_extend_nat {P} : forall {Γ : ctx P} {Γ' σ M s} {r : Ru_nat P s},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ' ⊢ M : ℕ }} ->
    {{ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }}.
Proof with mautosolve.
  intros.
  assert {{ Γ ⊢ ℕ : Sort@s }} by mauto 3.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_eq_extend_cong_nat wf_sub_eq_extend_compose_nat wf_sub_eq_p_extend_nat : mcpts.
