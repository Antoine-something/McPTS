From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic.System Require Import Definitions Lemmas.Instances Lemmas.CorePresup.
Import Syntax_Notations.

(** * Lemmas for sorts and well-sorted expressions *)
Lemma wf_typ_eq_refl_sort {P : PtsSig} : forall {Γ : ctx P} {s},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ Sort@s ≈ Sort@s }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_eq_refl_sort : mcpts.

Lemma wf_typ_eq_sort_sub_sub {P : PtsSig} : forall {Γ : ctx P} {Γ' Γ'' σ τ s1},
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢ Sort@s1[σ][τ] ≈ Sort@s1 }}.
Proof.
  intros.
  transitivity {{{ Sort@s1[σ∘τ] }}}; mauto.
Qed.

#[export]
Hint Resolve wf_typ_eq_sort_sub_sub : mcpts.
#[export]
Hint Rewrite -> @wf_typ_eq_sort_sub_sub using mauto 4 : mcpts.


(** ** Invariance of sorts under substitutions *)
Lemma wf_typ_subtyp_sort_sub_left {P} : forall {Γ : ctx P} {Γ' σ s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ Sort@s[σ] ⊆ Sort@s }}.
Proof.
  intros.
  econstructor; mauto 3.
Qed.

Lemma wf_typ_subtyp_sort_sub_right {P} : forall {Γ : ctx P} {Γ' σ s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ Sort@s ⊆ Sort@s[σ] }}.
Proof.
  intros.
  econstructor; mauto 4.
Qed.

#[export]
Hint Resolve wf_typ_subtyp_sort_sub_left wf_typ_subtyp_sort_sub_right : mcpts.

Lemma wf_exp_eq_sort_sub_sub {P : PtsSig} : forall {Γ : ctx P} {Γ' Γ'' σ τ s1 s2},
    {{ Γ'' ⊢ Sort@s1 : Sort@s2 }} ->
    {{ Γ ⊢ Sort@s1 : Sort@s2 }} ->
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢ Sort@s1[σ][τ] ≈ Sort@s1 : Sort@s2 }}.
Proof.
  intros.
  transitivity {{{ Sort@s1[σ∘τ] }}}; [symmetry |]; mauto 3.
  enough {{ Γ ⊢ Sort@s2[σ∘τ] ⊆ Sort@s2 }}; mauto 3.
  enough {{ Γ ⊢ Sort@s1[σ∘τ] ≈ Sort@s1[σ][τ] : Sort@s2[σ∘τ] }}; mauto 3.
  mauto 4.
Qed.

#[export]
Hint Resolve wf_exp_eq_sort_sub_sub : mcpts.
#[export]
Hint Rewrite -> @wf_exp_eq_sort_sub_sub using mauto 4 : mcpts.

(** ** Well-sorted expressions remain well-sorted under substitutions *)
Lemma wf_exp_sub_sorted {P} : forall {Γ : ctx P} {Γ' A σ s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A : Sort@s }} ->
    {{ Γ ⊢ A[σ] : Sort@s }}.
Proof.
  intros.
  assert {{ Γ ⊢ A[σ] : Sort@s[σ] }} by mauto 4.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ Sort@s[σ] ⊆ Sort@s }} by mauto 3.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_sub_sorted : mcpts.

Lemma wf_exp_eq_sub_cong_sorted1 {P : PtsSig} : forall {Γ : ctx P} {Γ' A A' σ s},
    {{ Γ' ⊢ A ≈ A' : Sort@s }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ A[σ] ≈ A'[σ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ Sort@s }} by mauto 3.
  assert {{ Γ ⊢s σ ≈ σ : Γ' }} by mauto 2.
  assert {{ Γ ⊢ A[σ] ≈ A'[σ] : Sort@s[σ] }} by mauto 4.
  econstructor; mauto 3.
Qed.
             
Lemma wf_exp_eq_sub_cong_sorted2 {P} : forall {Γ : ctx P} {Γ' A σ τ s},
    {{ Γ' ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢s σ ≈ τ : Γ' }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ Sort@s }} by mauto 3.
  assert {{ Γ' ⊢ A ≈ A : Sort@s }} by mauto 3.
  econstructor; mauto 4.
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_cong_sorted1 wf_exp_eq_sub_cong_sorted2 : mcpts.

(** ** Optimized rules for propagating substitutions in well-sorted expressions *)
Lemma wf_exp_eq_sub_compose_sorted1 {P} : forall {Γ : ctx P} {Γ' Γ'' A A' σ τ s},
    {{ Γ'' ⊢ A' : Sort@s }} ->
    {{ Γ'' ⊢ A ≈ A' : Sort@s }} ->
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢ A[σ∘τ] ≈ A'[σ][τ] : Sort@s }}.
Proof.
  intros.
  assert {{ Γ ⊢ Sort@s[σ∘τ] ≈ Sort@s }} by mauto.
  assert {{ Γ ⊢ Sort@s[σ∘τ] ⊆ Sort@s }} by mauto.
  assert {{ Γ ⊢ A'[σ∘τ] ≈ A'[σ][τ] : Sort@s[σ∘τ] }} by mauto 4.
  transitivity {{{ A'[σ∘τ] }}}; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_sorted1 : mcpts.

Lemma wf_exp_eq_sub_compose_sorted2 {P : PtsSig} : forall {Γ : ctx P} {Γ' Γ'' A σ τ s},
    {{ Γ'' ⊢ A : Sort@s }} ->
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_sorted2 : mcpts.


Lemma wf_exp_eq_sub_sub_compose_cong {P : PtsSig} : forall {Γ : ctx P} {Γ'1 Γ'2 Γ'' σ τ σ' τ' A s},
    {{ Γ'' ⊢ A : Sort@s }} ->
    {{ Γ'1 ⊢s σ : Γ'' }} ->
    {{ Γ'2 ⊢s σ' : Γ'' }} ->
    {{ Γ ⊢s τ : Γ'1 }} ->
    {{ Γ ⊢s τ' : Γ'2 }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Γ'' }} ->
    {{ Γ ⊢ A[σ][τ] ≈ A[σ'][τ'] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] : Sort@s }} by mauto 2.
  assert {{ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] : Sort@s }} by mauto 3.
  enough {{ Γ ⊢ A[σ'∘τ'] ≈ A[σ'][τ'] : Sort@s }}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_sub_compose_cong : mcpts.

Lemma wf_exp_eq_sub_compose_weaken_extend_sorted {P : PtsSig} : forall {Γ : ctx P} {Γ' s σ A B M},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A : Sort@s }} ->
    {{ Γ' ⊢ B }} ->
    {{ Γ ⊢ M : B[σ] }} ->
    {{ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ', B ⊢s Wk : Γ' }} by mauto 4.
  assert {{ Γ ⊢s Wk∘(σ,,M) ≈ σ : Γ' }} by mauto 3.
  transitivity {{{ A[Wk∘(σ,,M)] }}}; mauto 4.
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_weaken_extend_sorted : mcpts.

Lemma exp_eq_sub_compose_weaken_id_extend_typ {P : PtsSig} : forall {Γ : ctx P} {s A B M},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ ⊢ A[Wk][Id,,M] ≈ A : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ B ≈ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ M : B[Id] }} by mauto 2.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_id_extend_typ : mcpts.

Lemma wf_exp_eq_sub_compose_double_weaken_double_extend_sorted {P : PtsSig} : forall {Γ : ctx P} {Γ' s σ A B M C N},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A : Sort@s }} ->
    {{ Γ' ⊢ B }} ->
    {{ Γ ⊢ M : B[σ] }} ->
    {{ Γ', B ⊢ C }} ->
    {{ Γ ⊢ N : C[σ,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk][σ,,M,,N] ≈ A[σ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ', B ⊢s Wk : Γ' }} by mauto 3.
  assert {{ Γ', B, C ⊢s Wk : Γ', B }} by mauto 4.
  assert {{ Γ', B ⊢ Sort@s }} by mauto 3.
  assert {{ Γ', B ⊢ A[Wk] : Sort@s }} by mauto 3.
  transitivity {{{ A[Wk][Wk][σ,,M,,N] }}}; [eapply wf_exp_eq_sub_cong_sorted1; mautosolve 3 |].
  transitivity {{{ A[Wk][σ,,M] }}}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_double_weaken_double_extend_sorted : mcpts.

Lemma wf_exp_eq_sub_compose_double_weaken_id_double_extend_sorted {P : PtsSig} : forall {Γ : ctx P} {s A B M C N},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ, B ⊢ C }} ->
    {{ Γ ⊢ N : C[Id,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk][Id,,M,,N] ≈ A : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ B ≈ B[Id]  }} by mauto 3.
  assert {{ Γ ⊢ M : B[Id] }} by mauto 3.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_double_weaken_id_double_extend_sorted : mcpts.

(** ** Lemmas for well-sorted variables *)
Lemma vlookup_0_typ {P : PtsSig} : forall {Γ : ctx P} {s},
    {{ ⊢ Γ }} ->
    {{ Γ, Sort@s ⊢ #0 : Sort@s }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ, Sort@s ⊢s Wk : Γ }} by mauto 4.
  eapply wf_exp_conv_typ_eq; mauto 3. 
Qed.

Lemma vlookup_1_typ {P : PtsSig} : forall {Γ : ctx P} {s A},
    {{ Γ, Sort@s ⊢ A }} ->
    {{ Γ, Sort@s, A ⊢ #1 : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ, Sort@s ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, Sort@s, A ⊢s Wk : Γ, Sort@s }} by (econstructor; mauto 4).
  assert {{ ⊢ Γ, Sort@s, A }} by mauto 3.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ, Sort@s ⊢ Sort@s[Wk] }} by mauto 3.
  assert {{ Γ, Sort@s, A ⊢ Sort@s[Wk][Wk] }} by mauto 3.
  eapply wf_exp_conv; mauto 3.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve vlookup_0_typ vlookup_1_typ : mcpts.

Lemma wf_exp_sub_typ_helper {P : PtsSig} : forall {Γ : ctx P} {Γ' σ M s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ M : Sort@s }} ->
    {{ Γ ⊢ M : Sort@s[σ] }}.
Proof.
  intros.
  do 3 (econstructor; mauto 4).
Qed.

#[export]
Hint Resolve wf_exp_sub_typ_helper : mcpts.

Lemma wf_exp_eq_var_0_sub_typ {P : PtsSig} : forall {Γ : ctx P} {Γ' σ M s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ M : Sort@s }} ->
    {{ Γ ⊢ #0[σ,,M] ≈ M : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ ⊢ Sort@s[σ] ⊆ Sort@s  }} by mauto 5.
  eapply wf_exp_eq_conv; mauto 4.
Qed.

Lemma wf_exp_eq_var_1_sub_typ {P : PtsSig} : forall {Γ : ctx P} {Γ' σ A M s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ #0 : Sort@s[Wk] ∈ Γ' }} ->
    {{ Γ ⊢ #1[σ,,M] ≈ #0[σ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  inversion H2; subst.
  assert {{ ⊢ Γ0 }} by mauto 3.
  assert {{ Γ0, Sort@s ⊢s Wk : Γ0 }} by mauto 3.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_var_0_sub_typ wf_exp_eq_var_1_sub_typ : mcpts.
#[export]
Hint Rewrite -> @wf_exp_eq_var_0_sub_typ @wf_exp_eq_var_1_sub_typ : mcpts.

Lemma wf_exp_eq_var_0_weaken_typ {P : PtsSig} : forall {Γ : ctx P} {A s},
    {{ ⊢ Γ, A }} ->
    {{ #0 : Sort@s[Wk] ∈ Γ }} ->
    {{ Γ, A ⊢ #0[Wk] ≈ #1 : Sort@s }}.
Proof with mautosolve 3.
  inversion_clear 1.
  inversion 1 as [? Γ'|]; subst.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ', Sort@s ⊢s Wk : Γ' }} by mauto 4.
  assert {{ Γ', Sort@s, A ⊢s Wk : Γ', Sort@s }} by mauto 4.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_var_0_weaken_typ : mcpts.


(** ** Lemmas about substitutions involving well-sorted expressions *)
Lemma wf_sub_extend_typ {P : PtsSig} : forall {Γ : ctx P} {Γ' σ M s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ M : Sort@s }} ->
    {{ Γ ⊢s σ,,M : Γ', Sort@s }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_extend_typ : mcpts.

Lemma wf_sub_eq_extend_cong_typ {P : PtsSig} : forall {Γ : ctx P} {Γ' σ σ' M M' s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢s σ ≈ σ' : Γ' }} ->
    {{ Γ ⊢ M ≈ M' : Sort@s }} ->
    {{ Γ ⊢s σ,,M ≈ σ',,M' : Γ', Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ' }} by mauto 2.
  econstructor; mauto 2.
  eapply wf_exp_eq_conv; mauto 3.
Qed.

Lemma wf_sub_eq_extend_compose_typ {P : PtsSig} : forall {Γ : ctx P} {Γ' Γ'' τ σ A s M},
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ'' ⊢ A }} ->
    {{ Γ' ⊢ M : Sort@s }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', Sort@s }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

Lemma wf_sub_eq_p_extend_typ {P : PtsSig} : forall {Γ : ctx P} {Γ' σ M s},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ' ⊢ M : Sort@s }} ->
    {{ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_eq_extend_cong_typ wf_sub_eq_extend_compose_typ wf_sub_eq_p_extend_typ : mcpts.
