From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic.System Require Import Definitions Lemmas.Instances Lemmas.CorePresup Lemmas.SortLemmas Lemmas.NatLemmas.
Import Syntax_Notations.

(** ** Lemmas for closures *)
Lemma wf_exp_eq_sub_sub_compose_cong {P : PtsSig} : forall {Γ : ctx P} {Γ'1 Γ'2 Γ'' σ τ σ' τ' M A},
    {{ Γ'' ⊢ A }} ->
    {{ Γ'' ⊢ M : A }} ->
    {{ Γ'1 ⊢s σ : Γ'' }} ->
    {{ Γ'2 ⊢s σ' : Γ'' }} ->
    {{ Γ ⊢s τ : Γ'1 }} ->
    {{ Γ ⊢s τ' : Γ'2 }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Γ'' }} ->
    {{ Γ ⊢ M[σ][τ] ≈ M[σ'][τ'] : A[σ∘τ] }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] }} by mauto.
  assert {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : A[σ∘τ] }} by mauto 4.
  assert {{ Γ ⊢ M[σ∘τ] ≈ M[σ'∘τ'] : A[σ∘τ] }} by mauto 4.
  assert {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ'∘τ'] }} by mauto.
  enough {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ∘τ] }} by mauto.
  eapply wf_exp_eq_conv_typ_eq; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_sub_compose_cong : mcpts.

Lemma wf_exp_sub_compose_weak_extend_sigma_sigma {P : PtsSig} : forall {Γ : ctx P} {Γ' σ A B M},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ' ⊢ M : A[σ] }} ->
    {{ Γ' ⊢ B[Wk][σ,,M] ≈ B[σ] }}.
Proof.
  intros.
  gen_core_presups.
  assert {{ Γ', A[σ] ⊢s Wk : Γ' }} by mauto 3.
  assert {{ Γ' ⊢s σ,,M : Γ, A }} by mauto 3.
  assert {{ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }} by mauto 3.
  transitivity {{{ B[Wk∘(σ,,M)] }}}; [symmetry| ]; mauto 4.
Qed.
  
#[export]  
Hint Resolve wf_exp_sub_compose_weak_extend_sigma_sigma : mcpts.
 
Lemma wf_exp_sub_id_on_typ {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A[Id] }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  eapply wf_exp_conv_typ_eq; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_sub_id_on_typ : mcpts.

Lemma wf_exp_sub_id_on_typ_sorted {P : PtsSig} : forall {Γ : ctx P} {M A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A[Id] }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_exp_sub_id_on_typ_sorted : mcpts.


Lemma wf_exp_eq_sub_id_on_typ {P : PtsSig} : forall {Γ : ctx P} {M M' A},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ M ≈ M' : A[Id] }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  eapply wf_exp_eq_conv_typ_eq; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_id_on_typ : mcpts.

Lemma wf_exp_eq_sub_id_on_typ_sorted {P : PtsSig} : forall {Γ : ctx P} {M M' A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ M ≈ M' : A[Id] }}.
Proof. mauto 3. Qed.
  
#[export]
Hint Resolve wf_exp_eq_sub_id_on_typ_sorted : mcpts.


(** ** Lemmas for substitution well-formedness *)
Lemma wf_sub_id_extend {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s Id,,M : Γ, A }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_id_extend : mcpts.

Lemma wf_sub_id_extend_sorted {P : PtsSig} : forall {Γ : ctx P} {M A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s Id,,M : Γ, A }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_id_extend_sorted : mcpts.

(** Lemmas for well-formedness of q σ *)
Lemma wf_sub_q {P : PtsSig} : forall {Γ : ctx P} {Γ' A σ},
    {{ Γ' ⊢ A }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ, A[σ] ⊢s q σ : Γ', A }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ A[σ] }} by mauto 3.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 3.
  econstructor; mauto 2.
  eapply wf_exp_conv_typ_eq; mauto 3.
Qed.

Lemma wf_sub_q_sort {P : PtsSig} : forall {Γ : ctx P} {Γ' σ s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ, Sort@s ⊢s q σ : Γ', Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ, Sort@s ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, Sort@s ⊢s σ∘Wk : Γ' }} by mauto 4.
  assert {{ Γ, Sort@s ⊢ Sort@s[Wk] ≈ Sort@s }} by mauto 4.
  assert {{ Γ, Sort@s ⊢ #0 : Sort@s }} by mauto 3.
  econstructor...
Qed.

Lemma wf_sub_q_nat {P} : forall {Γ : ctx P} {Γ' σ s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ, ℕ ⊢s q σ : Γ', ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, ℕ ⊢s σ∘Wk : Γ' }} by mauto 4.
  assert {{ Γ, ℕ ⊢ #0 : ℕ }}...
Qed.

#[export]
Hint Resolve wf_sub_q wf_sub_q_sort wf_sub_q_nat : mcpts.


(** Extending substitutions with natural numbers *)
Lemma wf_sub_id_extend_zero {P} : forall {Γ : ctx P} {s} {r : Ru_nat P s},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢s Id,,zero : Γ, ℕ }}.
Proof. mauto 4. Qed.

#[export]
Hint Resolve wf_sub_id_extend_zero : mcpts.
  
Lemma wf_sub_weak_compose_weak_extend_succ_var1 {P} : forall {Γ : ctx P} {A s} {r : Ru_nat P s},
    {{ Γ, ℕ ⊢ A }} ->
    {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ  }} by mauto 4.
  enough {{ Γ, ℕ, A ⊢s Wk∘Wk : Γ }}...
Qed.

#[export]
Hint Resolve wf_sub_weak_compose_weak_extend_succ_var1 : mcpts.

Lemma wf_sub_weak_compose_weak_extend_succ_var1_sorted {P} : forall {Γ : ctx P} {A s s'} {r : Ru_nat P s},
    {{ Γ, ℕ ⊢ A : Sort@s' }} ->
    {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_weak_compose_weak_extend_succ_var1_sorted : mcpts.


(** ** Lemmas about substitution equality *)
Lemma wf_sub_eq_weaken_var0_id {P : PtsSig} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    {{ Γ, A ⊢s Wk,,#0 ≈ Id : Γ, A }}.
Proof with mautosolve 4.
  intros * ?.
  gen_core_presups.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, A ⊢s (Wk∘Id),,#0[Id] ≈ Id : Γ, A }} by mauto.
  assert {{ Γ, A ⊢s Wk ≈ Wk∘Id : Γ }} by mauto.
  assert {{ Γ, A ⊢s Wk,,#0 ≈ Wk∘Id,,#0[Id] : Γ, A }} by (eapply wf_sub_eq_extend_cong; mauto 4).
  enough {{ Γ, A ⊢ #0 ≈ #0[Id] : A[Wk] }} by (etransitivity; mauto 3).
  symmetry; econstructor; econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_eq_weaken_var0_id : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_weaken_var0_id using mauto 4 : mcpts.

Lemma wf_sub_eq_p_id_extend {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s Wk∘(Id,,M) ≈ Id : Γ }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_eq_p_id_extend : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_p_id_extend using mauto 4 : mcpts.


Lemma wf_sub_eq_p_id_extend_sorted {P : PtsSig} : forall {Γ : ctx P} {M A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s Wk∘(Id,,M) ≈ Id : Γ }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_p_id_extend_sorted : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_p_id_extend_sorted using mauto 4 : mcpts.

Lemma wf_sub_eq_id_extend_cong {P : PtsSig} : forall {Γ : ctx P} {M M' A},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢s Id,,M ≈ Id,,M' : Γ, A }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_eq_id_extend_cong : mcpts.


Lemma wf_sub_eq_id_extend_cong_sorted {P : PtsSig} : forall {Γ : ctx P} {M M' A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢s Id,,M ≈ Id,,M' : Γ, A }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_id_extend_cong_sorted : mcpts.

Lemma wf_sub_eq_id_extend_compose {P : PtsSig} : forall {Γ : ctx P} {Γ' M A σ},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A }} ->
    {{ Γ' ⊢ M : A }} ->
    {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Γ', A }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ' ⊢s Id : Γ' }} by mauto 3.
  assert {{ Γ' ⊢ M : A[Id] }} by mauto.
  assert {{ Γ ⊢s (Id,,M)∘σ ≈ (Id∘σ),,M[σ] : Γ', A }} by mauto 3.
  assert {{ Γ ⊢ M[σ] : A[Id][σ] }} by mauto.
  assert {{ Γ ⊢ A[Id][σ] ≈ A[Id∘σ] }} by (symmetry; mauto 3).
  assert {{ Γ ⊢ A[Id∘σ] }} by mauto 3.
  assert {{ Γ ⊢ A[Id][σ] ⊆ A[Id∘σ] }} by mauto 4.
  assert {{ Γ ⊢ M[σ] : A[Id∘σ] }} by (eapply wf_exp_conv_typ_eq; mauto 3).
  enough {{ Γ ⊢ M[σ] ≈ M[σ] : A[Id∘σ] }}...
Qed.

#[export]
Hint Resolve wf_sub_eq_id_extend_compose : mcpts.

Lemma wf_sub_eq_id_extend_compose_sorted {P : PtsSig} : forall {Γ : ctx P} {Γ' M A σ s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A : Sort@s }} ->
    {{ Γ' ⊢ M : A }} ->
    {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Γ', A }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_id_extend_compose_sorted : mcpts.

Lemma wf_sub_eq_sigma_compose_weak_id_extend {P : PtsSig} : forall {Γ : ctx P} {Γ' M A σ},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Γ' }}.
Proof with mautosolve.
  intros.
  assert {{ Γ ⊢s Id,,M : Γ, A }} by mauto.
  assert {{ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ∘(Wk∘(Id,,M)) : Γ' }} by mauto 4.
  assert {{ Γ ⊢s Wk∘(Id,,M) ≈ Id : Γ }} by mauto.
  enough {{ Γ ⊢s σ∘(Wk∘ (Id,,M)) ≈ σ∘Id : Γ' }} by mauto 4.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_eq_sigma_compose_weak_id_extend : mcpts.

Lemma wf_sub_eq_sigma_compose_weak_id_extend_sorted {P : PtsSig} : forall {Γ : ctx P} {Γ' M A σ s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Γ' }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_sigma_compose_weak_id_extend_sorted : mcpts.

(** Propagation of q *)
Lemma wf_sub_eq_q_sigma_id_extend {P : PtsSig} : forall {Γ : ctx P} {Γ' M A σ},
    {{ Γ' ⊢ A }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢s q σ∘(Id,,M) ≈ σ,,M : Γ', A }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  assert {{ Γ ⊢ A[σ] }} by mauto 3.
  assert {{ Γ ⊢ M : A[σ] }} by mauto.
  assert {{ Γ ⊢s Id,,M : Γ, A[σ] }} by mauto.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 3.
  assert {{ Γ ⊢ A[σ] }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 4.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by (eapply wf_exp_conv_typ_eq; mauto 3).
  assert {{ Γ ⊢s q σ∘(Id,,M) ≈ ((σ∘Wk)∘(Id,,M)),,#0[Id,,M] : Γ', A }} by mauto.
  assert {{ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Γ' }} by mauto.
  assert {{ Γ ⊢ M : A[σ][Id] }} by mauto 4.
  assert {{ Γ ⊢ #0[Id,,M] ≈ M : A[σ][Id] }} by mauto 4.
  assert {{ Γ ⊢ #0[Id,,M] ≈ M : A[σ] }} by mauto 4.
  enough {{ Γ ⊢ #0[Id,,M] ≈ M : A[(σ∘Wk)∘(Id,,M)] }} by mauto.
  assert {{ Γ ⊢s (σ∘Wk)∘(Id,,M) : Γ' }} by mauto 3.
  assert {{ Γ ⊢ A[(σ∘Wk)∘(Id,,M)] }} by mauto 3.
  eapply wf_exp_eq_conv_typ_eq; mauto 4.
Qed.

#[export]
Hint Resolve wf_sub_eq_q_sigma_id_extend : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_q_sigma_id_extend using mauto 4 : mcpts.

Lemma wf_sub_eq_q_sigma_id_extend_sorted {P : PtsSig} : forall {Γ : ctx P} {Γ' M A σ s},
    {{ Γ' ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢s q σ∘(Id,,M) ≈ σ,,M : Γ', A }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_q_sigma_id_extend_sorted : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_q_sigma_id_extend_sorted using mauto 4 : mcpts.

Lemma wf_sub_eq_q_sigma_extend_tau {P} : forall {Γ1 : ctx P} {Γ2 Γ3 A σ τ M},
    {{ Γ3 ⊢ A }} ->
    {{ Γ2 ⊢s σ : Γ3 }} ->
    {{ Γ1 ⊢s τ : Γ2 }} ->
    {{ Γ1 ⊢ M : A[σ][τ] }} ->
    {{ Γ1 ⊢s (q σ)∘(τ,,M) ≈ (σ∘τ),,M : Γ3, A }}.
Proof.
  intros.
  assert {{ Γ2, A[σ] ⊢s σ ∘ Wk : Γ3 }} by mauto.
  assert {{ Γ2 ⊢ A[σ] }} by mauto 3.
  assert {{ Γ2, A[σ] ⊢s Wk : Γ2 }} by mauto 3.
  assert {{ Γ2, A[σ] ⊢ A[σ][Wk] }} by mauto 3.
  assert {{ Γ2, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 4.
  assert {{ Γ2, A[σ] ⊢ A[σ][Wk] ≈ A[σ∘Wk] }} by mauto.
  assert {{ Γ2, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto 3.
  assert {{ Γ1 ⊢s (q σ) ∘ (τ,,M) ≈ ((σ∘Wk)∘(τ,,M)),,#0[τ,,M] : Γ3, A }} by mauto 3.
  assert {{ Γ1 ⊢s (σ∘Wk)∘(τ,,M) ≈ σ∘(Wk∘(τ,,M)) : Γ3 }} by (econstructor; mauto 3).
  assert {{ Γ1 ⊢s σ∘(Wk∘(τ,,M)) ≈ σ∘τ : Γ3 }} by mauto 4.
  assert {{ Γ1 ⊢s (σ ∘ Wk) ∘ (τ,,M) ≈ σ∘τ : Γ3 }} by (etransitivity; mauto).
  assert {{ Γ1 ⊢ #0[τ,,M] ≈ M : A[σ][τ] }} by mauto.
  assert {{ Γ3 ⊢ A }} by mauto 2.
  assert {{ Γ1 ⊢ A[σ][τ] ≈ A[σ∘τ] }} by mauto 3.
  assert {{ Γ1 ⊢ A[σ][τ] ≈ A[(σ∘Wk)∘(τ,,M)] }} by (etransitivity; mauto 4).
  assert {{ Γ1 ⊢s (σ∘Wk)∘(τ,,M) : Γ3 }} by mauto 3.
  assert {{ Γ1 ⊢ A[(σ∘Wk)∘(τ,,M)] }} by mauto 2.
  assert {{ Γ1 ⊢s (σ∘Wk)∘(τ,,M),,#0[τ,,M] ≈ σ∘τ,,M : Γ3, A }} by (econstructor; mauto).
  do 2 etransitivity; mauto.
Qed.

#[export]
Hint Resolve wf_sub_eq_q_sigma_extend_tau : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_q_sigma_extend_tau using mauto 4 : mcpts.

Lemma wf_sub_eq_q_sigma_extend_tau_sorted {P} : forall {Γ1 : ctx P} {Γ2 Γ3 A σ τ M s},
    {{ Γ3 ⊢ A : Sort@s }} ->
    {{ Γ2 ⊢s σ : Γ3 }} ->
    {{ Γ1 ⊢s τ : Γ2 }} ->
    {{ Γ1 ⊢ M : A[σ][τ] }} ->
    {{ Γ1 ⊢s (q σ)∘(τ,,M) ≈ (σ∘τ),,M : Γ3, A }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_q_sigma_extend_tau : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_q_sigma_extend_tau using mauto 4 : mcpts.

Lemma wf_sub_eq_p_q_sigma {P : PtsSig} : forall {Γ : ctx P} {Γ' A σ},
    {{ Γ' ⊢ A }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ, A[σ] ⊢s Wk∘q σ ≈ σ∘Wk : Γ' }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ ⊢ A[σ] }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 4.
  enough {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto.
  eapply wf_exp_conv_typ_eq; mauto 3.
Qed.

#[export]
Hint Resolve wf_sub_eq_p_q_sigma : mcpts.

Lemma wf_sub_eq_p_q_sigma_sorted {P : PtsSig} : forall {Γ : ctx P} {Γ' A σ s},
    {{ Γ' ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ, A[σ] ⊢s Wk∘q σ ≈ σ∘Wk : Γ' }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_p_q_sigma_sorted : mcpts.

Lemma wf_sub_eq_p_q_sigma_nat {P} : forall {Γ : ctx P} {Γ' σ s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ, ℕ ⊢s Wk∘q σ ≈ σ∘Wk : Γ' }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, ℕ ⊢ #0 : ℕ }}...
Qed.

#[export]
Hint Resolve wf_sub_eq_p_q_sigma_nat : mcpts.

Lemma wf_sub_eq_p_p_q_q_sigma_nat {P} : forall {Γ : ctx P} {Γ' A σ s} {r : Ru_nat P s},
    {{ Γ', ℕ ⊢ A }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ, ℕ, A[q σ] ⊢s Wk∘(Wk∘q (q σ)) ≈ (σ∘Wk)∘Wk : Γ' }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ, ℕ ⊢ A[q σ] }} by mauto 4.
  assert {{ ⊢ Γ, ℕ, A[q σ] }} by mauto 3.
  assert {{ ⊢ Γ', ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A[q σ] ⊢s Wk∘q (q σ) ≈ q σ∘Wk : Γ', ℕ }} by mauto.
  assert {{ Γ, ℕ, A[q σ] ⊢s Wk∘(Wk∘q (q σ)) ≈ Wk∘(q σ∘Wk) : Γ' }} by mauto 3.
  assert {{ Γ', ℕ ⊢s Wk : Γ' }} by mauto.
  assert {{ Γ, ℕ ⊢s q σ : Γ', ℕ }} by mauto.
  assert {{ Γ, ℕ, A[q σ] ⊢s Wk∘(q σ∘Wk) ≈ (Wk∘q σ)∘Wk : Γ' }} by mauto 4.
  assert {{ Γ, ℕ ⊢s Wk∘q σ ≈ σ∘Wk : Γ' }} by mauto.
  enough {{ Γ, ℕ, A[q σ] ⊢s (Wk∘q σ)∘Wk ≈ (σ∘Wk)∘Wk : Γ' }}...
Qed.

#[export]
Hint Resolve wf_sub_eq_p_p_q_q_sigma_nat : mcpts.

Lemma wf_sub_eq_p_p_q_q_sigma_nat_sorted {P} : forall {Γ : ctx P} {Γ' A σ s s'} {r : Ru_nat P s},
    {{ Γ', ℕ ⊢ A : Sort@s' }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ, ℕ, A[q σ] ⊢s Wk∘(Wk∘q (q σ)) ≈ (σ∘Wk)∘Wk : Γ' }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_p_p_q_q_sigma_nat_sorted : mcpts.

(** ** Equality of variables under substitutions *)
Lemma wf_exp_eq_var_1_sub_q_q_sigma_nat {P} : forall {Γ : ctx P} {Γ' A σ s} {r : Ru_nat P s},
    {{ Γ', ℕ ⊢ A }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #1 : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ, ℕ ⊢s q σ : Γ', ℕ }} by mauto 3.
  assert {{ Γ, ℕ ⊢ A[q σ] }} by mauto 4.
  assert {{ ⊢ Γ, ℕ, A[q σ] }} by (econstructor; mauto 2).
  assert {{ Γ', ℕ ⊢ #0 : ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A[q σ] ⊢ #0 : A[q σ][Wk] }} by mauto 3.
  assert {{ Γ, ℕ, A[q σ] ⊢s q σ∘Wk : Γ', ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A[q σ] ⊢ A[q σ∘Wk] ≈ A[q σ][Wk]  }} by mauto 4.
  assert {{ Γ, ℕ, A[q σ] ⊢ #0 : A[q σ∘Wk] }} by (eapply wf_exp_conv_typ_eq; mauto 4).
  assert {{ Γ, ℕ, A[q σ] ⊢s q σ∘Wk : Γ', ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #0[q σ∘Wk] : ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A[q σ] ⊢ #0[q σ∘Wk] ≈ #0[q σ][Wk] : ℕ }} by mauto 4.
  assert {{ Γ, ℕ ⊢s σ∘Wk : Γ' }} by mauto 4.
  assert {{ Γ, ℕ ⊢ #0 : ℕ }} by mauto 3.
  assert {{ Γ, ℕ ⊢ #0 : ℕ[σ∘Wk] }} by mauto 3.
  assert {{ Γ, ℕ ⊢ #0[q σ] ≈ #0 : ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : ℕ }} by mauto 3.
  etransitivity; [eassumption |].
  etransitivity...
Qed.

#[export]
Hint Resolve wf_exp_eq_var_1_sub_q_q_sigma_nat : mcpts.

Lemma wf_exp_eq_var_1_sub_q_q_sigma_nat_sorted {P} : forall {Γ : ctx P} {Γ' A σ s s'} {r : Ru_nat P s},
    {{ Γ', ℕ ⊢ A : Sort@s' }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #1 : ℕ }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_exp_eq_var_1_sub_q_q_sigma_nat_sorted : mcpts.

(** More propagation of q, useful when dealing with the recursor *)
Lemma wf_sub_eq_q_sigma_compose_weak_weak_extend_succ_var1 {P} : forall {Γ : ctx P} {Γ' A σ s} {r : Ru_nat P s},
    {{ Γ', ℕ ⊢ A }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ, ℕ, A[q σ] ⊢s q σ∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘q (q σ) : Γ', ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ', ℕ, A }} by mauto 3.
  assert {{ ⊢ Γ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
  assert {{ Γ, ℕ ⊢s σ∘Wk : Γ' }} by mauto 3.
  assert {{ Γ, ℕ ⊢ A[q σ] }} by mauto 4.
  set (Γ'' := {{{ Γ, ℕ, A[q σ] }}}).
  set (WkWksucc := {{{ (Wk∘Wk),,succ #1 }}}).
  assert {{ ⊢ Γ'' }} by mauto 2.
  assert {{ Γ'' ⊢s Wk∘Wk : Γ }} by mauto 3.
  assert {{ Γ'' ⊢s WkWksucc : Γ, ℕ }} by mauto 4.
  assert {{ Γ, ℕ ⊢ #0 : ℕ}} by mauto 3.
  assert {{ Γ'' ⊢s q σ∘WkWksucc ≈ ((σ∘Wk)∘WkWksucc),,#0[WkWksucc] : Γ', ℕ }} by mautosolve 3.
  assert {{ Γ'' ⊢ #1 : ℕ[Wk][Wk] }} by mauto.
  assert {{ Γ'' ⊢ ℕ[Wk][Wk] ≈ ℕ : Sort@s }} by mauto 3.
  assert {{ Γ'' ⊢ #1 : ℕ }} by mauto 2.
  assert {{ Γ'' ⊢ succ #1 : ℕ }} by mauto.
  assert {{ Γ'' ⊢s Wk∘WkWksucc : Γ }} by mauto 4.
  assert {{ Γ'' ⊢s Wk∘WkWksucc ≈ Wk∘Wk : Γ }} by mauto 4.
  assert {{ Γ ⊢s σ ≈ σ : Γ' }} by mauto.
  assert {{ Γ'' ⊢s σ∘(Wk∘WkWksucc) ≈ σ∘(Wk∘Wk) : Γ' }} by mauto 3.
  assert {{ Γ'' ⊢s (σ∘Wk)∘WkWksucc ≈ σ∘(Wk∘Wk) : Γ' }} by mauto 3.
  assert {{ Γ'' ⊢s σ∘(Wk∘Wk) ≈ (σ∘Wk)∘Wk : Γ' }} by mauto 4.
  assert {{ Γ'' ⊢s (σ∘Wk)∘Wk ≈ Wk∘(Wk∘q (q σ)) : Γ' }} by mauto.
  assert {{ Γ', ℕ ⊢s Wk : Γ' }} by mauto 4.
  assert {{ Γ', ℕ, A ⊢s Wk : Γ', ℕ }} by mauto 4.
  assert {{ Γ', ℕ, A ⊢s Wk∘Wk : Γ' }} by mauto 4.
  assert {{ Γ'' ⊢s q (q σ) : Γ', ℕ, A }} by mauto.
  assert {{ Γ'' ⊢s Wk∘(Wk∘q (q σ)) ≈ (Wk∘Wk)∘q (q σ) : Γ' }} by mauto 3.
  assert {{ Γ'' ⊢s σ∘(Wk∘Wk) ≈ (Wk∘Wk)∘q (q σ) : Γ' }} by mauto 3.
  assert {{ Γ'' ⊢ #0[WkWksucc] ≈ succ #1 : ℕ }} by mauto.
  assert {{ Γ'' ⊢ succ #1[q (q σ)] ≈ succ #1 : ℕ }} by mauto .
  assert {{ Γ', ℕ, A ⊢ #1 : ℕ }} by mauto 2.
  assert {{ Γ'' ⊢ succ #1 ≈ (succ #1)[q (q σ)] : ℕ }} by mauto 4.
  assert {{ Γ'' ⊢ #0[WkWksucc] ≈ (succ #1)[q (q σ)] : ℕ }} by mauto 2.
  assert {{ Γ'' ⊢s (σ∘Wk)∘WkWksucc : Γ' }} by mauto 3.
  assert {{ Γ'' ⊢s ((σ∘Wk)∘WkWksucc),,#0[WkWksucc] ≈ ((Wk∘Wk)∘q (q σ)),,(succ #1)[q (q σ)] : Γ', ℕ }} by mauto 3.
  assert {{ Γ', ℕ, A ⊢ #1 : ℕ[Wk][Wk] }} by mauto 4.
  assert {{ Γ', ℕ, A ⊢ ℕ[Wk][Wk] ≈ ℕ : Sort@s }} by mauto 3.
  assert {{ Γ', ℕ, A ⊢ succ #1 : ℕ }} by mauto 4.
  enough {{ Γ'' ⊢s ((Wk∘Wk)∘q (q σ)),,(succ #1)[q (q σ)] ≈ WkWksucc∘q (q σ) : Γ', ℕ }}...
Qed.

#[export]
Hint Resolve wf_sub_eq_q_sigma_compose_weak_weak_extend_succ_var1 : mcpts.

Lemma wf_sub_eq_q_sigma_compose_weak_weak_extend_succ_var1_unsorted {P} : forall {Γ : ctx P} {Γ' A σ s s'} {r : Ru_nat P s},
    {{ Γ', ℕ ⊢ A : Sort@s' }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ, ℕ, A[q σ] ⊢s q σ∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘q (q σ) : Γ', ℕ }}.
Proof. mauto 3. Qed.
#[export]
Hint Resolve wf_sub_eq_q_sigma_compose_weak_weak_extend_succ_var1_unsorted : mcpts.
