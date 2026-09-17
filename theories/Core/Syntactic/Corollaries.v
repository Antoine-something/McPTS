From Coq Require Import Setoid Nat.
From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

(** ** Lemmas related to identity substitutions *)
Corollary wf_exp_sub_id_on_typ' {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A[Id] }}.
Proof. 
  intros.
  gen_presups.
  mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_sub_id_on_typ' : mcpts.
#[export]
Remove Hints wf_exp_sub_id_on_typ : mcpts.

Corollary wf_exp_invert_sub_id {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M[Id] : A }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros * [? [? [?%wf_sub_id_inversion []]]]%wf_exp_sub_inversion.
  mauto 4.
Qed.

#[export]
Hint Resolve wf_exp_invert_sub_id : mcpts.

Corollary wf_typ_invert_sub_id {P : PtsSig} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A[Id] }} ->
    {{ Γ ⊢ A }}.
Proof.
  intros * H.
  inversion_clear H; [assert {{ Γ ⊢ A : Sort@s }} by mauto 2 |]; mauto 3.
Qed.

Hint Resolve wf_typ_invert_sub_id : mcpts.


Corollary wf_exp_invert_sub_id_on_typ {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A[Id] }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros.
  dependent destruction H;
    gen_presups.
  - assert {{ Γ ⊢ A }} by mauto 3.
    assert {{ Γ ⊢ A[Id] ≈ A }} by mauto 3.
    mauto 3.
  - pose proof (wf_sub_id_inversion H).
    assert {{ Γ ⊢ A[Id] ≈ A }} by mauto 3.
    mauto 3.
  - assert {{ Γ ⊢ A[Id] ≈ A }} by mauto 3.
    mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_invert_sub_id_on_typ : mcpts.

Lemma wf_sub_invert_compose_id {P : PtsSig} : forall {Γ : ctx P} {Γ' σ},
    {{ Γ ⊢s σ∘Id : Γ' }} ->
    {{ Γ ⊢s σ : Γ' }}.
Proof.
  intros * [? []]%wf_sub_compose_inversion.
  mauto 4.
Qed.

#[export]
Hint Resolve wf_sub_invert_compose_id : mcpts.

(** ** Rewrite rules for applying substitutions *)
Add Parametric Morphism {P : PtsSig} (Γ : ctx P) Γ' : a_sub
    with signature wf_typ_subtyp Γ' ==> wf_sub_eq Γ Γ' ==> wf_typ_subtyp Γ as wf_typ_subtyp_cong.
Proof.
  intros.
  gen_presups.
  mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ : ctx P) Γ' : a_sub
    with signature wf_typ_eq Γ' ==> wf_sub_eq Γ Γ' ==> wf_typ_eq Γ as wf_typ_eq_sub_cong.
Proof.
  intros.
  gen_presups.
  mauto 4.
Qed.

Add Parametric Morphism {P : PtsSig} (s : P) Γ Γ' : a_sub
    with signature wf_exp_eq Γ' {{{ Sort@s }}} ==> wf_sub_eq Γ Γ' ==> wf_exp_eq Γ {{{ Sort@s }}} as wf_exp_eq_sorted_sub_cong.
Proof.
  intros.
  gen_presups.
  mauto 4.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ1 : ctx P) Γ2 Γ3 : a_compose
    with signature wf_sub_eq Γ2 Γ3 ==> wf_sub_eq Γ1 Γ2 ==> wf_sub_eq Γ1 Γ3 as sub_compose_cong.
Proof. mauto. Qed.


(** ** Additional properties of contexts *)
Lemma wf_ctx_subtyp_length {P : PtsSig} : forall {Γ : ctx P} {Γ'},
    {{ ⊢ Γ ⊆ Γ' }} ->
    length Γ = length Γ'.
Proof. induction 1; simpl; auto. Qed.

Lemma wf_ctx_eq_length {P : PtsSig} : forall {Γ : ctx P} {Γ'},
    {{ ⊢ Γ ⊆ Γ' }} ->
    length Γ = length Γ'.
Proof. induction 1; simpl; auto. Qed.

Open Scope list_scope.

(** ** Deep variable lookups in local contexts *)
Lemma app_ctx_lookup {P : PtsSig} : forall (Γ' : ctx P) A Γ n,
    length Γ' = n ->
    {{ #n : ^(iter (S n) (fun A' => {{{ A'[Wk] }}}) A) ∈ ^(Γ' ++ A :: Γ) }}.
Proof.
  induction Γ'; intros; simpl in *; subst; mauto.
Qed.

Lemma app_ctx_vlookup {P : PtsSig} : forall (Γ' : ctx P) A Γ n,
    {{ ⊢ ^(Γ' ++ A :: Γ) }} ->
    length Γ' = n ->
    {{ ^(Γ' ++ A :: Γ) ⊢ #n : ^(iter (S n) (fun A' => {{{ A'[Wk] }}}) A) }}.
Proof.
  intros.
  assert {{ #n : ^(iter (S n) (fun A' => {{{ A'[Wk] }}}) A) ∈ ^(Γ' ++ A :: Γ) }} by (eapply app_ctx_lookup; mauto).
  subst.
  mauto 2.
Qed.


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

Lemma wf_typ_subtyp_sub_cong {P : PtsSig} : forall {Γ' : ctx P} {A B},
    {{ Γ' ⊢ A ⊆ B }} ->
    forall Γ σ σ',
      {{ Γ ⊢s σ ≈ σ' : Γ' }} ->
      {{ Γ ⊢ A[σ] ⊆ B[σ'] }}.
Proof.
  induction 1; intros * Hσσ'; gen_presup Hσσ'; mauto 3.
  - etransitivity; mauto 3.
  - assert {{ Γ0 ⊢ Sort@s2[σ'] ≈ Sort@s2 }} by mauto 2.
    transitivity {{{ Sort@s1 }}}; mauto 3.
    transitivity {{{ Sort@s2 }}}; mauto 3.
  - assert {{ Γ0 ⊢ A'[σ] ≈ A'[σ'] : Sort@s1 }} by mauto 2.
    assert {{ ⊢ Γ0 ≈ Γ0 }} by mauto 3.
    assert {{ ⊢ Γ0, A'[σ] ≈ Γ0, A'[σ'] }} by mauto 3.
    assert {{ Γ0, A[σ] ⊢s q σ : Γ, A }} by mauto 3.
    assert {{ Γ0, A'[σ] ⊢s q σ ≈ q σ' : Γ, A' }} by mauto 3.
    assert {{ Γ0, A'[σ'] ⊢s q σ ≈ q σ' : Γ, A' }} by mauto 3.
    assert {{ Γ0 ⊢ (Π r A B)[σ] ≈ Π r A[σ] B[q σ] }} by mauto 3.
    transitivity {{{ Π r (A[σ]) (B[q σ]) }}}; mauto 2.
    assert {{ Γ0 ⊢ (Π r A' B')[σ'] ≈ Π r A'[σ'] B'[q σ'] }} by mauto 3.
    transitivity {{{ Π r (A'[σ']) (B'[q σ']) }}}; mauto 3.
    assert {{ Γ0 ⊢ A[σ] ≈ A'[σ'] : Sort@s1 }} by mauto 3.
    assert {{ Γ0, A'[σ'] ⊢s q σ' : Γ, A' }} by mauto 3.
    eapply wf_typ_subtyp_pi'; mauto 2.    
Qed.

#[export]
Hint Resolve wf_typ_subtyp_sub_cong : mcpts.
    
Lemma wf_exp_ax_typ_sub_lhs {P : PtsSig} : forall {Γ Γ' σ s1 s2},
    Ax_typ P s1 s2 ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ Sort@s1[σ] : Sort@s2 }}.
Proof.
  intros; gen_presups; mauto 3.
Qed.
#[export]
Hint Resolve wf_exp_ax_typ_sub_lhs : mcpts.

Lemma sub_decompose_q {P : PtsSig} : forall {Γ : ctx P} {Γ' Γ'' A σ τ M},
  {{ Γ ⊢ A }} ->
  {{ Γ' ⊢s σ : Γ }} ->
  {{ Γ'' ⊢s τ : Γ' }} ->
  {{ Γ'' ⊢ M : A[σ][τ] }} ->
  {{ Γ'' ⊢s q σ ∘ (τ ,, M) ≈ σ ∘ τ ,, M : Γ, A }}.
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

#[local]
Hint Rewrite -> @sub_decompose_q using mauto : mcpts.

(** ** Lemmas about natural numbers *)
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

Lemma sub_decompose_q_typ {P : PtsSig} : forall {Γ : ctx P} {A B σ Γ' Γ'' τ M},
  {{ Γ, A ⊢ B }} ->
  {{ Γ' ⊢s σ : Γ }} ->
  {{ Γ'' ⊢s τ : Γ' }} ->
  {{ Γ'' ⊢ M : A[σ][τ] }} ->
  {{ Γ'' ⊢ B[σ∘τ,,M] ≈ B[q σ][τ,,M]  }}.
Proof.
  intros. gen_presups.
  assert {{ Γ'' ⊢s q σ ∘ (τ ,, M) ≈ σ ∘ τ ,, M : Γ, A }} by mauto 3.
  assert  {{ Γ'' ⊢ B[q σ∘(τ,,M)] ≈ B[σ∘τ,,M] }} by mauto 3.
  transitivity {{{ B[(q σ)∘(τ,,M)] }}}; mauto 3.
  eapply wf_typ_eq_sub_compose; mauto 4.
Qed.

Lemma sub_decompose_q_typ_sorted {P : PtsSig} : forall {Γ : ctx P} {A B σ Γ' Γ'' τ M s},
  {{ Γ, A ⊢ B : Sort@s }} ->
  {{ Γ' ⊢s σ : Γ }} ->
  {{ Γ'' ⊢s τ : Γ' }} ->
  {{ Γ'' ⊢ M : A[σ][τ] }} ->
  {{ Γ'' ⊢ B[σ∘τ,,M] ≈ B[q σ][τ,,M] : Sort@s }}.
Proof.
  intros. gen_presups.
  assert {{ Γ'' ⊢s q σ ∘ (τ ,, M) ≈ σ ∘ τ ,, M : Γ, A }} by mauto 3. 
  assert {{ Γ'' ⊢s τ,,M : Γ', A[σ] }} by mauto 4.
  assert {{ Γ'' ⊢s q σ∘(τ,,M) : Γ, A }} by mauto 4.
  assert  {{ Γ'' ⊢ B[q σ∘(τ,,M)] ≈ B[σ∘τ,,M] : Sort@s }} by mauto 3.
  transitivity {{{ B[(q σ)∘(τ,,M)] }}}; mauto 3.
  assert {{ Γ'' ⊢ B[q σ∘(τ,,M)] ≈ B[q σ][τ,,M] : Sort@s[q σ∘(τ,,M)] }} by (eapply wf_exp_eq_sub_compose; mauto 3).
  mauto 3.
Qed.

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

Lemma wf_exp_eq_elim_sub_lhs_typ_gen {P : PtsSig} : forall {Γ : ctx P} {Γ' σ M A B},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ', A ⊢ B }} ->
    {{ Γ' ⊢ M : A }} ->
    {{ Γ ⊢ B[Id,,M][σ] ≈ B[σ,,M[σ]] }}.
Proof.
  intros.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ' ⊢ A }} by mauto 3.
  assert {{ Γ' ⊢s Id,,M : Γ', A }} by mauto 4.
  assert {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Γ', A }} by mauto 3.
  transitivity {{{ B[(Id,,M)∘σ] }}}; mauto 3.
Qed.
#[export]
Hint Resolve wf_exp_eq_elim_sub_lhs_typ_gen : mcpts.

Lemma wf_exp_eq_elim_sub_lhs_typ_gen_sorted {P : PtsSig} : forall {Γ : ctx P} {Γ' σ M A B s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ', A ⊢ B : Sort@s }} ->
    {{ Γ' ⊢ M : A }} ->
    {{ Γ ⊢ B[Id,,M][σ] ≈ B[σ,,M[σ]] : Sort@s }}.
Proof.
  intros.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ' ⊢ A }} by mauto 3.
  assert {{ Γ' ⊢s Id,,M : Γ', A }} by mauto 4.
  assert {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Γ', A }} by mauto 3.
  transitivity {{{ B[(Id,,M)∘σ] }}}; mauto 3.
Qed.
#[export]
Hint Resolve wf_exp_eq_elim_sub_lhs_typ_gen_sorted : mcpts.

Lemma wf_exp_eq_elim_sub_rhs_typ {P : PtsSig} : forall {Γ : ctx P} {Γ' σ M A B},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ', A ⊢ B }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ B[q σ][Id,,M] ≈ B[σ,,M] }}.
Proof.
  intros.
  assert {{ Γ' ⊢ A }} by mauto 3.
  transitivity {{{ B[(σ∘Id),,M] }}}.
  - symmetry.
    eapply sub_decompose_q_typ; mauto 3.
  - eapply wf_typ_eq_sub_cong; mauto 2.
    eapply wf_sub_eq_extend_cong; mauto 2.
    eapply wf_exp_eq_conv'; mauto.
Qed.
#[export]
Hint Resolve wf_exp_eq_elim_sub_rhs_typ : mcpts.

Lemma wf_exp_eq_elim_sub_rhs_typ_sorted {P : PtsSig} : forall {Γ : ctx P} {Γ' σ M A B s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ', A ⊢ B : Sort@s }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ B[q σ][Id,,M] ≈ B[σ,,M] : Sort@s }}.
Proof.
  intros.
  assert {{ Γ' ⊢ A }} by mauto 3.
  transitivity {{{ B[(σ∘Id),,M] }}}.
  - symmetry.
    eapply sub_decompose_q_typ_sorted; mauto 3.
  - gen_presups.
    assert {{ Γ ⊢s σ∘Id ≈ σ : Γ' }} by mauto 3.
    assert {{ Γ ⊢s σ∘Id,,M : Γ', A }} by (econstructor; mauto 4).
    assert {{ Γ ⊢ B[σ∘Id,,M] ≈ B[σ,,M] : Sort@s[σ∘Id,,M] }} by (eapply wf_exp_eq_sub_cong; mauto).
    eapply wf_exp_eq_conv'; mauto 4.    
Qed.
#[export]
Hint Resolve wf_exp_eq_elim_sub_rhs_typ_sorted : mcpts.

Lemma wf_typ_eq_sub_cong2 {P : PtsSig} : forall {Γ : ctx P} {Γ' A σ τ},
    {{ Γ' ⊢ A }} ->
    {{ Γ ⊢s σ ≈ τ : Γ' }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] }}.
Proof with mautosolve 3.
  mauto 3.
Qed.

#[export]
Hint Resolve wf_typ_eq_sub_cong2 : mcpts.

Lemma wf_exp_eq_sorted_sub_cong2 {P : PtsSig} : forall {Γ : ctx P} {Γ' A σ τ s},
    {{ Γ' ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ ≈ τ : Γ' }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] : Sort@s }}.
Proof. 
  intros; gen_presups; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_sorted_sub_cong2 : mcpts.

Lemma wf_exp_pi_sub_lhs {P : PtsSig} : forall {Γ Γ' σ A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A : Sort@s1 }} ->
    {{ Γ', A ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ (Π r A B)[σ] : Sort@s3 }}.
Proof. 
  intros.
  gen_presups.
  mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_pi_sub_lhs : mcpts.

Lemma wf_exp_pi_sub_rhs {P : PtsSig} : forall {Γ Γ' σ A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A : Sort@s1 }} ->
    {{ Γ', A ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ Π r A[σ] B[q σ] : Sort@s3 }}.
Proof.
  intros.
  gen_presups.
  assert {{ Γ ⊢ A[σ] : Sort@s1 }} by mauto 2.
  assert {{ Γ, A[σ] ⊢s q σ : Γ', A }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ B[q σ] : Sort@s2 }} by mauto 3.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_pi_sub_rhs : mcpts.

Lemma wf_exp_pi_eta_rhs_body {P : PtsSig} : forall {Γ A B M s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ M : Π r A B }} ->
    {{ Γ, A ⊢ M[Wk] #0 : B }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }}) as [] by mauto 2.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊢s q Wk : Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢ M[Wk] : (Π r A B)[Wk] }} by mauto 3.
  assert {{ Γ, A ⊢ Π r A[Wk] B[q Wk] ≈ (Π r A B)[Wk] : Sort@s3 }} by mauto 3.
  assert {{ Γ, A ⊢ M[Wk] : Π r A[Wk] B[q Wk] }} by mauto 3.
  assert {{ Γ, A ⊢ #0 : A[Wk] }} by mauto 3.
  assert {{ Γ, A ⊢ M[Wk] #0 : B[q Wk][Id,,#0] }} by mauto 3.
  enough {{ Γ, A ⊢ B ≈ B[q Wk][Id,,#0] }} by mauto 3.
  assert {{ Γ, A ⊢s Id : Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢ B[q Wk][Id,,#0] ≈ B[Wk,,#0] }} as -> by mauto 3.
  assert {{ Γ, A ⊢s Wk,,#0 ≈ Id : Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢ B[Wk,,#0] ≈ B[Id] }} by mauto 3.
  assert {{ Γ, A ⊢ B[Id] ≈ B }} by mauto 3.
  transitivity {{{ B[Id] }}}; mauto 3.
Qed.
#[export]
Hint Resolve wf_exp_pi_eta_rhs_body : mcpts.

(** This works for both var_0 and var_S cases *)
Lemma wf_exp_eq_var_sub_rhs_typ_gen {P : PtsSig} : forall {Γ : ctx P} {Γ' σ A M},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] }}.
Proof.
  intros.
  assert {{ Γ ⊢s σ,,M : Γ', A }} by mauto 3.
  assert {{ Γ', A ⊢s Wk : Γ' }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][σ,,M] ≈ A[Wk∘(σ,,M)] }} by (symmetry; mauto 4).
  assert {{ Γ ⊢s Wk∘(σ,,M) ≈ σ : Γ' }} by mauto 2.
  assert {{ Γ ⊢ A[Wk∘(σ,,M)] ≈ A[σ] }} by mauto 3.
  transitivity {{{ A[Wk∘(σ,,M)] }}}; mauto 2.
Qed.
#[export]
Hint Resolve wf_exp_eq_var_sub_rhs_typ_gen : mcpts.

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

Lemma wf_ctx_eq_extend_wf_exp {P} : forall {Γ : ctx P} {Γ' A B M},
    {{ ⊢ Γ ≈ Γ' }} ->
    {{ Γ, A ⊢ M : B }} ->
    {{ Γ', A ⊢ M : B }}.
Proof.
  intros; gen_presups.
  assert {{ Γ ⊢ A ≈ A }} by mauto 3.
  assert {{ ⊢ Γ, A ≈ Γ', A }} by mauto 3.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_ctx_eq_extend_wf_exp : mcpts.

Lemma wf_exp_sub_ctx_extend_sub_q {P} : forall {Γ : ctx P} {Γ' σ A B M},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ', A ⊢ M : B }} ->
    {{ Γ, A[σ] ⊢ M[q σ] : B[q σ] }}.
Proof.
  intros; gen_presups.
  assert {{ Γ, A[σ] ⊢s q σ : Γ', A }} by mauto 3.
  mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_sub_ctx_extend_sub_q : mcpts.

Lemma wf_exp_sub_ctx_extend_sub_q_sorted {P} : forall {Γ : ctx P} {Γ' σ s A M},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ', A ⊢ M : Sort@s }} ->
    {{ Γ, A[σ] ⊢ M[q σ] : Sort@s }}.
Proof.
  intros; gen_presups.
  assert {{ Γ, A[σ] ⊢s q σ : Γ', A }} by mauto 3.
  mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_sub_ctx_extend_sub_q_sorted : mcpts.
  

Lemma wf_typ_eq_compose_cong {P} : forall {Γ : ctx P} {Γ' Γ'' A A' σ τ},
    {{ Γ'' ⊢ A' }} ->
    {{ Γ'' ⊢ A ≈ A' }} ->
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢ A[σ∘τ] ≈ A'[σ][τ] }}.
Proof.
  intros.
  assert {{ Γ ⊢ A'[σ∘τ] ≈ A'[σ][τ] }} as <- by mauto 4.
  mauto 3.
Qed.

#[export]
Hint Resolve wf_typ_eq_compose_cong : mcpts.
