From Coq Require Import Setoid Nat.
From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

Corollary sub_id_typ {P : PtsSig} : forall (Γ : ctx P) M A,
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A[Id] }}.
Proof.
  intros.
  gen_presups.
  mauto 3.
Qed.

#[export]
Hint Resolve sub_id_typ : mcpts.

Corollary invert_sub_id {P : PtsSig} : forall (Γ : ctx P) M A,
    {{ Γ ⊢ M[Id] : A }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros * [? [? [?%wf_sub_id_inversion []]]]%wf_exp_sub_inversion.
  mauto 4.
Qed.

#[export]
Hint Resolve invert_sub_id : mcpts.

Corollary invert_typ_id {P : PtsSig} : forall (Γ : ctx P) A,
    {{ Γ ⊢ A[Id] }} ->
    {{ Γ ⊢ A }}.
Proof.
  intros * H.
  inversion_clear H; [assert {{ Γ ⊢ A : Sort@s }} by mauto 2 |]; mauto 3.
Qed.

Hint Resolve invert_typ_id : mcpts.


Corollary invert_sub_id_typ {P : PtsSig} : forall (Γ : ctx P) M A,
    {{ Γ ⊢ M : A[Id] }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros.
  inversion_clear H;
    gen_presups.
  - inversion H2.
  - assert {{ Γ ⊢ A }} by mauto 3.
    assert {{ Γ ⊢ A[Id] ≈ A }} by mauto 3.
    mauto 3.
  - assert {{ Γ ⊢ A[Id] ≈ A }} by mauto 3.
    mauto 3.
Qed.

#[export]
Hint Resolve invert_sub_id_typ : mcpts.

Lemma invert_compose_id {P : PtsSig} : forall {Γ : ctx P} {σ Δ},
    {{ Γ ⊢s σ∘Id : Δ }} ->
    {{ Γ ⊢s σ : Δ }}.
Proof.
  intros * [? []]%wf_sub_compose_inversion.
  mauto 4.
Qed.

#[export]
Hint Resolve invert_compose_id : mcpts.

Add Parametric Morphism {P : PtsSig} (s : P) Γ Δ : a_sub
    with signature wf_exp_eq Δ {{{ Sort@s }}} ==> wf_sub_eq Γ Δ ==> wf_exp_eq Γ {{{ Sort@s }}} as sub_typ_cong.
Proof.
  intros.
  gen_presups.
  mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ1 : ctx P) Γ2 Γ3 : a_compose
    with signature wf_sub_eq Γ2 Γ3 ==> wf_sub_eq Γ1 Γ2 ==> wf_sub_eq Γ1 Γ3 as sub_compose_cong.
Proof. mauto. Qed.

Lemma wf_ctx_sub_length {P : PtsSig} : forall (Γ : ctx P) Δ,
    {{ ⊢ Γ ⊆ Δ }} ->
    length Γ = length Δ.
Proof. induction 1; simpl; auto. Qed.

Open Scope list_scope.

Lemma app_ctx_lookup {P : PtsSig} : forall (Δ : ctx P) T Γ n,
    length Δ = n ->
    {{ #n : ^(iter (S n) (fun T => {{{ T[Wk] }}}) T) ∈ ^(Δ ++ T :: Γ) }}.
Proof.
  induction Δ; intros; simpl in *; subst; mauto.
Qed.

Lemma ctx_lookup_functional {P : PtsSig} : forall n (T : exp P) Γ,
    {{ #n : T ∈ Γ }} ->
    forall T',
      {{ #n : T' ∈ Γ }} ->
      T = T'.
Proof.
  induction 1; intros; progressive_inversion; eauto.
  assert (A = A0) by mauto.
  subst.
  mauto.
Qed.

Lemma app_ctx_vlookup {P : PtsSig} : forall (Δ : ctx P) T Γ n,
    {{ ⊢ ^(Δ ++ T :: Γ) }} ->
    length Δ = n ->
    {{ ^(Δ ++ T :: Γ) ⊢ #n : ^(iter (S n) (fun T => {{{ T[Wk] }}}) T) }}.
Proof.
  intros.
  assert {{ #n : ^(iter (S n) (fun T' => {{{ T'[Wk] }}}) T) ∈ ^(Δ ++ T :: Γ) }} by (eapply app_ctx_lookup; mauto).
  subst.
  eapply wf_vlookup'; mauto.
Qed.

Lemma sub_q_eq {P : PtsSig} : forall (Δ : ctx P) A Γ σ σ',
    {{ Δ ⊢ A }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ, A[σ] ⊢s q σ ≈ q σ' : Δ, A }}.
Proof.
  intros. gen_presup H0.
  econstructor; mauto 3.
  - econstructor; mauto 4.
  - assert {{ #0 : A[σ][Wk] ∈ Γ, A[σ] }} by mauto.
    assert {{ Γ, A[σ] ⊢ #0 ≈ #0 : A[σ][Wk] }} by mauto.
    assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 3.    
    eapply wf_exp_eq_conv'; mauto 3.
Qed.
#[export]
Hint Resolve sub_q_eq : mcpts.

Lemma wf_subtyp_subst_eq {P : PtsSig} : forall (Δ : ctx P) A B,
    {{ Δ ⊢ A ⊆ B }} ->
    forall Γ σ σ',
      {{ Γ ⊢s σ ≈ σ' : Δ }} ->
      {{ Γ ⊢ A[σ] ⊆ B[σ'] }}.
Proof.
  induction 1; intros * Hσσ'; gen_presup Hσσ'; mauto 3.
  - etransitivity; mauto 3.
  - (* autorewrite with mcpts. *)
    assert {{ Γ0 ⊢ Sort@s2[σ'] ≈ Sort@s2 }} by mauto 2.
    transitivity {{{ Sort@s1 }}}; mauto 3.
    transitivity {{{ Sort@s2 }}}; mauto 3.
  - (* autorewrite with mcpts. *)
    assert {{ Γ0 ⊢ A'[σ] ≈ A'[σ'] : Sort@s1 }} by mauto 2.
    assert {{ Γ0, A[σ] ⊢s q σ : Γ, A }} by mauto 3.
    assert {{ Γ0, A'[σ'] ⊢s q σ ≈ q σ' : Γ, A' }} by mauto 5.
    transitivity {{{ Π r (A[σ]) (B[q σ]) }}}; mauto 4.
    transitivity {{{ Π r (A'[σ']) (B'[q σ']) }}}; [| econstructor; mauto 4].
    eapply wf_subtyp_pi; mauto 4.
Qed.

Lemma wf_subtyp_subst {P : PtsSig} : forall (Δ : ctx P) A B,
    {{ Δ ⊢ A ⊆ B }} ->
    forall Γ σ,
      {{ Γ ⊢s σ : Δ }} ->
      {{ Γ ⊢ A[σ] ⊆ B[σ] }}.
Proof.
  intros; mauto 2 using wf_subtyp_subst_eq.
Qed.
#[export]
Hint Resolve wf_subtyp_subst_eq wf_subtyp_subst : mcpts.


Lemma exp_typ_sub_lhs {P : PtsSig} : forall {Γ σ Δ s1 s2},
    Ax_typ P s1 s2 ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ Sort@s1[σ] : Sort@s2 }}.
Proof.
  intros; mauto 4.
Qed.
#[export]
Hint Resolve exp_typ_sub_lhs : mcpts.

Lemma sub_decompose_q {P : PtsSig} : forall (Γ : ctx P) A σ Δ Δ' τ M,
  {{ Γ ⊢ A }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ' ⊢s τ : Δ }} ->
  {{ Δ' ⊢ M : A[σ][τ] }} ->
  {{ Δ' ⊢s q σ ∘ (τ ,, M) ≈ σ ∘ τ ,, M : Γ, A }}.
Proof.
  intros. gen_presups.
  simpl.
  rewrite wf_sub_eq_extend_compose; mauto 3.
  - assert {{ Δ' ⊢s (σ∘Wk)∘(τ,,M) ≈ σ∘(Wk∘(τ,,M)) : Γ }}.
    {
      eapply wf_sub_eq_compose_assoc; mauto 3.
      econstructor; mauto 3.
    }
    assert {{ Δ' ⊢s σ∘(Wk∘(τ,,M)) ≈ σ∘τ : Γ }} by (eapply wf_sub_eq_compose_cong; mauto).
    assert {{ Δ' ⊢s (σ∘Wk)∘(τ,,M) ≈ σ∘τ : Γ}} by (etransitivity; mauto).
    assert {{ Δ' ⊢ #0[τ,,M] ≈ M : A[σ][τ] }} by (eapply wf_exp_eq_var_0_sub; mauto 3).
    eapply wf_sub_eq_extend_cong; mauto 2.
    assert {{ Γ ⊢ A ≈ A }} by mauto.
    assert {{ Δ' ⊢ A[σ][τ] ≈ A[σ∘τ] }} by mauto.
    assert {{ Δ' ⊢ A[σ∘τ] ≈ A[(σ∘Wk)∘(τ,,M)] }} by mauto 4.
    assert {{ Δ' ⊢ A[σ][τ] ≈ A[(σ∘Wk)∘(τ,,M)]  }} by (etransitivity; mauto).
    eapply wf_exp_eq_conv; mauto 3.
  - mauto 5.
  - assert {{ Δ, A[σ] ⊢s Wk : Δ }} by mauto 4.
    assert {{ Δ, A[σ] ⊢s σ∘Wk : Γ }} by mauto 2.
    assert {{ Δ, A[σ] ⊢ A[σ][Wk] ≈ A[σ∘Wk] }} by mauto 2.
    assert {{ #0 : A[σ][Wk] ∈ Δ, A[σ] }} by mauto.
    gen_presup H3.
    eapply wf_exp_conv with (A := {{{ A[σ][Wk] }}}); mauto 3.
Qed.

#[local]
  Hint Rewrite -> @sub_decompose_q using mauto : mcpts.


Lemma exp_nat_sub_lhs {P} : forall {Γ : ctx P} {σ Δ s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ ℕ[σ] : Sort@s }}.
Proof.
  intros; mauto 4.
Qed.
#[export]
Hint Resolve exp_nat_sub_lhs : mcpts.

Lemma exp_zero_sub_lhs {P} : forall {Γ : ctx P} {σ Δ s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ zero[σ] : ℕ }}.
Proof.
  intros; mauto 4.
Qed.
#[export]
Hint Resolve exp_zero_sub_lhs : mcpts.

Lemma exp_succ_sub_lhs {P} : forall {Γ : ctx P} {σ Δ M s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢ (succ M)[σ] : ℕ }}.
Proof.
  intros; mauto 3.
Qed.
#[export]
Hint Resolve exp_succ_sub_lhs : mpts.

Lemma exp_succ_sub_rhs {P} : forall {Γ : ctx P} {σ Δ M s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢ succ (M[σ]) : ℕ }}.
Proof.
  intros; mauto 3.
Qed.
#[export]
Hint Resolve exp_succ_sub_rhs : mcpts.

Lemma sub_decompose_q_typ {P : PtsSig} : forall (Γ : ctx P) A B σ Δ Δ' τ M,
  {{ Γ, A ⊢ B }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ' ⊢s τ : Δ }} ->
  {{ Δ' ⊢ M : A[σ][τ] }} ->
  {{ Δ' ⊢ B[σ∘τ,,M] ≈ B[q σ][τ,,M]  }}.
Proof.
  intros. gen_presups.
  assert {{ Δ' ⊢s q σ ∘ (τ ,, M) ≈ σ ∘ τ ,, M : Γ, A }} by (eapply sub_decompose_q; mauto 2).
  assert  {{ Δ' ⊢ B[q σ∘(τ,,M)] ≈ B[σ∘τ,,M] }} by mauto 4.
  transitivity {{{ B[(q σ)∘(τ,,M)] }}}; mauto 4.
  eapply wf_typ_eq_sub_compose; mauto 4.
Qed.

Lemma sub_decompose_q_typ_sorted {P : PtsSig} : forall (Γ : ctx P) A B σ Δ Δ' τ M s,
  {{ Γ, A ⊢ B : Sort@s }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ' ⊢s τ : Δ }} ->
  {{ Δ' ⊢ M : A[σ][τ] }} ->
  {{ Δ' ⊢ B[σ∘τ,,M] ≈ B[q σ][τ,,M] : Sort@s }}.
Proof.
  intros. gen_presups.
  assert {{ Δ' ⊢s q σ ∘ (τ ,, M) ≈ σ ∘ τ ,, M : Γ, A }} by (eapply sub_decompose_q; mauto 2).
  assert {{ Δ' ⊢s τ,,M : Δ, A[σ] }} by mauto 4.
  assert {{ Δ' ⊢s q σ∘(τ,,M) : Γ, A }} by mauto 4.
  assert  {{ Δ' ⊢ B[q σ∘(τ,,M)] ≈ B[σ∘τ,,M] : Sort@s }} by mauto 4.
  transitivity {{{ B[(q σ)∘(τ,,M)] }}}; mauto 4.
  assert {{ Δ' ⊢ B[q σ∘(τ,,M)] ≈ B[q σ][τ,,M] : Sort@s[q σ∘(τ,,M)] }} by (eapply wf_exp_eq_sub_compose_typ; mauto 3).
  mauto 3.
Qed.

Lemma sub_eq_p_q_sigma_compose_tau_extend {P : PtsSig} : forall {Δ' : ctx P} {τ Δ M A σ Γ},
    {{ Δ ⊢s σ : Γ }} ->
    {{ Δ' ⊢s τ : Δ }} ->
    {{ Γ ⊢ A }} ->
    {{ Δ' ⊢ M : A[σ][τ] }} ->
    {{ Δ' ⊢s Wk∘(q σ∘(τ,,M)) ≈ σ∘τ : Γ }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Δ, A[σ] ⊢s q σ : Γ, A }} by mauto 2.
  assert {{ Δ' ⊢s τ,,M : Δ, A[σ] }} by mauto 3.
  transitivity {{{ Wk∘((σ∘τ),,M) }}}; [| autorewrite with mcpts; mauto 3].
  eapply wf_sub_eq_compose_cong; [| mauto 2].
  autorewrite with mcpts.
  econstructor; mauto 3.
  assert {{ Δ' ⊢ A[σ∘τ] ≈ A[σ][τ] }} by mauto.
  eapply wf_exp_eq_conv; mauto 4.
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma_compose_tau_extend : mcpts.
#[export]
Hint Rewrite -> @sub_eq_p_q_sigma_compose_tau_extend using mauto 4 : mcpts.

Lemma exp_eq_elim_sub_lhs_typ_gen {P : PtsSig} : forall {Γ : ctx P} {σ Δ M A B},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, A ⊢ B }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢ B[Id,,M][σ] ≈ B[σ,,M[σ]] }}.
Proof.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Δ ⊢ A }} by mauto 3.
  assert {{ Δ ⊢s Id,,M : Δ, A }} by mauto 4.
  assert {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Δ, A }} by mauto 3.
  transitivity {{{ B[(Id,,M)∘σ] }}}; mauto 3.
Qed.
#[export]
Hint Resolve exp_eq_elim_sub_lhs_typ_gen : mcpts.

Lemma exp_eq_elim_sub_lhs_typ_gen_sorted {P : PtsSig} : forall {Γ : ctx P} {σ Δ M A B s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, A ⊢ B : Sort@s }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢ B[Id,,M][σ] ≈ B[σ,,M[σ]] : Sort@s }}.
Proof.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Δ ⊢ A }} by mauto 3.
  assert {{ Δ ⊢s Id,,M : Δ, A }} by mauto 4.
  assert {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Δ, A }} by mauto 3.
  transitivity {{{ B[(Id,,M)∘σ] }}}; mauto 3.
Qed.
#[export]
Hint Resolve exp_eq_elim_sub_lhs_typ_gen_sorted : mcpts.

Lemma exp_eq_elim_sub_rhs_typ {P : PtsSig} : forall {Γ : ctx P} {σ Δ M A B},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, A ⊢ B }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ B[q σ][Id,,M] ≈ B[σ,,M] }}.
Proof.
  intros.
  assert {{ Δ ⊢ A }} by mauto 3.
  transitivity {{{ B[(σ∘Id),,M] }}}.
  - symmetry.
    eapply sub_decompose_q_typ; mauto 3.
  - eapply wf_typ_eq_sub_cong; mauto 2.
    eapply wf_sub_eq_extend_cong; mauto 2.
    eapply wf_exp_eq_conv'; mauto.
Qed.
#[export]
Hint Resolve exp_eq_elim_sub_rhs_typ : mcpts.

Lemma exp_eq_elim_sub_rhs_typ_sorted {P : PtsSig} : forall {Γ : ctx P} {σ Δ M A B s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, A ⊢ B : Sort@s }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ B[q σ][Id,,M] ≈ B[σ,,M] : Sort@s }}.
Proof.
  intros.
  assert {{ Δ ⊢ A }} by mauto 3.
  transitivity {{{ B[(σ∘Id),,M] }}}.
  - symmetry.
    eapply sub_decompose_q_typ_sorted; mauto 3.
  - gen_presups.
    assert {{ Γ ⊢s σ∘Id ≈ σ : Δ }} by mauto 3.
    assert {{ Γ ⊢s σ∘Id,,M : Δ, A }} by (econstructor; mauto 4).
    assert {{ Γ ⊢ B[σ∘Id,,M] ≈ B[σ,,M] : Sort@s[σ∘Id,,M] }} by (eapply wf_exp_eq_sub_cong_typ; mauto).
    eapply wf_exp_eq_conv'; mauto 4.    
Qed.
#[export]
Hint Resolve exp_eq_elim_sub_rhs_typ_sorted : mcpts.

Lemma exp_eq_sub_cong_typ2 {P : PtsSig} : forall {Δ : ctx P} {Γ A σ τ},
    {{ Δ ⊢ A }} ->
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] }}.
Proof with mautosolve 3.
  mauto.
Qed.

#[export]
  Hint Resolve exp_eq_sub_cong_typ2 : mcpts.


Lemma exp_eq_sub_cong_typ2_sorted {P : PtsSig} : forall {Δ : ctx P} {Γ A σ τ s},
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] : Sort@s }}.
Proof. 
  intros; gen_presups; mauto.
Qed.

#[export]
Hint Resolve exp_eq_sub_cong_typ2_sorted : mcpts.

Lemma exp_pi_sub_lhs {P : PtsSig} : forall {Γ : ctx P} {σ Δ A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ Δ, A ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ (Π r A B)[σ] : Sort@s3 }}.
Proof.
  intros.
  mauto 4.
Qed.

#[export]
Hint Resolve exp_pi_sub_lhs : mcpts.

Lemma exp_pi_sub_rhs {P : PtsSig} : forall {Γ : ctx P} {σ Δ A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ Δ, A ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ Π r A[σ] B[q σ] : Sort@s3 }}.
Proof.
  intros.
  econstructor; mauto 4.
Qed.

#[export]
Hint Resolve exp_pi_sub_rhs : mcpts.

Lemma exp_pi_eta_rhs_body {P : PtsSig} : forall {Γ : ctx P} {A B M s1 s2 s3} {r : Ru_pi P s1 s2 s3},
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
  assert {{ Γ, A ⊢ M[Wk] : Π r A[Wk] B[q Wk] }} by mauto 4.
  eapply wf_conv_typ; [ econstructor; revgoals; mauto 3 |]; mauto 3.
  transitivity {{{ B[Wk∘Id,,#0] }}}.
  {
    symmetry.
    eapply sub_decompose_q_typ; mauto 4.
  }
  transitivity {{{ B[Wk,,#0] }}}.
  - eapply wf_typ_eq_sub_cong with (Δ := {{{ Γ, A }}}); [mauto 3 |].
    eapply wf_sub_eq_extend_cong; mauto 2.
    eapply wf_exp_eq_conv'; mauto 3.
    eapply wf_typ_eq_sub_cong; mauto 3.
  - assert {{ Γ, A ⊢s Wk,,#0 ≈ Id : Γ, A }} by mauto 3.
    transitivity {{{ B[Id] }}}; mauto.
Qed.
#[export]
Hint Resolve exp_pi_eta_rhs_body : mcpts.

(** This works for both var_0 and var_S cases *)
Lemma exp_eq_var_sub_rhs_typ_gen {P : PtsSig} : forall {Γ : ctx P} {σ Δ A M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] }}.
Proof.
  intros.
  assert {{ Γ ⊢s σ,,M : Δ, A }} by mauto 3.
  assert {{ Δ, A ⊢s Wk : Δ }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][σ,,M] ≈ A[Wk∘(σ,,M)] }} by (symmetry; mauto 4).
  assert {{ Γ ⊢s Wk∘(σ,,M) ≈ σ : Δ }} by mauto 2.
  assert {{ Γ ⊢ A[Wk∘(σ,,M)] ≈ A[σ] }} by mauto 3.
  transitivity {{{ A[Wk∘(σ,,M)] }}}; mauto 2.
Qed.
#[export]
Hint Resolve exp_eq_var_sub_rhs_typ_gen : mcpts.

Lemma exp_sub_decompose_double_q_with_id_double_extend {P : PtsSig} : forall (Γ : ctx P) A B C σ Δ M N L,
    {{ Γ, B, C ⊢ A }} ->
    {{ Γ, B, C ⊢ M : A }} ->
    {{ Δ ⊢s σ : Γ }} ->
    {{ Δ ⊢ N : B[σ] }} ->
    {{ Δ ⊢ L : C[σ,,N] }} ->
    {{ Δ ⊢ M[σ,,N,,L] ≈ M[q (q σ)][Id,,N,,L] : A[σ,,N,,L] }}.
Proof.
  intros.
  gen_presups.
  assert {{ Γ ⊢ B }} by mauto 3.

  assert {{ Δ, B[σ] ⊢s q σ : Γ, B }} by mauto 3.
  assert {{ Δ ⊢s Id,,N : Δ, B[σ] }} by mauto 3.
  assert {{ Δ ⊢s q σ∘(Id,,N) ≈ σ,,N : Γ, B }} by mauto 3.
  assert {{ Γ, B ⊢ C }} by mauto 3.
  assert {{ Δ ⊢ C[q σ][Id,,N] }} by mauto 4.  
  assert {{ Δ ⊢ C[σ,,N] ≈ C[q σ][Id,,N] }} by mauto 4.
  assert {{ Δ ⊢ L : C[q σ][Id,,N] }} by mauto 3.
  assert {{ Δ ⊢ L : C[q σ∘(Id,,N)] }} by mauto 3.
  assert {{ Δ ⊢s Id,,N,,L : Δ, B[σ], C[q σ] }} by mauto 3.
  assert {{ Δ ⊢s q σ∘(Id,,N) ≈ σ,,N : Γ, B }} by mauto 3.
  assert {{ Δ ⊢ C[q σ∘(Id,,N)] ≈ C[σ,,N] }} by mauto 3.
  assert {{ Δ ⊢ C[q σ][Id,,N] ≈ C[σ,,N] }} by mauto 3.
  assert {{ Δ ⊢s q (q σ)∘(Id,,N,,L) : Γ, B, C }} by mauto 3.
  assert {{ Δ ⊢s q (q σ)∘(Id,,N,,L) ≈ (q σ∘(Id,,N)),,L : Γ, B, C }} by (eapply sub_decompose_q; mauto 3).
  assert {{ Δ ⊢s q (q σ)∘(Id,,N,,L) ≈ σ,,N,,L : Γ, B, C }} by (bulky_rewrite; mauto 3).
  assert {{ Δ ⊢ A[q (q σ)][Id,,N,,L] ≈ A[q (q σ)∘(Id,,N,,L)] }} by mauto 3.
  assert {{ Δ ⊢s q (q σ)∘(Id,,N,,L) ≈ σ,,N,,L : Γ, B, C }} by mauto 3.
  assert {{ Δ ⊢ A[q (q σ)∘(Id,,N,,L)] ≈ A[σ,,N,,L] }} by mauto 3.
  assert {{ Δ ⊢ M[q (q σ)][Id,,N,,L] ≈ M[q (q σ)∘(Id,,N,,L)] : A[q (q σ)∘(Id,,N,,L)] }} by mauto 4.
  assert {{ Δ ⊢ M[q (q σ)][Id,,N,,L] ≈ M[σ,,N,,L] : A[q (q σ)∘(Id,,N,,L)] }} by (bulky_rewrite; mauto 4).
  symmetry; mauto 3.
Qed.

#[export]
  Hint Resolve exp_sub_decompose_double_q_with_id_double_extend : mcpts.

Lemma exp_eq_natrec_cong_rhs_typ {P} : forall {Γ : ctx P} {M M' A A' s} {r : Ru_nat P s},
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
  Hint Resolve exp_eq_natrec_cong_rhs_typ : mcpts.

Lemma exp_eq_nat_beta_succ_rhs_typ_gen {P} : forall {Γ : ctx P} {σ Δ A M N s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, ℕ ⊢ A }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ N : A[σ,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk,,succ #1][σ,,M,,N] ≈ A[σ,,succ M] }}.
Proof.
  intros.
  assert {{ ⊢ Δ }} by mauto 3.
  assert {{ Δ, ℕ ⊢s Wk : Δ }} by mauto 3.
  assert {{ Δ, ℕ, A ⊢s Wk : Δ, ℕ }} by mauto 4.
  assert {{ Δ, ℕ, A ⊢s Wk∘Wk : Δ }} by mauto 3.
  assert {{ Δ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by mauto 4.
  assert {{ Γ ⊢s σ,,M : Δ, ℕ }} by mauto 4.
  assert {{ Γ ⊢s σ,,M,,N : Δ, ℕ, A }} by mauto 3.
  assert {{ Γ ⊢s σ,,M,,N : Δ, ℕ, A }} by mauto 3.
  autorewrite with mcpts.
  assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M,,N) : Δ, ℕ }} by mauto 3.
  assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M,,N) ≈ ((Wk∘Wk)∘(σ,,M,,N)),,(succ #1)[σ,,M,,N] : Δ, ℕ }} by mauto 4.
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ Wk∘(Wk∘(σ,,M,,N)) : Δ }} by mauto 3.
  assert {{ Γ ⊢s Wk∘(σ,,M,,N) ≈ σ,,M : Δ, ℕ }} by (autorewrite with mcpts; mauto 3).
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ Wk∘(σ,,M) : Δ }} by (unshelve bulky_rewrite; constructor).
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ σ : Δ }} by bulky_rewrite.
  assert {{ Γ ⊢ (succ #1)[σ,,M,,N] ≈ succ (#1[σ,,M,,N]) : ℕ }} by mauto 3.
  assert {{ Γ ⊢ (succ #1)[σ,,M,,N] ≈ succ (#0[σ,,M]) : ℕ }} by (bulky_rewrite; mauto 4).
  assert {{ Γ ⊢ (succ #1)[σ,,M,,N] ≈ succ M : ℕ }} by (bulky_rewrite; mauto 3).
  assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N),,(succ #1)[σ,,M,,N] ≈ σ,,succ M : Δ, ℕ }} by mauto 3.
  assert {{ Γ ⊢ A[(Wk∘Wk,,succ #1)∘(σ,,M,,N)] ≈ A[(Wk∘Wk)∘(σ,,M,,N),,(succ #1)[σ,,M,,N]] }} by mauto 3.
  assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M,,N) ≈ σ,,(succ M) : Δ, ℕ }} by mauto 3.
  transitivity {{{ A[(Wk∘Wk)∘(σ,,M,,N),,(succ #1)[σ,,M,,N]] }}}; mauto 4.
Qed.
#[export]
Hint Resolve exp_eq_nat_beta_succ_rhs_typ_gen : mcpts.


Lemma sub_eq_q_compose {P : PtsSig} : forall {Γ : ctx P} {A σ Δ τ Δ'},
  {{ Γ ⊢ A }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ' ⊢s τ : Δ }} ->
  {{ Δ', A[σ∘τ] ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, A }}.
Proof.
  intros.
  assert {{ ⊢ Δ' }} by mauto 3.
  assert {{ Δ' ⊢ A[σ∘τ] ≈ A[σ][τ] }} by mauto.
  assert {{ ⊢ Δ', A[σ][τ] }} by mauto 4.
  assert {{ ⊢ Δ', A[σ∘τ] ≈ Δ', A[σ][τ] }} as -> by mauto.
  assert {{ ⊢ Δ }} by mauto 3.
  assert {{ ⊢ Δ, A[σ] }} by mauto 3.
  assert {{ Δ, A[σ] ⊢s Wk : Δ }} by mauto 3.
  assert {{ Δ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 3.
  assert {{ Δ, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto 3.
  transitivity {{{ ((σ∘Wk)∘q τ),,#0[q τ] }}}; [econstructor; mauto 3 |].
  symmetry; econstructor; mauto 3; symmetry.
  - transitivity {{{ σ∘(Wk∘q τ) }}}; [mauto 4 |].
    assert {{ Δ' ⊢ A[σ][τ] }} by mauto 4.
    assert {{ Δ', A[σ][τ] ⊢s Wk : Δ' }} by mauto 3.
    transitivity {{{ σ∘(τ∘Wk) }}}; [| mauto 3].
    econstructor; mauto 3.
  - assert {{ Δ', A[σ][τ] ⊢s (σ∘τ)∘Wk ≈ σ∘(τ∘Wk) : Γ }} by mauto 3.
    gen_presup H10.
    assert {{ Δ', A[σ][τ] ⊢s τ∘Wk : Δ }} by mauto 3.
    assert {{ Δ', A[σ][τ] ⊢s (σ∘τ)∘Wk : Γ }} by mauto 3.
    assert {{ Δ', A[σ][τ] ⊢ A[(σ∘τ)∘Wk] ≈ A[σ∘(τ∘Wk)] }} by mauto 3.
    assert {{ Δ', A[σ][τ] ⊢ A[σ∘(τ∘Wk)] ≈ A[σ][τ∘Wk] }} by mauto 3.
    assert {{ Δ', A[σ][τ] ⊢ A[(σ∘τ)∘Wk] ≈ A[σ][τ∘Wk] }} by mauto 3.
    assert {{ Δ', A[σ][τ] ⊢ A[(σ∘τ)∘Wk] ≈ A[σ∘τ][Wk] }} by mauto.
    assert {{ Δ', A[σ][τ] ⊢ A[σ∘τ][Wk] ≈ A[σ][τ][Wk] }} by mauto 3.
    eapply eq_conv_typ with (A := {{{ A[σ][τ∘Wk] }}}); mauto 3.
    eapply wf_exp_eq_var_0_sub; mauto 3.
    eapply wf_conv_typ with (A := {{{ A[σ][τ][Wk] }}}); mauto 3.
    symmetry.
    transitivity {{{ A[σ∘τ][Wk] }}}; mauto 4.
Qed.

#[export]
Hint Resolve sub_eq_q_compose : mcpts.
#[export]
Hint Rewrite -> @sub_eq_q_compose using mauto 4 : mcpts.

Lemma sub_eq_q_compose_nat {P} : forall {Γ : ctx P} {σ Δ τ Δ' s} {r : Ru_nat P s},
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ' ⊢s τ : Δ }} ->
  {{ Δ', ℕ ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, ℕ }}.
Proof.
  intros.
  assert {{ Γ ⊢ ℕ : Sort@s }} by mauto 4.
  assert {{ Δ' ⊢ ℕ[σ∘τ] ≈ ℕ : Sort@s }} by mauto 3.
  assert {{ ⊢ Δ' }} by mauto 3.
  assert {{ Δ' ⊢ ℕ : Sort@s }} by mauto 3.
  assert {{ Δ' ⊢ ℕ[σ∘τ] : Sort@s }} by mauto 3.
  assert {{ ⊢ Δ', ℕ[σ∘τ] ≈ Δ', ℕ }} by (econstructor; mauto 4).
  mautosolve 4.
Qed.

#[export]
Hint Resolve sub_eq_q_compose_nat : mcpts.
#[export]
Hint Rewrite -> @sub_eq_q_compose_nat using mauto 4 : mcpts.

Lemma exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1 {P} : forall {Γ : ctx P} {Δ σ A s} {r : Ru_nat P s},
    {{ Δ ⊢s σ : Γ }} ->
    {{ Γ, ℕ ⊢ A }} ->
    {{ Δ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q σ)] }}.
Proof.
  intros.
  assert {{ Δ, ℕ ⊢s q σ : Γ, ℕ }} by (econstructor; mauto 3).
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by (eapply @sub_weak_compose_weak_extend_succ_var_1 with (P := P); mauto 3).
  assert {{ Δ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[q σ∘(Wk∘Wk,,succ #1)] }} as -> by mauto 3.

  assert {{ Δ, ℕ, A[q σ] ⊢s q (q σ) : Γ, ℕ, A }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by (eapply @sub_weak_compose_weak_extend_succ_var_1 with (P := P); mauto 3).
  assert {{ Δ, ℕ, A[q σ] ⊢ A[Wk∘Wk,,succ #1][q (q σ)] ≈ A[(Wk∘Wk,,succ #1)∘q (q σ)] }} by (symmetry; mauto 3).
  transitivity {{{ A[(Wk∘Wk,,succ #1)∘q (q σ)] }}}; mauto 2.
  mauto 4.
Qed.

#[export]
Hint Resolve exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1 : mcpts.
