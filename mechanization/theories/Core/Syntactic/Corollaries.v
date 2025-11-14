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
  mauto 4.
Qed.

#[export]
Hint Resolve sub_id_typ : mcpts.

Corollary invert_sub_id {P : PtsSig} : forall (Γ : ctx P) M A,
    {{ Γ ⊢ M[Id] : A }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros * [? [? [?%wf_sub_id_inversion []]]]%wf_exp_sub_inversion.
  assert {{ x ⊢ M : x0[Id] }} by (eapply sub_id_typ; mauto).
  assert {{ Γ ⊢ M : x0[Id] }} by mauto.
  eapply wf_conv'; mauto 4.
Qed.

#[export]
Hint Resolve invert_sub_id : mcpts.

Corollary invert_typ_id {P : PtsSig} : forall (Γ : ctx P) A,
    {{ Γ ⊢ A[Id] }} ->
    {{ Γ ⊢ A }}.
Proof.
  intros * H.
  inversion_clear H.
  - assert {{ Γ ⊢ A : Sort@s }} by mauto.
    mauto 2.
  - assert {{ ⊢ Γ ≈ Δ }} by mauto.
    mauto 3.
Qed.

Hint Resolve invert_typ_id : mcpts.

Corollary invert_sub_id_typ {P : PtsSig} : forall (Γ : ctx P) M A,
    {{ Γ ⊢ M : A[Id] }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros.
  gen_presups.
  assert {{ Γ ⊢ A }} by mauto.
  assert {{ Γ ⊢ A[Id] ≈ A }} by mauto.
  eapply wf_conv'; mauto.
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
    {{ ⊢ Γ ≈ Δ }} ->
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
  econstructor; mauto.
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
    eapply wf_exp_eq_conv'; mauto.
Qed.
#[export]
Hint Resolve sub_q_eq : mcpts.

Lemma wf_subtyp_subst_eq {P : PtsSig} : forall (Δ : ctx P) A B,
    {{ Δ ⊢ A ≈ B }} ->
    forall Γ σ σ',
      {{ Γ ⊢s σ ≈ σ' : Δ }} ->
      {{ Γ ⊢ A[σ] ≈ B[σ'] }}.
Proof.
  mauto.
Qed.

Lemma wf_subtyp_subst {P : PtsSig} : forall (Δ : ctx P) A B,
    {{ Δ ⊢ A ≈ B }} ->
    forall Γ σ,
      {{ Γ ⊢s σ : Δ }} ->
      {{ Γ ⊢ A[σ] ≈ B[σ] }}.
Proof.
  mauto.
Qed.
#[export]
Hint Resolve wf_subtyp_subst_eq wf_subtyp_subst : mcpts.

Lemma exp_typ_sub_lhs {P : PtsSig} : forall {Γ σ Δ s1 s2},
    Ax P s1 s2 ->
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
    assert {{ Δ' ⊢ #0[τ,,M] ≈ M : A[σ][τ] }} by (eapply wf_exp_eq_var_0_sub; mauto).
    eapply wf_sub_eq_extend_cong; mauto 2.
    assert {{ Γ ⊢ A ≈ A }} by mauto.
    assert {{ Δ' ⊢ A[σ][τ] ≈ A[σ∘τ] }} by mauto.
    assert {{ Δ' ⊢ A[σ∘τ] ≈ A[(σ∘Wk)∘(τ,,M)] }} by mauto.
    assert {{ Δ' ⊢ A[σ][τ] ≈ A[(σ∘Wk)∘(τ,,M)] }} by (etransitivity; mauto).
    eapply wf_exp_eq_conv; mauto 4.
  - mauto 5.
  - assert {{ Δ, A[σ] ⊢ A[σ][Wk] ≈ A[σ∘Wk] }} by (eapply exp_eq_sub_compose_typ; mauto 4).
    assert {{ #0 : A[σ][Wk] ∈ Δ, A[σ] }} by mauto.
    gen_presup H3.
    eapply wf_exp_conv with (A := {{{ A[σ][Wk] }}}); mauto.
Qed.

#[local]
Hint Rewrite -> @sub_decompose_q using mauto : mcpts.

Lemma sub_decompose_q_typ {P : PtsSig} : forall (Γ : ctx P) A B σ Δ Δ' τ M,
  {{ Γ, A ⊢ B }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ' ⊢s τ : Δ }} ->
  {{ Δ' ⊢ M : A[σ][τ] }} ->
  {{ Δ' ⊢ B[σ∘τ,,M] ≈ B[q σ][τ,,M] }}.
Proof.
  intros. gen_presups.
  assert {{ Δ' ⊢s q σ ∘ (τ ,, M) ≈ σ ∘ τ ,, M : Γ, A }} by (eapply sub_decompose_q; mauto 2).
  transitivity {{{ B[(q σ)∘(τ,,M)] }}}.
  - eapply wf_typ_eq_sub_cong; mauto 2.
  - eapply wf_typ_eq_sub_compose; mauto 4.
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
  eapply wf_exp_eq_conv; mauto 3.
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma_compose_tau_extend : mcpts.
#[export]
Hint Rewrite -> @sub_eq_p_q_sigma_compose_tau_extend using mauto 4 : mcpts.


(** This works for both natrec_sub and app_sub cases *)
Lemma exp_eq_elim_sub_lhs_typ_gen {P : PtsSig} : forall {Γ : ctx P} {σ Δ M A B},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, A ⊢ B }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢ B[Id,,M][σ] ≈ B[σ,,M[σ]] }}.
Proof.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert ({{ Δ ⊢ A }}) by mauto 3.
  assert {{ Δ ⊢s Id,,M : Δ, A }} by mauto 4.
  autorewrite with mcpts.
  assert {{ Γ ⊢ M[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢s σ,,M[σ] ≈ (Id,,M)∘σ : Δ, A }} by mauto.
  eapply wf_typ_eq_sub_cong; mauto 2.
Qed.
#[export]
Hint Resolve exp_eq_elim_sub_lhs_typ_gen : mcpts.

(** This works for both natrec_sub and app_sub cases *)
Lemma exp_eq_elim_sub_rhs_typ {P : PtsSig} : forall {Γ : ctx P} {σ Δ M A B},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, A ⊢ B }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ B[q σ][Id,,M] ≈ B[σ,,M] }}.
Proof.
  intros.
  assert ({{ Δ ⊢ A }}) by mauto 3.
  transitivity {{{ B[(σ∘Id),,M] }}}.
  - symmetry.
    eapply sub_decompose_q_typ; mauto 2.
    assert {{ Γ ⊢s σ∘Id,,M ≈ σ,,M : Δ, A }}.
    {
      eapply wf_sub_eq_extend_cong; mauto 2.
      eapply wf_exp_eq_conv'; mauto.
    }
    econstructor; mauto 2.
  - eapply wf_typ_eq_sub_cong; mauto 2.
    eapply wf_sub_eq_extend_cong; mauto 2.
    eapply wf_exp_eq_conv'; mauto.
Qed.
#[export]
Hint Resolve exp_eq_elim_sub_rhs_typ : mcpts.

Lemma exp_eq_sub_cong_typ2 {P : PtsSig} : forall {Δ : ctx P} {Γ A σ τ},
    {{ Δ ⊢ A }} ->
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] }}.
Proof with mautosolve 3.
  mauto.
Qed.

#[export]
Hint Resolve exp_eq_sub_cong_typ2 : mcpts.
#[export]
Remove Hints exp_eq_sub_cong_typ2' : mcpts.

Lemma exp_pi_sub_lhs {P : PtsSig} : forall {Γ : ctx P} {σ Δ A B s1 s2 s3} {r : Ru P s1 s2 s3},
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

Lemma exp_pi_sub_rhs {P : PtsSig} : forall {Γ : ctx P} {σ Δ A B s1 s2 s3} {r : Ru P s1 s2 s3},
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

Lemma exp_pi_eta_rhs_body {P : PtsSig} : forall {Γ : ctx P} {A B M s1 s2 s3} {r : Ru P s1 s2 s3},
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
  econstructor; [econstructor; revgoals; mauto 3 | mauto 3 |]. 
  (* eapply wf_typ_eq_exp. *)
  transitivity {{{ B[Wk∘Id,,#0] }}}.
  { 
    symmetry.
    eapply sub_decompose_q_typ; mauto 4.
  }
  transitivity {{{ B[Wk,,#0] }}}.
  - eapply wf_typ_eq_sub_cong with (Δ := {{{ Γ, A }}}); [| mauto 3].
    eapply wf_sub_eq_extend_cong; mauto 2.
    eapply wf_exp_eq_conv'; mauto 3.
    eapply wf_typ_eq_sub_cong; mauto 3.
  - assert {{ Γ, A ⊢s Wk,,#0 ≈ Id : Γ, A }}.
    {
      transitivity {{{ (^(@a_weaken P)∘Id),,#0[Id] }}}; mauto.
      eapply wf_sub_eq_extend_cong; mauto.
    }
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
  transitivity {{{ A[Wk∘(σ,,M)] }}}; mauto 3.
  mauto 4.
Qed.
#[export]
Hint Resolve exp_eq_var_sub_rhs_typ_gen : mcpts.

Lemma exp_sub_decompose_double_q_with_id_double_extend {P : PtsSig} : forall (Γ : ctx P) A B C σ Δ M N L,
  {{ Γ, B, C ⊢ M : A }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ ⊢ N : B[σ] }} ->
  {{ Δ ⊢ L : C[σ,,N] }} ->
  {{ Δ ⊢ M[σ,,N,,L] ≈ M[q (q σ)][Id,,N,,L] : A[σ,,N,,L] }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Γ ⊢ B }}) by mauto 3.
  assert {{ Δ, B[σ] ⊢s q σ : Γ, B }} by mauto 3.
  assert {{ Δ ⊢s Id,,N : Δ, B[σ] }} by mauto 3.
  assert {{ Δ ⊢ L : C[q σ][Id,,N] }} by mauto.
  assert {{ Δ ⊢ L : C[q σ∘(Id,,N)] }} by mauto.
  assert {{ Δ ⊢s Id,,N,,L : Δ, B[σ], C[q σ] }} by mauto 4.
  assert {{ Δ ⊢s q σ∘(Id,,N) ≈ σ,,N : Γ, B }} by mauto 3.
  assert {{ Δ ⊢ C[q σ][Id,,N] ≈ C[σ,,N] }} by mauto.
  assert {{ Δ ⊢s q (q σ)∘(Id,,N,,L) ≈ (q σ∘(Id,,N)),,L : Γ, B, C }} by (eapply sub_decompose_q; mauto 3).
  assert {{ Δ ⊢s q (q σ)∘(Id,,N,,L) ≈ σ,,N,,L : Γ, B, C }} by (bulky_rewrite; mauto 4).
  assert {{ Δ ⊢ A[q (q σ)][Id,,N,,L] ≈ A[q (q σ)∘(Id,,N,,L)] }} by mauto.
  assert {{ Δ ⊢ A[q (q σ)∘(Id,,N,,L)] ≈ A[σ,,N,,L] }} by mauto.
  assert {{ Δ ⊢ M[q (q σ)][Id,,N,,L] ≈ M[q (q σ)∘(Id,,N,,L)] : A[q (q σ)∘(Id,,N,,L)] }} by mauto. 
  assert {{ Δ ⊢ M[q (q σ)][Id,,N,,L] ≈ M[σ,,N,,L] : A[q (q σ)∘(Id,,N,,L)] }} by (bulky_rewrite; mauto 3).  
  symmetry; mauto 3.
Qed.

#[export]
Hint Resolve exp_sub_decompose_double_q_with_id_double_extend : mcpts.

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
    assert {{ Δ' ⊢ A[σ][τ] }} by mauto 3.
    assert {{ Δ', A[σ][τ] ⊢s Wk : Δ' }} by mauto 3.
    transitivity {{{ σ∘(τ∘Wk) }}}; [| mauto 3].
    econstructor; mauto 3.
  - assert {{ Δ', A[σ][τ] ⊢ A[(σ∘τ)∘Wk] ≈ A[σ∘(τ∘Wk)] }} by mauto 4.
    assert {{ Δ', A[σ][τ] ⊢ A[σ∘(τ∘Wk)] ≈ A[σ][τ∘Wk] }} by mauto.
    assert {{ Δ', A[σ][τ] ⊢ A[(σ∘τ)∘Wk] ≈ A[σ][τ∘Wk] }} by mauto 3.
    assert {{ Δ', A[σ][τ] ⊢ A[(σ∘τ)∘Wk] ≈ A[σ∘τ][Wk] }} by mauto 4.
    assert {{ Δ', A[σ][τ] ⊢ A[σ∘τ][Wk] ≈ A[σ][τ][Wk] }} by mauto 3.
    eapply wf_exp_eq_conv' with (A := {{{ A[σ][τ∘Wk] }}}); mauto 3.
    eapply wf_exp_eq_var_0_sub; mauto 4.
Qed.

#[export]
Hint Resolve sub_eq_q_compose : mcpts.
#[export]
Hint Rewrite -> @sub_eq_q_compose using mauto 4 : mcpts.



(** Lemmas need to go from untyped judgment back to typed judgments *)
(* Lemma pi_is_not_a_sort {P} : forall {Γ : ctx P} {s1 s2 s3} {r : Ru P s1 s2 s3} {s A B}, *)
(*     {{ Γ ⊢ Sort@s ≈ Π r A B }} -> False. *)
(* Proof. *)
(* Abort.  *)

(* Lemma wf_exp_eq_pi_inversion {P} : forall {Γ : ctx P} {s1 s2 s3} {r : Ru P s1 s2 s3} {A B C K}, *)
(*     {{ Γ ⊢ Π r A B ≈ C : K }} -> *)
(*     exists A' B', {{ Γ ⊢ A ≈ A' : Sort@s1 }} /\ {{ Γ, A ⊢ B ≈ B' : Sort@s2 }} /\ (C = {{{ Π r A' B' }}}). *)
(* Proof. *)
(*   intros * H. *)
(*   dependent induction H; subst. *)
(*   - do 2 eexists; repeat split; mauto 3. *)
(*   - assert {{ Γ ⊢ Sort@s3 ≈ Π r0 A0 B0 }} by (eapply wf_pi_inversion; mauto 3). *)
(*     assert False. *)
(*     { *)
(*       inversion H2; subst. *)
(*       + inversion H3; subst. *)
(*     } *)
(*     do 2 eexists; repeat split; mauto 3. *)
(*     admit. *)
(*   -  *)
(* Abort. *)
    
(* Lemma wf_typ_eq_pi_inversion {P} : forall {Γ : ctx P} {s1 s2 s3} {r : Ru P s1 s2 s3} {A B C}, *)
(*     {{ Γ ⊢ Π r A B ≈ C }} -> *)
(*     exists A' B', {{ Γ ⊢ A ≈ A' : Sort@s1 }} /\ {{ Γ, A ⊢ B ≈ B' : Sort@s2 }} /\ (C = {{{ Π r A' B' }}}). *)
(* Proof. *)
(*   intros * H. *)
(*   dependent induction H. *)
(* Abort. *)
  
(* Lemma wf_exp_wf_typ_eq_implies_wf_exp {P} : forall {Γ : ctx P} {A B K}, *)
(*     {{ Γ ⊢ A : K }} -> *)
(*     {{ Γ ⊢ A ≈ B }} -> *)
(*     {{ Γ ⊢ B : K }}. *)
(* Proof. *)
(*   intros * HAK. *)
(*   gen B. *)
(*   dependent induction HAK; intros; mauto 3. *)
(*   - admit. *)
(*   - *)
(* Abort. *)
    

(* Lemma wf_exp_wf_typ_eq_implies_wf_exp_eq {P} : forall {Γ : ctx P} {A B K}, *)
(*     {{ Γ ⊢ A : K }} -> *)
(*     {{ Γ ⊢ A ≈ B }} -> *)
(*     {{ Γ ⊢ A ≈ B : K }}. *)
(* Proof. *)
(*   intros * HAK. *)
(*   gen B. *)
(*   dependent induction HAK; intros. *)
(*   - inversion_clear H1; mauto 3. *)
(* Abort. *)
  
Lemma wf_exp_sub_sort_implies_wf_exp_sort {P} : forall {Γ Δ : ctx P} {σ A s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] : Sort@s }} ->
    {{ Δ ⊢ A : Sort@s }}.
Proof.
  intros * Hσ.
  dependent induction Hσ; intros; mauto 3.
  - admit.
  - admit.
  - admit.
Admitted.

(* Lemma wf_exp_sort_wf_exp_eq_sort_implies_wf_exp_eq_sort {P} : forall {Γ : ctx P} {A A' s s'}, *)
(*     {{ Γ ⊢ A : Sort@s }} -> *)
(*     {{ Γ ⊢ A ≈ A' : Sort@s' }} -> *)
(*     {{ Γ ⊢ A ≈ A' : Sort@s }}. *)
(* Proof. *)
(*   intros * HA. *)
(*   gen s' A'. *)
(*   induction HA. *)
  
(*   induction HAA'; intros s HA; mauto 3. *)
(*   - econstructor; mauto 3. *)
(*   - admit. *)
(*   -  *)
  
Lemma wf_exp_sort_wf_typ_eq_implies_wf_exp_eq_sort_right {P} : forall {Γ : ctx P} {A A' s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ A ≈ A' }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }}.
Proof.
  
  intros * HA HAA'.
  gen HA s.
  dependent induction HAA'; intros s' HA; mauto 3.
  - admit.
  - admit.
  - gen_presup H.
    assert {{ Δ ⊢ A : Sort@s' }} by (eapply (wf_exp_sub_sort_implies_wf_exp_sort Hσ HA); mauto).
    assert {{ Δ ⊢ A ≈ A' : Sort@s' }} by mauto.
    econstructor; mauto 3.
  - assert {{ Γ ⊢s σ∘τ : Γ'' }} by mauto 3.
    assert {{ Γ'' ⊢ A : Sort@s' }} by (eapply wf_exp_sub_sort_implies_wf_exp_sort; mauto).
    econstructor; mauto 3.
  - admit.
  - assert {{ Γ ⊢ A1 ≈ A2 : Sort@s' }} by mauto.
    gen_presups.
    assert {{ Γ ⊢ A2 ≈ A3 : Sort@s' }} by mauto.
    etransitivity; mauto 2.
Admitted.

#[export]
Hint Resolve wf_exp_sort_wf_typ_eq_implies_wf_exp_eq_sort_right : mcpts.


Lemma wf_exp_sort_wf_typ_eq_implies_wf_exp_eq_sort_left {P} : forall {Γ : ctx P} {A A' s},
    {{ Γ ⊢ A' : Sort@s }} ->
    {{ Γ ⊢ A ≈ A' }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_exp_sort_wf_typ_eq_implies_wf_exp_eq_sort_left : mcpts.


Lemma wf_exp_sort_wf_typ_eq_implies_wf_exp_sort_left {P} : forall {Γ : ctx P} {A A' s},
    {{ Γ ⊢ A' : Sort@s }} ->
    {{ Γ ⊢ A ≈ A' }} ->
    {{ Γ ⊢ A : Sort@s }}.
Proof. 
  intros.
  assert {{ Γ ⊢ A ≈ A' : Sort@s }} by mauto.
  gen_presups.
  eassumption.  
Qed.

#[export]
Hint Resolve wf_exp_sort_wf_typ_eq_implies_wf_exp_sort_left : mcpts.
  
Lemma wf_exp_sort_wf_typ_eq_implies_wf_exp_sort_right {P} : forall {Γ : ctx P} {A A' s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ A ≈ A' }} ->
    {{ Γ ⊢ A' : Sort@s }}.
Proof. mauto. Qed.
  
#[export]
Hint Resolve wf_exp_sort_wf_typ_eq_implies_wf_exp_sort_right : mcpts.
