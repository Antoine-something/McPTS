From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export CtxEq.
Import Syntax_Notations.

(** * Presuposition cases for [wf_exp_eq] *)

(** ** Function cases *)
Lemma presup_wf_exp_eq_fn_cong_right {P : PtsSig} : forall {Δ : gctx P} {Γ A A' B B' M' s1 s2 s3} (r : Ru_pi P s1 s2 s3),
    {{ Δ ⊢ Γ }} ->
    {{ Δ ; Γ ⊢ A : Sort@s1 }} ->
    {{ Δ ; Γ ⊢ A' : Sort@s1 }} ->
    {{ Δ ; Γ ⊢ A ≈ A' : Sort@s1 }} ->
    {{ Δ ⊢ Γ, A }} ->
    {{ Δ ; Γ, A ⊢ B : Sort@s2 }} ->
    {{ Δ ; Γ, A ⊢ B' : Sort@s2 }} ->
    {{ Δ ; Γ, A ⊢ B ≈ B' : Sort@s2 }} ->
    {{ Δ ; Γ, A ⊢ M' : B' }} ->
    {{ Δ ; Γ ⊢ λ r A' B' M' : Π r A B }}.
Proof.
  intros.
  assert {{ Δ ; Γ ⊢ Π r A B ≈ Π r A' B' : Sort@s3 }} by mauto 3.
  assert {{ Δ ⊢ Γ, A ≈ Γ, A' }} by (econstructor; mauto 3).
  assert {{ Δ ; Γ, A' ⊢ B' : Sort@s2 }} by mauto 3.
  assert {{ Δ ; Γ, A' ⊢ M' : B' }} by mauto 2.
  assert {{ Δ ; Γ ⊢ Π r A B : Sort@s3 }} by mauto 2.
  assert {{ Δ ; Γ ⊢ Π r A' B' : Sort@s3 }} by mauto 4.
  enough {{ Δ ; Γ ⊢ λ r A' B' M' : Π r A' B' }}; mautosolve 3.
Qed.
#[local]
Hint Resolve presup_wf_exp_eq_fn_cong_right : mcpts.

Lemma presup_wf_exp_eq_fn_sub_right {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ A B M s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ⊢ Γ }} ->
    {{ Δ ⊢ Γ' }} ->
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ; Γ' ⊢ A : Sort@s1 }} ->
    {{ Δ ⊢ Γ', A }} ->
    {{ Δ ; Γ', A ⊢ B : Sort@s2 }} ->
    {{ Δ ; Γ', A ⊢ M : B }} ->
    {{ Δ ; Γ ⊢ λ r A[σ] B[q σ] M[q σ] : (Π r A B)[σ] }}.
Proof.
  intros.
  assert {{ Δ ; Γ ⊢ A[σ] : Sort@s1 }} by mauto 2.
  assert {{ Δ ; Γ, A[σ] ⊢ B[q σ] : Sort@s2 }} by mauto 4.
  assert {{ Δ ; Γ ⊢ Π r A[σ] B[q σ] : Sort@s3 }} by mauto 2.
  assert {{ Δ ; Γ ⊢ Π r A[σ] B[q σ] ≈ Π r A[σ] B[q σ] : Sort@s3 }} by mauto 2.
  assert {{ Δ ; Γ, A[σ] ⊢s q σ : Γ', A }} by mauto 3.
  assert {{ Δ ; Γ, A[σ] ⊢ M[q σ] : B[q σ] }} by mauto 3.
  assert {{ Δ ; Γ ⊢ λ r A[σ] B[q σ] M[q σ] : Π r A[σ] B[q σ] }} by mauto 3.
  eapply wf_exp_conv_exp_eq; mauto 3.
Qed.

#[local]
Hint Resolve presup_wf_exp_eq_fn_sub_right : mcpts.

Lemma presup_wf_exp_eq_app_cong_right {P : PtsSig} : forall {Δ : gctx P} {Γ A B M' N N' s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ⊢ Γ }} ->
    {{ Δ ; Γ ⊢ A : Sort@s1 }} ->
    {{ Δ ⊢ Γ, A }} ->
    {{ Δ ; Γ, A ⊢ B : Sort@s2 }} ->
    {{ Δ ; Γ ⊢ M' : Π r A B }} ->
    {{ Δ ; Γ ⊢ N : A }} ->
    {{ Δ ; Γ ⊢ N' : A }} ->
    {{ Δ ; Γ ⊢ N ≈ N' : A }} ->
    {{ Δ ; Γ ⊢ M' N' : B[Id,,N] }}.
Proof.
  intros.
  assert {{ Δ ; Γ ⊢s Id ≈ Id : Γ }} by mauto 2.
  assert {{ Δ ; Γ ⊢ A ≈ A[Id] : Sort@s1 }} by mauto 3.
  assert {{ Δ ; Γ ⊢ N ≈ N' : A[Id] }} by mauto 3.
  assert {{ Δ ; Γ ⊢s Id,,N ≈ Id,,N' : Γ, A }} by mauto 3.
  assert {{ Δ ; Γ ⊢ B[Id,,N] ≈ B[Id,,N'] : Sort@s2 }} by mauto 4.
  assert {{ Δ ; Γ ⊢ B[Id,,N] : Sort@s2 }} by mauto 4.
  eapply wf_exp_conv_exp_eq; mauto 3.
Qed.

#[local]
Hint Resolve presup_wf_exp_eq_app_cong_right : mcpts.

Lemma presup_wf_exp_eq_app_sub_left {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ A B M N s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ⊢ Γ }} ->
    {{ Δ ⊢ Γ' }} ->
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ; Γ' ⊢ A : Sort@s1 }} ->
    {{ Δ ⊢ Γ', A }} ->
    {{ Δ ; Γ', A ⊢ B : Sort@s2 }} ->
    {{ Δ ; Γ' ⊢ M : Π r A B }} ->
    {{ Δ ; Γ' ⊢ N : A }} ->
    {{ Δ ; Γ ⊢ (M N)[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  assert {{ Δ ; Γ, A[σ] ⊢s q σ : Γ', A }} by mauto 3.
  assert {{ Δ ; Γ ⊢ (Π r A B)[σ] : Sort@s3 }} by mauto 3.
  assert {{ Δ ; Γ ⊢ M[σ] : (Π r A B)[σ] }} by mauto 4.
  assert {{ Δ ; Γ ⊢ A[σ] : Sort@s1 }} by mauto 2.
  assert {{ Δ ; Γ, A[σ] ⊢ B[q σ] : Sort@s2 }} by mauto 2.
  assert {{ Δ ; Γ ⊢ Π r A[σ] B[q σ] : Sort@s3 }} by mauto 2.
  assert {{ Δ ; Γ ⊢ (Π r A B)[σ] ≈ Π r A[σ] B[q σ] : Sort@s3 }} by mauto 3.
  assert {{ Δ ; Γ ⊢ M[σ] : Π r A[σ] B[q σ] }} by mauto 2.
  assert {{ Δ ; Γ' ⊢ N : A[Id] }} by mauto 2.
  assert {{ Δ ; Γ ⊢s (Id,,N)∘σ ≈ Id∘σ,,N[σ] : Γ', A }} by mauto 4.
  assert {{ Δ ; Γ ⊢s (Id,,N)∘σ ≈ σ,,N[σ] : Γ', A }} by mauto 3.
  assert {{ Δ ; Γ' ⊢s Id,,N : Γ', A }} by mauto 3.
  assert {{ Δ ; Γ ⊢s (Id,,N)∘σ : Γ', A }} by mauto 3.
  assert {{ Δ ; Γ ⊢ B[(Id,,N)∘σ] ≈ B[σ,,N[σ]] : Sort@s2 }} by mauto 3.
  assert {{ Δ ; Γ ⊢ N[σ] : A[σ] }} by mauto 3.
  assert {{ Δ ; Γ ⊢s σ,,N[σ] : Γ', A }} by mauto 3.
  assert {{ Δ ; Γ ⊢ B[σ,,N[σ]] : Sort@s2 }} by mauto 2.
  assert {{ Δ ; Γ' ⊢ B[Id,,N] : Sort@s2 }} by mauto 2.
  assert {{ Δ ; Γ ⊢ B[Id,,N][σ] : Sort@s2 }} by mauto 2.
  assert {{ Δ ; Γ ⊢ B[(Id,,N)∘σ] ≈ B[Id,,N][σ] : Sort@s2 }} by mauto 3.
  assert {{ Δ ; Γ ⊢ B[Id,,N][σ] ≈ B[σ,,N[σ]] : Sort@s2 }} by mauto 3.
  enough {{ Δ ; Γ ⊢ (M N)[σ] : B[Id,,N][σ] }} by mauto 2.
  econstructor; mauto 2.
Qed.

#[local]
Hint Resolve presup_wf_exp_eq_app_sub_left : mcpts.

Lemma presup_wf_exp_eq_app_sub_right {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ A B M N s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ⊢ Γ }} ->
    {{ Δ ⊢ Γ' }} ->
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ; Γ' ⊢ A : Sort@s1 }} ->
    {{ Δ ⊢ Γ', A }} ->
    {{ Δ ; Γ', A ⊢ B : Sort@s2 }} ->
    {{ Δ ; Γ' ⊢ M : Π r A B }} ->
    {{ Δ ; Γ' ⊢ N : A }} ->
    {{ Δ ; Γ ⊢ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  assert {{ Δ ; Γ ⊢ A[σ] : Sort@s1 }} by mauto 2.
  assert {{ Δ ; Γ, A[σ] ⊢s q σ : Γ', A }} by mauto 3.
  assert {{ Δ ; Γ, A[σ] ⊢ B[q σ] : Sort@s2 }} by mauto 2.
  assert {{ Δ ; Γ ⊢ (Π r A B)[σ] ≈ Π r A[σ] B[q σ] }} by mauto 3.
  assert {{ Δ; Γ ⊢ (Π r A B)[σ] : Sort@s3 }} by mauto 3.
  assert {{ Δ; Γ ⊢ (Π r A B)[σ] }} by mauto 2.
  assert {{ Δ ; Γ ⊢ M[σ] : (Π r A B)[σ] }} by mauto 4.
  assert {{ Δ ; Γ ⊢ M[σ] : Π r A[σ] B[q σ] }} by (eapply wf_exp_conv_typ_eq; mauto 3).
  assert {{ Δ ; Γ ⊢ N[σ] : A[σ] }} by mauto 3.
  assert {{ Δ ; Γ ⊢s q σ∘(Id,,N[σ]) ≈ σ,,N[σ] : Γ', A }} by mauto 3.
  assert {{ Δ ; Γ ⊢s Id,,N[σ] : Γ, A[σ] }} by mauto 3.
  assert {{ Δ ; Γ ⊢s q σ∘(Id,,N[σ]) : Γ', A }} by mauto 2.
  assert {{ Δ ; Γ ⊢ B[q σ∘(Id,,N[σ])] ≈ B[σ,,N[σ]] : Sort@s2 }} by mauto 3.
  assert {{ Δ ; Γ ⊢ B[q σ][Id,,N[σ]] : Sort@s2 }} by mauto 2.
  assert {{ Δ ; Γ ⊢ B[q σ][Id,,N[σ]] ≈ B[q σ∘(Id,,N[σ])] : Sort@s2 }} by (symmetry; mauto).
  assert {{ Δ ; Γ ⊢ B[q σ][Id,,N[σ]] ≈ B[σ,,N[σ]] : Sort@s2 }} by mauto 3.
  eapply wf_exp_conv_exp_eq; mauto 3.
  mauto 4.
Qed.

#[local]
Hint Resolve presup_wf_exp_eq_app_sub_right : mcpts.

Lemma presup_wf_exp_eq_pi_eta_right {P : PtsSig} : forall {Δ : gctx P} {Γ A B M s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ⊢ Γ }} ->
    {{ Δ ; Γ ⊢ A : Sort@s1 }} ->
    {{ Δ ⊢ Γ, A }} ->
    {{ Δ ; Γ, A ⊢ B : Sort@s2 }} ->
    {{ Δ ; Γ ⊢ M : Π r A B }} ->
    {{ Δ ; Γ ⊢ λ r A B (M[Wk] #0) : Π r A B }}.
Proof.
  intros.
  assert {{ Δ ; Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ Δ ; Γ, A, A[Wk] ⊢s q Wk : Γ, A }} by mauto 3.
  assert {{ Δ ; Γ, A ⊢ A[Wk] : Sort@s1 }} by mauto 2.
  assert {{ Δ ; Γ, A, A[Wk] ⊢ B[q Wk] : Sort@s2 }} by mauto 2.
  assert {{ Δ ; Γ, A ⊢ (Π r A B)[Wk] ≈ Π r A[Wk] B[q Wk] }} by mauto 3.
  assert {{ Δ ; Γ, A ⊢ (Π r A B)[Wk] : Sort@s3 }} by mauto 3.
  assert {{ Δ ; Γ, A ⊢ (Π r A B)[Wk] }} by mauto 2.
  assert {{ Δ ; Γ, A ⊢ Π r A[Wk] B[q Wk] : Sort@s3 }} by mauto 3.
  assert {{ Δ ; Γ, A ⊢ Π r A[Wk] B[q Wk] }} by mauto 2.
  assert {{ Δ ; Γ, A ⊢ M[Wk] : (Π r A B)[Wk] }} by mauto 4.
  assert {{ Δ ; Γ, A ⊢ M[Wk] : Π r A[Wk] B[q Wk] }} by (eapply wf_exp_conv_typ_eq; mauto 3).
  assert {{ Δ ; Γ, A ⊢ A[Wk] : Sort@s1 }} by mauto 3.
  assert {{ Δ ; Γ, A ⊢ #0 : A[Wk] }} by mauto 2.
  assert {{ Δ ; Γ, A ⊢s q Wk∘(Id,,#0) ≈ Id : Γ, A }} by (etransitivity; mauto 3).
  assert {{ Δ ; Γ, A ⊢s Id,,#0 : Γ, A, A[Wk] }} by mauto 3.
  assert {{ Δ ; Γ, A ⊢ B[q Wk∘(Id,,#0)] ≈ B[Id] : Sort@s2 }} by mauto 3.
  assert {{ Δ ; Γ, A ⊢ B[q Wk][Id,,#0] ≈ B[Id] : Sort@s2 }} by (transitivity {{{ B[q Wk∘(Id,,#0)] }}}; mauto 3).
  econstructor; eauto.
  eapply wf_exp_conv_typ_eq; mauto 3.
  mauto 4.
Qed.
#[local]
Hint Resolve presup_wf_exp_eq_pi_eta_right : mcpts.

(** Variable cases *)
Lemma wf_exp_eq_gvar_sub_left {P : PtsSig} : forall {Δ : gctx P} {Γ σ A x},
    {{ Δ ; Γ ⊢s σ : ⋅ }} ->
    {{ `#x : A ∈ Δ }} ->
    {{ Δ ; Γ ⊢ `#x[σ] : A[σ] }}.
Proof.
  intros.
  gen_core_presups.
  assert {{ Δ ; ⋅ ⊢s Id : ⋅ }} by mauto 2.
  assert {{ Δ ; ⋅ ⊢ `#x : A[Id] }} by mauto 2.
  assert {{ Δ ; ⋅ ⊢ A[Id] ≈ A }} by mauto 3.
  assert {{ Δ ; ⋅ ⊢ `#x : A }} by mauto 3.
  mauto 3.
Qed.

#[local]
Hint Resolve wf_exp_eq_gvar_sub_left : mcpts.
 
Lemma presup_wf_exp_eq_var_0_sub_left {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ A M},
    {{ Δ ⊢ Γ }} ->
    {{ Δ ⊢ Γ' }} ->
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ; Γ' ⊢ A }} ->
    {{ Δ ; Γ ⊢ M : A[σ] }} ->
    {{ Δ ; Γ ⊢ #0[σ,,M] : A[σ] }}.
Proof.
  intros.
  assert {{ Δ ⊢ Γ', A }} by mauto 2.
  assert {{ Δ ; Γ', A ⊢ A[Wk] }} by mauto 3.
  assert {{ Δ ; Γ', A ⊢ #0 : A[Wk] }} by mauto 2.
  eapply wf_exp_conv_typ_eq; mauto 3.
Qed.

#[local]
Hint Resolve presup_wf_exp_eq_var_0_sub_left : mcpts.

Lemma presup_wf_exp_eq_var_S_sub_left {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ A M B x},
    {{ Δ ⊢ Γ }} ->
    {{ Δ ⊢ Γ' }} ->
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ; Γ' ⊢ A }} ->
    {{ Δ ; Γ ⊢ M : A[σ] }} ->
    {{ #x : B ∈ Γ' }} ->
    {{ Δ ; Γ ⊢ #(S x)[σ,,M] : B[σ] }}.
Proof.
  intros.
  assert {{ Δ ⊢ Γ', A }} by mauto 2.
  assert {{ Δ ; Γ' ⊢ B }} by (eapply presup_ctx_lookup_typ; mauto).
  assert {{ Δ ; Γ', A ⊢ B[Wk] }} by mauto 3.
  assert {{ Δ ; Γ', A ⊢ #(S x) : B[Wk] }} by mauto 3.
  eapply wf_exp_conv_typ_eq; mauto 3.
Qed.

#[local]
Hint Resolve presup_wf_exp_eq_var_S_sub_left : mcpts.

(** Closure cases *)
Lemma presup_wf_exp_eq_sub_cong_right {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ σ' A M M'},
    {{ Δ ⊢ Γ' }} ->
    {{ Δ ; Γ' ⊢ A }} ->
    {{ Δ ; Γ' ⊢ M : A }} ->
    {{ Δ ; Γ' ⊢ M' : A }} ->
    {{ Δ ; Γ' ⊢ M ≈ M' : A }} ->
    {{ Δ ⊢ Γ }} ->
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ; Γ ⊢s σ' : Γ' }} ->
    {{ Δ ; Γ ⊢s σ ≈ σ' : Γ' }} ->
    {{ Δ ; Γ ⊢ M'[σ'] : A[σ] }}.
Proof.
  intros.
  eapply wf_exp_conv_typ_eq; mauto 3.
Qed.
#[local]
Hint Resolve presup_wf_exp_eq_sub_cong_right : mcpts.

Lemma presup_wf_exp_eq_sub_compose_right {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' Γ'' τ σ A M},
    {{ Δ ⊢ Γ }} ->
    {{ Δ ⊢ Γ' }} ->
    {{ Δ ; Γ ⊢s τ : Γ' }} ->
    {{ Δ ⊢ Γ'' }} ->
    {{ Δ ; Γ' ⊢s σ : Γ'' }} ->
    {{ Δ ; Γ'' ⊢ A }} ->
    {{ Δ ; Γ'' ⊢ M : A }} ->
    {{ Δ ; Γ ⊢ M[σ][τ] : A[σ∘τ] }}.
Proof.
  intros.
  eapply wf_exp_conv_typ_eq; mauto 4.
Qed.
#[local]
Hint Resolve presup_wf_exp_eq_sub_compose_right : mcpts.

Lemma presup_wf_exp_sub_id_left {P} : forall {Δ : gctx P} {Γ M A},
    {{ Δ ; Γ ⊢ M : A }} ->
    {{ Δ ; Γ ⊢ M[Id] : A }}.
Proof.
  intros * H.
  assert {{ Δ ; Γ ⊢s Id : Γ }} by mauto 3.
  induction H; try solve [econstructor; mauto 2].
  - assert {{ Δ ; Γ ⊢ Sort@s1 : Sort@s2 }} by mauto 2.
    mauto 2.
  - assert {{ Δ ; Γ ⊢ Π r A B : Sort@s3 }} by mauto 2.
    mauto 2.
  - eapply wf_exp_conv_typ_eq with (A := {{{ (Π r A B)[Id] }}}); mauto 4.
    econstructor; mauto 3.
  - assert {{ Δ ; Γ ⊢s Id,,N : Γ, A }} by mauto 3.
    assert {{ Δ ; Γ ⊢ B[Id,,N] : Sort@s2 }} by mauto 2.
    eapply wf_exp_conv_typ_eq with (A := {{{ B[Id,,N][Id] }}}); mauto 4.
  - eapply wf_exp_conv_typ_eq with (A := {{{ A[Id] }}}); mauto 4.
  - gen_core_presups.
    assert {{ Δ ; Γ ⊢ A[σ][Id] ≈ A[σ∘Id] }} by mauto 3.
    assert {{ Δ ; Γ ⊢ A[σ∘Id] ≈ A[σ] }} by mauto 4.
    assert {{ Δ ; Γ ⊢ A[σ][Id] ≈ A[σ] }} by (etransitivity; mauto 2).
    eapply wf_exp_conv_typ_eq with (A := {{{ A[σ][Id] }}}); mauto 3.
    mauto 4.
  - mauto 3.
  - mauto 3.
  - assert {{ Δ ; Γ ⊢ succ M : ℕ }} by mauto 2.
    mauto 2.
  - assert {{ Δ ; Γ ⊢s Id,,M : Γ, ℕ }} by mauto 3.
    assert {{ Δ ; Γ ⊢ A[Id,,M] }} by mauto 3.
    eapply wf_exp_conv_typ_eq with (A := {{{ A[Id,,M][Id] }}}); mauto 2.
    econstructor; mauto 2.
  - assert {{ Δ ; Γ ⊢ M[σ] : A[σ] }} by mauto 2.
    assert {{ Δ ; Γ ⊢ M[σ][Id] : A[σ][Id] }} by mauto 3.
    assert {{ Δ ; Γ ⊢ A[σ][Id] }} by mauto 3.
    assert {{ Δ ; Γ ⊢ A[σ][Id] ≈ A[σ] }} by mauto 3.
    eapply wf_exp_conv_typ_eq with (A := {{{ A[σ][Id] }}}); mauto 3.
Qed.

#[local]
Hint Resolve presup_wf_exp_sub_id_left : mcpts.

(** Nat cases *)
Lemma presup_wf_exp_eq_natrec_cong_right {P} : forall {Δ : gctx P} {Γ A A' MZ' MS' M M' s} {r : Ru_nat P s},
    {{ Δ ⊢ Γ, ℕ }} ->
    {{ Δ ; Γ, ℕ ⊢ A }} ->
    {{ Δ ; Γ, ℕ ⊢ A' }} ->
    {{ Δ ; Γ, ℕ ⊢ A ≈ A' }} ->
    {{ Δ ⊢ Γ }} ->
    {{ Δ ; Γ ⊢ MZ' : A[Id,,zero] }} ->
    {{ Δ ⊢ Γ, ℕ, A }} ->
    {{ Δ ; Γ, ℕ, A ⊢ MS' : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ; Γ ⊢ M : ℕ }} ->
    {{ Δ ; Γ ⊢ M' : ℕ }} ->
    {{ Δ ; Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Δ ; Γ ⊢ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }}.
Proof.
  intros.
  assert {{ Δ ; Γ ⊢s Id,,M : Γ, ℕ }} by mauto 3.
  assert {{ Δ ; Γ ⊢s Id,,M' : Γ, ℕ }} by mauto 3.
  assert {{ Δ ; Γ ⊢s Id,,M ≈ Id,,M' : Γ, ℕ }} by mauto 3.
  assert {{ Δ ; Γ ⊢ A[Id,,M] ≈ A'[Id,,M'] }} by mauto 4.
  assert {{ Δ ; Γ ⊢s Id,,zero : Γ, ℕ }} by mauto 4.
  assert {{ Δ ; Γ ⊢ A[Id,,zero] ≈ A'[Id,,zero] }} by mauto 3.
  assert {{ Δ ; Γ ⊢ MZ' : A'[Id,,zero] }} by mauto 4.
  assert {{ Δ ; Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 3 using wf_sub_weak_compose_weak_extend_succ_var1.
  assert {{ Δ ; Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1] ≈ A'[Wk∘Wk,,succ #1] }} by mauto 3.
  assert {{ Δ ; Γ, ℕ, A ⊢ MS' : A'[Wk∘Wk,,succ #1] }} by mauto 4.
  assert {{ Δ ⊢ Γ, ℕ, A ≈ Γ, ℕ, A' }} by mauto 3.
  assert {{ Δ ; Γ, ℕ, A' ⊢ MS' : A'[Wk∘Wk,,succ #1] }} by mauto 3.
  eapply wf_exp_conv_typ_eq; mauto 2.
Qed.
#[local]
Hint Resolve presup_wf_exp_eq_natrec_cong_right : mcpts.

Lemma presup_wf_exp_eq_natrec_sub_left {P} : forall {Δ : gctx P}  {Γ Γ' σ A MZ MS M s} {r : Ru_nat P s},
    {{ Δ ⊢ Γ }} ->
    {{ Δ ⊢ Γ' }} ->
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ⊢ Γ', ℕ }} ->
    {{ Δ ; Γ', ℕ ⊢ A }} ->
    {{ Δ ; Γ' ⊢ MZ : A[Id,,zero] }} ->
    {{ Δ ⊢ Γ', ℕ, A }} ->
    {{ Δ ; Γ', ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ; Γ' ⊢ M : ℕ }} ->
    {{ Δ ; Γ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] : A[σ,,M[σ]] }}.
Proof.
  intros.
  assert {{ Δ ; Γ ⊢s σ,,M[σ] : Γ', ℕ }} by mauto 3.
  assert {{ Δ ; Γ ⊢ A[σ,,M[σ]] }} by mauto 3.
  assert {{ Δ ; Γ' ⊢s Id,,M : Γ', ℕ }} by mauto 3.
  assert {{ Δ ; Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Γ', ℕ }} by mauto 3.
  assert {{ Δ ; Γ ⊢ A[Id,,M][σ] ≈ A[σ,,M[σ]]  }} by (etransitivity; mauto 3).
  enough {{ Δ ; Γ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] : A[Id,,M][σ] }} by mauto 4.
  econstructor; mauto 3.
Qed.
#[local]
Hint Resolve presup_wf_exp_eq_natrec_sub_left : mcpts.

Lemma presup_wf_exp_eq_natrec_sub_right_helper {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ A M s} {r : Ru_nat P s},
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ; Γ', ℕ ⊢ A }} -> 
    {{ Δ ; Γ ⊢ M : ℕ }} ->
    {{ Δ ; Γ ⊢ A[q σ][Id,,M] }} /\ {{ Δ ; Γ ⊢ A[q σ][Id,,M] ≈ A[σ,,M] }}.
Proof.
  intros.
  assert {{ Δ ; Γ ⊢ M : ℕ[σ] }} by mauto 3.
  assert {{ Δ ; Γ ⊢s Id,,M : Γ, ℕ }} by mauto 4.
  assert {{ Δ ; Γ ⊢s q σ∘(Id,,M) ≈ σ,,M : Γ', ℕ }} by mauto 4.
  assert {{ Δ ; Γ ⊢s σ,,M : Γ', ℕ }} by mauto 2.
  assert {{ Δ ; Γ ⊢ A[q σ][Id,,M] ≈ A[q σ∘(Id,,M)] }} by mauto 3.
  assert {{ Δ ; Γ ⊢ A[q σ∘(Id,,M)] ≈ A[σ,,M] }} by mauto 4.
  split; mauto 3.
  mauto 4.
Qed.

#[local]
Hint Resolve presup_wf_exp_eq_natrec_sub_right_helper : mcpts. 
 
Lemma presup_wf_exp_eq_natrec_sub_right {P} : forall {Δ : gctx P} {Γ Γ' σ A MZ MS M s} {r : Ru_nat P s},
    {{ Δ ⊢ Γ }} ->
    {{ Δ ⊢ Γ' }} ->
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ⊢ Γ', ℕ }} ->
    {{ Δ ; Γ', ℕ ⊢ A  }} ->
    {{ Δ ; Γ' ⊢ MZ : A[Id,,zero] }} ->
    {{ Δ ⊢ Γ', ℕ, A }} ->
    {{ Δ ; Γ', ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ; Γ' ⊢ M : ℕ }} ->
    {{ Δ ; Γ ⊢ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }}.
Proof.
  intros.
  assert {{ Δ ; Γ, ℕ ⊢s q σ : Γ', ℕ }} by mauto 2.
  assert {{ Δ ; Γ, ℕ, A[q σ] ⊢s q (q σ) : Γ', ℕ, A }} by mauto 2.
  assert {{ Δ ; Γ, ℕ ⊢ A[q σ] }} by mauto 3.
  assert {{ Δ ; Γ' ⊢ zero : ℕ }} by mauto 2.
  assert {{ Δ ; Γ' ⊢s Id,,zero : Γ', ℕ }} by mauto.
  assert {{ Δ ; Γ ⊢ zero[σ] ≈ zero : ℕ }} by mauto 2.
  assert {{ Δ ; Γ ⊢s σ,,zero[σ] ≈ σ,,zero : Γ', ℕ }} by mauto 3.
  assert {{ Δ ; Γ ⊢s (Id,,zero)∘σ ≈ σ,,zero : Γ', ℕ }} by mauto 4.
  assert ({{ Δ ; Γ ⊢ A[q σ][Id,,zero] }} /\ {{ Δ ; Γ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] }}) as [] by mauto 3.
  assert {{ Δ ; Γ ⊢ A[(Id,,zero)∘σ] ≈ A[σ,,zero] }} by mauto 3.
  assert {{ Δ ; Γ ⊢ A[q σ][Id,,zero] ≈ A[Id,,zero][σ]  }} by (etransitivity; [| symmetry]; mauto 4).
  assert {{ Δ ; Γ ⊢ MZ[σ] : A[Id,,zero][σ] }} by mauto 4.
  assert {{ Δ ; Γ ⊢ A[Id,,zero][σ] ⊆ A[q σ][Id,,zero] }} by (econstructor; mauto 3).
  assert {{ Δ ; Γ ⊢ MZ[σ] : A[q σ][Id,,zero] }} by (eapply wf_exp_conv; mauto 3).
  
  assert {{ Δ ; Γ', ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ', ℕ }} by mauto 3.   
  assert {{ Δ ; Γ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }}  by mauto 3. 
  assert {{ Δ ; Γ, ℕ, A[q σ] ⊢s q σ∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘q (q σ) : Γ', ℕ }} by mauto 2.
  assert {{ Δ ; Γ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q σ)] }} by mauto 3.
  assert {{ Δ ; Γ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by (eapply wf_exp_conv_typ_eq; mauto 4).
  (* Final *)
  assert {{ Δ ; Γ ⊢ A[σ,,M[σ]] }} by mauto 4.
  assert ({{ Δ ; Γ ⊢ A[q σ][Id,,M[σ]] }} /\ {{ Δ ; Γ ⊢ A[q σ][Id,,M[σ]] ≈ A[σ,,M[σ]] }}) as [] by mauto 3.
  enough {{ Δ ; Γ ⊢ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[q σ][Id,,M[σ]] }} by (eapply wf_exp_conv_typ_eq; mauto 3).
  econstructor; mauto 2.
Qed.
#[local]
Hint Resolve presup_wf_exp_eq_natrec_sub_right : mcpts.

Lemma presup_wf_exp_eq_beta_succ_right {P} : forall {Δ : gctx P} {Γ A MZ MS M s} {r : Ru_nat P s},
    {{ Δ ⊢ Γ, ℕ }} ->
    {{ Δ ; Γ, ℕ ⊢ A  }} ->
    {{ Δ ⊢ Γ }} ->
    {{ Δ ; Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Δ ⊢ Γ, ℕ, A }} ->
    {{ Δ ; Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ; Γ ⊢ M : ℕ }} ->
    {{ Δ ; Γ ⊢ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }}.
Proof.
  intros.
  (** Coq was having trouble inferring P here, expanded definition for now **)
  (* set (WkWksucc := {{{ Wk∘Wk,,succ #1 }}}). *)
  set (recM := {{{ rec M return A | zero -> MZ | succ -> MS end }}}).
  set (IdMrecM := {{{ Id,,M,,recM }}}).
  (* Assertion for type *)
  assert {{ Δ ; Γ ⊢ recM : A[Id,,M] }} by mauto 4.
  assert {{ Δ ; Γ, ℕ ⊢s Wk : Γ }} by mauto 2.
  assert {{ Δ ; Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 2.
  assert {{ Δ ; Γ, ℕ, A ⊢s Wk∘Wk : Γ }} by mauto 2.
  assert {{ Δ ; Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 4.
  assert {{ Δ ; Γ ⊢s Id : Γ }} by mauto 2.
  assert {{ Δ ; Γ ⊢s IdMrecM : Γ, ℕ, A }} by mauto 3.
  assert {{ Δ ; Γ ⊢s (Wk∘Wk,,succ #1)∘IdMrecM ≈ (Wk∘Wk)∘IdMrecM,,(succ #1)[IdMrecM] : Γ, ℕ }}
    by mauto 4 using wf_sub_eq_extend_compose_nat.
  assert {{ Δ ; Γ ⊢s (Wk∘Wk)∘IdMrecM : Γ }} by mauto 2.
  assert {{ Δ ; Γ ⊢s (Wk∘Wk)∘IdMrecM ≈ Wk∘(Wk∘IdMrecM) : Γ }} by mauto 2.
  assert {{ Δ ; Γ ⊢s Id,,M : Γ, ℕ }} by mauto 2.
  assert {{ Δ ; Γ ⊢s Wk∘(Wk∘IdMrecM) ≈ Wk∘(Id,,M) : Γ }} by (econstructor; mauto 2).
  assert {{ Δ ; Γ ⊢s (Wk∘Wk)∘IdMrecM ≈ Id : Γ }} by (etransitivity; mauto 3).
  assert {{ Δ ; Γ ⊢ #1[IdMrecM] ≈ #0[Id,,M] : ℕ }} by mauto 3.
  assert {{ Δ ; Γ ⊢ #1[IdMrecM] ≈ M : ℕ }} by mauto 3.
  assert {{ Δ ; Γ ⊢ succ #1[IdMrecM] ≈ succ M : ℕ }} by mauto 2.
  assert {{ Δ ; Γ ⊢ (succ #1)[IdMrecM] ≈ succ M : ℕ }} by (etransitivity; mauto 3).
  assert {{ Δ ; Γ ⊢s (Wk∘Wk)∘IdMrecM,,(succ #1)[IdMrecM] ≈ Id,,succ M : Γ, ℕ }} by mauto 2.
  assert {{ Δ ; Γ ⊢s (Wk∘Wk,,succ #1)∘IdMrecM : Γ, ℕ }} by mauto 3.
  assert {{ Δ ; Γ ⊢s Id,,succ M : Γ, ℕ }} by mauto 3.
  assert {{ Δ ; Γ ⊢s (Wk∘Wk,,succ #1)∘IdMrecM ≈ Id,,succ M : Γ, ℕ }} by mauto 2.
  assert {{ Δ ; Γ ⊢ A[(Wk∘Wk,,succ #1)∘IdMrecM] ≈ A[Id,,succ M] }} by mauto 3.
  assert {{ Δ ; Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1]  }} by mauto 3.
  assert {{ Δ ; Γ ⊢ MS[IdMrecM] : A[Wk∘Wk,,succ #1][IdMrecM] }} by mauto 3.
  assert {{ Δ ; Γ ⊢ A[Wk∘Wk,,succ #1][IdMrecM] ≈ A[(Wk∘Wk,,succ #1)∘IdMrecM] }} by mauto 3.
  enough {{ Δ ; Γ ⊢ A[Wk∘Wk,,succ #1][IdMrecM] ≈ A[Id,,succ M] }}; [eapply wf_exp_conv | etransitivity]; mauto 3.
Qed.
#[local]
Hint Resolve presup_wf_exp_eq_beta_succ_right : mcpts.

#[local]
Ltac gen_presup_IH presup_exp_eq presup_sub_eq presup_subtyp presup_typ_eq H :=
  match type of H with
  | {{ ^?Δ ; ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HM := fresh "HM" in
      let HN := fresh "HN" in
      let HA := fresh "HA" in
      pose proof presup_exp_eq _ _ _ _ _ _ H as [HΔ [HΓ [HM [HN HA]]]]
  | {{ ^?Δ ; ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Γ' }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HΓ' := fresh "HΓ'" in
      let Hσ := fresh "Hσ" in
      let Hτ := fresh "Hτ" in
      pose proof presup_sub_eq _ _ _ _ _ _ H as [HΔ [HΓ [HΓ' [Hσ Hτ]]]]
  | {{ ^?Δ ; ^?Γ ⊢ ^?A ≈ ^?B }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HA := fresh "HA" in
      let HB := fresh "HB" in
      pose proof presup_typ_eq _ _ _ _ _ H as [HΔ [HΓ [HA HB]]]
  | {{ ^?Δ ; ^?Γ ⊢ ^?A ⊆ ^?B }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HA := fresh "HA" in
      let HB := fresh "HB" in
      pose proof presup_subtyp _ _ _ _ _ H as [HΔ [HΓ [HA HB]]]
  end.

Lemma presup_exp_eq {P : PtsSig} : forall {Δ : gctx P} {Γ M M' A}, {{ Δ ; Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Δ }} /\ {{ Δ ⊢ Γ }} /\ {{ Δ ; Γ ⊢ M : A }} /\ {{ Δ ; Γ ⊢ M' : A }} /\ {{ Δ ; Γ ⊢ A }}
with presup_sub_eq {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ σ'}, {{ Δ ; Γ ⊢s σ ≈ σ' : Γ' }} -> {{ ⊢ Δ }} /\ {{ Δ ⊢ Γ }} /\ {{ Δ ⊢ Γ' }} /\ {{ Δ ; Γ ⊢s σ : Γ' }} /\ {{ Δ ; Γ ⊢s σ' : Γ' }}
with presup_subtyp {P} : forall {Δ : gctx P} {Γ A B}, {{ Δ ; Γ ⊢ A ⊆ B }} -> {{ ⊢ Δ }} /\ {{ Δ ⊢ Γ }} /\ {{ Δ ; Γ ⊢ A }} /\ {{ Δ ; Γ ⊢ B }}
with presup_typ_eq {P} : forall {Δ : gctx P} {Γ A B}, {{ Δ ; Γ ⊢ A ≈ B }} -> {{ ⊢ Δ }} /\ {{ Δ ⊢ Γ }} /\ {{ Δ ; Γ ⊢ A }} /\ {{ Δ ; Γ ⊢ B }}.
Proof with mautosolve 5.
  all: inversion_clear 1;
    (on_all_hyp: gen_presup_IH presup_exp_eq presup_sub_eq presup_subtyp presup_typ_eq);
    gen_core_presups;
    clear presup_exp_eq presup_sub_eq presup_subtyp presup_typ_eq;
    repeat split; try mautosolve 4;
    try (eexists; unshelve solve [mauto 4]; constructor).

  all: try (econstructor; mautosolve 4).
  - econstructor; mauto 3.
    assert  {{ Δ ⊢ Γ, A0 ≈ Γ, A' }} by (econstructor; mauto 3).
    mauto 3.
  - econstructor; mauto 3.
    assert {{ Δ ; Γ ⊢ A[σ0∘τ] }} by mauto 4.
    assert {{ Δ ; Γ ⊢ M[τ] : A[σ0][τ] }} by mauto 3.
    assert {{ Δ ; Γ ⊢ A[σ0∘τ] ≈ A[σ0][τ] }} by mauto 3.
    eapply wf_exp_conv; mauto 3.
  - econstructor; mauto 3.
    assert {{ Δ ; Γ0 ⊢ A }} by mauto 2.
    assert {{ Δ ; Γ ⊢s Wk∘σ : Γ0 }} by mauto 3.
    assert {{ Δ ; Γ ⊢ A[Wk∘σ] }} by mauto 3.
    eapply wf_exp_conv_typ_eq with (A := {{{ A[Wk][σ] }}}); mauto 3.
    econstructor; mauto 2.
Qed.    


Ltac gen_presup_IH' presup_exp_eq presup_sub_eq presup_subtyp presup_typ_eq H :=
  match type of H with
  | {{ ^?Δ ; ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HM := fresh "HM" in
      let HN := fresh "HN" in
      let HA := fresh "HA" in
      pose proof presup_exp_eq _ _ _ _ _ _ H as [HΔ [HΓ [HM [HN HA]]]]
  | {{ ^?Δ ; ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Γ' }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HΓ' := fresh "HΓ'" in
      let Hσ := fresh "Hσ" in
      let Hτ := fresh "Hτ" in
      pose proof presup_sub_eq _ _ _ _ _ _ H as [HΔ [HΓ [HΓ' [Hσ Hτ]]]]
  | {{ ^?Δ ; ^?Γ ⊢ ^?A ⊆ ^?B }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HA := fresh "HA" in
      let HB := fresh "HB" in
      pose proof presup_subtyp _ _ _ _ _ H as [HΔ [HΓ [HA HB]]]
  | {{ ^?Δ ; ^?Γ ⊢ ^?A ≈ ^?B }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HA := fresh "HA" in
      let HB := fresh "HB" in
      pose proof presup_typ_eq _ _ _ _ _ H as [HΔ [HΓ [HA HB]]]
  end.


Ltac gen_presup H := gen_presup_IH' @presup_exp_eq @presup_sub_eq @presup_subtyp @presup_typ_eq H + gen_core_presup H.

Ltac gen_presups := (on_all_hyp: fun H => gen_presup H); invert_wf_ctx; (on_all_hyp: fun H => gen_lookup_presup H); clear_dups.
