From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export CtxEq.
Import Syntax_Notations.


Lemma presup_exp_eq_fn_cong_right {P : PtsSig} : forall {Γ : ctx P} {s1 A A' s2 B M' s3} (r : Ru P s1 s2 s3),
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ Γ ⊢ A' : Sort@s1 }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢ B : Sort@s2 }} ->
    {{ Γ, A ⊢ M' : B }} ->
    {{ Γ ⊢ λ r A' M' : Π r A B }}.
Proof.
  intros.
  assert {{ Γ ⊢ Π r A B ≈ Π r A' B : Sort@s3 }} by mauto 3.
  assert {{ Γ ⊢ A ≈ A' }} by mauto 2.
  assert {{ ⊢ Γ, A ≈ Γ, A' }} by (econstructor; mauto 3).
  assert {{ Γ, A' ⊢ M' : B }} by mauto 4.
  assert {{ Γ ⊢ Π r A B : Sort@s3 }} by mauto 2.
  enough {{ Γ ⊢ λ r A' M' : Π r A' B }}; mauto.
Qed.

#[local]
Hint Resolve presup_exp_eq_fn_cong_right : mcpts.

Lemma presup_exp_eq_fn_sub_right {P : PtsSig} : forall {Γ : ctx P} {σ Δ s1 A s2 B M s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Δ, A }} ->
    {{ Δ, A ⊢ B : Sort@s2 }} ->
    {{ Δ, A ⊢ M : B }} ->
    {{ Γ ⊢ λ r A[σ] M[q σ] : (Π r A B)[σ] }}.
Proof.
  intros.
  assert {{ Γ ⊢ A[σ] : Sort@s1 }} by mauto 2.  
  assert {{ Γ, A[σ] ⊢ B[q σ] : Sort@s2 }} by mauto 4.
  assert {{ Γ ⊢ Π r A[σ] B[q σ] : Sort@s3 }} by mauto 2.
  assert {{ Γ ⊢ Π r A[σ] B[q σ] ≈ Π r A[σ] B[q σ] : Sort@s3 }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ M[q σ] : B[q σ] }} by mauto 4.
  assert {{ Γ ⊢ λ r A[σ] M[q σ] : Π r A[σ] B[q σ] }} by mauto 3.
  eapply wf_conv; mauto 4.
Qed.

#[local]
Hint Resolve presup_exp_eq_fn_sub_right : mcpts.

Lemma presup_exp_eq_app_cong_right {P : PtsSig} : forall {Γ : ctx P} {s1 A B M' N N' s2 s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ M' : Π r A B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ N' : A }} ->
    {{ Γ ⊢ N ≈ N' : A }} ->
    {{ Γ ⊢ M' N' : B[Id,,N] }}.
Proof.
  intros.
  assert {{ Γ ⊢s Id ≈ Id : Γ }} by mauto 2.
  assert {{ Γ ⊢ A ≈ A[Id] : Sort@s1 }} by mauto 3.
  assert {{ Γ ⊢ N ≈ N' : A[Id] }} by mauto 3.
  assert {{ Γ ⊢s Id,,N ≈ Id,,N' : Γ, A }} by mauto 3.
  assert {{ Γ ⊢ B[Id,,N] ≈ B[Id,,N'] : Sort@s2 }} by (eapply wf_exp_eq_conv; mauto 4).
  assert {{ Γ ⊢ B[Id,,N] : Sort@s2 }} by mauto 4.
  eapply wf_conv; mauto 4.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_cong_right : mcpts.

Lemma presup_exp_eq_app_sub_left {P : PtsSig} : forall {Γ : ctx P} {σ Δ s1 A B M N s2 s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Δ, A }} ->
    {{ Δ, A ⊢ B : Sort@s2 }} ->
    {{ Δ ⊢ M : Π r A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ (M N)[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  assert {{ Γ, A[σ] ⊢s q σ : Δ, A }} by mauto 3.
  assert {{ Γ ⊢ M[σ] : (Π r A B)[σ] }} by mauto 3.
  assert {{ Γ ⊢ Π r A[σ] B[q σ] : Sort@s3 }} by mauto 4.
  assert {{ Γ ⊢ M[σ] : Π r A[σ] B[q σ] }} by mauto.
  assert {{ Δ ⊢ N : A[Id] }} by mauto 3.
  assert {{ Γ ⊢s (Id,,N)∘σ ≈ Id∘σ,,N[σ] : Δ, A }} by mauto 4.
  assert {{ Γ ⊢s (Id,,N)∘σ ≈ σ,,N[σ] : Δ, A }} by mauto 3.
  assert {{ Δ ⊢s Id,,N : Δ, A }} by mauto 3.
  assert {{ Γ ⊢s (Id,,N)∘σ : Δ, A }} by mauto 3.
  assert {{ Γ ⊢ B[(Id,,N)∘σ] ≈ B[σ,,N[σ]] : Sort@s2 }} by (eapply wf_exp_eq_conv; mauto 3).
  assert {{ Γ ⊢s σ,,N[σ] : Δ, A }} by mauto 4.
  assert {{ Γ ⊢ B[σ,,N[σ]] : Sort@s2 }} by mauto 2.
  assert {{ Γ ⊢ B[(Id,,N)∘σ] ≈ B[Id,,N][σ] : Sort@s2 }} by mauto.
  assert {{ Γ ⊢ B[Id,,N][σ] ≈ B[σ,,N[σ]] : Sort@s2 }} by mauto 3.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_sub_left : mcpts.

Lemma presup_exp_eq_app_sub_right {P : PtsSig} : forall {Γ : ctx P} {σ Δ s1 A B M N s2 s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Δ, A }} ->
    {{ Δ, A ⊢ B : Sort@s2 }} ->
    {{ Δ ⊢ M : Π r A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  assert {{ Γ ⊢ A[σ] : Sort@s1 }} by mauto 2.
  assert {{ Γ, A[σ] ⊢s q σ : Δ, A }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ B[q σ] : Sort@s2 }} by mauto 2.
  assert {{ Γ ⊢ M[σ] : Π r A[σ] B[q σ] }} by (eapply wf_conv; mauto 3).
  assert {{ Γ ⊢ N[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢s q σ∘(Id,,N[σ]) ≈ σ,,N[σ] : Δ, A }} by mauto 3.
  assert {{ Γ ⊢s Id,,N[σ] : Γ, A[σ] }} by mauto 3.
  assert {{ Γ ⊢s q σ∘(Id,,N[σ]) : Δ, A }} by mauto 2.
  assert {{ Γ ⊢ B[q σ∘(Id,,N[σ])] ≈ B[σ,,N[σ]] : Sort@s2 }} by (eapply wf_exp_eq_conv; mauto 3).
  assert {{ Γ ⊢ B[q σ][Id,,N[σ]] : Sort@s2 }} by mauto 2.
  assert {{ Γ ⊢ B[q σ][Id,,N[σ]] ≈ B[q σ∘(Id,,N[σ])] : Sort@s2 }} by (symmetry; mauto).
  assert {{ Γ ⊢ B[q σ][Id,,N[σ]] ≈ B[σ,,N[σ]] : Sort@s2 }} by (eapply wf_exp_eq_conv; mauto 3).
  eapply wf_conv; mauto.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_sub_right : mcpts.

Lemma presup_exp_eq_pi_eta_right {P : PtsSig} : forall {Γ : ctx P} {s1 A B M s2 s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ M : Π r A B }} ->
    {{ Γ ⊢ λ r A (M[Wk] #0) : Π r A B }}.
Proof.
  intros.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, A, A[Wk] ⊢s q Wk : Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢ A[Wk] : Sort@s1 }} by mauto 2.
  assert {{ Γ, A, A[Wk] ⊢ B[q Wk] : Sort@s2 }} by mauto 2.
  assert {{ Γ, A ⊢ M[Wk] : Π r A[Wk] B[q Wk] }} by (eapply wf_conv; mauto 3).
  assert {{ Γ, A ⊢ #0 : A[Wk] }} by mauto 2.
  assert {{ Γ, A ⊢s q Wk∘(Id,,#0) ≈ Id : Γ, A }} by (etransitivity; mauto 3).
  assert {{ Γ, A ⊢s Id,,#0 : Γ, A, A[Wk] }} by mauto 3.
  assert {{ Γ, A ⊢ B[q Wk∘(Id,,#0)] ≈ B[Id] : Sort@s2 }} by (eapply wf_exp_eq_conv; mauto 3).
  assert {{ Γ, A ⊢ B[q Wk][Id,,#0] ≈ B[Id] : Sort@s2 }} by (transitivity {{{ B[q Wk∘(Id,,#0)] }}}; eapply wf_exp_eq_conv; mauto 3).
  econstructor; eauto.
  eapply wf_conv; mauto 4.
Qed.

#[local]
Hint Resolve presup_exp_eq_pi_eta_right : mcpts.

(* The next four lemmas are provable, but probably only used for propositional equality, so we might want to remove them *)
Lemma presup_exp_eq_prop_eq_var0 {P : PtsSig} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    {{ Γ, A, A[Wk] ⊢ #0 : A[Wk∘Wk] }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ ⊢ Γ, A, A[Wk] }} by mauto 3.
  eapply wf_exp_conv with (A := {{{ A[Wk][Wk] }}}); mauto 4.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_var0 : mcpts.

Lemma presup_exp_eq_prop_eq_var1 {P : PtsSig} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    {{ Γ, A, A[Wk] ⊢ #1 : A[Wk∘Wk] }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ ⊢ Γ, A, A[Wk] }} by mauto 3.
  eapply var_compose_subs; mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_var1 : mcpts.

Lemma presup_exp_eq_prop_eq_sub_helper2 {P : PtsSig} : forall {Γ : ctx P} {σ Δ A M1 M2},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A }} ->
    {{ Δ ⊢ M1 : A }} ->
    {{ Δ ⊢ M2 : A }} ->
    {{ Γ ⊢s σ,,M1[σ],,M2[σ] : Δ, A, A[Wk] }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A }} by mauto 3.
  assert {{ Δ, A ⊢s Wk : Δ }} by mauto 2.
  assert {{ Γ ⊢s σ,,M1[σ] : Δ, A }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] ≈ A[Wk∘(σ,,M1[σ])] }} by mauto.
  assert {{ Γ ⊢ A[Wk∘(σ,,M1[σ])] ≈ A[σ] }} by mauto.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] ≈ A[σ] }} by (transitivity {{{ A[Wk∘(σ,,M1[σ])] }}}; mauto 3).
  assert {{ Γ ⊢ M2[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] }} by mauto 3.
  assert {{ Γ ⊢ M2[σ] : A[Wk][σ,,M1[σ]] }} by (eapply wf_conv; mauto 3).
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_sub_helper2 : mcpts.

Lemma presup_exp_eq_prop_eq_id_sub_helper2 {P : PtsSig} : forall {Γ : ctx P} {A M1 M2},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ M1 : A }} ->
    {{ Γ ⊢ M2 : A }} ->
    {{ Γ ⊢s Id,,M1,,M2 : Γ, A, A[Wk] }}.
Proof.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢s Id : Γ }} by mauto 2.
  assert {{ Γ ⊢s Id,,M1 : Γ, A }} by mauto 2.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢ A[Wk] }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][Id,,M1] }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][Id,,M1] ≈ A[Wk∘(Id,,M1)] }} by mauto.
  assert {{ Γ ⊢ A[Wk∘(Id,,M1)] ≈ A[Id] }} by mauto.
  assert {{ Γ ⊢ A[Wk][Id,,M1] ≈ A }} by mauto.
  assert {{ Γ ⊢ M2 : A[Wk][Id,,M1] }} by (eapply wf_conv; mauto 3).
  mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_id_sub_helper2 : mcpts.


Lemma presup_exp_eq_var_0_sub_left {P : PtsSig} : forall {Γ : ctx P} {σ Δ A M},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ #0[σ,,M] : A[σ] }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A }} by mauto 2.
  assert {{ Δ, A ⊢ #0 : A[Wk] }} by mauto 2.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_var_0_sub_left : mcpts.

Lemma presup_exp_eq_var_S_sub_left {P : PtsSig} : forall {Γ : ctx P} {σ Δ A M B x},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ #x : B ∈ Δ }} ->
    {{ Γ ⊢ #(S x)[σ,,M] : B[σ] }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A }} by mauto 2.
  assert ({{ Δ ⊢ B }}) by (eapply presup_ctx_lookup_typ; mauto).
  assert {{ Δ, A ⊢ #(S x) : B[Wk] }} by mauto 3.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_var_S_sub_left : mcpts.

Lemma presup_exp_eq_sub_cong_right {P : PtsSig} : forall {Γ : ctx P} {σ σ' Δ A M M'},
    {{ ⊢ Δ }} ->
    {{ Δ ⊢ A }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Δ ⊢ M' : A }} ->
    {{ Δ ⊢ M ≈ M' : A }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ' : Δ }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢ M'[σ'] : A[σ] }}.
Proof.
  intros.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_sub_cong_right : mcpts.

Lemma presup_exp_eq_sub_compose_right {P : PtsSig} : forall {Γ : ctx P} {τ Γ' σ Γ'' A M},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ' }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ ⊢ Γ'' }} ->
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ'' ⊢ A }} ->
    {{ Γ'' ⊢ M : A }} ->
    {{ Γ ⊢ M[σ][τ] : A[σ∘τ] }}.
Proof.
  intros.
  eapply wf_conv; mauto 3.
Qed.

#[local]
  Hint Resolve presup_exp_eq_sub_compose_right : mcpts.

Lemma presup_exp_eq_natrec_cong_right {P} : forall {Γ : ctx P} {A A' MZ' MS' M M' s s'} {r : Ru_nat P s},
    {{ ⊢ Γ, ℕ }} ->
    {{ Γ, ℕ ⊢ A : Sort@s' }} ->
    {{ Γ, ℕ ⊢ A' : Sort@s' }} ->
    {{ Γ, ℕ ⊢ A ≈ A' }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ MZ' : A[Id,,zero] }} ->
    {{ ⊢ Γ, ℕ, A }} ->
    {{ Γ, ℕ, A ⊢ MS' : A[Wk∘Wk,,succ #1] }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ M' : ℕ }} ->
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }}.
Proof.
  intros.
  assert {{ Γ, ℕ ⊢ A }} by mauto 3.
  assert {{ Γ, ℕ ⊢ A' }} by mauto 3.
  assert {{ Γ ⊢s Id,,M : Γ, ℕ }} by mauto 3.
  assert {{ Γ ⊢s Id,,M' : Γ, ℕ }} by mauto 3.
  assert {{ Γ ⊢s Id,,M ≈ Id,,M' : Γ, ℕ }} by mauto 3.
  assert {{ Γ ⊢ A[Id,,M] ≈ A'[Id,,M'] }} by (transitivity {{{ A[Id,,M'] }}}; mauto).
  assert {{ Γ ⊢s Id,,zero : Γ, ℕ }} by mauto 4.
  assert {{ Γ ⊢ MZ' : A'[Id,,zero] }} by mauto 4.
  assert {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by (eapply @sub_weak_compose_weak_extend_succ_var_1 with (P := P); mauto).
    
  assert {{ Γ, ℕ, A ⊢ MS' : A'[Wk∘Wk,,succ #1] }} by mauto 4.
  assert {{ ⊢ Γ, ℕ, A ≈ Γ, ℕ, A' }} by mauto 3.
  assert {{ Γ, ℕ, A' ⊢ MS' : A'[Wk∘Wk,,succ #1] }} by mauto 3.
  eapply wf_conv; mauto 2.
Qed.

#[local]
  Hint Resolve presup_exp_eq_natrec_cong_right : mcpts.


Lemma presup_exp_eq_natrec_sub_left {P} : forall {Γ : ctx P}  {σ Δ A MZ MS M s s'} {r : Ru_nat P s},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ ⊢ Δ, ℕ }} ->
    {{ Δ, ℕ ⊢ A : Sort@s' }} ->
    {{ Δ ⊢ MZ : A[Id,,zero] }} ->
    {{ ⊢ Δ, ℕ, A }} ->
    {{ Δ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] : A[σ,,M[σ]] }}.
Proof.
  intros.
  assert {{ Δ, ℕ ⊢ A }} by mauto 2.
  assert {{ Γ ⊢s σ,,M[σ] : Δ, ℕ }} by mauto 3.
  assert {{ Γ ⊢ A[σ,,M[σ]] }} by mauto 2.
  assert {{ Δ ⊢s Id,,M : Δ, ℕ }} by mauto 3.
  assert {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Δ, ℕ }} by mauto.
  assert {{ Γ ⊢ A[(Id,,M)∘σ] ≈ A[σ,,M[σ]] }} by mauto 3.
  assert {{ Γ ⊢ A[Id,,M][σ] ≈ A[σ,,M[σ]] }} by mauto 3.
  eapply wf_conv; mauto 3.
Qed.

#[local]
  Hint Resolve presup_exp_eq_natrec_sub_left : mcpts.



Lemma presup_exp_eq_natrec_sub_right {P} : forall {Γ : ctx P} {σ Δ A MZ MS M s s'} {r : Ru_nat P s},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ ⊢ Δ, ℕ }} ->
    {{ Δ, ℕ ⊢ A : Sort@s' }} ->
    {{ Δ ⊢ MZ : A[Id,,zero] }} ->
    {{ ⊢ Δ, ℕ, A }} ->
    {{ Δ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }}.
Proof.
  intros.
  assert {{ Δ, ℕ ⊢ A }} by mauto 2.
  assert {{ Γ, ℕ ⊢s q σ : Δ, ℕ }} by mauto 2.
  assert {{ Γ, ℕ, A[q σ] ⊢s q (q σ) : Δ, ℕ, A }} by mauto 2.
  assert {{ Γ, ℕ ⊢ A[q σ] }} by mauto 3.
  (* Possible lemma? *)
  assert (forall N, {{ Γ ⊢ N : ℕ }} -> {{ Γ ⊢ A[q σ][Id,,N] }} /\ {{ Γ ⊢ A[q σ][Id,,N] ≈ A[σ,,N] }}).
  {
    intros.
    assert {{ Γ ⊢ N : ℕ[σ] }} by mauto 3.
    assert {{ Γ ⊢s Id,,N : Γ, ℕ }} by mauto 3.
    assert {{ Γ ⊢s q σ∘(Id,,N) ≈ σ,,N : Δ, ℕ }} by mauto 3.
    assert {{ Γ ⊢s σ,,N : Δ, ℕ }} by mauto 2.
    assert {{ Γ ⊢ A[q σ∘(Id,,N)] ≈ A[σ,,N] }} by mauto 3.
    split; mauto 3.
  }
  (* Assertion for M *)
  assert {{ Γ ⊢ M[σ] : ℕ }} by mauto 3.
  (* Assertion for type *)
  assert ({{ Γ ⊢ A[q σ][Id,,M[σ]] }} /\ {{ Γ ⊢ A[q σ][Id,,M[σ]] ≈ A[σ,,M[σ]] }}) as [] by mauto 3.
   (* Assertion for MZ *)
  assert {{ Δ ⊢ zero : ℕ }} by mauto 2.
  assert {{ Δ ⊢s Id,,zero : Δ, ℕ }} by mauto.
  assert {{ Γ ⊢ zero[σ] ≈ zero : ℕ }} by mauto 2.
  assert {{ Γ ⊢s σ,,zero[σ] ≈ σ,,zero : Δ, ℕ }} by mauto 3.
  assert {{ Γ ⊢s (Id,,zero)∘σ ≈ σ,,zero : Δ, ℕ }} by mauto.
  assert ({{ Γ ⊢ A[q σ][Id,,zero] }} /\ {{ Γ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] }}) as [] by mauto 3.
  assert {{ Γ ⊢ A[(Id,,zero)∘σ] ≈ A[σ,,zero] }} by mauto 3.
  assert {{ Γ ⊢ A[q σ][Id,,zero] ≈ A[Id,,zero][σ] }} by (etransitivity; [| symmetry]; mauto 3).
  assert {{ Γ ⊢ MZ[σ] : A[q σ][Id,,zero] }} by mauto 4.
  (* Assertion for MS *)
  assert {{ Δ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }}  by (eapply @sub_weak_compose_weak_extend_succ_var_1 with (P := P); mauto). 
  assert {{ Γ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }}  by (eapply @sub_weak_compose_weak_extend_succ_var_1 with (P := P); mauto). 
  assert {{ Γ, ℕ, A[q σ] ⊢s q σ∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘q (q σ) : Δ, ℕ }} by mauto 2.
  assert {{ Γ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q σ)] }} by mauto 2.
  assert {{ Γ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by (eapply wf_conv; mauto 2).
  (* Final *)
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_natrec_sub_right : mcpts.


Lemma presup_exp_eq_beta_succ_right {P} : forall {Γ : ctx P} {A MZ MS M s s'} {r : Ru_nat P s},
    {{ ⊢ Γ, ℕ }} ->
    {{ Γ, ℕ ⊢ A : Sort@s' }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ ⊢ Γ, ℕ, A }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }}.
Proof.
  intros.
  assert {{ Γ, ℕ ⊢ A }} by mauto 2.
  (** Coq was having trouble inferring P here, expanded definition for now **)
  (** set (WkWksucc := {{{ Wk∘Wk,,succ #1 }}}). **)
  set (recM := {{{ rec M return A | zero -> MZ | succ -> MS end }}}).
  set (IdMrecM := {{{ Id,,M,,recM }}}).
  (* Assertion for type *)
  assert {{ Γ ⊢ ℕ  }} by mauto 3.
  assert {{ Γ ⊢ recM : A[Id,,M] }} by mauto 4.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 2.
  assert {{ Γ, ℕ, A ⊢s Wk∘Wk : Γ }} by mauto 2.
  assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘IdMrecM ≈ (Wk∘Wk)∘IdMrecM,,(succ #1)[IdMrecM] : Γ, ℕ }}
    by (eapply @sub_eq_extend_compose_nat with (P := P); mauto 3).
  assert {{ Γ ⊢s Id : Γ }} by mauto 2.
  assert {{ Γ ⊢s IdMrecM : Γ, ℕ, A }} by mauto 3.
  assert {{ Γ ⊢s (Wk∘Wk)∘IdMrecM : Γ }} by mauto 2.
  assert {{ Γ ⊢s (Wk∘Wk)∘IdMrecM ≈ Wk∘(Wk∘IdMrecM) : Γ }} by mauto 2.
  assert {{ Γ ⊢s Id,,M : Γ, ℕ }} by mauto 2.
  assert {{ Γ ⊢s Wk∘(Wk∘IdMrecM) ≈ Wk∘(Id,,M) : Γ }} by (econstructor; mauto 2).
  assert {{ Γ ⊢s (Wk∘Wk)∘IdMrecM ≈ Id : Γ }} by (etransitivity; mauto 3).
  assert {{ Γ ⊢ #1[IdMrecM] ≈ #0[Id,,M] : ℕ }} by mauto 3.
  assert {{ Γ ⊢ #1[IdMrecM] ≈ M : ℕ }} by mauto 3.
  assert {{ Γ ⊢ succ #1[IdMrecM] ≈ succ M : ℕ }} by mauto 2.
  assert {{ Γ ⊢ (succ #1)[IdMrecM] ≈ succ M : ℕ }} by (etransitivity; mauto 3).
  assert {{ Γ ⊢s (Wk∘Wk)∘IdMrecM,,(succ #1)[IdMrecM] ≈ Id,,succ M : Γ, ℕ }} by mauto 2.
  assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘IdMrecM : Γ, ℕ }} by mauto 5.
  assert {{ Γ ⊢s Id,,succ M : Γ, ℕ }} by mauto 3.
  assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘IdMrecM ≈ Id,,succ M : Γ, ℕ }} by mauto 2.
  assert {{ Γ ⊢ A[(Wk∘Wk,,succ #1)∘IdMrecM] ≈ A[Id,,succ M] }} by mauto.
  enough {{ Γ ⊢ A[Wk∘Wk,,succ #1][IdMrecM] ≈ A[Id,,succ M] }}; [eapply wf_conv | etransitivity]; mauto 5.
Qed.

#[local]
  Hint Resolve presup_exp_eq_beta_succ_right :
  mcpts.


#[local]
Ltac gen_presup_IH presup_exp_eq presup_sub_eq presup_typ_eq H :=
  match type of H with
  | {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} =>
      let HΓ := fresh "HΓ" in
      let HM := fresh "HM" in
      let HN := fresh "HN" in
      let HA := fresh "HA" in
      pose proof presup_exp_eq _ _ _ _ _ H as [HΓ [HM [HN HA]]]
  | {{ ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Δ }} =>
      let HΓ := fresh "HΓ" in
      let Hσ := fresh "Hσ" in
      let Hτ := fresh "Hτ" in
      let HΔ := fresh "HΔ" in
      pose proof presup_sub_eq _ _ _ _ _ H as [HΓ [Hσ [Hτ HΔ]]]
  | {{ ^?Γ ⊢ ^?A ≈ ^?B }} =>
      let HΓ := fresh "HΓ" in
      let HA := fresh "HA" in
      let HB := fresh "HB" in
      pose proof presup_typ_eq _ _ _ _ H as [HΓ [HA HB]]
  end.

Lemma presup_exp_eq {P : PtsSig} : forall {Γ : ctx P} {M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ M : A }} /\ {{ Γ ⊢ M' : A }} /\ {{ Γ ⊢ A  }}
with presup_sub_eq {P : PtsSig} : forall {Γ : ctx P} {Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢s σ : Δ }} /\ {{ Γ ⊢s σ' : Δ }} /\ {{ ⊢ Δ }}
with presup_typ_eq {P : PtsSig} : forall {Γ : ctx P} {A A'}, {{ Γ ⊢ A ≈ A' }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ A }} /\ {{ Γ ⊢ A' }}.
Proof with mautosolve 5.
  all: inversion_clear 1;
    (on_all_hyp: gen_presup_IH presup_exp_eq presup_sub_eq presup_typ_eq);
    gen_core_presups;
    clear presup_exp_eq presup_sub_eq presup_typ_eq;
    repeat split; try mautosolve 3;
    try (eexists; unshelve solve [mauto 4]; constructor).

  all: try (econstructor; mautosolve 4).
  - econstructor; mauto 3.
    assert {{ ⊢ Γ, A0 ≈ Γ, A' }} by (econstructor; mauto 2).
    eapply wf_conv; mauto 3.
  - econstructor; mauto 3.
    eapply wf_conv...
  - econstructor; mauto 3.
    eapply wf_conv; mauto 5.
Qed.

Ltac gen_presup H := gen_presup_IH @presup_exp_eq @presup_sub_eq @presup_typ_eq H + gen_core_presup H.

Ltac gen_presups := (on_all_hyp: fun H => gen_presup H); invert_wf_ctx; (on_all_hyp: fun H => gen_lookup_presup H); clear_dups.
