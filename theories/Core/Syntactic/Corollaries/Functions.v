From Coq Require Import Setoid Nat.
From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Export SystemOpt.
From McPTS.Core.Syntactic.Corollaries Require Import TermStructure.
Import Syntax_Notations.

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
