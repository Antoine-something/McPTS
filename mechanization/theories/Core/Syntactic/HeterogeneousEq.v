From Coq Require Import Setoid Nat.
From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

(** Helper lemmas for cases related to sorts *)
Lemma wf_exp_sort_sort {P} : forall {Γ : ctx P} {s A},
    {{ Γ ⊢ Sort@s : A }} ->
    exists s', {{ Γ ⊢ Sort@s' ≈ A }}.
Proof.
  intros * HA.
  dependent induction HA.
  - eexists; mauto.
  - specialize (IHHA s A0 ltac:(reflexivity) ltac:(reflexivity)).
    destruct IHHA as [s' ?].
    exists s'.
    etransitivity; mauto 2.
Qed.

#[local]
Hint Resolve wf_exp_sort_sort : mcpts.

Lemma wf_exp_sort_under_sub {P} : forall {Γ Δ : ctx P} {σ s K},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ Sort@s : K }} ->
    {{ Γ ⊢ Sort@s : K[σ] }}.
Proof.
  intros * Hσ HK.
  dependent induction HK.
  - assert {{ Γ ⊢ Sort@s2[σ] ≈ Sort@s2 }} by mauto 2.
    eapply wf_conv; mauto 3.
  - specialize (IHHK Γ σ s A Hσ ltac:(reflexivity) ltac:(reflexivity)).
    assert {{ Γ ⊢ A[σ] ≈ K[σ] }} by mauto 2.
    eapply wf_conv; mauto 2.
Qed.

#[local]
Hint Resolve wf_exp_sort_under_sub : mcpts.

Lemma wf_exp_sort_under_sub' {P} : forall {Γ Δ : ctx P} {σ s K},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ Sort@s : K }} ->
    {{ Γ ⊢ Sort@s[σ] : K }}.
Proof.
  intros * Hσ HK.
  dependent induction HK.
  - gen_presup Hσ.
    assert {{ Δ ⊢ Sort@s : Sort@s2 }} by mauto 2.
    assert {{ Γ ⊢ Sort@s2[σ] ≈ Sort@s2 }} by mauto 2.
    eapply wf_conv; mauto 2.
  - specialize (IHHK Δ σ s A Hσ ltac:(reflexivity) ltac:(reflexivity)).
    eapply wf_conv; mauto 2.
Qed.

#[local]
Hint Resolve wf_exp_sort_under_sub' : mcpts.


Lemma wf_exp_sort_wf_eq_sort_sub {P} : forall {Γ Δ : ctx P} {σ s K},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ Sort@s : K }} ->
    {{ Γ ⊢ Sort@s[σ] ≈ Sort@s : K }}.
Proof.
  intros * Hσ HK.
  dependent induction HK; mauto 3.
Qed.

#[local]
Hint Resolve wf_exp_sort_wf_eq_sort_sub : mcpts.


Lemma wf_exp_sort_sub_wf_eq_sort_sub {P} : forall {Γ Δ : ctx P} {σ s K},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ Sort@s[σ] : K }} ->
    {{ Γ ⊢ Sort@s[σ] ≈ Sort@s : K }}.
Proof.
  intros * Hσ HK.
  dependent induction HK; mauto 3.
Qed.

#[local]
Hint Resolve wf_exp_sort_sub_wf_eq_sort_sub : mcpts.


Lemma wf_exp_sort_sub_wf_exp_sort {P} : forall {Γ Δ : ctx P} {σ s K},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ Sort@s[σ] : K }} ->
    {{ Γ ⊢ Sort@s : K }}.
Proof.
  intros * Hσ HK.
  assert {{ Γ ⊢ Sort@s[σ] ≈ Sort@s : K }} by mauto 2.
  gen_presups.
  eassumption.
Qed.

#[local]
Hint Resolve wf_exp_sort_sub_wf_exp_sort : mcpts.
  
  

(** Helper lemmas for cases related to functions *)
Lemma wf_exp_pi_sub_wf_exp_pi {P} : forall {Γ : ctx P} {A B K σ s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ (Π r A B)[σ] : K }} ->
    {{ Γ ⊢ Π r A[σ] B[q σ] : K }}.
Proof.
  intros * H; gen_presup H.
  
  assert (exists Δ K', {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ Π r A B : K' }} /\ {{ Γ ⊢ K'[σ] ≈ K }}) by mauto 2.
  destruct H0 as [Δ [K' [? []]]].

  assert ({{ Δ ⊢ A : Sort@s1 }} /\ {{ Δ, A ⊢ B : Sort@s2 }} /\ {{ Δ ⊢ Sort@s3 ≈ K' }}) by mauto 2.
  destruct_conjs.

  assert {{ Γ ⊢ A[σ] : Sort@s1 }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ B[q σ] : Sort@s2 }} by mauto 4.
  assert {{ Γ ⊢ Π r A[σ] B[q σ] : Sort@s3 }} by mauto 2.

  assert {{ Γ ⊢ Sort@s3 ≈ Sort@s3[σ] }} by mauto 3.
  assert {{ Γ ⊢ Sort@s3[σ] ≈ K'[σ] }} by mauto 2.
  assert {{ Γ ⊢ Sort@s3 ≈ K }} by (do 2 etransitivity; mauto 3).

  eapply wf_conv; mauto 2.
Qed.

#[local]
Hint Resolve wf_exp_pi_sub_wf_exp_pi : mcpts.

Lemma wf_exp_pi_sub_wf_exp_eq_pi {P} : forall {Γ : ctx P} {A B K σ s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ (Π r A B)[σ] : K }} ->
    {{ Γ ⊢ (Π r A B)[σ] ≈ Π r A[σ] B[q σ] : K }}.
Proof.
  intros * H; gen_presup H.

  assert (exists Δ K', {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ Π r A B : K' }} /\ {{ Γ ⊢ K'[σ] ≈ K }}) by mauto 2.
  destruct H0 as [Δ [K' [? []]]].

  assert ({{ Δ ⊢ A : Sort@s1 }} /\ {{ Δ, A ⊢ B : Sort@s2 }} /\ {{ Δ ⊢ Sort@s3 ≈ K' }}) by mauto 2.
  destruct_conjs.

  assert {{ Γ ⊢ Sort@s3 ≈ Sort@s3[σ] }} by mauto 3.
  assert {{ Γ ⊢ Sort@s3[σ] ≈ K'[σ] }} by mauto 2.
  assert {{ Γ ⊢ Sort@s3 ≈ K }} by (do 2 etransitivity; mauto 3).

  eapply wf_exp_eq_conv'; mauto 2.
Qed.
  
#[local]
Hint Resolve wf_exp_pi_sub_wf_exp_eq_pi : mcpts.

Lemma wf_exp_pi_wf_exp_pi_sub_helper {P} : forall {Γ : ctx P} {A B K σ s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ Π r A[σ] B[q σ] : K }} ->
    exists Δ K', {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ Π r A B : K' }} /\ {{ Γ ⊢ K'[σ] ≈ K }}.
Proof.
  intros * H.
  assert ({{ Γ ⊢ A[σ] : Sort@s1 }} /\ {{ Γ, A[σ] ⊢ B[q σ] : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ≈ K }}) by mauto 2.
  destruct_conjs.

  assert (exists Δ K', {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ A : K' }} /\ {{ Γ ⊢ K'[σ] ≈ Sort@s1 }}) by mauto 2.
  destruct H3 as [Δ [K' [? []]]].

Admitted.


  
Lemma wf_exp_pi_wf_exp_eq_pi_sub {P} : forall {Γ : ctx P} {A B K σ s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ Π r A[σ] B[q σ] : K }} ->
    {{ Γ ⊢ (Π r A B)[σ] ≈ Π r A[σ] B[q σ] : K }}.
Proof.
  intros * H; gen_presup H.
  assert (exists Δ K', {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ Π r A B : K' }} /\ {{ Γ ⊢ K'[σ] ≈ K }}) by (eapply wf_exp_pi_wf_exp_pi_sub_helper; mauto 2).
  destruct H0 as [Δ [K' [? []]]].
  assert ({{ Δ ⊢ A : Sort@s1 }} /\ {{ Δ, A ⊢ B : Sort@s2 }} /\ {{ Δ ⊢ Sort@s3 ≈ K' }}) by mauto 2.
  destruct_conjs.
  mauto 4.
Qed.

#[local]
Hint Resolve wf_exp_pi_wf_exp_eq_pi_sub : mcpts.

Corollary wf_exp_pi_wf_exp_pi_sub {P} : forall {Γ : ctx P} {A B K σ s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ Π r A[σ] B[q σ] : K }} ->
    {{ Γ ⊢ (Π r A B)[σ] : K }}.
Proof.
  intros * H.
  assert {{ Γ ⊢ (Π r A B)[σ] ≈ Π r A[σ] B[q σ] : K }} by mauto 2.
  gen_presups; eassumption.
Qed.

#[local]
Hint Resolve wf_exp_pi_wf_exp_pi_sub : mcpts.


(** Main theorem *)
Theorem wf_exp_eq_escape {P} : forall {Γ : ctx P} {A B K},
    {{ Γ ⊢ A ≈ B : K }} ->
    forall K',
      ({{ Γ ⊢ A : K' }} -> {{ Γ ⊢ B : K' }} /\ {{ Γ ⊢ A ≈ B : K' }}) /\
        ({{ Γ ⊢ B : K' }} -> {{ Γ ⊢ A : K' }} /\ {{ Γ ⊢ A ≈ B : K' }})
          
with wf_typ_eq_escape {P} : forall {Γ : ctx P} {A B},
    {{ Γ ⊢ A ≈ B }} ->
    forall K,
      ({{ Γ ⊢ A : K }} -> {{ Γ ⊢ B : K }} /\ {{ Γ ⊢ A ≈ B : K }}) /\
        ({{ Γ ⊢ B : K }} -> {{ Γ ⊢ A : K }} /\ {{ Γ ⊢ A ≈ B : K }})

with wf_sub_eq_escape {P} : forall {Γ Δ : ctx P} {σ τ},
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    forall Γ' Δ',
      ({{ Γ' ⊢s σ : Δ' }} -> {{ Γ' ⊢s τ : Δ' }} /\ {{ Γ' ⊢s σ ≈ τ : Δ' }}) /\
        ({{ Γ' ⊢s τ : Δ' }} -> {{ Γ' ⊢s σ : Δ' }} /\ {{ Γ' ⊢s σ ≈ τ : Δ' }}).
Proof.
  all: clear wf_exp_eq_escape wf_typ_eq_escape wf_sub_eq_escape;
    intros * H;
    dependent induction H; intros; mauto 2;
    split; intros; split; mauto 3.

Admitted.
 
Corollary wf_typ_eq_het_wf_exp_left {P} : forall {Γ : ctx P} {A B K},
    {{ Γ ⊢ A ≈ B }} ->
    {{ Γ ⊢ A : K }} ->
    {{ Γ ⊢ B : K }}.
Proof. intros; eapply wf_typ_eq_escape; mauto 2. Qed.

Corollary wf_typ_eq_het_wf_exp_right {P} : forall {Γ : ctx P} {A B K},
    {{ Γ ⊢ A ≈ B }} ->
    {{ Γ ⊢ B : K }} ->
    {{ Γ ⊢ A : K }}.
Proof. intros; eapply wf_typ_eq_escape; mauto 2. Qed.

Corollary wf_typ_eq_het_wf_exp_eq_left {P} : forall {Γ : ctx P} {A B K},
    {{ Γ ⊢ A ≈ B }} ->
    {{ Γ ⊢ A : K }} ->
    {{ Γ ⊢ A ≈ B : K }}.
Proof.
  intros.
  assert ({{ Γ ⊢ B : K }} /\ {{ Γ ⊢ A ≈ B : K }}) by (eapply wf_typ_eq_escape; mauto 2).
  destruct_conjs; eassumption.
Qed.

Corollary wf_typ_eq_het_wf_exp_eq_right {P} : forall {Γ : ctx P} {A B K},
    {{ Γ ⊢ A ≈ B }} ->
    {{ Γ ⊢ B : K }} ->
    {{ Γ ⊢ A ≈ B : K }}.
Proof.
  intros.
  assert ({{ Γ ⊢ A : K }} /\ {{ Γ ⊢ A ≈ B : K }}) by (eapply wf_typ_eq_escape; mauto 2).
  destruct_conjs; eassumption.
Qed.

#[export]
Hint Resolve wf_typ_eq_het_wf_exp_left wf_typ_eq_het_wf_exp_right wf_typ_eq_het_wf_exp_eq_left wf_typ_eq_het_wf_exp_eq_right : mcpts.
