From Coq Require Import Setoid.
From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export CtxEq.
Import Syntax_Notations.


Lemma wf_pi_inversion {P : PtsSig} : forall {Γ : ctx P} {A B C s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ Π r A B : C }} ->
    {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ⊆ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups; mauto 3.
  - assert {{ ⊢ Γ }} by mauto 2.
    assert {{ Γ ⊢ Sort@s3 }} by mauto 3.
    repeat split; mauto 3.
  - split; [|split];
      [| | transitivity A0; mauto 2];
      eapply IHwf_exp; mauto 2.
Qed.

#[export]
Hint Resolve wf_pi_inversion : mcpts.

Corollary wf_pi_inversion' {P : PtsSig} : forall {Γ : ctx P} {A B C s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ Π r A B : C }} ->
    {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }}.
Proof with mautosolve 4.
  intros * ?%wf_pi_inversion.
  destruct_conjs; mauto 2.
Qed.

Corollary wf_pi_inversion_typ {P} : forall {Γ : ctx P} {A B C s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ Π r A B : C }} ->
    {{ Γ ⊢ Sort@s3 ⊆ C }}.
Proof.
  intros * ?%wf_pi_inversion.
  destruct_conjs; mauto 2.
Qed.

#[export]
Hint Resolve wf_pi_inversion' wf_pi_inversion_typ : mcpts.

Corollary wf_typ_pi_inversion {P : PtsSig} : forall {Γ : ctx P} {A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ Π r A B }} ->
    {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }}.
Proof.
  inversion 1; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_pi_inversion : mcpts.

Corollary wf_typ_pi_inversion' {P : PtsSig} : forall {Γ : ctx P} {A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ Π r A B }} ->
    {{ Γ ⊢ Π r A B : Sort@s3 }}.
Proof.
  intros.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }}) by mauto 2.
  destruct_conjs.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_pi_inversion' : mcpts.

Corollary wf_fn_inversion {P : PtsSig} : forall {Γ : ctx P} {A B M C s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ λ r A B M : C }} ->
    {{ Γ, A ⊢ M : B }} /\ {{ Γ ⊢ Π r A B ⊆ C }}.
Proof with solve [mauto].
  intros * H.
  dependent induction H;
    gen_core_presups.
  - split; mauto.
  - specialize (IHwf_exp A B M A0 s1 s2 s3 r ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    split; mauto 2.
Qed.

#[export]
Hint Resolve wf_fn_inversion : mcpts.

Lemma wf_app_inversion {P : PtsSig} : forall {Γ : ctx P} {M N C},
    {{ Γ ⊢ M N : C }} ->
    exists A B s1 s2 s3 (r : Ru_pi P s1 s2 s3), {{ Γ ⊢ M : Π r A B }} /\ {{ Γ ⊢ N : A }} /\ {{ Γ ⊢ B[Id,,N] ⊆ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - do 6 eexists; repeat split; eauto.
    assert {{ Γ ⊢ B[Id,,N] : Sort@s2 }} by mauto 3.
    eapply wf_subtyp_refl; mauto 3.
  - specialize (IHwf_exp M N A ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    do 6 eexists; repeat split; mauto.
Qed.

#[export]
Hint Resolve wf_app_inversion : mcpts.

Lemma wf_sigma_inversion {P : PtsSig} : forall {Γ : ctx P} {A B C s1 s2 s3} {r : Ru_sigma P s1 s2 s3},
    {{ Γ ⊢ Σ r A B : C }} ->
    {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ⊆ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - assert {{ ⊢ Γ }} by mauto 2.
    assert {{ Γ ⊢ Sort@s3 }} by mauto 3.
    repeat split; mauto 3.
  - split; [|split];
      [| | transitivity A0; mauto 2];
      eapply IHwf_exp; mauto 2.
Qed.

#[export]
Hint Resolve wf_sigma_inversion : mcpts.

Corollary wf_sigma_inversion' {P : PtsSig} : forall {Γ : ctx P} {A B C s1 s2 s3} {r : Ru_sigma P s1 s2 s3},
    {{ Γ ⊢ Σ r A B : C }} ->
    {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }}.
Proof with mautosolve 4.
  intros * ?%wf_sigma_inversion.
  destruct_conjs; mauto 2.
Qed.

Corollary wf_sigma_inversion_typ {P} : forall {Γ : ctx P} {A B C s1 s2 s3} {r : Ru_sigma P s1 s2 s3},
    {{ Γ ⊢ Σ r A B : C }} ->
    {{ Γ ⊢ Sort@s3 ⊆ C }}.
Proof.
  intros * ?%wf_sigma_inversion.
  destruct_conjs; mauto 2.
Qed.

#[export]
Hint Resolve wf_sigma_inversion' wf_sigma_inversion_typ : mcpts.

Corollary wf_typ_sigma_inversion {P : PtsSig} : forall {Γ : ctx P} {A B s1 s2 s3} {r : Ru_sigma P s1 s2 s3},
    {{ Γ ⊢ Σ r A B }} ->
    {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }}.
Proof.
  inversion 1; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_sigma_inversion : mcpts.

Corollary wf_typ_sigma_inversion' {P : PtsSig} : forall {Γ : ctx P} {A B s1 s2 s3} {r : Ru_sigma P s1 s2 s3},
    {{ Γ ⊢ Σ r A B }} ->
    {{ Γ ⊢ Σ r A B : Sort@s3 }}.
Proof.
  intros.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }}) by mauto 2.
  destruct_conjs.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_sigma_inversion' : mcpts.

Corollary wf_pair_inversion {P : PtsSig} : forall {Γ : ctx P} {A B M N C s1 s2 s3} {r : Ru_sigma P s1 s2 s3},
    {{ Γ ⊢ ⟨r; M : A; N : B⟩ : C }} ->
    {{ Γ ⊢ M : A }} /\ {{ Γ ⊢ N : B[Id,,M] }} /\ {{ Γ ⊢ Σ r A B ⊆ C }}.
Proof with solve [mauto].
  intros * H.
  dependent induction H;
    gen_core_presups.
  - split; mauto.
  - specialize (IHwf_exp A B M N A0 s1 s2 s3 r ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    repeat (split; mauto 2).
Qed.

#[export]
Hint Resolve wf_pair_inversion : mcpts.

Lemma wf_fst_inversion {P : PtsSig} : forall {Γ : ctx P} {M C},
    {{ Γ ⊢ fst M : C }} ->
    exists A B s1 s2 s3 (r : Ru_sigma P s1 s2 s3), {{ Γ ⊢ M : Σ r A B }} /\ {{ Γ ⊢ A ⊆ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - do 6 eexists; repeat split; eauto.
    eapply wf_subtyp_refl; mauto 3.
  - specialize (IHwf_exp M A ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    do 6 eexists; repeat split; mauto.
Qed.

#[export]
Hint Resolve wf_fst_inversion : mcpts.

Lemma wf_snd_inversion {P : PtsSig} : forall {Γ : ctx P} {M C},
    {{ Γ ⊢ snd M : C }} ->
    exists A B s1 s2 s3 (r : Ru_sigma P s1 s2 s3), {{ Γ ⊢ M : Σ r A B }} /\ {{ Γ ⊢ B[Id,,fst M] ⊆ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - do 6 eexists; repeat split; eauto.
    assert {{ Γ ⊢ fst M : A }} by mauto 2.
    assert {{ Γ ⊢s Id,,fst M : Γ, A }} by mauto 3.
    eapply wf_subtyp_refl; mauto 4.
  - specialize (IHwf_exp M A ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    do 6 eexists; repeat split; mauto.
Qed.

#[export]
Hint Resolve wf_snd_inversion : mcpts.

Lemma wf_vlookup_inversion {P : PtsSig} : forall {Γ : ctx P} {A : exp P} {x},
    {{ Γ ⊢ #x : A }} ->
    exists A', {{ #x : A' ∈ Γ }} /\ {{ Γ ⊢ A' ⊆ A }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - do 2 eexists; mauto 3.
  - specialize (IHwf_exp A0 x ltac:(reflexivity) ltac:(reflexivity)) as [A' []].
    do 2 eexists; mauto 3.
Qed.

#[export]
Hint Resolve wf_vlookup_inversion : mcpts.

Lemma wf_nat_inversion {P} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ ℕ : A }} ->
    exists s (r : Ru_nat P s),
      {{ Γ ⊢ Sort@s ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H.
  - do 2 eexists; mauto 3.
  - specialize (IHwf_exp A0 ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    eexists; mauto 3. 
Qed.

#[export]
Hint Resolve wf_nat_inversion : mcpts.

Corollary wf_zero_inversion {P} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ zero : A }} ->
    exists s (r : Ru_nat P s),
      {{ Γ ⊢ ℕ ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H.
  - eexists. mauto.
  - specialize (IHwf_exp A0 ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    do 2 eexists. apply H3.
    etransitivity; mauto.
Qed.

#[export]
Hint Resolve wf_zero_inversion : mcpts.

Corollary wf_succ_inversion {P} : forall {Γ : ctx P} {A M},
    {{ Γ ⊢ succ M : A }} ->
    {{ Γ ⊢ M : ℕ }} /\ {{ Γ ⊢ ℕ ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H.
  - eexists; mautosolve.
  - specialize (IHwf_exp A0 M ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    eexists; mauto 3. 
Qed.

#[export]
Hint Resolve wf_succ_inversion : mcpts.

Lemma wf_natrec_inversion {P} : forall {Γ : ctx P} {A M A' MZ MS},
    {{ Γ ⊢ rec M return A' | zero -> MZ | succ -> MS end : A }} ->
    {{ Γ ⊢ MZ : A'[Id,,zero] }} /\ {{ Γ, ℕ, A' ⊢ MS : A'[Wk∘Wk,,succ(#1)] }} /\ {{ Γ ⊢ M : ℕ }} /\ {{ Γ ⊢ A'[Id,,M] ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H.
  - do 3 (eexists; mauto 2).
    assert {{ ⊢ Γ }} by mauto 3.
    assert {{ Γ ⊢s Id,,M : Γ, ℕ }} by mauto 3.
    assert {{ Γ ⊢ A'[Id,,M] }} by mauto 3.
    eapply wf_subtyp_refl; mauto 3.
  - specialize (IHwf_exp A0 M A' MZ MS ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    repeat split; mauto.
Qed.

#[export]
Hint Resolve wf_natrec_inversion : mcpts.

Lemma wf_exp_sub_inversion {P} : forall {Γ : ctx P} {M σ A},
    {{ Γ ⊢ M[σ] : A }} ->
    exists Δ A', {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ M : A' }} /\ {{ Γ ⊢ A'[σ] ⊆ A }}.
Proof with mautosolve 3.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - do 2 eexists; repeat split; mauto 2.
    assert {{ Γ ⊢ A0[σ] }} by mauto 3.
    eapply wf_subtyp_refl; mauto 2.
  - specialize (IHwf_exp M σ A0 ltac:(reflexivity) ltac:(reflexivity)) as [Δ [A' [? []]]].
    do 2 eexists; repeat split; mauto 2.
Qed.    
    
#[export]
Hint Resolve wf_exp_sub_inversion : mcpts.


(** We omit [wf_conv] as they do not give useful inversions *)

Lemma wf_sub_id_inversion {P : PtsSig} : forall (Γ : ctx P) Δ,
    {{ Γ ⊢s Id : Δ }} ->
    {{ ⊢ Γ ⊆ Δ }}.
Proof.
  intros * H.
  dependent induction H; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_sub_id_inversion : mcpts.

Lemma wf_sub_weaken_inversion {P : PtsSig} : forall {Γ : ctx P} {Δ},
    {{ Γ ⊢s Wk : Δ }} ->
    exists Γ' A, {{ ⊢ Γ ≈ Γ', A }} /\ {{ ⊢ Γ' ⊆ Δ }}.
Proof.
  intros * H.
  dependent induction H;
    firstorder;
    progressive_inversion.
  - repeat eexists; mauto 2.
  - assert (exists Γ' A, {{ ⊢ Γ ≈ Γ', A }} /\ {{ ⊢ Γ' ⊆ Δ0 }}) by (eapply IHwf_sub; mauto).
    destruct_conjs.
    repeat eexists; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_weaken_inversion : mcpts.

Lemma wf_sub_compose_inversion {P : PtsSig} : forall {Γ1 : ctx P} {σ1 σ2 Γ3},
    {{ Γ1 ⊢s σ1 ∘ σ2 : Γ3 }} ->
    exists Γ2, {{ Γ1 ⊢s σ2 : Γ2 }} /\ {{ Γ2 ⊢s σ1 : Γ3 }}.
Proof with mautosolve 3.
  intros * H.
  dependent induction H; mauto 3.
  assert (exists Γ2, {{ Γ ⊢s σ2 : Γ2 }} /\ {{ Γ2 ⊢s σ1 : Δ }}) by (eapply IHwf_sub; mauto).
  destruct_conjs.
  eexists; split; mauto.
Qed.

#[export]
Hint Resolve wf_sub_compose_inversion : mcpts.

Lemma wf_sub_extend_inversion {P : PtsSig} : forall {Γ : ctx P} {σ M Δ},
    {{ Γ ⊢s σ,,M : Δ }} ->
    exists Δ' A', {{ ⊢ Δ', A' ⊆ Δ }} /\ {{ Γ ⊢s σ : Δ' }} /\ {{ Γ ⊢ M : A'[σ] }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - repeat eexists...
  - assert (exists Δ' A', {{ ⊢ Δ', A' ⊆ Δ0 }} /\ {{ Γ ⊢s σ : Δ' }} /\ {{ Γ ⊢ M : A'[σ] }}) by (eapply IHwf_sub; mauto).
    destruct_conjs.
    repeat eexists...
Qed.

#[export]
Hint Resolve wf_sub_extend_inversion : mcpts.

Lemma wf_typ_inversion {P} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    (exists s, {{ Γ ⊢ A ≈ Sort@s }} \/ {{ Γ ⊢ A : Sort@s }}).
Proof.
  induction 1; mauto.
  destruct IHwf_typ as [s []].
  - eexists; left.
    transitivity {{{ Sort@s[σ] }}}; mauto 3.
  - eexists; right; mauto 3.
Qed.
