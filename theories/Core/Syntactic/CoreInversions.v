From Coq Require Import Setoid.
From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export CtxEq.
Import Syntax_Notations.


Lemma wf_pi_inversion {P : PtsSig} : forall {Γ : ctx P} {A B C s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ Π r A B : C }} ->
    {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ≈ C }}.
Proof with mautosolve 4.  
  intros * H.
  dependent induction H;
    gen_core_presups; mauto.
  split; [|split];
    [| | transitivity A0; mauto 2];
    eapply IHwf_exp1; mauto 2.
Qed.

#[export]
Hint Resolve wf_pi_inversion : mcpts.

Corollary wf_pi_inversion' {P : PtsSig} : forall {Γ : ctx P} {A B C s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ Π r A B : C }} ->
    {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B : Sort@s2 }}.
Proof with mautosolve 4.
  intros.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ≈ C }}) by (eapply wf_pi_inversion; mauto 2).
  destruct_conjs; mauto 2.
Qed.

Corollary wf_pi_inversion_typ {P} : forall {Γ : ctx P} {A B C s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ Π r A B : C }} ->
    {{ Γ ⊢ Sort@s3 ≈ C }}.
Proof.
  intros.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ≈ C }}) by (eapply wf_pi_inversion; mauto 2).
  destruct_conjs; mauto 2.  
Qed.


#[export]
Hint Resolve wf_pi_inversion' wf_pi_inversion_typ : mcpts.

Corollary wf_typ_pi_inversion {P : PtsSig} : forall {Γ : ctx P} {A B s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ Π r A B }} ->
    {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B : Sort@s2 }}.
Proof.
  intros * H; inversion H; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_pi_inversion : mcpts.

Corollary wf_typ_pi_inversion' {P : PtsSig} : forall {Γ : ctx P} {A B s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ Π r A B }} ->
    {{ Γ ⊢ Π r A B : Sort@s3 }}.
Proof.
  intros * H.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B : Sort@s2 }}) by mauto 2.
  destruct_conjs.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_pi_inversion' : mcpts.

(** It would be better if could get {{ Γ ⊢ Π r A B ≈ C : Sort@s3, but that is only possible after we prove injectivity of type constructors *)
Corollary wf_fn_inversion {P : PtsSig} : forall {Γ : ctx P} {A M C s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ λ r A M : C }} ->
    exists B, {{ Γ, A@s1 ⊢ M : B }} /\ {{ Γ ⊢ Π r A B ≈ C }}.
Proof with solve [mauto].
  intros * H.
  dependent induction H;
    gen_core_presups.
  - eexists; split; mauto.
  - specialize (IHwf_exp1 A M A0 s1 s2 s3 r ltac:(reflexivity) ltac:(reflexivity)) as [B []].
    destruct_conjs.
    eexists; split; mauto 2.
Qed.

#[export]
Hint Resolve wf_fn_inversion : mcpts.

Lemma wf_app_inversion {P : PtsSig} : forall {Γ : ctx P} {M N C},
    {{ Γ ⊢ M N : C }} ->
    exists A B s1 s2 s3 (r : Ru P s1 s2 s3), {{ Γ ⊢ M : Π r A B }} /\ {{ Γ ⊢ N : A }} /\ {{ Γ ⊢ B[Id,,N] ≈ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - do 6 eexists; repeat split; eauto.
    eapply wf_typ_eq_refl.
    assert {{ Γ ⊢ Π r A B : Sort@s3 }} by mauto.
    assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B : Sort@s2 }}) by mauto.
    destruct_conjs.
    econstructor; mauto 3.
  - assert (exists A0 B s1 s2 s3 r, {{ Γ ⊢ M : Π r A0 B }} /\ {{ Γ ⊢ N : A0 }} /\ {{ Γ ⊢ B[Id,,N] ≈ A }}) by (eapply IHwf_exp1; mauto).
    destruct_conjs.
    do 6 eexists; repeat split; mauto.  
Qed.

#[export]
Hint Resolve wf_app_inversion : mcpts.


(** Again, it would be nicer to obtain {{ Γ ⊢ A' ≈ A }}, but this will require injectivity of type constructors *)
Lemma wf_vlookup_inversion {P : PtsSig} : forall {Γ : ctx P} {x A},
    {{ Γ ⊢ #x : A }} ->
    exists A' s, {{ #x : A'@s ∈ Γ }} /\ {{ Γ ⊢ A' ≈ A }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - do 2 eexists; split; mauto.
  - specialize (IHwf_exp1 x A0 ltac:(reflexivity) ltac:(reflexivity)) as [A' [s' []]].
    do 2 eexists; split; mauto.
Qed.

#[export]
  Hint Resolve wf_vlookup_inversion : mcpts.

Lemma wf_nat_inversion {P} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ ℕ : A }} ->
    exists s (r : Ru_nat P s),
      {{ Γ ⊢ Sort@s ≈ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H.
  - eexists. mauto.
  - specialize (IHwf_exp1 A0 ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    do 2 eexists. apply H3.
    etransitivity; mauto.
Qed.

#[export]
  Hint Resolve wf_nat_inversion : mcpts.

Corollary wf_zero_inversion {P} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ zero : A }} ->
    exists s (r : Ru_nat P s),
      {{ Γ ⊢ ℕ ≈ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H.
  - eexists. mauto.
  - specialize (IHwf_exp1 A0 ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    do 2 eexists. apply H3.
    etransitivity; mauto.
Qed.

#[export]
Hint Resolve wf_zero_inversion : mcpts.

Corollary wf_succ_inversion {P} : forall {Γ : ctx P} {A M},
    {{ Γ ⊢ succ M : A }} ->
    {{ Γ ⊢ M : ℕ }} /\ {{ Γ ⊢ ℕ ≈ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H.
  - eexists; mautosolve.
  - specialize (IHwf_exp1 A0 M ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    eexists. apply H3.
    etransitivity; mauto.
Qed.

#[export]
Hint Resolve wf_succ_inversion : mcpts.

Lemma wf_natrec_inversion {P} : forall {Γ : ctx P} {s s' A M A' MZ MS},
    {{ Γ ⊢ rec M return A' | zero -> MZ | succ -> MS end : A }} ->
    {{ Γ ⊢ MZ : A'[Id,,zero] }} /\ {{ Γ, ℕ@s, A'@s' ⊢ MS : A'[Wk∘Wk,,succ(#1)] }} /\ {{ Γ ⊢ M : ℕ }} /\ {{ Γ ⊢ A'[Id,,M] ≈ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H.
  - (* do 3 (eexists; mauto). *)
    (* eapply wf_typ_eq_refl. *)
    (* assert {{ Γ, ℕ ⊢ A' }}; mauto 2. *)
    (* assert {{ Γ ⊢s Id,,M : Γ, ℕ }} by mauto 4. *)
  (* mauto 2. *)
    admit.
  - specialize (IHwf_exp1 s s' A0 M A' MZ MS ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    repeat split; mauto.
Admitted.
    
#[export]
Hint Resolve wf_natrec_inversion : mcpts.


  
(** Here, we get a disjunction because we cannot know in advance if A' is a sort or not *)
Lemma wf_exp_sub_inversion {P : PtsSig} : forall {Γ : ctx P} {M σ A},
    {{ Γ ⊢ M[σ] : A }} ->
    exists Δ A' s, {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ M : A' }} /\
              (({{ Γ ⊢ A'[σ] ≈ A }} /\ {{ Δ ⊢ A' : Sort@s }}) \/ ({{ Γ ⊢ A' ≈ A }} /\ {{ Δ ⊢ A' ≈ Sort@s }})).
Proof with mautosolve 3.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - assert {{ Γ ⊢ A0[σ] ≈ A0[σ] : Sort@s }} by mauto 3.
    do 3 eexists; repeat split; mauto 4.
    
  - do 3 eexists; repeat split; mauto 4.
    right; split; mauto 3.
  - specialize (IHwf_exp1 M σ A0 ltac:(reflexivity) ltac:(reflexivity)) as [Δ [A' [s']]].
    destruct_conjs.
    do 3 eexists; repeat split; mauto.
    destruct H5; destruct_conjs.
    + left; split; mauto 3.      
    + right; split; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_sub_inversion : mcpts.  
  
(** We omit [wf_conv] as they do not give useful inversions *)

Lemma wf_sub_id_inversion {P : PtsSig} : forall (Γ : ctx P) Δ,
    {{ Γ ⊢s Id : Δ }} ->
    {{ ⊢ Γ ≈ Δ }}.
Proof.
  intros * H.
  dependent induction H; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_sub_id_inversion : mcpts.

Lemma wf_sub_weaken_inversion {P : PtsSig} : forall {Γ : ctx P} {Δ},
    {{ Γ ⊢s Wk : Δ }} ->
    exists Γ' A s, {{ ⊢ Γ ≈ Γ', A@s }} /\ {{ ⊢ Γ' ≈ Δ }}.
Proof.
  intros * H.
  
  dependent induction H;
    firstorder;
    progressive_inversion.  
  - repeat eexists; mauto 2.
  - assert (exists Γ' A s, {{ ⊢ Γ ≈ Γ', A@s }} /\ {{ ⊢ Γ' ≈ Δ0 }}) by (eapply IHwf_sub; mauto).
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
    exists Δ' A' s, {{ ⊢ Δ', A'@s ≈ Δ }} /\ {{ Γ ⊢s σ : Δ' }} /\ {{ Γ ⊢ M : A'[σ] }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - repeat eexists...
  - assert (exists Δ' A' s', {{ ⊢ Δ', A'@s' ≈ Δ0 }} /\ {{ Γ ⊢s σ : Δ' }} /\ {{ Γ ⊢ M : A'[σ] }}) by (eapply IHwf_sub; mauto).
    destruct_conjs.
    repeat eexists...
Qed.

#[export]
Hint Resolve wf_sub_extend_inversion : mcpts.
    
