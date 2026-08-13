From Coq Require Import Setoid.
From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export CtxEq.
Import Syntax_Notations.

(** * Inversion principles for [wf_exp] *)

(** ** For sorts *)
Lemma wf_exp_sort_inversion {P} : forall {Δ : gctx P} {Γ s1 K},
    {{ Δ ▶ Γ ⊢ Sort@s1 : K }} ->
    exists s2,
      Ax_typ P s1 s2 /\
        {{ Δ ▶ Γ ⊢ Sort@s2 ⊆ K }}.
Proof.
  intros * H.
  dependent induction H.
  - eexists; split; mauto 2.
  - specialize (IHwf_exp _ s1 A ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [s2 []].
    repeat eexists; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_sort_inversion : mcpts.


(** ** For function *)
Lemma wf_exp_pi_inversion {P : PtsSig} : forall {Δ : gctx P} {Γ A B C s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ▶ Γ ⊢ Π r A B : C }} ->
    {{ Δ ▶ Γ ⊢ A : Sort@s1 }} /\ {{ Δ ▶ Γ, A ⊢ B : Sort@s2 }} /\ {{ Δ ▶ Γ ⊢ Sort@s3 ⊆ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups; mauto 3.
  - assert {{ Δ ▶ Γ }} by mauto 2.
    assert {{ Δ ▶ Γ ⊢ Sort@s3 }} by mauto 3.
    repeat split; mauto 3.
  - split; [|split];
      [| | transitivity A0; mauto 2];
      eapply IHwf_exp; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_pi_inversion : mcpts.

Corollary wf_exp_pi_inversion' {P : PtsSig} : forall {Δ : gctx P} {Γ A B C s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ▶ Γ ⊢ Π r A B : C }} ->
    {{ Δ ▶ Γ ⊢ A : Sort@s1 }} /\ {{ Δ ▶ Γ, A ⊢ B : Sort@s2 }}.
Proof with mautosolve 4.
  intros * ?%wf_exp_pi_inversion.
  destruct_conjs; mauto 2.
Qed.

Corollary wf_exp_pi_inversion_typ {P} : forall {Δ : gctx P} {Γ A B C s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ▶ Γ ⊢ Π r A B : C }} ->
    {{ Δ ▶ Γ ⊢ Sort@s3 ⊆ C }}.
Proof.
  intros * ?%wf_exp_pi_inversion.
  destruct_conjs; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_pi_inversion' wf_exp_pi_inversion_typ : mcpts.


Corollary wf_exp_fn_inversion {P : PtsSig} : forall {Δ : gctx P} {Γ A B M C s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ▶ Γ ⊢ λ r A B M : C }} ->
    {{ Δ ▶ Γ, A ⊢ M : B }} /\ {{ Δ ▶ Γ ⊢ Π r A B ⊆ C }}.
Proof with solve [mauto].
  intros * H.
  dependent induction H;
    gen_core_presups.
  - split; mauto.
  - specialize (IHwf_exp Γ A B M A0 s1 s2 s3 r ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    split; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_fn_inversion : mcpts.

Lemma wf_exp_app_inversion {P : PtsSig} : forall {Δ : gctx P} {Γ M N C},
    {{ Δ ▶ Γ ⊢ M N : C }} ->
    exists A B s1 s2 s3 (r : Ru_pi P s1 s2 s3),
      {{ Δ ▶ Γ ⊢ M : Π r A B }} /\ {{ Δ ▶ Γ ⊢ N : A }} /\ {{ Δ ▶ Γ ⊢ B[Id,,N] ⊆ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - do 6 eexists; repeat split; eauto.
    assert {{ Δ ▶ Γ ⊢ B[Id,,N] : Sort@s2 }} by mauto 3.
    eapply wf_typ_subtyp_refl; mauto 3.
  - specialize (IHwf_exp Γ M N A ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    do 6 eexists; repeat split; mauto.
Qed.

#[export]
Hint Resolve wf_exp_app_inversion : mcpts.


(** ** For variables *)
Lemma wf_exp_gvlookup_inversion {P : PtsSig} : forall {Δ : gctx P} {Γ A x},
    {{ Δ ▶ Γ ⊢ `#x : A }} ->
    exists A' σ, {{ `#x : A' ∈ Δ }} /\ {{ Δ ▶ Γ ⊢s σ : ⋅ }} /\ {{ Δ ▶ Γ ⊢ A'[σ] ⊆ A }}.
Proof.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - repeat eexists; mauto 4.
  - specialize (IHwf_exp Γ A0 x ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [A' [σ [? []]]].
    repeat eexists; mauto 4.
Qed.

#[export]
Hint Resolve wf_exp_gvlookup_inversion : mcpts.
 
Lemma wf_exp_vlookup_inversion {P : PtsSig} : forall {Δ : gctx P} {Γ A x},
    {{ Δ ▶ Γ ⊢ #x : A }} ->
    exists A', {{ #x : A' ∈ Γ }} /\ {{ Δ ▶ Γ ⊢ A' ⊆ A }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - do 2 eexists; mauto 3.
  - specialize (IHwf_exp Γ A0 x ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [A' []].
    do 2 eexists; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_vlookup_inversion : mcpts.


(** ** For natural numbers *)
Lemma wf_exp_nat_inversion {P} : forall {Δ : gctx P} {Γ A},
    {{ Δ ▶ Γ ⊢ ℕ : A }} ->
    exists s (r : Ru_nat P s),
      {{ Δ ▶ Γ ⊢ Sort@s ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H.
  - do 2 eexists; mauto 3.
  - specialize (IHwf_exp Γ A0 ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    eexists; mauto 3. 
Qed.

#[export]
Hint Resolve wf_exp_nat_inversion : mcpts.

Corollary wf_exp_zero_inversion {P} : forall {Δ : gctx P} {Γ A},
    {{ Δ ▶ Γ ⊢ zero : A }} ->
    exists s (r : Ru_nat P s),
      {{ Δ ▶ Γ ⊢ ℕ ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H.
  - eexists. mauto.
  - specialize (IHwf_exp Γ A0 ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [s [r]].
    destruct_conjs.
    do 2 eexists; mauto 2. 
Qed.

#[export]
Hint Resolve wf_exp_zero_inversion : mcpts.

Corollary wf_exp_succ_inversion {P} : forall {Δ : gctx P} {Γ A M},
    {{ Δ ▶ Γ ⊢ succ M : A }} ->
    {{ Δ ▶ Γ ⊢ M : ℕ }} /\ {{ Δ ▶ Γ ⊢ ℕ ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H.
  - eexists; mautosolve.
  - specialize (IHwf_exp Γ A0 M ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [].
    eexists; mauto 2. 
Qed.

#[export]
Hint Resolve wf_exp_succ_inversion : mcpts.

Lemma wf_exp_natrec_inversion {P} : forall {Δ : gctx P} {Γ A M A' MZ MS},
    {{ Δ ▶ Γ ⊢ rec M return A' | zero -> MZ | succ -> MS end : A }} ->
    {{ Δ ▶ Γ ⊢ MZ : A'[Id,,zero] }} /\ {{ Δ ▶ Γ, ℕ, A' ⊢ MS : A'[Wk∘Wk,,succ(#1)] }} /\ {{ Δ ▶ Γ ⊢ M : ℕ }} /\ {{ Δ ▶ Γ ⊢ A'[Id,,M] ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H.
  - do 3 (eexists; mauto 2).
    assert {{ Δ ▶ Γ }} by mauto 3.
    assert {{ Δ ▶ Γ ⊢s Id,,M : Γ, ℕ }} by mauto 3.
    assert {{ Δ ▶ Γ ⊢ A'[Id,,M] }} by mauto 3.
    eapply wf_typ_subtyp_refl; mauto 3.
  - specialize (IHwf_exp Γ A0 M A' MZ MS ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [? [? []]].
    repeat split; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_natrec_inversion : mcpts.


(** ** For closures *)
Lemma wf_exp_sub_inversion {P} : forall {Δ : gctx P} {Γ M σ A},
    {{ Δ ▶ Γ ⊢ M[σ] : A }} ->
    exists Γ' A', {{ Δ ▶ Γ ⊢s σ : Γ' }} /\ {{ Δ ▶ Γ' ⊢ M : A' }} /\ {{ Δ ▶ Γ ⊢ A'[σ] ⊆ A }}.
Proof with mautosolve 3.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - do 2 eexists; repeat split; mauto 2.
    assert {{ Δ ▶ Γ ⊢ A0[σ] }} by mauto 3.
    eapply wf_typ_subtyp_refl; mauto 2.
  - specialize (IHwf_exp Γ M σ A0 ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [Γ' [A' [? []]]].
    repeat eexists; mauto 2.
Qed.    
    
#[export]
Hint Resolve wf_exp_sub_inversion : mcpts.

(** * Inversion principles for [wf_typ] *)

Lemma wf_typ_inversion {P} : forall {Δ : gctx P} {Γ A},
    {{ Δ ▶ Γ ⊢ A }} ->
    (exists s, {{ Δ ▶ Γ ⊢ A ≈ Sort@s }} \/ {{ Δ ▶ Γ ⊢ A : Sort@s }}).
Proof.
  induction 1; mauto 4.
  destruct IHwf_typ as [s []].
  - eexists; left.
    transitivity {{{ Sort@s[σ] }}}; mauto 3.
  - eexists; right; mauto 3.
Qed.

#[export]
Hint Resolve wf_typ_inversion : mcpts.

(** ** For functions *)
Corollary wf_typ_pi_inversion {P : PtsSig} : forall {Δ : gctx P} {Γ A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ▶ Γ ⊢ Π r A B }} ->
    {{ Δ ▶ Γ ⊢ A : Sort@s1 }} /\ {{ Δ ▶ Γ, A ⊢ B : Sort@s2 }}.
Proof.
  inversion 1; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_pi_inversion : mcpts.

Corollary wf_typ_pi_inversion' {P : PtsSig} : forall {Δ : gctx P} {Γ A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ▶ Γ ⊢ Π r A B }} ->
    {{ Δ ▶ Γ ⊢ Π r A B : Sort@s3 }}.
Proof.
  intros * ?%wf_typ_pi_inversion.
  destruct_conjs; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_pi_inversion' : mcpts.


(** * Inversion principles for [wf_sub] *)

Lemma wf_sub_id_inversion {P : PtsSig} : forall {Δ : gctx P} {Γ Γ'},
    {{ Δ ▶ Γ ⊢s Id : Γ' }} ->
    {{ Δ ▶ Γ ⊆ Γ' }}.
Proof.
  intros * H.
  dependent induction H; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_sub_id_inversion : mcpts.

Lemma wf_sub_weaken_inversion {P : PtsSig} : forall {Δ : gctx P} {Γ Γ'},
    {{ Δ ▶ Γ ⊢s Wk : Γ' }} ->
    exists Γ'' A, {{ Δ ▶ Γ ≈ Γ'', A }} /\ {{ Δ ▶ Γ'' ⊆ Γ' }}.
Proof.
  intros * H.
  dependent induction H;
    firstorder;
    progressive_inversion.
  - repeat eexists; mauto 2.
  - specialize (IHwf_sub Γ Γ'0 ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [Γ'' [A []]].
    repeat eexists; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_weaken_inversion : mcpts.

Lemma wf_sub_compose_inversion {P : PtsSig} : forall {Δ : gctx P} {Γ1 Γ3 σ1 σ2},
    {{ Δ ▶ Γ1 ⊢s σ1 ∘ σ2 : Γ3 }} ->
    exists Γ2, {{ Δ ▶ Γ1 ⊢s σ2 : Γ2 }} /\ {{ Δ ▶ Γ2 ⊢s σ1 : Γ3 }}.
Proof with mautosolve 3.
  intros * H.
  dependent induction H; mauto 3.
  specialize (IHwf_sub Γ1 Γ' σ1 σ2 ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [Γ2 []].
  repeat eexists; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_compose_inversion : mcpts.

Lemma wf_sub_extend_inversion {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ M},
    {{ Δ ▶ Γ ⊢s σ,,M : Γ' }} ->
    exists Γ'' A', {{ Δ ▶ Γ'', A' ⊆ Γ' }} /\ {{ Δ ▶ Γ ⊢s σ : Γ'' }} /\ {{ Δ ▶ Γ ⊢ M : A'[σ] }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - repeat eexists; mauto 3.
  - specialize (IHwf_sub Γ Γ'0 σ M ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as [Γ'' [A' [? []]]].
    repeat eexists; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_extend_inversion : mcpts.
