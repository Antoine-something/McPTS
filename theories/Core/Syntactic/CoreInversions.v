From Coq Require Import Setoid.
From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Export CtxEq.
Import Syntax_Notations.

(** * Inversion principles for [wf_exp] *)

(** ** For sorts *)
Lemma wf_exp_sort_inversion {P} : forall {Γ s1 K},
    {{ Γ ⊢ Sort@s1 : K }} ->
    exists s2,
      Ax_typ P s1 s2 /\
        {{ Γ ⊢ Sort@s2 ⊆ K }}.
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
Lemma wf_exp_pi_inversion {P : PtsSig} : forall {Γ A B C s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ Π r A B : C }} ->
    {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ⊆ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups; mauto 3.
  - assert {{ Γ ⊢ Sort@s3 }} by mauto 3.
    repeat split; mauto 3.
  - split; [|split];
      [| | transitivity A0; mauto 2];
      eapply IHwf_exp; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_pi_inversion : mcpts.

Corollary wf_exp_pi_inversion' {P : PtsSig} : forall {Γ A B C s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ Π r A B : C }} ->
    {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }}.
Proof with mautosolve 4.
  intros * ?%wf_exp_pi_inversion.
  destruct_conjs; mauto 2.
Qed.

Corollary wf_exp_pi_inversion_typ {P} : forall {Γ A B C s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ Π r A B : C }} ->
    {{ Γ ⊢ Sort@s3 ⊆ C }}.
Proof.
  intros * ?%wf_exp_pi_inversion.
  destruct_conjs; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_pi_inversion' wf_exp_pi_inversion_typ : mcpts.


Corollary wf_exp_fn_inversion {P : PtsSig} : forall {Γ A B M C s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ λ r A B M : C }} ->
    {{ Γ, A ⊢ M : B }} /\ {{ Γ ⊢ Π r A B ⊆ C }}.
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

Lemma wf_exp_app_inversion {P : PtsSig} : forall {Γ M N C},
    {{ Γ ⊢ M N : C }} ->
    exists A B s1 s2 s3 (r : Ru_pi P s1 s2 s3),
      {{ Γ ⊢ M : Π r A B }} /\ {{ Γ ⊢ N : A }} /\ {{ Γ ⊢ B[Id,,N] ⊆ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - do 6 eexists; repeat split; eauto.
    assert {{ Γ ⊢ B[Id,,N] : Sort@s2 }} by mauto 3.
    eapply wf_typ_subtyp_refl; mauto 3.
  - specialize (IHwf_exp Γ M N A ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)).
    destruct_conjs.
    do 6 eexists; repeat split; mauto.
Qed.

#[export]
Hint Resolve wf_exp_app_inversion : mcpts.


(** ** For variables *) 
Lemma wf_exp_vlookup_inversion {P : PtsSig} : forall {Γ : ctx P} {A x},
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
Hint Resolve wf_exp_vlookup_inversion : mcpts.


(** ** For natural numbers *)
Lemma wf_exp_nat_inversion {P} : forall {Γ A},
    {{ Γ ⊢ ℕ : A }} ->
    exists s (r : Ru_nat P s),
      {{ Γ ⊢ Sort@s ⊆ A }}.
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

Corollary wf_exp_zero_inversion {P} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ zero : A }} ->
    exists s (r : Ru_nat P s),
      {{ Γ ⊢ ℕ ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H.
  - eexists. mauto.
  - specialize (IHwf_exp A0 ltac:(reflexivity) ltac:(reflexivity)) as [s [r]].
    destruct_conjs.
    do 2 eexists; mauto 2. 
Qed.

#[export]
Hint Resolve wf_exp_zero_inversion : mcpts.

Corollary wf_exp_succ_inversion {P} : forall {Γ : ctx P} {A M},
    {{ Γ ⊢ succ M : A }} ->
    {{ Γ ⊢ M : ℕ }} /\ {{ Γ ⊢ ℕ ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H.
  - eexists; mautosolve.
  - specialize (IHwf_exp A0 M ltac:(reflexivity) ltac:(reflexivity)) as [].
    eexists; mauto 2. 
Qed.

#[export]
Hint Resolve wf_exp_succ_inversion : mcpts.

Lemma wf_exp_natrec_inversion {P} : forall {Γ : ctx P} {A M A' MZ MS},
    {{ Γ ⊢ rec M return A' | zero -> MZ | succ -> MS end : A }} ->
    {{ Γ ⊢ MZ : A'[Id,,zero] }} /\ {{ Γ, ℕ, A' ⊢ MS : A'[Wk∘Wk,,succ(#1)] }} /\ {{ Γ ⊢ M : ℕ }} /\ {{ Γ ⊢ A'[Id,,M] ⊆ A }}.
Proof with mautosolve.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - do 3 (eexists; mauto 2).
    assert {{ Γ ⊢s Id,,M : Γ, ℕ }} by mauto 3.
    assert {{ Γ ⊢ A'[Id,,M] }} by mauto 3.
    eapply wf_typ_subtyp_refl; mauto 3.
  - specialize (IHwf_exp A0 M A' MZ MS ltac:(reflexivity) ltac:(reflexivity)) as [? [? []]].
    repeat split; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_natrec_inversion : mcpts.


(** ** For closures *)
Lemma wf_exp_sub_inversion {P} : forall {Γ : ctx P} {M σ A},
    {{ Γ ⊢ M[σ] : A }} ->
    exists Γ' A', {{ Γ ⊢s σ : Γ' }} /\ {{ Γ' ⊢ M : A' }} /\ {{ Γ ⊢ A'[σ] ⊆ A }}.
Proof with mautosolve 3.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - do 2 eexists; repeat split; mauto 2.
    assert {{ Γ ⊢ A0[σ] }} by mauto 3.
    eapply wf_typ_subtyp_refl; mauto 2.
  - specialize (IHwf_exp M σ A0 ltac:(reflexivity) ltac:(reflexivity)) as [Γ' [A' [? []]]].
    repeat eexists; mauto 2.
Qed.    
    
#[export]
Hint Resolve wf_exp_sub_inversion : mcpts.

(** * Inversion principles for [wf_typ] *)

Lemma wf_typ_inversion {P} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    (exists s, {{ Γ ⊢ A ≈ Sort@s }} \/ {{ Γ ⊢ A : Sort@s }}).
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
Corollary wf_typ_pi_inversion {P : PtsSig} : forall {Γ A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ Π r A B }} ->
    {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }}.
Proof.
  inversion 1; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_pi_inversion : mcpts.

Corollary wf_typ_pi_inversion' {P : PtsSig} : forall {Γ A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ Π r A B }} ->
    {{ Γ ⊢ Π r A B : Sort@s3 }}.
Proof.
  intros * ?%wf_typ_pi_inversion.
  destruct_conjs; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_pi_inversion' : mcpts.


(** * Inversion principles for [wf_sub] *)

Lemma wf_sub_id_inversion {P : PtsSig} : forall {Γ : ctx P} {Γ'},
    {{ Γ ⊢s Id : Γ' }} ->
    {{ ⊢ Γ ⊆ Γ' }}.
Proof.
  intros * H.
  dependent induction H; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_sub_id_inversion : mcpts.

Lemma wf_sub_weaken_inversion {P : PtsSig} : forall {Γ : ctx P} {Γ'},
    {{ Γ ⊢s Wk : Γ' }} ->
    exists Γ'' A, {{ ⊢ Γ ≈ Γ'', A }} /\ {{ ⊢ Γ'' ⊆ Γ' }}.
Proof.
  intros * H.
  dependent induction H;
    firstorder;
    progressive_inversion.
  - repeat eexists; mauto 2.
  - specialize (IHwf_sub Γ'0 ltac:(reflexivity) ltac:(reflexivity)) as [Γ'' [A []]].
    repeat eexists; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_weaken_inversion : mcpts.

Lemma wf_sub_compose_inversion {P : PtsSig} : forall {Γ1 : ctx P} {Γ3 σ1 σ2},
    {{ Γ1 ⊢s σ1 ∘ σ2 : Γ3 }} ->
    exists Γ2, {{ Γ1 ⊢s σ2 : Γ2 }} /\ {{ Γ2 ⊢s σ1 : Γ3 }}.
Proof with mautosolve 3.
  intros * H.
  dependent induction H; mauto 3.
  specialize (IHwf_sub Γ' σ1 σ2 ltac:(reflexivity) ltac:(reflexivity)) as [Γ2 []].
  repeat eexists; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_compose_inversion : mcpts.

Lemma wf_sub_extend_inversion {P : PtsSig} : forall {Γ : ctx P} {Γ' σ M},
    {{ Γ ⊢s σ,,M : Γ' }} ->
    exists Γ'' A', {{ ⊢ Γ'', A' ⊆ Γ' }} /\ {{ Γ ⊢s σ : Γ'' }} /\ {{ Γ ⊢ M : A'[σ] }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - repeat eexists; mauto 3.
  - specialize (IHwf_sub Γ'0 σ M ltac:(reflexivity) ltac:(reflexivity)) as [Γ'' [A' [? []]]].
    repeat eexists; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_extend_inversion : mcpts.
