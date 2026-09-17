From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic.System Require Import Definitions Lemmas.Instances Lemmas.CorePresup Lemmas.SortLemmas Lemmas.SubstitutionLemmas.
Import Syntax_Notations.

(** * Lemmas for judgments related to types *)
(** ** Optimized congruence rules for type equality *)
Lemma wf_typ_eq_sub_cong1 {P : PtsSig} : forall {Γ : ctx P} {Γ' A A' σ},
    {{ Γ' ⊢ A ≈ A' }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ A[σ] ≈ A'[σ] }}.
Proof. mauto. Qed.

Lemma wf_typ_eq_sub_cong2  {P} : forall {Γ : ctx P} {Γ' A σ τ},
    {{ Γ' ⊢ A }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢s σ ≈ τ : Γ' }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_eq_sub_cong1 wf_typ_eq_sub_cong2 : mcpts.
  
Lemma wf_typ_eq_sub_compose_typ  {P : PtsSig} : forall {Γ : ctx P} {Γ' Γ'' A σ τ},
    {{ Γ'' ⊢ A }} ->
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_eq_sub_compose_typ : mcpts.

Lemma wf_typ_eq_sub_compose_cong {P : PtsSig} : forall {Γ : ctx P} {Γ'1 Γ'2 Γ'' σ τ σ' τ' A},
    {{ Γ'' ⊢ A }} ->
    {{ Γ'1 ⊢s σ : Γ'' }} ->
    {{ Γ'2 ⊢s σ' : Γ'' }} ->
    {{ Γ ⊢s τ : Γ'1 }} ->
    {{ Γ ⊢s τ' : Γ'2 }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Γ'' }} ->
    {{ Γ ⊢ A[σ][τ] ≈ A[σ'][τ'] }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] }} by mauto 3.
  assert {{ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] }} by mauto 3.
  enough {{ Γ ⊢ A[σ'∘τ'] ≈ A[σ'][τ'] }}...
Qed.

#[export]
Hint Resolve wf_typ_eq_sub_compose_cong : mcpts.


(** ** Substitution propagation in types *)
Lemma wf_typ_eq_sub_compose_weaken_extend {P : PtsSig} : forall {Γ : ctx P} {Γ' σ A B M},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A }} ->
    {{ Γ' ⊢ B }} ->
    {{ Γ ⊢ M : B[σ] }} ->
    {{ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] }}.
Proof with mautosolve 3.
  intros.  
  assert {{ Γ', B ⊢s Wk : Γ' }} by mauto 4.
  transitivity {{{ A[Wk∘(σ,,M)] }}}; [mautosolve 4 |].
  eapply wf_typ_eq_sub_cong2...
Qed.

#[export]
Hint Resolve wf_typ_eq_sub_compose_weaken_extend : mcpts.

Lemma wf_typ_eq_sub_compose_weaken_id_extend {P : PtsSig} : forall {Γ : ctx P} {A B M},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ ⊢ A[Wk][Id,,M] ≈ A }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ B ≈ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ M : B[Id] }} by mauto 2.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve wf_typ_eq_sub_compose_weaken_id_extend : mcpts.

Lemma wf_typ_eq_sub_compose_double_weaken_double_extend {P : PtsSig} : forall {Γ : ctx P} {Γ' σ A B M C N},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A }} ->
    {{ Γ' ⊢ B }} ->
    {{ Γ ⊢ M : B[σ] }} ->
    {{ Γ', B ⊢ C }} ->
    {{ Γ ⊢ N : C[σ,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk][σ,,M,,N] ≈ A[σ] }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ', B ⊢s Wk : Γ' }} by mauto 3.
  assert {{ Γ', B, C ⊢s Wk : Γ', B }} by mauto 4.
  assert {{ Γ', B ⊢ A[Wk] }} by mauto 3.
  transitivity {{{ A[Wk][Wk][σ,,M,,N] }}}; [eapply wf_typ_eq_sub_cong1; mautosolve 3 |].
  transitivity {{{ A[Wk][σ,,M] }}}...
Qed.

#[export]
Hint Resolve wf_typ_eq_sub_compose_double_weaken_double_extend : mcpts.

Lemma wf_typ_eq_sub_compose_double_weaken_id_double_extend {P : PtsSig} : forall {Γ : ctx P} {A B M C N},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ, B ⊢ C }} ->
    {{ Γ ⊢ N : C[Id,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk][Id,,M,,N] ≈ A }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ B ≈ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ M : B[Id] }} by mauto 3.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve wf_typ_eq_sub_compose_double_weaken_id_double_extend : mcpts.


(** ** Lemmas about subtyping *)
Fact wf_typ_subtyp_refl_sorted {P} : forall {Γ : ctx P} {A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ A ⊆ A }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_subtyp_refl_sorted : mcpts.

Lemma wf_typ_subtyp_sub {P} : forall {Γ' : ctx P} {A A'},
    {{ Γ' ⊢ A ⊆ A' }} ->
    forall Γ σ,
      {{ Γ ⊢s σ : Γ' }} ->
      {{ Γ ⊢ A[σ] ⊆ A'[σ] }}.
Proof.
  induction 1; intros; mauto 4.
  - assert {{ ⊢ Γ0 }} by mauto 2.
    assert {{ Γ ⊢ Sort@s1 ⊆ Sort@s2 }} by mauto.
    assert {{ Γ ⊢ Sort@s1 }} by mauto.
    assert {{ Γ0 ⊢ Sort@s1[σ] ≈ Sort@s1 }} by mauto.
    assert {{ Γ0 ⊢ Sort@s2 ≈ Sort@s2[σ] }} by (symmetry; mauto).
    transitivity {{{ Sort@s1 }}}; mauto 3.
    transitivity {{{ Sort@s2 }}}; mauto 3.
  - assert {{ Γ0 ⊢ A[σ] : Sort@s1 }} by mauto 3.
    assert {{ Γ0, A[σ] ⊢ B[q σ] : Sort@s2 }} by mauto 4.
    assert {{ Γ0 ⊢ Π r A[σ] B[q σ] }} by mauto 3.
    transitivity {{{ Π r (A[σ]) (B[q σ]) }}}; [econstructor; mauto 3|].
    transitivity {{{ Π r (A'[σ]) (B'[q σ]) }}}; [ | econstructor; mauto 4].
    eapply wf_typ_subtyp_pi; mauto 4.
Qed.

#[export]
Hint Resolve wf_typ_subtyp_sub : mcpts.

Lemma wf_subtyp_sort_weaken {P} : forall {Γ : ctx P} {s1 s2 A},
    {{ Γ ⊢ Sort@s1 ⊆ Sort@s2 }} ->
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢ Sort@s1 ⊆ Sort@s2 }}.
Proof.    
  intros.
  assert {{ Γ ⊢ Sort@s2  }} by mauto 2.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  transitivity {{{ Sort@s1[Wk] }}}; mauto 3.
  transitivity {{{ Sort@s2[Wk] }}}; mauto 3.
Qed.

#[export]
Hint Resolve wf_subtyp_sort_weaken : mcpts.

(** ** Properties of context lookups with related contexts *)
Lemma wf_ctx_eq_ctx_lookup {P : PtsSig} : forall {Γ : ctx P} {Γ' A x},
    {{ ⊢ Γ ≈ Γ' }} ->
    {{ #x : A ∈ Γ }} ->
    exists B,
      {{ #x : B ∈ Γ' }} /\
        {{ Γ ⊢ A ≈ B }} /\
        {{ Γ' ⊢ A ≈ B }} /\
        {{ Γ' ⊢ A }}.
Proof with (repeat eexists; mautosolve 3).
  intros * HΓΓ' Hx.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ A }} by mauto 3.
  gen Γ' Hx.
  induction 1 as [|* ? IHHx]; inversion_clear 1 as [|? ? ? ? HΓΓ'0];
    assert {{ ⊢ Γ'0 }} by mauto 2.
  - assert {{ ⊢ Γ, A }} by mauto 3.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
    assert {{ Γ'0, A' ⊢s Wk : Γ'0 }} by mauto 3.
    eexists.
    do 3 (split; mauto 3).
  - specialize (IHHx ltac:(mauto 2) ltac:(mauto 3) _ HΓΓ'0).
    destruct_conjs.
    assert {{ Γ, B ⊢s Wk : Γ }} by mauto 2.
    assert {{ Γ'0, A' ⊢s Wk : Γ'0 }} by mauto 3.
    eexists.
    do 3 (split; mauto 3).
Qed.

#[export]
Hint Resolve wf_ctx_eq_ctx_lookup : mcpts.

Lemma wf_ctx_subtyp_ctx_lookup {P} : forall {Γ : ctx P} {Γ'},
    {{ ⊢ Γ' ⊆ Γ }} ->
    forall {A x},
      {{ #x : A ∈ Γ }} ->
      exists B,
        {{ #x : B ∈ Γ' }} /\
          {{ Γ' ⊢ B ⊆ A }}.
Proof with (do 2 eexists; repeat split; mautosolve).
  induction 1; intros * Hx; progressive_inversion.
  dependent destruction Hx.
  - eexists; split; mauto 3.
    eapply wf_typ_subtyp_sub; mauto 4.
  - edestruct IHwf_ctx_subtyp as [? []]; try eassumption...
Qed.

#[export]
Hint Resolve wf_ctx_subtyp_ctx_lookup : mcpts.
