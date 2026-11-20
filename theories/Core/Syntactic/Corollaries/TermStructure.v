From Coq Require Import Setoid Nat.
From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Export SystemOpt.
From McPTS.Core.Syntactic.Corollaries Require Import Substitutions.
Import Syntax_Notations.

(** ** Lemmas related to identity substitutions *)
Corollary wf_exp_sub_id_on_typ' {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A[Id] }}.
Proof. 
  intros.
  gen_presups.
  mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_sub_id_on_typ' : mcpts.
#[export]
Remove Hints wf_exp_sub_id_on_typ : mcpts.

Corollary wf_exp_invert_sub_id {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M[Id] : A }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros * [? [? [?%wf_sub_id_inversion []]]]%wf_exp_sub_inversion.
  mauto 4.
Qed.

#[export]
Hint Resolve wf_exp_invert_sub_id : mcpts.

Corollary wf_typ_invert_sub_id {P : PtsSig} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A[Id] }} ->
    {{ Γ ⊢ A }}.
Proof.
  intros * H.
  inversion_clear H; [assert {{ Γ ⊢ A : Sort@s }} by mauto 2 |]; mauto 3.
Qed.

Hint Resolve wf_typ_invert_sub_id : mcpts.


Corollary wf_exp_invert_sub_id_on_typ {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A[Id] }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros.
  dependent destruction H;
    gen_presups.
  - assert {{ Γ ⊢ A }} by mauto 3.
    assert {{ Γ ⊢ A[Id] ≈ A }} by mauto 3.
    mauto 3.
  - pose proof (wf_sub_id_inversion H).
    assert {{ Γ ⊢ A[Id] ≈ A }} by mauto 3.
    mauto 3.
  - assert {{ Γ ⊢ A[Id] ≈ A }} by mauto 3.
    mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_invert_sub_id_on_typ : mcpts.

(** ** Rewrite rules for applying substitutions *)
Add Parametric Morphism {P : PtsSig} (Γ : ctx P) Γ' : a_sub
    with signature wf_typ_subtyp Γ' ==> wf_sub_eq Γ Γ' ==> wf_typ_subtyp Γ as wf_typ_subtyp_cong.
Proof.
  intros.
  gen_presups.
  mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ : ctx P) Γ' : a_sub
    with signature wf_typ_eq Γ' ==> wf_sub_eq Γ Γ' ==> wf_typ_eq Γ as wf_typ_eq_sub_cong.
Proof.
  intros.
  gen_presups.
  mauto 4.
Qed.

Add Parametric Morphism {P : PtsSig} (s : P) Γ Γ' : a_sub
    with signature wf_exp_eq Γ' {{{ Sort@s }}} ==> wf_sub_eq Γ Γ' ==> wf_exp_eq Γ {{{ Sort@s }}} as wf_exp_eq_sorted_sub_cong.
Proof.
  intros.
  gen_presups.
  mauto 4.
Qed.

(** ** Quickly applying substitutions to sorts *)
(* Note: this is the only corollary about sorts, so I put it there instead of making a seperate file for sort corollaries.  If we ever find that we need more sort corollaries, then we should give them their own file to enable parallel compilation *)
Lemma wf_exp_ax_typ_sub_lhs {P : PtsSig} : forall {Γ Γ' σ s1 s2},
    Ax_typ P s1 s2 ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ Sort@s1[σ] : Sort@s2 }}.
Proof.
  intros; gen_presups; mauto 3.
Qed.
#[export]
Hint Resolve wf_exp_ax_typ_sub_lhs : mcpts.


Lemma wf_exp_sub_sub_compose {P} : forall {Γ1 : ctx P} {σ σ' A K1},
    {{ Γ1 ⊢ A[σ][σ'] : K1 }} ->
    {{ Γ1 ⊢ A[σ∘σ'] ≈ A[σ][σ'] : K1 }}.
Proof.
  intros.
  pose proof (wf_exp_sub_inversion H) as [Γ2 [K2 [? []]]].
  pose proof (wf_exp_sub_inversion H1) as [Γ3 [K3 [? []]]].
  assert {{ Γ1 ⊢ K3[σ][σ'] ⊆ K2[σ'] }} by mauto 3.
  assert {{ Γ1 ⊢ K3[σ][σ'] ⊆ K1 }} by mauto 3.
  gen_presups.
  assert {{ Γ1 ⊢ K3[σ∘σ'] ≈ K3[σ][σ'] }} by mauto 3.
  assert {{ Γ1 ⊢ A[σ∘σ'] ≈ A[σ][σ'] : K3[σ][σ'] }} by mauto 4.
  mauto 3.  
Qed.

#[export]
Hint Resolve wf_exp_sub_sub_compose : mcpts.

Lemma wf_exp_sub_compose_decompose {P} : forall {Γ1 : ctx P} {σ σ' A K1},
    {{ Γ1 ⊢ A[σ∘σ'] : K1 }} ->
    {{ Γ1 ⊢ A[σ∘σ'] ≈ A[σ][σ'] : K1 }}.
Proof.
  intros.
  pose proof (wf_exp_sub_inversion H) as [Γ3 [K3 [? []]]].
  pose proof (wf_sub_compose_inversion H0) as [Γ2 []].
  gen_presups.
  assert {{ Γ1 ⊢ A[σ∘σ'] ≈ A[σ][σ'] : K3[σ∘σ'] }} by mauto 3.
  mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_sub_compose_decompose : mcpts.

Lemma wf_typ_sub_sub_compose {P} : forall {Γ1 : ctx P} {σ σ' A},
    {{ Γ1 ⊢ A[σ][σ'] }} ->
    {{ Γ1 ⊢ A[σ∘σ'] ≈ A[σ][σ'] }}.
Proof.
  intros.
  inversion H; subst; mauto 3.
  inversion H4; subst; mauto 3.
  pose proof (wf_exp_sub_inversion H0) as [Γ2 [K [? []]]].
  gen_presups.
  assert {{ Γ1 ⊢ A[σ∘σ'] ≈ A[σ][σ'] : K[σ][σ'] }} by mauto 4.
  assert {{ Γ1 ⊢ K[σ][σ'] ⊆ Sort@s[σ'] }} by mauto 3.
  assert {{ Γ1 ⊢ K[σ][σ'] ⊆ Sort@s }} by mauto 3.
  mauto 3.
Qed.

#[export]
Hint Resolve wf_typ_sub_sub_compose : mcpts.

Lemma wf_typ_compose_decompose {P} : forall {Γ1 : ctx P} {σ σ' A},
    {{ Γ1 ⊢ A[σ∘σ'] }} ->
    {{ Γ1 ⊢ A[σ∘σ'] ≈ A[σ][σ'] }}.
Proof.
  intros.
  inversion H; subst; mauto 3.
  pose proof (wf_sub_compose_inversion H3) as [Γ2 []].
  mauto 3.
Qed.

#[export]
Hint Resolve wf_typ_compose_decompose : mcpts.

Lemma wf_typ_subtyp_sub_cong {P : PtsSig} : forall {Γ' : ctx P} {A B},
    {{ Γ' ⊢ A ⊆ B }} ->
    forall Γ σ σ',
      {{ Γ ⊢s σ ≈ σ' : Γ' }} ->
      {{ Γ ⊢ A[σ] ⊆ B[σ'] }}.
Proof.
  induction 1; intros * Hσσ'; gen_presup Hσσ'; mauto 3.
  - etransitivity; mauto 3.
  - assert {{ Γ0 ⊢ Sort@s2[σ'] ≈ Sort@s2 }} by mauto 2.
    transitivity {{{ Sort@s1 }}}; mauto 3.
    transitivity {{{ Sort@s2 }}}; mauto 3.
  - assert {{ Γ0 ⊢ A'[σ] ≈ A'[σ'] : Sort@s1 }} by mauto 2.
    assert {{ ⊢ Γ0 ≈ Γ0 }} by mauto 3.
    assert {{ ⊢ Γ0, A'[σ] ≈ Γ0, A'[σ'] }} by mauto 3.
    assert {{ Γ0, A[σ] ⊢s q σ : Γ, A }} by mauto 3.
    assert {{ Γ0, A'[σ] ⊢s q σ ≈ q σ' : Γ, A' }} by mauto 3.
    assert {{ Γ0, A'[σ'] ⊢s q σ ≈ q σ' : Γ, A' }} by mauto 3.
    assert {{ Γ0 ⊢ (Π r A B)[σ] ≈ Π r A[σ] B[q σ] }} by mauto 3.
    transitivity {{{ Π r (A[σ]) (B[q σ]) }}}; mauto 2.
    assert {{ Γ0 ⊢ (Π r A' B')[σ'] ≈ Π r A'[σ'] B'[q σ'] }} by mauto 3.
    transitivity {{{ Π r (A'[σ']) (B'[q σ']) }}}; mauto 3.
    assert {{ Γ0 ⊢ A[σ] ≈ A'[σ'] : Sort@s1 }} by mauto 3.
    assert {{ Γ0, A'[σ'] ⊢s q σ' : Γ, A' }} by mauto 3.
    eapply wf_typ_subtyp_pi'; mauto 2.    
Qed.

#[export]
Hint Resolve wf_typ_subtyp_sub_cong : mcpts.

Lemma wf_exp_of_sort_under_q {P} : forall {Γ : ctx P} {Γ' σ A B s},
    {{ Γ ⊢ A }} ->
    {{ Γ, A ⊢ B : Sort@s }} ->
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ', A[σ] ⊢ B[q σ] : Sort@s }}.
Proof.
  intros.
  assert {{ Γ', A[σ] ⊢s q σ : Γ, A }} by mauto 3.
  mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_of_sort_under_q : mcpts.

Lemma sub_decompose_q_typ {P : PtsSig} : forall {Γ : ctx P} {A B σ Γ' Γ'' τ M},
  {{ Γ, A ⊢ B }} ->
  {{ Γ' ⊢s σ : Γ }} ->
  {{ Γ'' ⊢s τ : Γ' }} ->
  {{ Γ'' ⊢ M : A[σ][τ] }} ->
  {{ Γ'' ⊢ B[σ∘τ,,M] ≈ B[q σ][τ,,M]  }}.
Proof.
  intros. gen_presups.
  assert {{ Γ'' ⊢s q σ ∘ (τ ,, M) ≈ σ ∘ τ ,, M : Γ, A }} by mauto 3.
  assert  {{ Γ'' ⊢ B[q σ∘(τ,,M)] ≈ B[σ∘τ,,M] }} by mauto 3.
  transitivity {{{ B[(q σ)∘(τ,,M)] }}}; mauto 3.
  eapply wf_typ_eq_sub_compose; mauto 4.
Qed.

#[export]
Hint Resolve sub_decompose_q_typ : mcpts.

Lemma sub_decompose_q_typ_sorted {P : PtsSig} : forall {Γ : ctx P} {A B σ Γ' Γ'' τ M s},
  {{ Γ, A ⊢ B : Sort@s }} ->
  {{ Γ' ⊢s σ : Γ }} ->
  {{ Γ'' ⊢s τ : Γ' }} ->
  {{ Γ'' ⊢ M : A[σ][τ] }} ->
  {{ Γ'' ⊢ B[σ∘τ,,M] ≈ B[q σ][τ,,M] : Sort@s }}.
Proof.
  intros. gen_presups.
  assert {{ Γ'' ⊢s q σ ∘ (τ ,, M) ≈ σ ∘ τ ,, M : Γ, A }} by mauto 3. 
  assert {{ Γ'' ⊢s τ,,M : Γ', A[σ] }} by mauto 4.
  assert {{ Γ'' ⊢s q σ∘(τ,,M) : Γ, A }} by mauto 4.
  assert  {{ Γ'' ⊢ B[q σ∘(τ,,M)] ≈ B[σ∘τ,,M] : Sort@s }} by mauto 3.
  transitivity {{{ B[(q σ)∘(τ,,M)] }}}; mauto 3.
Qed.

#[export]
Hint Resolve sub_decompose_q_typ_sorted : mcpts.

Lemma wf_exp_eq_elim_sub_lhs_typ_gen {P : PtsSig} : forall {Γ : ctx P} {Γ' σ M A B},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ', A ⊢ B }} ->
    {{ Γ' ⊢ M : A }} ->
    {{ Γ ⊢ B[Id,,M][σ] ≈ B[σ,,M[σ]] }}.
Proof.
  intros.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ' ⊢ A }} by mauto 3.
  assert {{ Γ' ⊢s Id,,M : Γ', A }} by mauto 4.
  assert {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Γ', A }} by mauto 3.
  transitivity {{{ B[(Id,,M)∘σ] }}}; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_elim_sub_lhs_typ_gen : mcpts.

Lemma wf_exp_eq_elim_sub_lhs_typ_gen_sorted {P : PtsSig} : forall {Γ : ctx P} {Γ' σ M A B s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ', A ⊢ B : Sort@s }} ->
    {{ Γ' ⊢ M : A }} ->
    {{ Γ ⊢ B[Id,,M][σ] ≈ B[σ,,M[σ]] : Sort@s }}.
Proof.
  intros.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ' ⊢ A }} by mauto 3.
  assert {{ Γ' ⊢s Id,,M : Γ', A }} by mauto 4.
  assert {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Γ', A }} by mauto 3.
  transitivity {{{ B[(Id,,M)∘σ] }}}; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_elim_sub_lhs_typ_gen_sorted : mcpts.

Lemma wf_exp_eq_elim_sub_rhs_typ {P : PtsSig} : forall {Γ : ctx P} {Γ' σ M A B},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ', A ⊢ B }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ B[q σ][Id,,M] ≈ B[σ,,M] }}.
Proof.
  intros.
  assert {{ Γ' ⊢ A }} by mauto 3.
  transitivity {{{ B[(σ∘Id),,M] }}}.
  - symmetry.
    eapply sub_decompose_q_typ; mauto 3.
  - eapply wf_typ_eq_sub_cong; mauto 2.
    eapply wf_sub_eq_extend_cong; mauto 2.
    eapply wf_exp_eq_conv'; mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_elim_sub_rhs_typ : mcpts.

Lemma wf_exp_eq_elim_sub_rhs_typ_sorted {P : PtsSig} : forall {Γ : ctx P} {Γ' σ M A B s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ', A ⊢ B : Sort@s }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ B[q σ][Id,,M] ≈ B[σ,,M] : Sort@s }}.
Proof.
  intros.
  assert {{ Γ' ⊢ A }} by mauto 3.
  transitivity {{{ B[(σ∘Id),,M] }}}.
  - symmetry.
    eapply sub_decompose_q_typ_sorted; mauto 3.
  - gen_presups.
    assert {{ Γ ⊢s σ∘Id ≈ σ : Γ' }} by mauto 3.
    assert {{ Γ ⊢s σ∘Id,,M : Γ', A }} by (econstructor; mauto 4).
    assert {{ Γ ⊢ B[σ∘Id,,M] ≈ B[σ,,M] : Sort@s[σ∘Id,,M] }} by (eapply wf_exp_eq_sub_cong; mauto).
    eapply wf_exp_eq_conv'; mauto 4.    
Qed.

#[export]
Hint Resolve wf_exp_eq_elim_sub_rhs_typ_sorted : mcpts.

Lemma wf_typ_eq_sub_cong2 {P : PtsSig} : forall {Γ : ctx P} {Γ' A σ τ},
    {{ Γ' ⊢ A }} ->
    {{ Γ ⊢s σ ≈ τ : Γ' }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] }}.
Proof with mautosolve 3.
  mauto 3.
Qed.

#[export]
Hint Resolve wf_typ_eq_sub_cong2 : mcpts.

Lemma wf_exp_eq_sorted_sub_cong2 {P : PtsSig} : forall {Γ : ctx P} {Γ' A σ τ s},
    {{ Γ' ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ ≈ τ : Γ' }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] : Sort@s }}.
Proof. 
  intros; gen_presups; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_sorted_sub_cong2 : mcpts.

(** This works for both var_0 and var_S cases *)
Lemma wf_exp_eq_var_sub_rhs_typ_gen {P : PtsSig} : forall {Γ : ctx P} {Γ' σ A M},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] }}.
Proof.
  intros.
  assert {{ Γ ⊢s σ,,M : Γ', A }} by mauto 3.
  assert {{ Γ', A ⊢s Wk : Γ' }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][σ,,M] ≈ A[Wk∘(σ,,M)] }} by (symmetry; mauto 4).
  assert {{ Γ ⊢s Wk∘(σ,,M) ≈ σ : Γ' }} by mauto 2.
  assert {{ Γ ⊢ A[Wk∘(σ,,M)] ≈ A[σ] }} by mauto 3.
  transitivity {{{ A[Wk∘(σ,,M)] }}}; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_var_sub_rhs_typ_gen : mcpts.
