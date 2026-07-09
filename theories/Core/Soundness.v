From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import CoreInversions SystemAnnotated.
From McPTS.Core Require Import Completeness.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Semantic Require Export NbE.
From McPTS.Core.Soundness Require Export FundamentalTheorem.
Import Domain_Notations.

Theorem soundness {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    exists W, nbe Γ M A W /\ {{ Γ ⊢ M ≈ W : A }}.
Proof.
  intros * H.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ ⟪ pred_P ⟫ ⊨ Γ }} as [env_relΓ] by (apply completeness_fundamental_ctx; eassumption).
  destruct (soundness_fundamental_exp pred_P _ _ _ H) as [anns [so [Sb []]]].
  pose proof (per_ctx_then_per_env_initial_env ltac:(eassumption)) as [p].
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Γ ⊢s Id ® p ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto).
  destruct_glu_rel_exp_with_sub_unsorted.
  - assert {{ Γ ⊢ M[Id] : A[Id] ® m ∈ glu_elem_top_unsorted pred_P so_None d{{{ Sort@s }}} }} by (eapply realize_glu_elem_top_unsorted; mauto).
    simpl in H8.
    dependent destruction H8.
    match_by_head (@per_top P) ltac:(fun H => destruct (H (length Γ)) as [W []]).
    eexists.
    split; [econstructor |]; mauto 3.
    dependent destruction H10.
    dependent destruction H13.
    simpl_glu_rel.
    assert {{ Γ ⊢ M[Id][Id] ≈ W : A[Id][Id] }} as HM by mauto 3.
    assert {{ Γ ⊢ M[Id][Id] ≈ W : A[Id][Id] }} as HM' by mauto 3.
    assert {{ Γ ⊢ M[Id] ≈ M : A[Id] }} by mauto 3.
    assert {{ Γ ⊢ M[Id][Id] ≈ M : A[Id] }} by (transitivity {{{ M[Id] }}}; mauto 3).
    assert {{ Γ ⊢ A[Id] ≈ A }}  as <- by mauto 3.
    assert {{ Γ ⊢ A[Id][Id] ≈ A[Id] }} as <- by mauto 3.
    transitivity {{{ M[Id][Id] }}}; mauto 3.
  - assert {{ Γ ⊢ M[Id] : A[Id] ® m ∈ glu_elem_top pred_P s a }} as [] by (eapply realize_glu_elem_top; mauto).
    match_by_head (@per_top P) ltac:(fun H => destruct (H (length Γ)) as [W []]).
    eexists.
    split; [econstructor |]; try eassumption.
    assert {{ Γ ⊢ A[Id] : Sort@s }} by (eapply glu_sort_elem_sort_lvl; mauto 2).
    assert {{ Γ ⊢ A[Id] ≈ A : Sort@s }} by mauto 3.
    assert {{ Γ ⊢ A[Id][Id] ≈ A : Sort@s }} as HA by (transitivity {{{ A[Id] }}}; mauto 3).
    assert {{ Γ ⊢ M[Id][Id] ≈ W : A[Id][Id] }} as HM by mauto 3.
    assert {{ Γ ⊢ M[Id][Id] ≈ W : A }} as HM' by mauto 3.
    assert {{ Γ ⊢ M[Id] ≈ M : A }} by mauto 3.
    assert {{ Γ ⊢ M[Id][Id] ≈ M : A }} by (transitivity {{{ M[Id] }}}; mauto 3).
    transitivity {{{ M[Id][Id] }}}; mauto 3.
Qed.

Theorem soundness' {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {M A W},
    {{ Γ ⊢ M : A }} ->
    nbe Γ M A W ->
    {{ Γ ⊢ M ≈ W : A }}.
Proof.
  intros * [? []]%(soundness pred_P) ?.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.

Lemma soundness_ty {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    exists W, nbe_ty Γ A W /\ {{ Γ ⊢ A ≈ W }}.
Proof.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
              
  eapply wf_typ_inversion in H as [s []].
  - assert {{ ⟪ pred_P ⟫ ⊨ Γ }} as [env_relΓ] by (eapply completeness_fundamental_ctx; mauto 2).
    unshelve (epose proof completeness_typ_unsorted H as [W []]); try eassumption.
    inversion H3; subst.
    simplify_evals.
    inversion H6; subst.
    eexists; split; mauto 3.
  - assert (exists W, nbe Γ A {{{ Sort@s }}} W /\ {{ Γ ⊢ A ≈ W : Sort@s }}) as [W [?%nbe_type_to_nbe_ty Heq]] by mauto using soundness.
    eexists; split; mauto 3.
Qed.

Lemma soundness_ty' {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A W},
    {{ Γ ⊢ A }} ->
    nbe_ty Γ A W ->
    {{ Γ ⊢ A ≈ W }}.
Proof.
  intros.
  assert (exists B', nbe_ty Γ A B' /\ {{ Γ ⊢ A ≈ B' }}) as [? [? Heq]] by mauto using soundness_ty.
  functional_nbe_rewrite_clear.
  eassumption.
Qed.
