From Coq Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness Require Export Realizability.
Import Domain_Notations.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s a Γ A M : (glu_elem_bot pred_P s a Γ A M)
    with signature per_bot ==> iff as glu_elem_bot_morphism_iff4.
Proof.
  intros m m' Hmm' *.
  split; intros []; econstructor; mauto 3;
    try (etransitivity; mauto 4);
    intros;
    specialize (Hmm' (length Δ)) as [? []];
    functional_read_rewrite_clear;
    mauto.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s a Γ A M R (H : per_sort_elem pred_P s R a a) : (glu_elem_top pred_P s a Γ A M)
    with signature R ==> iff as glu_elem_top_morphism_iff4.
Proof.
  intros m m' Hmm' *.
  split; intros []; econstructor; mauto 3;
    pose proof (per_elem_then_per_top H Hmm') as Hmm'';
    try (etransitivity; mauto 4);
    intros;
    specialize (Hmm'' (length Δ)) as [? []];
    functional_read_rewrite_clear;
    mauto.
Qed.

Lemma glu_sort_elem_typ_unique_upto_exp_eq {P} (pred_P : PredicativeSig P) : forall {s a typ_rel typ_rel' exp_rel exp_rel' Γ A A'},
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ ⊢ A' ® typ_rel' }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ A ® glu_typ_top pred_P s a }} as [] by mauto 3.
  assert {{ Γ ⊢ A' ® glu_typ_top pred_P s a }} as [] by mauto 3.
  match_by_head (@per_top_typ P) ltac:(fun H => destruct (H (length Γ)) as [V []]).
  clear_dups.
  functional_read_rewrite_clear.
  assert {{ Γ ⊢ A[Id] ≈ V : Sort@s }} by mauto 4.
  assert {{ Γ ⊢ A ≈ A[Id] : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ A ≈ V : Sort@s }} by (etransitivity; mauto 3).
  assert {{ Γ ⊢ A'[Id] ≈ V : Sort@s }} by mauto 4.
  assert {{ Γ ⊢ A' ≈ A'[Id] : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ A' ≈ V : Sort@s }} by (etransitivity; mauto 3).
  etransitivity; mauto 3.
Qed.

#[export]
Hint Resolve glu_sort_elem_typ_unique_upto_exp_eq : mcpts.


Lemma glu_sort_elem_per_sort_elem_typ_escape {P} (pred_P : PredicativeSig P) : forall {s a a' elem_rel typ_rel typ_rel' exp_rel exp_rel' Γ A A'},
    {{ DF a ≈ a' ∈ per_sort_elem pred_P s ↘ elem_rel }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ ⊢ A' ® typ_rel' }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }}.
Proof with mautosolve 4.
  simpl in *.
  intros * Hper Hglu Hglu' HA HA'.
  assert {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} by (setoid_rewrite Hper; eassumption).
  (handle_functional_glu_sort_elem P)...
Qed.

#[export]
Hint Resolve glu_sort_elem_per_sort_elem_typ_escape : mcpts.


Lemma glu_sort_elem_per_sort_typ_escape {P} (pred_P : PredicativeSig P) : forall {s a a' typ_rel typ_rel' exp_rel exp_rel' Γ A A'},
    {{ Dom a ≈ a' ∈ per_sort pred_P s }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ ⊢ A' ® typ_rel' }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }}.
Proof.
  intros * [] **...
  mauto 4.
Qed.

#[export]
Hint Resolve glu_sort_elem_per_sort_typ_escape : mcpts.



Lemma glu_sort_elem_exp_unique_upto_exp_eq {P} (pred_P : PredicativeSig P) : forall {s a typ_rel typ_rel' exp_rel exp_rel' Γ A A' M M' m},
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M' : A' ® m ∈ exp_rel' }} ->
    {{ Γ ⊢ M ≈ M' : A }}.
Proof.
  intros.
  assert {{ Γ ⊢ M : A ® m ∈ glu_elem_top pred_P s a }} as [] by mauto 3.
  assert {{ Γ ⊢ M' : A' ® m ∈ glu_elem_top pred_P s a }} as [] by mauto 3.
  assert {{ Γ ⊢ A ≈ A' : Sort@s }} by mauto 3.
  match_by_head (@per_top P) ltac:(fun H => destruct (H (length Γ)) as [W []]).
  clear_dups.
  assert {{ Γ ⊢ M[Id] ≈ W : A[Id] }} by mauto 4.
  assert {{ Γ ⊢ M[Id] ≈ W : A }} by (gen_presups; mauto 4).
  assert {{ Γ ⊢ M : A }} by mauto 4.
  assert {{ Γ ⊢ M'[Id] ≈ W : A'[Id] }} by mauto 4.
  assert {{ Γ ⊢ M'[Id] ≈ W : A' }} by (gen_presups; mauto 4).
  assert {{ Γ ⊢ M'[Id] ≈ W : A }} by (gen_presups; mauto 4).
  assert {{ Γ ⊢ M' : A }} by mauto 4.
  transitivity {{{M[Id]}}}; [mauto 3 |].
  transitivity W; [mauto 3 |].
  mauto 4.
Qed.

#[export]
Hint Resolve glu_sort_elem_exp_unique_upto_exp_eq : mcpts.

Lemma glu_sort_elem_exp_unique_upto_exp_eq' {P} (pred_P : PredicativeSig P) : forall {s a typ_rel exp_rel Γ A A' M M' m},
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M' : A' ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M ≈ M' : A }}.
Proof. mautosolve 4. Qed.

#[export]
Hint Resolve glu_sort_elem_exp_unique_upto_exp_eq' : mcpts.


Lemma glu_sort_elem_per_sort_typ_iff {P} (pred_P : PredicativeSig P) : forall {s a a' typ_rel typ_rel' exp_rel exp_rel'},
    {{ Dom a ≈ a' ∈ per_sort pred_P s }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    (typ_rel <∙> typ_rel') /\ (exp_rel <∙> exp_rel').
Proof.
  intros * Hper **.
  eapply functional_glu_sort_elem;
    [eassumption | rewrite Hper];
    eassumption.
Qed.


Lemma glu_sort_elem_per_typ_iff {P} (pred_P : PredicativeSig P) : forall {s a a' typ_rel typ_rel' exp_rel exp_rel'},
    {{ Dom a ≈ a' ∈ per_typ pred_P }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    (typ_rel <∙> typ_rel') /\ (exp_rel <∙> exp_rel').
Proof.
  intros * Hper **.
  assert (per_sort pred_P s a a) by mauto 2.
  unfold per_sort in H1.
  unfold per_typ in Hper.
  destruct_conjs.
  assert (per_sort_elem pred_P s Hper a a') by mauto 2.
  assert (per_sort pred_P s a a') by mauto 3.
  eapply glu_sort_elem_per_sort_typ_iff; mauto 2.
Qed.

Lemma glu_sort_elem_exp_conv {P} (pred_P : PredicativeSig P) : forall {s1 s2 s3 a a' typ_rel typ_rel' exp_rel exp_rel' Γ A M m},
    {{ Dom a ≈ a' ∈ per_sort pred_P s1 }} ->
    {{ DG a ∈ glu_sort_elem pred_P s2 ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s3 ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ A ® typ_rel' }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel' }}.
Proof.
  intros * [] ? ? ? ?.

  assert (per_typ_elem pred_P x a a') by mauto 2.
  assert (per_sort_elem pred_P s2 x a a').
  {
    assert (per_sort pred_P s2 a a) by mauto 2.
    destruct H5 as [R2 ?].
    mauto.
  }

  assert (per_sort_elem pred_P s3 x a' a).
  {
    assert (per_sort pred_P s3 a' a') by mauto 2.
    destruct H6 as [R3 ?].
    symmetry in H4.
    mauto.
  }
  assert (glu_sort_elem pred_P s2 typ_rel exp_rel a') by (eapply glu_sort_elem_resp_per_sort; mauto 3).
  assert (glu_sort_elem pred_P s3 typ_rel' exp_rel' a) by (eapply glu_sort_elem_resp_per_sort; mauto 3).

  invert_glu_sort_elem H0.
  - invert_glu_sort_elem H9.
    unfold sort_glu_exp_pred' in *.
    unfold glu_sort_typ_rec in *.
    apply_predicate_equivalence.
    destruct_conjs.
    repeat eexists; mauto 2.

  - invert_glu_sort_elem H12.
    assert ((typ_rel <∙> typ_rel') /\ (el_rel <∙> exp_rel')) by (eapply functional_glu_sort_elem; mauto 2).
    destruct_conjs.
    eapply H18.
    eassumption.

  - invert_glu_sort_elem H9.
    simpl_glu_rel.
    split; mauto 2.
    eapply glu_nat_rule_irrelevance; mauto 2.

  - invert_glu_sort_elem H10.
    simpl_glu_rel.
    econstructor; mauto 2.
    econstructor; mauto 2.
Qed.



Lemma mk_glu_rel_typ_with_sub' {P} (pred_P : PredicativeSig P) : forall {s Δ A σ ρ a},
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    (exists typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }}) ->
    (forall typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} -> {{ Δ ⊢ A[σ] ® typ_rel }}) ->
    glu_rel_typ_with_sub pred_P s Δ A σ ρ.
Proof.
  intros * ? [? []] HEl.
  econstructor; mauto.
  eapply HEl; mauto.
Qed.

#[export]
Hint Resolve mk_glu_rel_typ_with_sub' : mcpts.

Lemma mk_glu_rel_typ_with_sub'' {P} (pred_P : PredicativeSig P) : forall {s Δ A σ ρ a},
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ Dom a ≈ a ∈ per_sort pred_P s }} ->
    (forall typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} -> {{ Δ ⊢ A[σ] ® typ_rel }}) ->
    glu_rel_typ_with_sub pred_P s Δ A σ ρ.
Proof.
  intros * ? [] ?.
  assert (exists typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }}) as [? []] by mauto.
  eapply mk_glu_rel_typ_with_sub'; mauto.
Qed.

#[export]
Hint Resolve mk_glu_rel_typ_with_sub'' : mcpts.


Lemma mk_glu_rel_exp_with_sub' {P} (pred_P : PredicativeSig P) : forall {s Δ A M σ ρ a m},
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ ⟦ M ⟧ ρ ↘ m }} ->
    (exists typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }}) ->
    (forall typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} -> {{ Δ ⊢ M[σ] : A[σ] ® m ∈ exp_rel }}) ->
    glu_rel_exp_with_sub pred_P s Δ M A σ ρ.
Proof.
  intros * ? ? [? []] HEl.
  econstructor; mauto.
  eapply HEl; mauto.
Qed.

#[export]
Hint Resolve mk_glu_rel_exp_with_sub' : mcpts.

Lemma mk_glu_rel_exp_with_sub'' {P} (pred_P : PredicativeSig P) : forall {s Δ A M σ ρ a m},
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ ⟦ M ⟧ ρ ↘ m }} ->
    {{ Dom a ≈ a ∈ per_sort pred_P s }} ->
    (forall typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} -> {{ Δ ⊢ M[σ] : A[σ] ® m ∈ exp_rel }}) ->
    glu_rel_exp_with_sub pred_P s Δ M A σ ρ.
Proof.
  intros * ? ? [] ?.
  assert (exists typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }}) as [? []] by mauto.
  eapply mk_glu_rel_exp_with_sub'; mauto.
Qed.

#[export]
Hint Resolve mk_glu_rel_exp_with_sub'' : mcpts.


Lemma glu_rel_exp_with_sub_implies_glu_rel_exp_sub_with_typ {P} (pred_P : PredicativeSig P) : forall {s s' Δ A M σ Γ ρ},
    Ax P s s' ->
    {{ Δ ⊢s σ : Γ }} ->
    glu_rel_exp_with_sub pred_P s Δ M A σ ρ ->
    glu_rel_exp_with_sub pred_P s' Δ A {{{ Sort@s }}} σ ρ.
Proof.
  intros * ? ? [].
  econstructor; mauto.
  assert {{ Δ ⊢ A[σ] : Sort@s }} by mauto 3 using glu_sort_elem_trm_sort_lvl.
  repeat split; try do 2 eexists; mauto 3.
  split; mauto 4.
  eapply glu_sort_elem_trm_typ; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_exp_sub_with_typ : mcpts.


Lemma glu_rel_exp_with_sub_implies_glu_rel_typ_with_sub {P} (pred_P : PredicativeSig P) : forall {s Δ A s' σ ρ},
  glu_rel_exp_with_sub pred_P s Δ A {{{ Sort@s' }}} σ ρ ->
  glu_rel_typ_with_sub pred_P s' Δ A σ ρ.
Proof.
  intros * [].
  simplify_evals.
  match_by_head1 (@glu_sort_elem P) invert_glu_sort_elem.
  apply_predicate_equivalence.
  unfold sort_glu_exp_pred' in *.
  unfold glu_sort_typ_rec in *.
  destruct_conjs.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_typ_with_sub : mcpts.


Lemma glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub {P} (pred_P : PredicativeSig P) : forall {Δ A s s' σ Γ ρ},
    Ax P s s' ->
    {{ Δ ⊢s σ : Γ }} ->
    glu_rel_typ_with_sub pred_P s Δ A σ ρ ->
    glu_rel_exp_with_sub pred_P s' Δ A {{{ Sort@s }}} σ ρ.
Proof.
  intros * ? ? [].
  simplify_evals.
  econstructor; mauto.
  assert {{ Δ ⊢ A[σ] : Sort@s }} by mauto 4 using glu_sort_elem_sort_lvl.
  repeat split; try do 2 eexists; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub : mcpts.

(** *** Lemmas for [glu_ctx_env] *)

Lemma glu_ctx_env_sub_resp_ctx_eq {P} (pred_P : PredicativeSig P) : forall {Γ Sb},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    forall {Δ Δ' σ ρ},
      {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
      {{ ⊢ Δ ≈ Δ' }} ->
      {{ Δ' ⊢s σ ® ρ ∈ Sb }}.
Proof.
  induction 1; intros * HSb Hctxeq;
    apply_predicate_equivalence;
    simpl in *;
    mauto 4.

  destruct_by_head (@cons_glu_sub_pred P).
  econstructor; mauto 4.
  rewrite <- Hctxeq; eassumption.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) Sb Γ (H : glu_ctx_env pred_P Sb Γ) : Sb
    with signature wf_ctx_eq ==> eq ==> eq ==> iff as glu_ctx_env_sub_morphism_iff1.
Proof.
  intros.
  split; intros; eapply glu_ctx_env_sub_resp_ctx_eq; mauto.
Qed.

Lemma glu_ctx_env_sub_resp_sub_eq {P} (pred_P : PredicativeSig P) : forall {Γ Sb},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    forall {Δ σ σ' ρ},
      {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
      {{ Δ ⊢s σ ≈ σ' : Γ }} ->
      {{ Δ ⊢s σ' ® ρ ∈ Sb }}.
Proof.
  induction 1; intros * HSb Hsubeq;
    apply_predicate_equivalence;
    simpl in *;
    gen_presup Hsubeq;
    try eassumption.

  destruct_by_head (@cons_glu_sub_pred P).
  econstructor; mauto 4.
  assert {{ Γ, A@s ⊢s Wk : Γ }} by mauto 3.
  assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk][σ'] : Sort@s }} as <- by mauto 4.
  assert {{ Δ ⊢ #0[σ] ≈ #0[σ'] : A[Wk][σ] }} as <- by mauto 4.
  eassumption.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) Sb Γ (H : glu_ctx_env pred_P Sb Γ) Δ : (Sb Δ)
    with signature wf_sub_eq Δ Γ ==> eq ==> iff as glu_ctx_env_sub_morphism_iff2.
Proof.
  split; intros; eapply glu_ctx_env_sub_resp_sub_eq; mauto.
Qed.

Lemma cons_glu_sub_pred_resp_wf_sub_eq {P} (pred_P : PredicativeSig P) : forall {s Γ A Sb Δ σ σ' ρ},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Δ ⊢s σ ≈ σ' : Γ, A@s }} ->
    {{ Δ ⊢s σ ® ρ ∈ cons_glu_sub_pred pred_P s Γ A Sb }} ->
    {{ Δ ⊢s σ' ® ρ ∈ cons_glu_sub_pred pred_P s Γ A Sb }}.
Proof.
  intros * Hglu HA Heq Hσ.
  dependent destruction Hσ.
  gen_presup Heq.
  assert {{ Δ ⊢s Wk∘σ : Γ }} by mauto 3.
  assert {{ Δ ⊢s Wk∘σ' : Γ }} by mauto 3.
  assert {{ Δ ⊢s Wk∘σ ≈ Wk∘σ' : Γ }} by mauto 3.
  econstructor; mauto 3.
  - assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk][σ'] : Sort@s }} as <- by mauto.
    assert {{ Δ ⊢ #0[σ] ≈ #0[σ'] : A[Wk][σ] }} as <-; mauto 4.
  - assert {{ Δ ⊢s Wk∘σ ≈ Wk∘σ' : Γ }} as <-; eassumption.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s Γ A Sb Δ (Hglu : {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }}) (HA : {{ Γ ⊢ A : Sort@s }}) : (cons_glu_sub_pred pred_P s Γ A Sb Δ)
    with signature wf_sub_eq Δ {{{ Γ, A@s }}} ==> eq ==> iff as cons_glu_sub_pred_morphism_iff.
Proof.
  split; mauto using cons_glu_sub_pred_resp_wf_sub_eq.
Qed.

Lemma glu_ctx_env_per_env {P} (pred_P : PredicativeSig P) : forall {Γ Sb env_rel Δ σ ρ},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    {{ Dom ρ ≈ ρ ∈ env_rel }}.
Proof.
  intros * Hglu Hper.
  gen ρ σ Δ env_rel.
  induction Hglu; intros;
    invert_per_ctx_env Hper;
    apply_predicate_equivalence;
    handle_per_ctx_env_irrel;
    mauto 3.

  inversion_clear_by_head (@cons_glu_sub_pred P).
  assert {{ Dom ρ ↯ ≈ ρ ↯ ∈ tail_rel }} by intuition.
  destruct_rel_typ.
  handle_per_typ_elem_irrel.
  assert (exists typ_rel' exp_rel', {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }}) as [? []] by mauto 3.

  eexists; eauto.
  handle_functional_glu_sort_elem P.
  eapply glu_sort_elem_per_elem; mauto.
Qed.

Lemma glu_ctx_env_wf_ctx {P} (pred_P : PredicativeSig P) : forall {Γ Sb},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ ⊢ Γ }}.
Proof.
  induction 1; intros; mauto 3.
Qed.

Lemma glu_ctx_env_sub_escape {P} (pred_P : PredicativeSig P) : forall {Γ Sb},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    forall Δ σ ρ,
      {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
      {{ Δ ⊢s σ : Γ }}.
Proof.
  induction 1; intros;
    handle_functional_glu_sort_elem P;
    destruct_by_head (@cons_glu_sub_pred P);
    eassumption.
Qed.

#[export]
Hint Resolve glu_ctx_env_wf_ctx glu_ctx_env_sub_escape : mcpts.

Lemma glu_ctx_env_per_ctx_env {P} (pred_P : PredicativeSig P) : forall {Γ Sb},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    exists env_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}.
Proof.
  intros.
  enough {{ ⟪ pred_P ⟫ ⊨ Γ }} by eassumption.
  mauto 3 using completeness_fundamental_ctx.
Qed.

#[export]
Hint Resolve glu_ctx_env_per_ctx_env : mcpts.


Lemma glu_ctx_env_resp_per_ctx_helper {P} (pred_P : PredicativeSig P) : forall {Γ Γ' Sb Sb'},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ EG Γ' ∈ glu_ctx_env pred_P ↘ Sb' }} ->
    {{ ⊢ Γ ≈ Γ' }} ->
    (Sb -∙> Sb').
Proof.
  intros * Hglu Hglu' HΓΓ'.
  gen Sb' Γ'.
  induction Hglu; intros;
    destruct (completeness_fundamental_ctx_eq _ pred_P _ _ HΓΓ') as [env_relΓ Hper];
    apply_predicate_equivalence;
    handle_per_sort_elem_irrel;
    dependent destruction Hglu';
    apply_predicate_equivalence;
    invert_per_ctx_env Hper;
    handle_per_ctx_env_irrel;
    try firstorder.

  rename Γ0 into Γ'.
  rename A0 into A'.
  rename TSb0 into TSb'.

  inversion HΓΓ' as [|? ? l ? l']; subst.
  assert (TSb -∙> TSb') by intuition.
  intros Δ σ ρ [].
  saturate_refl_for (@per_ctx_env P).
  assert (per_ctx_env pred_P tail_rel Γ' Γ') by (transitivity Γ; [symmetry|]; eassumption).
  assert {{ Dom ρ0 ↯ ≈ ρ0 ↯ ∈ tail_rel }} by (eapply glu_ctx_env_per_env; [| | eapply H14]; eassumption).
  assert {{ Δ0 ⊢s Wk∘σ0 ® ρ0 ↯ ∈ TSb' }} by intuition.
  assert (glu_rel_typ_with_sub pred_P s0 Δ0 A' {{{ Wk∘σ0 }}} d{{{ ρ0 ↯ }}}) as [] by mautosolve 3.
  destruct_rel_typ.
  handle_functional_glu_sort_elem P.
  simplify_evals.
  rename a0 into a'.
  rename exp_rel0 into exp_rel'.
  rename typ_rel0 into typ_rel'.
  econstructor; mauto 4.

  assert (per_typ pred_P a a') by mauto 4.
  assert ((typ_rel <∙> typ_rel') /\ (exp_rel <∙> exp_rel')) by (eapply glu_sort_elem_per_typ_iff; mauto 4).
  destruct_conjs.
  eapply H18.

  enough {{ Δ0 ⊢ A[Wk][σ0] ≈ A'[Wk][σ0] : Sort@s0 }} by (eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 2).
  assert (typ_rel Δ0 {{{ A[Wk][σ0] }}}) by (eapply glu_sort_elem_trm_typ; mauto 4).
  apply_predicate_equivalence.
  assert {{ Δ0 ⊢ A[Wk][σ0] ≈ A'[Wk∘σ0] : Sort@s0 }} by mauto 2.
  transitivity {{{ A'[Wk∘σ0] }}}; mauto 2.
  eapply exp_eq_sub_compose_typ_sort; mauto 2.
  econstructor; mauto 3.
Qed.


Corollary functional_glu_ctx_env {P} (pred_P : PredicativeSig P) : forall {Γ Sb Sb'},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb' }} ->
    (Sb <∙> Sb').
Proof.
  intros.
  assert {{ ⊢ Γ ≈ Γ }} by mauto using glu_ctx_env_wf_ctx.
  split; eapply glu_ctx_env_resp_per_ctx_helper; eassumption.
Qed.


Ltac apply_functional_glu_ctx_env1 :=
  let tactic_error o1 o2 := fail 2 "functional_glu_ctx_env biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ EG ^?Γ ∈ glu_ctx_env ?pred_P ↘ ?Sb1 }},
      H2 : {{ EG ^?Γ ∈ glu_ctx_env ?pred_P ↘ ?Sb2 }} |- _ =>
      assert_fails (unify Sb1 Sb2);
      match goal with
      | H : Sb1 <∙> Sb2 |- _ => fail 1
      | _ => assert (Sb1 <∙> Sb2) by (eapply functional_glu_ctx_env; [apply H1 | apply H2]) || tactic_error Sb1 Sb2
      end
  end.

Ltac apply_functional_glu_ctx_env :=
  repeat apply_functional_glu_ctx_env1.

Ltac handle_functional_glu_ctx_env P :=
  functional_eval_rewrite_clear;
  fold (glu_typ_pred P) in *;
  fold (glu_exp_pred P) in *;
  apply_functional_glu_ctx_env;
  apply_predicate_equivalence;
  clear_dups.

Lemma glu_ctx_env_cons_clean_inversion {P} (pred_P : PredicativeSig P) : forall {s Γ TSb A Sb},
  {{ EG Γ ∈ glu_ctx_env pred_P ↘ TSb }} ->
  {{ EG Γ, A@s ∈ glu_ctx_env pred_P ↘ Sb }} ->
  {{ Γ ⊢ A : Sort@s }} /\
      (forall Δ σ ρ,
          {{ Δ ⊢s σ ® ρ ∈ TSb }} ->
          glu_rel_typ_with_sub pred_P s Δ A σ ρ) /\
      (Sb <∙> cons_glu_sub_pred pred_P s Γ A TSb).
Proof.
  intros.
  simpl in *.
  match_by_head (@glu_ctx_env P) progressive_invert.
  apply_functional_glu_ctx_env.

  intuition.
  rewrite -> H3.
  intros Δ σ ρ.
  split; intros [];
    econstructor; intuition.
Qed.

Ltac invert_glu_ctx_env H :=
  (unshelve eapply (glu_ctx_env_cons_clean_inversion _ _ _ _) in H; shelve_unifiable; [eassumption |];
   destruct H as [? [? []]])
  + dependent destruction H.


Lemma glu_ctx_env_eqtyp_sub_if {P} (pred_P : PredicativeSig P) : forall Γ Γ' Sb Sb' Δ σ ρ,
    {{ ⊢ Γ ≈ Γ' }} ->
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ EG Γ' ∈ glu_ctx_env pred_P ↘ Sb' }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb' }}.
Proof.
  intros * HΓΓ' HgluΓ HgluΓ'.
  assert (Sb -∙> Sb') by (eapply glu_ctx_env_resp_per_ctx_helper; mauto 2).
  intros.
  eapply H.
  eassumption.
Qed.


Lemma glu_ctx_env_sub_monotone {P} (pred_P : PredicativeSig P) : forall Γ Sb,
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    forall Δ' σ Δ τ ρ,
      {{ Δ ⊢s τ ® ρ ∈ Sb }} ->
      {{ Δ' ⊢w σ : Δ }} ->
      {{ Δ' ⊢s τ ∘ σ ® ρ ∈ Sb }}.
Proof.
  induction 1; intros * HSb Hσ;
    apply_predicate_equivalence;
    simpl in *;
    mauto 3.

  destruct_by_head (@cons_glu_sub_pred P).
  econstructor; mauto 3.
  - assert {{ Δ' ⊢ #0[σ0][σ] : A[Wk][σ0][σ] ® m ∈ exp_rel }} by (eapply glu_sort_elem_exp_monotone; mauto 3).
    assert {{ Γ, A@s ⊢ #0 : A[Wk] }} by mauto 3.
    assert {{ Γ, A@s ⊢s Wk : Γ }} by mauto 3.
    assert {{ Δ' ⊢ #0[σ0∘σ] ≈ #0[σ0][σ] : A[Wk][σ0∘σ] }} as -> by mauto 4.
    assert {{ Δ' ⊢s σ : Δ }} by mauto 3.
    assert {{ Δ' ⊢ A[Wk][σ0][σ] ≈ A[Wk][σ0∘σ] : Sort@s }} as <- by mauto 4.
    eassumption.
  - assert {{ Δ' ⊢s σ : Δ }} by mauto 3.
    assert {{ Γ, A@s ⊢s Wk : Γ }} by mauto 3.
    assert {{ Δ' ⊢s (Wk ∘ σ0) ∘ σ ≈ Wk ∘ (σ0 ∘ σ) : Γ }} as <- by mauto 3.
    mauto 3.
Qed.

Lemma cons_glu_sub_pred_helper {P} (pred_P : PredicativeSig P) : forall {Γ Sb Δ σ ρ A a s typ_rel exp_rel M c},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    {{ Γ ⊢ A : Sort@s }} ->
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Δ ⊢ M : A[σ] ® c ∈ exp_rel }} ->
    {{ Δ ⊢s σ,,M ® ρ ↦ c ∈ cons_glu_sub_pred pred_P s Γ A Sb }}.
Proof.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ Δ ⊢ M : A[σ] }} by mauto 2 using glu_sort_elem_trm_escape.
  assert {{ Δ ⊢s σ,,M : Γ, A@s }} by mauto 2.
  econstructor; mauto 3;
    autorewrite with mcpts; mauto 3.

  assert {{ Δ ⊢ #0[σ,,M] ≈ M : A[σ] }}; mauto 2.
  assert {{ Δ ⊢ A[Wk][σ,,M] ≈ A[σ] : Sort@s }} by mauto 4.
  enough (exp_rel Δ {{{ A[σ] }}} {{{ #0[σ,,M] }}} c) by (eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 3).
  enough (exp_rel Δ {{{ A[σ] }}} M c) by (eapply glu_sort_elem_trm_resp_exp_eq; mauto 4).
  mauto.
Qed.

#[export]
Hint Resolve cons_glu_sub_pred_helper : mcpts.


Lemma initial_env_glu_rel_exp {P} (pred_P : PredicativeSig P) : forall {Γ ρ Sb},
    initial_env Γ ρ ->
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ Γ ⊢s Id ® ρ ∈ Sb }}.
Proof.
  intros * Hinit HΓ.
  gen ρ.
  induction HΓ; intros * Hinit;
    dependent destruction Hinit;
    apply_predicate_equivalence;
    try solve [econstructor; mauto].

  rename ρ0 into ρ.
  assert (glu_rel_typ_with_sub pred_P s Γ A {{{ Id }}} ρ) as [] by mauto.

  functional_eval_rewrite_clear.
  econstructor; mauto.
  - match goal with
    | H: typ_rel Γ {{{ A[Id] }}} |- _ =>
        bulky_rewrite_in H
    end.
    eapply realize_glu_elem_bot; mauto.
    assert {{ ⊢ Γ }} by mauto 3.
    assert {{ Γ, A@s ⊢s Wk : Γ }} by mauto 4.
    assert {{ Γ, A@s ⊢ A[Wk] : Sort@s }} by mauto 4.
    assert {{ Γ, A@s ⊢ A[Wk] ≈ A[Wk][Id] : Sort@s }} as <- by mauto 3.
    assert {{ Γ, A@s ⊢ #0 ≈ #0[Id] : A[Wk] }} as <- by mauto.
    eapply var_glu_elem_bot; mauto.
  - assert {{ Γ, A@s ⊢s Wk : Γ }} by mauto 4.
    assert {{ Γ, A@s ⊢s Wk∘Id : Γ }} by mauto 4.
    assert {{ Γ, A@s ⊢s Id∘Wk ≈ Wk∘Id : Γ }} as <- by (transitivity (@a_weaken P); mauto 3).
    eapply glu_ctx_env_sub_monotone; mauto 4.
Qed.


(** *** Tactics for [glu_rel_*] *)

Ltac destruct_glu_rel_by_assumption sub_glu_rel H :=
  repeat
    match goal with
    | H' : {{ ^?Δ ⊢s ^?σ ® ^?ρ ∈ ?sub_glu_rel0 }} |- _ =>
        unify sub_glu_rel0 sub_glu_rel;
        destruct (H _ _ _ H') as [];
        destruct_conjs;
        mark_with H' 1
    end;
  unmark_all_with 1.

Ltac destruct_glu_rel_exp_with_sub :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ ?sub_glu_rel }} -> glu_rel_exp_with_sub _ _ _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; fail_if_dup; mark H
    | H : glu_rel_exp_with_sub _ _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.

Ltac destruct_glu_rel_sub_with_sub :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ ?sub_glu_rel }} -> glu_rel_sub_with_sub _ _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; fail_if_dup; mark H
    | H : glu_rel_sub_with_sub _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.

Ltac destruct_glu_rel_typ_with_sub :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ ?sub_glu_rel }} -> glu_rel_typ_with_sub _ _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; fail_if_dup; mark H
    | H : glu_rel_typ_with_sub _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.


(** *** Lemmas about [glu_rel_exp] *)

Lemma glu_rel_exp_clean_inversion1 {P} (pred_P : PredicativeSig P) : forall {s Γ Sb M A},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ M : A @ s}} ->
    glu_rel_exp_resp_sub_env pred_P s Sb M A.
Proof.
  intros * ? [].
  destruct_conjs.
  intros ? **.
  handle_functional_glu_ctx_env P.
  mauto.
Qed.

#[global]
Ltac invert_glu_rel_exp H :=
 (unshelve eapply (glu_rel_exp_clean_inversion1 _ _) in H; shelve_unifiable; [eassumption |];
  unfold glu_rel_exp_resp_sub_env in H)
  + (inversion H as [? [? [? ?]]]; subst).

Lemma glu_rel_exp_to_wf_exp {P} (pred_P : PredicativeSig P) : forall {s Γ A M},
    {{ ⟪ pred_P ⟫ Γ ⊩ M : A @ s }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros * [Sb].
  destruct_conjs.
  assert (exists env_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}) as [env_rel] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_rel }}) as [ρ] by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Γ ⊢s Id ® ρ ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_exp_with_sub.
  enough {{ Γ ⊢ M[Id] : A[Id] }} as HId; mauto 3 using glu_sort_elem_trm_escape.
Qed.

#[export]
Hint Resolve glu_rel_exp_to_wf_exp : mcpts.

(** *** Lemmas about [glu_rel_sub] *)

Lemma glu_rel_sub_clean_inversion1 {P} (pred_P : PredicativeSig P) : forall {Γ Sb τ Γ'},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩s τ : Γ' }} ->
    exists Sb' : glu_sub_pred P,
      glu_ctx_env pred_P Sb' Γ' /\ (forall (Δ : ctx P) (σ : sub P) (ρ : env P), Sb Δ σ ρ -> glu_rel_sub_with_sub pred_P Δ τ Sb' σ ρ).
Proof.
  intros * ? [? []].
  destruct_conjs.
  handle_functional_glu_ctx_env P.
  eexists; split; mauto 3.
  intros.
  rewrite_predicate_equivalence_left.
  mauto 3.
Qed.

Lemma glu_rel_sub_clean_inversion2 {P} (pred_P : PredicativeSig P) : forall {Γ τ Γ' Sb'},
    {{ EG Γ' ∈ glu_ctx_env pred_P ↘ Sb' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩s τ : Γ' }} ->
    exists Sb : glu_sub_pred P,
      glu_ctx_env pred_P Sb Γ /\ (forall (Δ : ctx P) (σ : sub P) (ρ : env P), Sb Δ σ ρ -> glu_rel_sub_with_sub pred_P Δ τ Sb' σ ρ).
Proof.
  intros * ? [? [Sb'0]].
  destruct_conjs.
  handle_functional_glu_ctx_env P.
  eexists; split; mauto 3.
  intros.
  assert (glu_rel_sub_with_sub pred_P Δ τ Sb'0 σ ρ) as [] by mauto 3.
  econstructor; mauto 3.
  rewrite_predicate_equivalence_left.
  mauto 3.
Qed.

Lemma glu_rel_sub_clean_inversion3 {P} (pred_P : PredicativeSig P) : forall {Γ Sb τ Γ' Sb'},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ EG Γ' ∈ glu_ctx_env pred_P ↘ Sb' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩s τ : Γ' }} ->
    glu_rel_sub_resp_sub_env pred_P Sb Sb' τ.
Proof.
  simpl. intros * ? ? Hglu.
  eapply glu_rel_sub_clean_inversion2 in Hglu; [| eassumption].
  destruct_conjs.
  handle_functional_glu_ctx_env P.
  intros.
  rewrite_predicate_equivalence_right.
  mauto 3.
Qed.

Ltac invert_glu_rel_sub H :=
  (unshelve eapply (glu_rel_sub_clean_inversion3 _ _ _) in H; shelve_unifiable; [eassumption | eassumption |])
  + (unshelve eapply (glu_rel_sub_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption |];
     destruct H as [? []])
  + (unshelve eapply (glu_rel_sub_clean_inversion1 _ _) in H; shelve_unifiable; [eassumption |];
     destruct H as [? []])
  + (inversion H; subst).

Lemma glu_rel_sub_wf_sub {P} (pred_P : PredicativeSig P) : forall {Γ σ Δ},
    {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }} ->
    {{ Γ ⊢s σ : Δ }}.
Proof.
  intros * [SbΓ [SbΔ]].
  destruct_conjs.
  assert (exists env_relΓ, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }}) as [env_relΓ] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ] by mauto 3 using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Γ ⊢s Id ® ρ ∈ SbΓ }} by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_sub_with_sub.
  mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_sub_wf_sub : mcpts.


Ltac saturate_glu_typ_from_el1 :=
  match goal with
  | H : glu_sort_elem _ _ _ ?exp_rel _, H1 : ?exp_rel _ _ _ _ |- _ =>
      pose proof (glu_sort_elem_trm_typ _ _ _ _ _ H _ _ _ _ H1);
      fail_if_dup
  end.

Ltac saturate_glu_typ_from_el :=
  fail_if_dup;
  repeat saturate_glu_typ_from_el1.

Ltac apply_glu_rel_judge P :=
  destruct_glu_rel_typ_with_sub;
  destruct_glu_rel_exp_with_sub;
  destruct_glu_rel_sub_with_sub;
  simplify_evals;
  match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H);
  handle_functional_glu_sort_elem P;
  unfold sort_glu_exp_pred' in *;
  destruct_conjs;
  clear_dups.


Lemma glu_rel_exp_preserves_lvl {P} (pred_P : PredicativeSig P) : forall {Γ Sb M A s},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    (forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        glu_rel_exp_with_sub pred_P s Δ M A σ ρ) ->
    {{ Γ ⊢ A : Sort@s }}.
Proof.
  intros.
  assert (exists env_relΓ, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }}) as [env_relΓ] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ] by mauto 3 using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Γ ⊢s Id ® ρ ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto 3).
  assert (glu_rel_exp_with_sub pred_P s Γ M A {{{ Id }}} ρ) by mauto 2.
  dependent destruction H4.
  saturate_glu_typ_from_el.
  saturate_glu_info.
  mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_preserves_lvl : mcpts.



Ltac saturate_syn_judge1 :=
  match goal with
  | H : {{ ⟪ ?pred_P ⟫ ^?Γ ⊩ ^?M : ^?A @ ^?s }} |- _ =>
      assert {{ Γ ⊢ M : A }} by mauto; fail_if_dup
  | H : {{ ⟪ ?pred_P ⟫ ^?Γ ⊩s ^?τ : ^?Γ' }} |- _ =>
      assert {{ Γ ⊢s τ : Γ' }} by mauto; fail_if_dup
  end.

#[global]
Ltac saturate_syn_judge :=
  repeat saturate_syn_judge1.

Ltac invert_sem_judge1 :=
  match goal with
  | H : {{ ⟪ ?pred_P ⟫ ^?Γ ⊩ ^?M : ^?A @ ^?s }} |- _ =>
      invert_glu_rel_exp H
  | H : {{ ⟪ ?pred_P ⟫ ^?Γ ⊩s ^?τ : ^?Γ' }} |- _ =>
      invert_glu_rel_sub H
  end.

#[global]
Ltac invert_sem_judge :=
  repeat invert_sem_judge1.


Lemma glu_rel_exp_typ_well_sorted {P} (pred_P : PredicativeSig P) : forall {Γ M A s},
    {{ ⟪ pred_P ⟫ Γ ⊩ M : A @ s }} ->
    {{ Γ ⊢ A : Sort@s }}.
Proof.
  intros.
  destruct H as [Sb []].
  assert (exists env_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}) as [env_rel] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_rel }}) as [ρ [ρ' []]] by mauto using per_ctx_then_per_env_initial_env.
  assert (Sb Γ {{{ Id }}} ρ) by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_exp_with_sub.
  mauto 2.
Qed.


Lemma glu_rel_exp_typ_implies_glu_rel_typ {P} {pred_P : PredicativeSig P} : forall {s s' Γ A σ ρ},
    glu_rel_exp_with_sub pred_P s' Γ A {{{ Sort@s }}} σ ρ ->
    glu_rel_typ_with_sub pred_P s Γ A σ ρ.
Proof.
  intros.
  inversion_clear H.
  simplify_evals.
  invert_glu_sort_elem H2.
  unfold sort_glu_exp_pred' in H0.
  unfold glu_sort_typ_rec in H0.
  apply H0 in H3.
  destruct_conjs.
  econstructor; mauto 2.
Qed.


Lemma glu_rel_typ_implies_glu_rel_exp_typ {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {s Γ A σ ρ},
    glu_rel_typ_with_sub pred_P s Γ A σ ρ ->
    exists s', glu_rel_exp_with_sub pred_P s' Γ A {{{ Sort@s }}} σ ρ.
Proof.
  intros.
  assert (exists s', Ax P s s') as [s'] by (eapply full_P).
  destruct H.
  eexists; econstructor; mauto 3.
  assert {{ Γ ⊢ A[σ] : Sort@s }} by (eapply glu_sort_elem_sort_lvl; mauto 3).
  gen_presup H3.
  assert (exists Δ K s', {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ A : K }} /\
                      (({{ Γ ⊢ K[σ] ≈ Sort@s }} /\ {{ Δ ⊢ K : Sort@s' }}) \/ ({{ Γ ⊢ K ≈ Sort@s }} /\ {{ Δ ⊢ K ≈ Sort@s' }}))) as [Δ [K [s'']]] by mauto 2.
  destruct_conjs.
  repeat split; mauto 3.
  repeat eexists; mauto 3.
Qed.


Lemma glu_rel_exp_sort_implies_ax {P} (pred_P : PredicativeSig P) : forall {Γ A s s'},
    {{ ⟪ pred_P ⟫ Γ ⊩ A: Sort@s @ s' }} ->
    Ax P s s'.
Proof.
  intros.
  destruct H as [SbΓ []].
  assert {{ ⊢ Γ }} by mauto 2.
  assert (exists env_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}) as [env_rel] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_rel }}) as [ρ [ρ' []]] by mauto using per_ctx_then_per_env_initial_env.
  assert (SbΓ Γ {{{ Id }}} ρ) by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  invert_glu_sort_elem H8.
  eassumption.
Qed.



(** Lemmas for unsorted logical relations *)
Lemma glu_rel_exp_implies_glu_rel_exp_unsorted {P} (pred_P : PredicativeSig P) : forall {Γ M A s},
    {{ ⟪ pred_P ⟫ Γ ⊩ M : A @ s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u M : A @ ^(Some s) }}.
Proof.
  intros * [SbΓ []].
  eexists; split; [eassumption |].
  intros.
  destruct (H0 Δ σ ρ H1).
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_implies_glu_rel_exp_unsorted : mcpts.

Lemma glu_rel_exp_unsorted_implies_glu_rel_exp {P} (pred_P : PredicativeSig P) : forall {Γ M A s},
    {{ ⟪ pred_P ⟫ Γ ⊩u M : A @ ^(Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ M : A @ s }}.
Proof.
  intros * [SbΓ []].
  eexists; split; [eassumption |].
  intros.
  pose proof (H0 Δ σ ρ H1).
  inversion_clear H2.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_unsorted_implies_glu_rel_exp : mcpts.


Lemma glu_rel_typ_implies_glu_rel_typ_unsorted {P} (pred_P : PredicativeSig P) : forall {Γ A s},
    {{ ⟪ pred_P ⟫ Γ ⊩ A @ s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u A @ ^(Some s) }}.
Proof.
  intros *[SbΓ []].
  eexists; split; [eassumption|].
  intros.
  destruct (H0 Δ σ ρ H1).
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_typ_implies_glu_rel_typ_unsorted : mcpts.

Lemma glu_rel_typ_unsorted_implies_glu_rel_typ {P} (pred_P : PredicativeSig P) : forall {Γ A s},
    {{ ⟪ pred_P ⟫ Γ ⊩u A @ ^(Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ A @ s }}.
Proof.
  intros *[SbΓ []].
  eexists; split; [eassumption|].
  intros.
  pose proof (H0 Δ σ ρ H1).
  inversion_clear H2.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_typ_unsorted_implies_glu_rel_typ : mcpts.


(** Lemmas for unsorted relations *)
Add Parametric Morphism {P} (pred_P : PredicativeSig P) so a Γ A M : (glu_elem_bot_unsorted pred_P so a Γ A M)
    with signature per_bot ==> iff as glu_elem_bot_unsorted_morphism_iff4.
Proof.
  intros m m' Hmm' *.
  split; inversion_clear 1;
    econstructor; mauto 3;
    intros;
    specialize (Hmm' (length Δ)) as [? []];
    specialize (H3 (length Δ)) as [? []];
    functional_read_rewrite_clear;
    mauto 3.
Qed.


Add Parametric Morphism {P} (pred_P : PredicativeSig P) so a Γ A M R (H : per_typ_elem pred_P R a a) : (glu_elem_top_unsorted pred_P so a Γ A M)
    with signature R ==> iff as glu_elem_top_unsorted_morphism_iff4.
Proof.
  intros m m' Hmm' *.
  split; inversion_clear 1.
  all: (econstructor; mauto 3;
        pose proof (per_typ_elem_then_per_top H Hmm') as Hmm'';
        [try (etransitivity; mauto 3) |];
        intros;
        specialize (Hmm'' (length Δ)) as [? []];
        functional_read_rewrite_clear;
        mauto 3).
Qed.


Lemma glu_typ_elem_exp_unique_upto_exp_eq {P} (pred_P : PredicativeSig P) : forall {so a typ_rel typ_rel' exp_rel exp_rel' Γ A A' M M' m},
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M' : A' ® m ∈ exp_rel' }} ->
    {{ Γ ⊢ M ≈ M' : A }}.
Proof.
  inversion_clear 1; inversion_clear 1; intros.
  - simpl_glu_rel.
    subst.
    mauto 3.
  - mauto 3.
Qed.

#[export]
Hint Resolve glu_typ_elem_exp_unique_upto_exp_eq : mcpts.

Lemma glu_typ_elem_exp_unique_upto_exp_eq' {P} (pred_P : PredicativeSig P) : forall {so a typ_rel exp_rel Γ A A' M M' m},
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M' : A' ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M ≈ M' : A }}.
Proof. mautosolve 4. Qed.

#[export]
Hint Resolve glu_typ_elem_exp_unique_upto_exp_eq' : mcpts.


Lemma glu_typ_elem_per_typ_iff {P} (pred_P : PredicativeSig P) : forall {so a a' typ_rel typ_rel' exp_rel exp_rel'},
    {{ Dom a ≈ a' ∈ per_typ pred_P }} ->
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_typ_elem pred_P so ↘ typ_rel' ↘ exp_rel' }} ->
    (typ_rel <∙> typ_rel') /\ (exp_rel <∙> exp_rel').
Proof.
  inversion 2; subst.
  - destruct H as [R].
    pose proof (per_typ_elem_then_per_top_typ H) as Haa'.
    specialize (Haa' 0) as [? []].
    inversion H3; subst.
    inversion H4; subst.
    inversion_clear 1.
    split; etransitivity; [| symmetry | | symmetry]; mauto 2.
  - inversion_clear 1.
    eapply glu_sort_elem_per_typ_iff; mauto 2.
Qed.


Lemma glu_rel_exp_unsorted_clean_inversion1 {P} (pred_P : PredicativeSig P) : forall {so Γ Sb M A},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u M : A @ so }} ->
    glu_rel_exp_resp_sub_env_unsorted pred_P so Sb M A.
Proof.
  intros * ? [].
  destruct_conjs.
  intros ? **.
  handle_functional_glu_ctx_env P.
  mauto.
Qed.

#[global]
Ltac invert_glu_rel_exp_unsorted H :=
  (unshelve eapply (glu_rel_exp_unsorted_clean_inversion1 _ _) in H; shelve_unifiable; [eassumption |];
   unfold glu_rel_exp_resp_sub_env_unsorted in H)
  + (inversion H as [? [? [? ?]]]; subst).

Ltac destruct_glu_rel_exp_unsorted_by_assumption sub_glu_rel H :=
  repeat
    match goal with
    | H' : {{ ^?Δ ⊢s ^?σ ® ^?ρ ∈ ?sub_glu_rel0 }} |- _ =>
        unify sub_glu_rel0 sub_glu_rel;
        let H'' := fresh "H''" in
        assert (glu_rel_exp_with_sub_unsorted _ _ _ _ _ _ _) as H'' by (eapply (H _ _ _ H'); mauto 3);
        inversion_clear H'' as [];
        subst;
        destruct_conjs;
        mark_with H' 1
    end;
  unmark_all_with 1.

Ltac destruct_glu_rel_exp_with_sub_unsorted :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ ?sub_glu_rel }} -> glu_rel_exp_with_sub_unsorted _ _ _ _ _ _ _) |- _ =>
        destruct_glu_rel_exp_unsorted_by_assumption sub_glu_rel H; fail_if_dup; mark H
    | H : glu_rel_exp_with_sub_unsorted _ _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.


Ltac destruct_glu_rel_typ_with_sub_unsorted :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ ?sub_glu_rel }} -> glu_rel_typ_with_sub_unsorted _ _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; fail_if_dup; mark H
    | H : glu_rel_typ_with_sub_unsorted _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.


Lemma glu_rel_exp_unsorted_to_wf_exp {P} (pred_P : PredicativeSig P) : forall {so Γ A M},
    {{ ⟪ pred_P ⟫ Γ ⊩u M : A @ so }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros * [Sb].
  destruct_conjs.
  assert (exists env_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}) as [env_rel] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_rel }}) as [ρ] by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Γ ⊢s Id ® ρ ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto 3).
  assert (glu_rel_exp_with_sub_unsorted pred_P so Γ M A {{{ Id }}} ρ) by mauto 3.
  dependent destruction H4.
  - inversion_clear H8.
    simpl_glu_rel.
    enough {{ Γ ⊢ M[Id] : Sort@s }} as HId; mauto 3 using glu_sort_elem_trm_escape.
    eapply glu_sort_elem_sort_lvl; mauto 2.
  - enough {{ Γ ⊢ M[Id] : A[Id] }} as HId; mauto 3 using glu_sort_elem_trm_escape.
Qed.

#[export]
Hint Resolve glu_rel_exp_unsorted_to_wf_exp : mcpts.


Lemma glu_rel_exp_with_sub_unsorted_typ_implies_glu_rel_typ_with_sub {P} (pred_P : PredicativeSig P) : forall {so s Δ A σ ρ},
    glu_rel_exp_with_sub_unsorted pred_P so Δ A {{{ Sort@s }}} σ ρ ->
    glu_rel_typ_with_sub pred_P s Δ A σ ρ.
Proof.
  intros * H.
  dependent destruction H.
  - inversion H2; subst.
    simpl_glu_rel.
    econstructor; mauto 2.
  - simplify_evals.
    invert_glu_sort_elem H1.
    unfold sort_glu_exp_pred' in H1.
    unfold glu_sort_typ_rec in H1.
    simpl_glu_rel.
    econstructor; mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_exp_with_sub_unsorted_typ_implies_glu_rel_typ_with_sub : mcpts.
