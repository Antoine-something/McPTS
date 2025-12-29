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

  - invert_glu_sort_elem H10.
    simpl_glu_rel.
    econstructor; mauto 2.
    econstructor; mauto 2.

  - invert_glu_sort_elem H9.
    simpl_glu_rel.
    split; mauto 2.
    eapply glu_nat_rule_irrelevance; mauto 2.
Qed.


Lemma glu_sort_elem_typ_conv {P} (pred_P : PredicativeSig P) : forall {s1 s2 s3 a a' typ_rel typ_rel' exp_rel exp_rel' Γ A},
    {{ Dom a ≈ a' ∈ per_sort pred_P s1 }} ->
    {{ DG a ∈ glu_sort_elem pred_P s2 ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s3 ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A ® typ_rel' }} ->
    {{ Γ ⊢ A ® typ_rel }}.
Proof.
  intros * [] ? ? ?.

  assert (per_typ_elem pred_P x a a') by mauto 2.
  assert (per_sort_elem pred_P s2 x a a').
  {
    assert (per_sort pred_P s2 a a) by mauto 2.
    destruct H4 as [R2 ?].
    mauto.
  }

  assert (per_sort_elem pred_P s3 x a' a).
  {
    assert (per_sort pred_P s3 a' a') by mauto 2.
    destruct H5 as [R3 ?].
    symmetry in H4.
    mauto.
  }
  assert (glu_sort_elem pred_P s2 typ_rel exp_rel a') by (eapply glu_sort_elem_resp_per_sort; mauto 3).
  assert (glu_sort_elem pred_P s3 typ_rel' exp_rel' a) by (eapply glu_sort_elem_resp_per_sort; mauto 3).

  invert_glu_sort_elem H0.
  - invert_glu_sort_elem H8.
    rewrite H8 in H3.
    unfold sort_glu_typ_pred in H3.
    
    
    saturate_glu_by_per.
    
    unfold sort_glu_exp_pred' in *.
    unfold glu_sort_typ_rec in *.
    
    apply_predicate_equivalence.    
    destruct_conjs.
    repeat eexists; mauto 2.
  


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
  assert {{ Δ ⊢ A[σ] : Sort@s }} by mauto using glu_sort_elem_trm_sort_lvl.
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

Lemma glu_ctx_env_sub_resp_ctx_eq {P} (pred_P : PredicativeSig P) : forall {Γ sts Sb},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
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

Add Parametric Morphism {P} (pred_P : PredicativeSig P) sts Sb Γ (H : glu_ctx_env pred_P sts Sb Γ) : Sb
    with signature wf_ctx_eq ==> eq ==> eq ==> iff as glu_ctx_env_sub_morphism_iff1.
Proof.
  intros.
  split; intros; eapply glu_ctx_env_sub_resp_ctx_eq; mauto.
Qed.

Lemma glu_ctx_env_sub_resp_sub_eq {P} (pred_P : PredicativeSig P) : forall {sts Γ Sb},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
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
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
  assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk][σ'] : Sort@s }} as <- by mauto 4.
  assert {{ Δ ⊢ #0[σ] ≈ #0[σ'] : A[Wk][σ] }} as <- by mauto 3.
  eassumption.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) sts Sb Γ (H : glu_ctx_env pred_P sts Sb Γ) Δ : (Sb Δ)
    with signature wf_sub_eq Δ Γ ==> eq ==> iff as glu_ctx_env_sub_morphism_iff2.
Proof.
  split; intros; eapply glu_ctx_env_sub_resp_sub_eq; mauto.
Qed.

Lemma cons_glu_sub_pred_resp_wf_sub_eq {P} (pred_P : PredicativeSig P) : forall {sts s Γ A Sb Δ σ σ' ρ},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Δ ⊢s σ ≈ σ' : Γ, A }} ->
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
    assert {{ Δ ⊢ #0[σ] ≈ #0[σ'] : A[Wk][σ] }} as <-; mauto 3.
  - assert {{ Δ ⊢s Wk∘σ ≈ Wk∘σ' : Γ }} as <-; eassumption.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) sts s Γ A Sb Δ (Hglu : {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }}) (HA : {{ Γ ⊢ A : Sort@s }}) : (cons_glu_sub_pred pred_P s Γ A Sb Δ)
    with signature wf_sub_eq Δ {{{ Γ, A }}} ==> eq ==> iff as cons_glu_sub_pred_morphism_iff.
Proof.
  split; mauto using cons_glu_sub_pred_resp_wf_sub_eq.
Qed.

Lemma glu_ctx_env_per_env {P} (pred_P : PredicativeSig P) : forall {sts Γ Sb env_rel Δ σ ρ},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
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
  destruct_rel_typ_unsorted.
  handle_per_typ_elem_irrel.
  assert (exists typ_rel' exp_rel', {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }}) as [? []] by mauto 3.

  eexists; eauto.
  handle_functional_glu_sort_elem P.
  eapply glu_sort_elem_per_elem; mauto.
  assert {{ Dom a ≈ a ∈ per_sort pred_P s }} by mauto 2.
  unfold per_sort in H5.
  destruct H5 as [].
  mauto.
Qed.

Lemma glu_ctx_env_wf_ctx {P} (pred_P : PredicativeSig P) : forall {sts Γ Sb},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
    {{ ⊢ Γ }}.
Proof.
  induction 1; intros; mauto 3.
Qed.

Lemma glu_ctx_env_sub_escape {P} (pred_P : PredicativeSig P) : forall {sts Γ Sb},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
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

Lemma glu_ctx_env_per_ctx_env {P} (pred_P : PredicativeSig P) : forall {sts Γ Sb},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
    exists env_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}.
Proof.
  intros.
  enough {{ ⟪ pred_P ⟫ ⊨ Γ }} by eassumption.
  mauto 3 using completeness_fundamental_ctx.
Qed.

#[export]
Hint Resolve glu_ctx_env_per_ctx_env : mcpts.


Lemma glu_ctx_env_resp_per_ctx_helper {P} (pred_P : PredicativeSig P) : forall {sts Γ Γ' Sb Sb'},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
    {{ EG Γ' ∈ glu_ctx_env pred_P sts ↘ Sb' }} ->
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
  
  (* rename i0 into j. *)
  (* rename Γ0 into Γ'. *)
  (* rename A0 into A'. *)
  (* rename TSb0 into TSb'. *)
  (* rename i1 into k. *)

  
  inversion HΓΓ' as [|? ? l ? l']; subst.
  assert (TSb -∙> TSb') by intuition.
  intros Δ σ ρ [].
  saturate_refl_for (@per_ctx_env P).
  assert {{ Dom ρ0 ↯ ≈ ρ0 ↯ ∈ tail_rel }}
    by (eapply glu_ctx_env_per_env; [| | eassumption]; eassumption).
  assert {{ Δ0 ⊢s Wk∘σ0 ® ρ0 ↯ ∈ TSb' }} by intuition.
  assert (glu_rel_typ_with_sub pred_P s Δ0 A' {{{ Wk∘σ0 }}} d{{{ ρ0 ↯ }}}) as [] by mauto 3.
  destruct_rel_typ_unsorted.
  handle_functional_glu_sort_elem P.
  rename a0 into a'.
  rename El0 into exp_rel'.
  rename P0 into typ_rel'.
  econstructor; mauto 4.

  assert (per_typ pred_P a a') by mauto 3.
  assert ((typ_rel' <∙> P1) /\ (El <∙> exp_rel')) by (eapply glu_sort_elem_per_typ_iff; mauto 2).
  destruct_conjs.
  eapply H33.

  enough {{ Δ0 ⊢ A[Wk][σ0] ≈ A'[Wk][σ0] : Sort@s }} by (eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 2).
  assert (typ_rel' Δ0 {{{ A[Wk][σ0] }}}) by (eapply glu_sort_elem_trm_typ; mauto 2).
  apply_predicate_equivalence.
  assert {{ Δ0 ⊢ A[Wk][σ0] ≈ A'[Wk∘σ0] : Sort@s }} by mauto 2.
  transitivity {{{ A'[Wk∘σ0] }}}; mauto 2.
  eapply exp_eq_sub_compose_typ_sort; mauto 2.
  econstructor; mauto 3.
Qed.


Corollary functional_glu_ctx_env {P} (pred_P : PredicativeSig P) : forall {sts Γ Sb Sb'},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb' }} ->
    (Sb <∙> Sb').
Proof.
  intros.
  assert {{ ⊢ Γ ≈ Γ }} by mauto using glu_ctx_env_wf_ctx.
  split; eapply glu_ctx_env_resp_per_ctx_helper; eassumption.
Qed.


Ltac apply_functional_glu_ctx_env1 :=
  let tactic_error o1 o2 := fail 2 "functional_glu_ctx_env biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ EG ^?Γ ∈ glu_ctx_env ?pred_P ?sts ↘ ?Sb1 }},
      H2 : {{ EG ^?Γ ∈ glu_ctx_env ?pred_P ?sts ↘ ?Sb2 }} |- _ =>
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

Lemma glu_ctx_env_cons_clean_inversion {P} (pred_P : PredicativeSig P) : forall {sts s Γ TSb A Sb},
  {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ TSb }} ->
  {{ EG Γ, A ∈ glu_ctx_env pred_P (cons s sts) ↘ Sb }} ->
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
  (* assert (Sb <∙> cons_glu_sub_pred pred_P s Γ A TSb0) as -> by eassumption. *)
  intros Δ σ ρ.
  split; intros [];
    econstructor; intuition.
Qed.

Ltac invert_glu_ctx_env H :=
  (unshelve eapply (glu_ctx_env_cons_clean_inversion _ _ _ _) in H; shelve_unifiable; [eassumption |];
   destruct H as [? [? []]])
  + dependent destruction H.


Lemma glu_ctx_env_eqtyp_sub_if {P} (pred_P : PredicativeSig P) : forall sts Γ Γ' Sb Sb' Δ σ ρ,
    {{ ⊢ Γ ≈ Γ' }} ->
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
    {{ EG Γ' ∈ glu_ctx_env pred_P sts ↘ Sb' }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb' }}.
Proof.
  intros * HΓΓ' HgluΓ HgluΓ'.
  assert (Sb -∙> Sb') by (eapply glu_ctx_env_resp_per_ctx_helper; mauto 2).
  intros.
  eapply H.
  eassumption.
Qed.


Lemma glu_ctx_env_sub_monotone {P} (pred_P : PredicativeSig P) : forall sts Γ Sb,
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
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
  - assert {{ Δ' ⊢ #0[σ0][σ] : A[Wk][σ0][σ] ® m ∈ El }} by (eapply glu_sort_elem_exp_monotone; mauto 3).
    assert {{ Γ, A ⊢ #0 : A[Wk] }} by mauto 3.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Δ' ⊢ #0[σ0∘σ] ≈ #0[σ0][σ] : A[Wk][σ0∘σ] }} as -> by mauto 3.
    assert {{ Δ' ⊢s σ : Δ }} by mauto 3.
    assert {{ Δ' ⊢ A[Wk][σ0][σ] ≈ A[Wk][σ0∘σ] : Sort@s }} as <-.
    {
      symmetry.
      eapply exp_eq_sub_compose_typ_sort; mauto 2.
      eapply eq_exp_sub_typ; mauto 2.
    }
    eassumption.
  - assert {{ Δ' ⊢s σ : Δ }} by mauto 3.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Δ' ⊢s (Wk ∘ σ0) ∘ σ ≈ Wk ∘ (σ0 ∘ σ) : Γ }} as <- by mauto 3.
    mauto 3.
Qed.

Lemma cons_glu_sub_pred_helper {P} (pred_P : PredicativeSig P) : forall {sts Γ Sb Δ σ ρ A a s P El M c},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    {{ Γ ⊢ A : Sort@s }} ->
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ P ↘ El }} ->
    {{ Δ ⊢ M : A[σ] ® c ∈ El }} ->
    {{ Δ ⊢s σ,,M ® ρ ↦ c ∈ cons_glu_sub_pred pred_P s Γ A Sb }}.
Proof.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ Δ ⊢ M : A[σ] }} by mauto 2 using glu_sort_elem_trm_escape.
  assert {{ Δ ⊢s σ,,M : Γ, A }} by mauto 2.
  econstructor; mauto 3;
    autorewrite with mcpts; mauto 3.

  assert {{ Δ ⊢ #0[σ,,M] ≈ M : A[σ] }}; mauto 2.
  assert {{ Δ ⊢ A[Wk][σ,,M] ≈ A[σ] : Sort@s }}.
  {
    transitivity {{{ A[Wk∘(σ,,M)] }}}; mauto 2.
    - symmetry; eapply exp_eq_sub_compose_typ_sort; mauto 2.
      econstructor; mauto 2.
    - eapply eq_exp_eq_sub_typ; mauto 2.
      econstructor; mauto 2.
      econstructor; mauto 2.
  }
  enough (El Δ {{{ A[σ] }}} {{{ #0[σ,,M] }}} c) by (eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 3).  
  enough (El Δ {{{ A[σ] }}} M c) by (eapply glu_sort_elem_trm_resp_exp_eq; mauto 4).
  mauto.
Qed.

#[export]
Hint Resolve cons_glu_sub_pred_helper : mcpts.


Lemma initial_env_glu_rel_exp {P} (pred_P : PredicativeSig P) : forall {sts Γ ρ Sb},
    initial_env Γ ρ ->
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
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
  rename P0 into typ_rel.
  
  functional_eval_rewrite_clear.
  econstructor; mauto.
  - match goal with
    | H: typ_rel Γ {{{ A[Id] }}} |- _ =>
        bulky_rewrite_in H
    end.
    eapply realize_glu_elem_bot; mauto.
    assert {{ ⊢ Γ }} by mauto 3.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 4.
    assert {{ Γ, A ⊢ A[Wk] : Sort@s }} by mauto 4.
    assert {{ Γ, A ⊢ A[Wk] ≈ A[Wk][Id] : Sort@s }} as <- by mauto 3.
    assert {{ Γ, A ⊢ #0 ≈ #0[Id] : A[Wk] }} as <- by mauto.
    eapply var_glu_elem_bot; mauto.
  - assert {{ Γ, A ⊢s Wk : Γ }} by mauto 4.
    assert {{ Γ, A ⊢s Wk∘Id : Γ }} by mauto 4.
    assert {{ Γ, A ⊢s Id∘Wk ≈ Wk∘Id : Γ }} as <- by (transitivity (@a_weaken P); mauto 3).
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
    | H : glu_rel_exp_with_sub _ _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.

Ltac destruct_glu_rel_typ_with_sub :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ ?sub_glu_rel }} -> glu_rel_typ_with_sub _ _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; fail_if_dup; mark H
    | H : glu_rel_exp_with_sub _ _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.


(** *** Lemmas about [glu_rel_exp] *)

Lemma glu_rel_exp_clean_inversion1 {P} (pred_P : PredicativeSig P) : forall {sts Γ Sb M A},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
    glu_rel_exp pred_P Γ sts M A ->
    (* {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A }} -> *)
    exists s,
    forall Δ σ ρ,
      {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
      glu_rel_exp_with_sub pred_P s Δ M A σ ρ.
Proof.
  intros * ? [].
  destruct_conjs.
  eexists; intros.
  handle_functional_glu_ctx_env P.
  mauto.
Qed.

Lemma glu_rel_exp_clean_inversion2 {P} (pred_P : PredicativeSig P) : forall {sts s Γ Sb M A},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
    glu_rel_exp pred_P Γ sts A {{{ Sort@s }}} ->
    (* {{ ⟪ pred_P ⟫ Γ :: sts ⊩ A : Sort@s }} -> *)
    glu_rel_exp pred_P Γ sts M A ->
    (* {{ ⟪ pred_P ⟫ Γ :: sts ⊩ M : A }} -> *)
    glu_rel_exp_resp_sub_env pred_P s Sb M A.
Proof.
  simpl.
  intros * ? HA HM.
  eapply glu_rel_exp_clean_inversion1 in HA; [| eassumption].
  eapply glu_rel_exp_clean_inversion1 in HM; [| eassumption].
  destruct HA as [s0 ?].
  destruct HM as [s1 ?].
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
  apply_predicate_equivalence.
  unfold sort_glu_exp_pred' in *.
  unfold glu_sort_typ_rec in *.
  destruct_conjs.
  econstructor; mauto 3.
  eapply glu_sort_elem_exp_conv; revgoals; mauto 3.
Qed.


#[global]
Ltac invert_glu_rel_exp H :=
  (unshelve eapply (glu_rel_exp_clean_inversion2 _ _ _ _ _) in H; shelve_unifiable; [eassumption | eassumption |];
   simpl in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion1 _ _ _ _) in H; shelve_unifiable; [eassumption |];
     destruct H as [])
  + (inversion H as [? [? [? ?]]]; subst).


Lemma glu_rel_exp_to_wf_exp {P} (pred_P : PredicativeSig P) : forall {sts Γ A M},
    glu_rel_exp pred_P Γ sts M A  ->
    (* {{ ⟪ pred_P ⟫ Γ :: sts ⊩ M : A }} -> *)
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

Lemma glu_rel_sub_clean_inversion1 {P} (pred_P : PredicativeSig P) : forall {sts sts' Γ Sb τ Γ'},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
    glu_rel_sub pred_P Γ sts τ Γ' sts' ->
    (* {{ ⟪ pred_P ⟫ Γ :: sts ⊩s τ : Γ' }} -> *)
    exists Sb' : glu_sub_pred P,
      glu_ctx_env pred_P sts' Sb' Γ' /\ (forall (Δ : ctx P) (σ : sub P) (ρ : env P), Sb Δ σ ρ -> glu_rel_sub_with_sub pred_P Δ τ Sb' σ ρ).
Proof.
  intros * ? [? []].
  destruct_conjs.
  handle_functional_glu_ctx_env P.
  eexists; split; mauto 3.
  intros.
  rewrite_predicate_equivalence_left.
  mauto 3.
Qed.

Lemma glu_rel_sub_clean_inversion2 {P} (pred_P : PredicativeSig P) : forall {sts sts' Γ τ Γ' Sb'},
    {{ EG Γ' ∈ glu_ctx_env pred_P sts' ↘ Sb' }} ->
    glu_rel_sub pred_P Γ sts τ Γ' sts' ->
    (* {{ Γ ⊩s τ : Γ' }} -> *)
    exists Sb : glu_sub_pred P,
      glu_ctx_env pred_P sts Sb Γ /\ (forall (Δ : ctx P) (σ : sub P) (ρ : env P), Sb Δ σ ρ -> glu_rel_sub_with_sub pred_P Δ τ Sb' σ ρ).
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

Lemma glu_rel_sub_clean_inversion3 {P} (pred_P : PredicativeSig P) : forall {sts sts' Γ Sb τ Γ' Sb'},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
    {{ EG Γ' ∈ glu_ctx_env pred_P sts' ↘ Sb' }} ->
    glu_rel_sub pred_P Γ sts τ Γ' sts' ->
    (* {{ Γ ⊩s τ : Γ' }} -> *)
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
  (unshelve eapply (glu_rel_sub_clean_inversion3 _ _ _ _ _ _) in H; shelve_unifiable; [eassumption | eassumption |])
  + (unshelve eapply (glu_rel_sub_clean_inversion2 _ _ _ _ _) in H; shelve_unifiable; [eassumption |];
     destruct H as [? []])
  + (unshelve eapply (glu_rel_sub_clean_inversion1 _ _ _ _ _) in H; shelve_unifiable; [eassumption |];
     destruct H as [? []])
  + (inversion H; subst).

Lemma glu_rel_sub_wf_sub {P} (pred_P : PredicativeSig P) : forall {sts sts' Γ σ Δ},
    glu_rel_sub pred_P Γ sts σ Δ sts' ->
    (* {{ Γ ⊩s σ : Δ }} -> *)
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


(* The proof `glu_univ_elem_exp_conv'` does not translate since it relies on cumulativity, but it would actually solve some problems if we could translate it somehow *)



(* Ltac unify_glu_univ_lvl1 i := *)
(*   match goal with *)
(*   | H1 : glu_univ_elem _ _ ?El _, H2 : glu_univ_elem i ?P _ _, H3 : ?P _ _, H4 : ?El _ _ _ _ *)
(*     |- _ => *)
(*       pose proof (glu_univ_elem_exp_conv' H1 H2 H4 H3); *)
(*       fail_if_dup *)
(*   end. *)

(* Ltac unify_glu_univ_lvl i := *)
(*   fail_if_dup; *)
(*   repeat unify_glu_univ_lvl1 i. *)

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


Lemma glu_rel_exp_preserves_lvl {P} (pred_P : PredicativeSig P) : forall sts Γ Sb M A s,
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
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
  (* destruct_glu_rel_exp_with_sub. *)
  saturate_glu_typ_from_el.
  saturate_glu_info.
  mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_preserves_lvl : mcpts.



Ltac saturate_syn_judge1 :=
  match goal with
  | H : (glu_rel_exp ?pred_P ?Γ ?sts ?M ?A) |- _ =>
      (* | H : {{ ⟪ ?pred_P ⟫ ^?Γ : ^?sts ⊩ ^?M : ^?A }} |- _ => *)
      assert {{ Γ ⊢ M : A }} by mauto; fail_if_dup
  | H : (glu_rel_sub ?pred_P ?Γ ?sts ?τ ?Γ' ?sts') |- _ =>
    (* | H : {{ ⟪ ?pred_P ⟫ ^?Γ : ^?sts ⊩s ^?τ : ^?Γ' }} |- _ => *)
      assert {{ Γ ⊢s τ : Γ' }} by mauto; fail_if_dup
  end.

#[global]
  Ltac saturate_syn_judge :=
  repeat saturate_syn_judge1.

Ltac invert_sem_judge1 :=
  match goal with
  | H : (glu_rel_exp ?pred_P ?Γ ?sts ?M ?A) |- _ =>
  (* | H : {{ ^?Γ ⊩ ^?M : ^?A }} |- _ => *)
      invert_glu_rel_exp H
  | H : (glu_rel_sub ?pred_P ?Γ ?sts ?τ ?Γ' ?sts') |- _ =>                         
  (* | H : {{ ^?Γ ⊩s ^?τ : ^?Γ' }} |- _ => *)
      invert_glu_rel_sub H
  end.

#[global]
  Ltac invert_sem_judge :=
  repeat invert_sem_judge1.
