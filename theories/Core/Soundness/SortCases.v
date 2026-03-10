From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness Require Import LogicalRelation TermStructureCases.
Import Domain_Notations.

Lemma glu_rel_exp_of_typ {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ Sb A s s'},
    Ax P s s' ->
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    (forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        {{ Δ ⊢ A[σ] : Sort@s }} /\
          exists a,
            {{ ⟦ A ⟧ ρ ↘ a }} /\
              {{ Dom a ≈ a ∈ per_sort pred_P s }} /\
              forall typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} -> {{ Δ ⊢ A[σ] ® typ_rel }}) ->
      {{ ⟪ pred_P ⟫ Γ ⊩ A : Sort@s @ s' }}.
Proof.
  intros * Hax ? Hbody.
  eexists; split; mauto.
  intros.
  edestruct Hbody as [? [? [? []]]]; mauto.
Qed.


Lemma glu_rel_exp_of_typ_unsorted {P} (pred_P : PredicativeSig P) : forall {Γ Sb A s},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    (forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        {{ Δ ⊢ A[σ] : Sort@s }} /\
          exists a,
            {{ ⟦ A ⟧ ρ ↘ a }} /\
              {{ Dom a ≈ a ∈ per_sort pred_P s }} /\
              forall typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} -> {{ Δ ⊢ A[σ] ® typ_rel }}) ->
      {{ ⟪ pred_P ⟫ Γ ⊩u A : Sort@s @ ^None }}.
Proof.
  intros * ? Hbody.
  eexists; split; mauto.
  intros.
  edestruct Hbody as [? [? [? []]]]; mauto.
  econstructor; try reflexivity; mauto 2.
  - econstructor; reflexivity.
  - split; [reflexivity|].
    assert (exists typ_rel exp_rel, glu_sort_elem pred_P s typ_rel exp_rel x) as [typ_rel [exp_rel]] by mauto 3.
    do 2 eexists; split; mauto 2.
    specialize (H4 typ_rel exp_rel H5).
    eassumption.
Qed.


Lemma glu_rel_exp_typ {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ s s' s''},
    Ax P s s' -> Ax P s' s'' ->
    {{ ⟪ pred_P ⟫ ⊩ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ Sort@s : Sort@s' @ s'' }}.
Proof.
  intros * Hax Hax' [].
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  split; mauto 4.
  eexists; repeat split; mauto.
  intros.
  match_by_head1 (@glu_sort_elem P) invert_glu_sort_elem.
  apply_predicate_equivalence.
  cbn.
  mauto 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_typ : mcpts.


Lemma glu_rel_exp_typ_unsorted {P} (pred_P : PredicativeSig P) : forall {Γ s s'},
    Ax P s s' ->
    {{ ⟪ pred_P ⟫ ⊩ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u Sort@s : Sort@s' @ ^None }}.
Proof.
  intros * Hax [].
  eapply glu_rel_exp_of_typ_unsorted; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  split; mauto 4.
  eexists; repeat split; mauto.
  intros.
  match_by_head1 (@glu_sort_elem P) invert_glu_sort_elem.
  apply_predicate_equivalence.
  cbn.
  mauto 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_typ_unsorted : mcpts.


Lemma glu_rel_exp_clean_inversion2' {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {s s' Γ Sb M},
    Ax P s s' ->
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ M : Sort@s @ s' }} ->
    glu_rel_exp_resp_sub_env pred_P s' Sb M {{{ Sort@s }}}.
Proof.
  intros * Hax ? HM.
  assert (exists s'', {{ ⟪ pred_P ⟫ Γ ⊩ Sort@s : Sort@s' @ s'' }}) as [s''] by mauto 3.
  eapply glu_rel_exp_clean_inversion2 in HM; mauto 3.
Qed.

#[local]
Ltac invert_glu_rel_exp_old H :=
  invert_glu_rel_exp H.

#[global]
Ltac invert_glu_rel_exp H :=
  (unshelve eapply (glu_rel_exp_clean_inversion2' _ _ _ _ _ _) in H; shelve_unifiable; [eassumption |];
   simpl in H)
  + invert_glu_rel_exp_old H.

Lemma glu_rel_exp_unsorted_clean_inversion2' {P} (pred_P : PredicativeSig P) : forall {s so Γ Sb M},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u M : Sort@s @ so }} ->
    glu_rel_exp_resp_sub_env_unsorted pred_P so Sb M {{{ Sort@s }}}.
Proof.
  intros * ? HM.
  destruct so.
  - destruct HM as [SbΓ []].
    simpl.
    intros.
    handle_functional_glu_ctx_env P.
    assert (glu_rel_exp_with_sub_unsorted pred_P None Δ M {{{ Sort@s }}} σ ρ) by mauto 2.
    dependent destruction H.
    inversion H5; subst.
    simpl_glu_rel.
    econstructor; mauto 3.
    eapply H7.
    split; [reflexivity|].
    repeat eexists; mauto 2.
  - assert {{ ⟪ pred_P ⟫ Γ ⊩u Sort@s : Sort@s0 @ ^None }} by mauto 3.
    eapply glu_rel_exp_unsorted_clean_inversion2 in HM; mauto 3.
Qed.

#[local]
Ltac invert_glu_rel_exp_unsorted_old H :=
  invert_glu_rel_exp_unsorted H.

#[global]
Ltac invert_glu_rel_exp_unsorted H :=
  (unshelve eapply (glu_rel_exp_unsorted_clean_inversion2' _ _ _ _ _ _) in H; shelve_unifiable; [eassumption |];
   simpl in H)
  + invert_glu_rel_exp_unsorted_old H.



Lemma glu_rel_exp_sub_typ {P} (pred_P : PredicativeSig P) : forall {s' Γ σ Δ s A},
    {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ⊩ A : Sort@s @ s' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ A[σ] : Sort@s @ s' }}.
Proof.
  intros.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ ⊩ A[σ] : Sort@s[σ] @ s' }} by mauto 4.
  
  simpl in H2.
  destruct_conjs.
  eexists.
  split; mauto.
  intros.
  assert (glu_rel_exp_with_sub pred_P s' Δ0 {{{ A[σ] }}} {{{ Sort@s[σ] }}} σ0 ρ) by mauto.
  dependent destruction H6.
  simplify_evals.
  econstructor; mauto.

  assert {{ Δ0 ⊢ Sort@s[σ][σ0] : Sort@s' }} by (eapply glu_sort_elem_trm_sort_lvl; mauto 2).

  assert {{ ⊢ Γ }} by mauto 2.
  assert (Ax P s s') by (eapply glu_rel_exp_sort_implies_ax; mauto 2).
  assert {{ Γ ⊢ Sort@s[σ] ≈ Sort@s : Sort@s' }} by mauto 4.  
  assert {{ Δ0 ⊢ Sort@s[σ][σ0] ≈ Sort@s[σ0] : Sort@s' }} as <- by mauto 4.
  eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_sub_typ : mcpts.


Lemma glu_rel_exp_sub_typ_unsorted {P} (pred_P : PredicativeSig P) : forall {so Γ σ Δ s A},
    {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ⊩u A : Sort@s @ so }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u A[σ] : Sort@s @ so }}.
Proof.
  intros.
  destruct so.
  - assert {{ Δ ⊢ A : Sort@s }} by mauto 3.
    assert {{ Γ ⊢s σ : Δ }} by mauto 3.
    destruct H as [SbΓ [? [? []]]].
    destruct H0 as [SbΔ []].
    handle_functional_glu_ctx_env P.
    eexists; split; [eassumption |].
    intros.
    destruct_glu_rel_sub_with_sub.
    rewrite <- H7 in H8.
    assert (glu_rel_exp_with_sub_unsorted pred_P None Δ0 A {{{ Sort@s }}} {{{ σ∘σ0 }}} ρ') by mauto 2.
    dependent destruction H9.
    econstructor; mauto 3.
    inversion_clear H12.
    simpl_glu_rel.
    repeat eexists; mauto 2.
    assert {{ Δ0 ⊢s σ0 : Γ }} by mauto 3.
    assert {{ Δ0 ⊢ M[σ∘σ0] ≈ M[σ][σ0] : Sort@s }} as <- by mauto 4.
    eassumption.

  - assert {{ ⟪ pred_P ⟫ Δ ⊩ A : Sort@s @ s0 }} by mauto 2.
    assert {{ ⟪ pred_P ⟫ Γ ⊩ A[σ] : Sort@s @ s0 }} by mauto 2.
    mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_exp_sub_typ_unsorted : mcpts.  

Lemma glu_rel_typ_sort {P} (pred_P : PredicativeSig P) : forall {Γ s s'},
    Ax P s s' ->
    {{ ⟪ pred_P ⟫ ⊩ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ Sort@s @ s' }}.
Proof.
  intros * Hax [SbΓ].
  eexists; split; mauto 2.
  intros.
  econstructor; mauto 3.
  unfold sort_glu_typ_pred.
  mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_typ_sort : mcpts.


Lemma glu_rel_typ_unsorted_sort_ax {P} (pred_P : PredicativeSig P) : forall {Γ s s'},
    Ax P s s' ->
    {{ ⟪ pred_P ⟫ ⊩ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u Sort@s @ ^(Some s') }}.
Proof.
  intros.
  mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_typ_unsorted_sort_ax : mcpts.

Lemma glu_rel_typ_unsorted_sort_none {P} (pred_P : PredicativeSig P) : forall {Γ s},
    {{ ⟪ pred_P ⟫ ⊩ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u Sort@s @ ^None}}.
Proof.
  intros * [SbΓ].
  eexists; split; [eassumption |].
  intros.
  econstructor; try reflexivity.
  econstructor; try reflexivity.
Qed.

#[export]
Hint Resolve glu_rel_typ_unsorted_sort_none : mcpts.


Lemma glu_rel_typ_sorted {P} (pred_P : PredicativeSig P) : forall {Γ A s s'},
    {{ ⟪ pred_P ⟫ Γ ⊩ A : Sort@s @ s' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ A @ s }}.
Proof.
  intros * [SbΓ []].
  eexists; split; mauto 2.
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  invert_glu_sort_elem H4.
  unfold sort_glu_exp_pred' in *.
  unfold glu_sort_typ_rec in *.
  apply_predicate_equivalence.
  destruct_conjs.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_typ_sorted : mcpts.


Lemma glu_rel_typ_unsorted_sorted {P} (pred_P : PredicativeSig P) : forall {Γ A s so},
    {{ ⟪ pred_P ⟫ Γ ⊩u A : Sort@s @ so }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u A @ ^(Some s) }}.
Proof.
  intros * [SbΓ []].
  eexists; split; mauto 2.
  intros.
  assert (glu_rel_exp_with_sub_unsorted pred_P so Δ A {{{ Sort@s }}} σ ρ) by mauto 2.
  dependent destruction H2.
  - inversion H5; subst.
    simpl_glu_rel.    
    econstructor; mauto 3.

  - simplify_evals.
    invert_glu_sort_elem H4.
    unfold sort_glu_exp_pred' in *.
    unfold glu_sort_typ_rec in *.
    apply_predicate_equivalence.
    destruct_conjs.
    econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_typ_unsorted_sorted : mcpts.


Lemma glu_exp_with_sub_unsorted_typ_none {P} (pred_P : PredicativeSig P) : forall {Γ A s so},
    {{ ⟪ pred_P ⟫ Γ ⊩u A : Sort@s @ so }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u A : Sort@s @ ^None }}.
Proof.
  intros.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ }} by mauto 2.
  assert {{ ⟪ pred_P ⟫ Γ ⊩u Sort@s @ ^None }} by mauto 3.
  mauto 2.
Qed.

#[export]
Hint Resolve glu_exp_with_sub_unsorted_typ_none : mcpts.
