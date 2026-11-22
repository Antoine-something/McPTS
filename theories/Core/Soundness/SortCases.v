From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness Require Import LogicalRelation TermStructureCases.
Import Domain_Notations.

Lemma glu_rel_exp_of_typ {P} (pred_P : PredicativeSig P) : forall {anns Γ Sb A s},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    (forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        {{ Δ ⊢ A[σ] : Sort@s }} /\
          exists a,
            {{ ⟦ A ⟧ ρ ↘ a }} /\
              {{ Dom a ≈ a ∈ per_sort pred_P s }} /\
              forall typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} -> {{ Δ ⊢ A[σ] ® typ_rel }}) ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A : Sort@s @ ^so_None }}.
Proof.
  intros * ? Hbody.
  eexists; split; mauto.
  intros.
  edestruct Hbody as [? [? [? []]]]; mauto.
  econstructor; try reflexivity; mauto 2.
  - econstructor; reflexivity.
  - split; [mauto 3|].
    assert (exists typ_rel exp_rel, glu_sort_elem pred_P s typ_rel exp_rel x) as [typ_rel [exp_rel]] by mauto 3.
    do 2 eexists; split; mauto 2.
    assert (typ_rel Γ' {{{ A[σ] }}}) by (eapply H4; mauto 2).
    eassumption.
Qed.

Lemma glu_rel_exp_st {P} (pred_P : PredicativeSig P) : forall {anns Γ s s'},
    Ax_typ P s s' ->
    {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ Sort@s : Sort@s' @ ^so_None }}.
Proof.
  intros * Hax [].
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  rename Δ into Γ'. (* Not sure where the name Δ comes from *)
  assert {{ Γ' ⊢s σ : Γ }} by mauto 3.
  split; mauto 4.
  eexists; repeat split; mauto.
  intros.
  match_by_head1 (@glu_sort_elem P) invert_glu_sort_elem.
  apply_predicate_equivalence.
  assert  {{ Γ ⊢ Sort@s : Sort@s' }} by mauto 3.
  assert  {{ Γ' ⊢ Sort@s : Sort@s' }} by mauto 3.
  cbn; mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_exp_st : mcpts.
    
Lemma glu_rel_typ_st {P} (pred_P : PredicativeSig P) : forall {anns Γ s},
    {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ Sort@s @ ^so_None }}.
Proof.
  intros * [SbΓ].
  eexists; split; [eassumption |].
  intros.
  econstructor; mauto 3.
  - econstructor; try reflexivity.
  - assert {{ Γ' ⊢s σ : Γ }} by mauto 2.
    simpl.
    mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_typ_st : mcpts.

Lemma glu_rel_typ_exp {P} (pred_P : PredicativeSig P) : forall {anns Γ A s s'},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A : Sort@s @ s' }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A @ ^(so_Some s) }}.
Proof.
  intros * [SbΓ []].
  eexists; split; [eassumption |].
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.

  match_by_head @glu_typ_elem ltac:(fun H => inversion H; subst).
  - simpl_glu_rel.
    econstructor; mauto 2.
    econstructor; mauto 2.
  - invert_glu_sort_elem H2.
    unfold sort_glu_exp_pred' in *.
    unfold glu_sort_typ_rec in *.
    apply_predicate_equivalence.
    destruct_conjs.
    econstructor; mauto 3.
    econstructor; mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_typ_exp : mcpts.
