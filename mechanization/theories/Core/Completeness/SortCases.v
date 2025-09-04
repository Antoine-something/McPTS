From Coq Require Import Morphisms_Relations RelationClasses.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import LogicalRelation.
Import Domain_Notations.

Lemma rel_exp_of_typ_inversion1 {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ A A' s},
    {{ ⟪ pred_P ⟫ Γ ⊨ A ≈ A' : Sort@s }} ->
    exists env_rel,
      {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} /\
        forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
          rel_exp A ρ A' ρ' (per_sort pred_P s).
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists;
  eexists; [eassumption |].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ P).
  invert_rel_typ_body.
  eassumption.
Qed.

Lemma rel_exp_of_typ_inversion2 {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ env_rel A A' s},
    {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ A ≈ A' : Sort@s }} ->
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      rel_exp A ρ A' ρ' (per_sort pred_P s).
Proof.
  intros * ? []%rel_exp_of_typ_inversion1.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eassumption.
Qed.

Lemma rel_exp_under_ctx_implies_rel_typ_under_ctx {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ env_rel A A' s},
    {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} ->
    (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
        rel_exp A ρ A' ρ' (per_sort pred_P s)) ->
    exists (elem_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}), relation (domain P)),
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      rel_typ pred_P s A ρ A' ρ' (elem_rel equiv_ρ_ρ').
Proof.
  intros * ? ?.
  exists (fun ρ ρ' _ m m' => forall R,
          rel_typ pred_P s A ρ A' ρ' R ->
          R m m').
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_rel).
  unfold per_sort in *.
  destruct_conjs.
  econstructor; mauto 3.
  rewrite per_sort_elem_morphism_iff; mauto 3.
  split; intros.
  - enough (rel_typ pred_P s A ρ A' ρ' _) by intuition.
    econstructor; mauto 3.
  - destruct_rel_typ.
    handle_per_sort_elem_irrel.
    eassumption.
Qed.

Ltac invert_rel_exp_of_typ H :=
  (unshelve epose proof (rel_exp_of_typ_inversion2 _ _ H); shelve_unifiable; [eassumption |]; clear H)
  + (pose proof (rel_exp_of_typ_inversion1 _ H) as []; clear H)
  + invert_rel_exp H.

Lemma rel_exp_of_typ {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ env_rel A A'},
    {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} ->
    (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
        rel_exp A ρ A' ρ' (per_typ pred_P)) ->
    {{ ⟪ pred_P ⟫ Γ ⊨ A ≈ A' }}.
Proof.
  intros.
  eexists.
  split.
  mauto.
  intros.
  assert (rel_exp A ρ A' ρ' (per_typ pred_P)) by (eapply H0; mauto).
  inversion H1.
  unfold per_typ in H4.
  destruct_conjs.
  eexists.
  mauto.
Qed.

#[export]
Hint Resolve rel_exp_of_typ : mcpts.

Ltac eexists_rel_exp_of_typ :=
  unshelve eapply (rel_exp_of_typ _);
  shelve_unifiable;
  [eassumption |].

Lemma valid_exp_typ {P : PtsSig} {pred_P : PredicativeSig P} : forall {s Γ},
    (* Ax P s s' -> *)
    {{ ⟪ pred_P ⟫ ⊨ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ Sort@s }}.
Proof.
  intros * [].
  eexists_rel_exp_of_typ.
  intros.
  econstructor; mauto.
  unfold per_typ.
  exists (per_sort pred_P s).
  econstructor; mauto.
  reflexivity.
Qed.

#[export]
Hint Resolve valid_exp_typ : mcpts.

Lemma rel_exp_typ_sub {P : PtsSig} {pred_P : PredicativeSig P} : forall {s Γ σ Δ},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ Sort@s[σ] ≈ Sort@s }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp_of_typ.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor; mauto.
  exists (per_sort pred_P s).
  econstructor; mauto.
  reflexivity.
Qed.

#[export]
Hint Resolve rel_exp_typ_sub : mcpts.
