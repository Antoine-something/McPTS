From Coq Require Import Morphisms_Relations Relation_Definitions.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import LogicalRelation SortCases TermStructureCases FunctionCases.
Import Domain_Notations.

Lemma t {P : PtsSig} {pred_P : PredicativeSig P} : forall s s' r m m', 
    st_subtyp s s' ->
    per_sort_elem pred_P s r m m' ->
    per_sort_elem pred_P s' r m m'.
Proof.
  intros.
  saturate_refl.
  specialize (ord_st_subtyp pred_P H) as ?.
  destruct H3; mauto.
Qed.
  

Lemma subtyp_refl {P : PtsSig} {pred_P : PredicativeSig P}  : forall Γ M M' s,
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M ⊆ M' }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_subtyp.
  intros.
  saturate_refl.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ P).
  invert_rel_typ_body.
  destruct_by_head (@rel_exp P).
  unfold per_sort_rec in *.
  destruct_conjs.
  handle_per_sort_elem_irrel.
  do 2 eexists.
  repeat split; econstructor; mauto 3; econstructor;
    etransitivity; try eassumption; symmetry; eassumption.
Qed.

Lemma subtyp_refl_unsorted {P : PtsSig} {pred_P : PredicativeSig P}  : forall Γ M M' s,
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M ⊆ M' }}.
Proof.
  intros * [env_relΓ]%rel_exp_unsorted_of_typ_inversion1.
  destruct_conjs.
  eexists_subtyp.
  intros.
  saturate_refl.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head @per_sort.
  handle_per_sort_elem_irrel.
  do 2 eexists.
  repeat split; repeat split; econstructor; mauto 3; econstructor;
    etransitivity; try eassumption; symmetry; eassumption.
Qed.

Lemma subtyp_trans {P : PtsSig} {pred_P : PredicativeSig P } : forall Γ M M' M'',
    {{ ⟪ pred_P ⟫ Γ ⊨ M ⊆ M' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M' ⊆ M'' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M ⊆ M'' }}.
Proof.
  intros * [env_relΓ [? ?]] [? [? ?]].
  destruct_conjs.
  pose env_relΓ.
  handle_per_ctx_env_irrel.
  eexists_subtyp.
  intros.
  saturate_refl.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  destruct_conjs.
  handle_per_sort_elem_irrel.
  do 2 eexists.
  repeat split; econstructor;
    eauto using per_sort_elem_cumu.
  etransitivity;
    eauto using per_subtyp_sorted_cumu.
Qed.

#[export]
Instance subtyp_Transitive {P} {pred_P : PredicativeSig P} Γ : Transitive ((@subtyp_under_ctx P pred_P) Γ).
Proof. eauto using subtyp_trans. Qed.

Lemma subtyp_sort {P} {pred_P : PredicativeSig P} : forall Γ s1 s2,
    {{ ⟪ pred_P ⟫ ⊨ Γ }} ->
    st_subtyp s1 s2 ->
    {{ ⟪ pred_P ⟫ Γ ⊨ Sort@s1 ⊆ Sort@s2 }}.
Proof.
  intros * [env_relΓ] ?.
  eexists_subtyp.
  intros.
  do 2 eexists.
  repeat split; econstructor; mauto; try econstructor; mauto; try reflexivity.
Qed.

Lemma subtyp_pi {P} {pred_P : PredicativeSig P} : forall {s1 s2 s3} {r : Ru_pi P s1 s2 s3} Γ A A' B B',
  {{ ⟪ pred_P ⟫ Γ ⊨u A ≈ A' : Sort@s1 }} ->
  {{ ⟪ pred_P ⟫ Γ , A@s1 ⊨u B : Sort@s2 }} ->
  {{ ⟪ pred_P ⟫ Γ , A'@s1 ⊨u B' : Sort@s2 }} ->
  {{ ⟪ pred_P ⟫ Γ , A'@s1 ⊨ B ⊆ B' }} ->
  {{ ⟪ pred_P ⟫ Γ ⊨ Π r A B ⊆ Π r A' B' }}.
Proof.
  intros * [env_relΓ]%rel_exp_unsorted_of_typ_inversion1 []%rel_exp_unsorted_of_typ_inversion1 []%rel_exp_unsorted_of_typ_inversion1 [? [? ?]].
  destruct_conjs.
  handle_per_ctx_env_irrel.
  invert_per_ctx_envs.
  match goal with
  | _: _ <~> cons_per_ctx_env env_relΓ ?x |- _ =>
      rename x into head_relA'
  end.
  handle_per_ctx_env_irrel.
  eexists_subtyp.
  intros.
  saturate_refl.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head @per_sort.
  handle_per_sort_elem_irrel.
  (* destruct H0. *)
  (* destruct_by_head (@rel_exp P). *)
  (* destruct_conjs. *)
  
  assert (forall c c', head_relA' ρ ρ' equiv_ρ_ρ' c c' -> cons_per_ctx_env env_relΓ head_relA' d{{{ ρ ↦ c }}} d{{{ ρ' ↦ c' }}}) as HΓA'
      by (intros; econstructor; mauto).
  assert (forall c c', head_rel ρ ρ' equiv_ρ_ρ' c c' -> cons_per_ctx_env env_relΓ head_rel d{{{ ρ ↦ c }}} d{{{ ρ' ↦ c' }}}) as HΓA'0
      by (intros; econstructor; mauto). 

  (** The proofs for the next two assertions are basically the same *)
  exvar (relation (domain P))
    ltac:(fun R => assert ({{ DF Π r a0 ρ B ≈ Π r a ρ' B ∈ per_sort_elem pred_P s3 ↘ R }})).
  {
    intros.
    per_sort_elem_econstructor; [econstructor | | | solve_refl].
    -  etransitivity; [| symmetry]; mauto.
    - eapply rel_exp_pi_core; [| reflexivity].
      intros.
      assert {{ Dom ρ ↦ c ≈ ρ' ↦ c' ∈ cons_per_ctx_env env_relΓ head_relA' }} as equiv_ρc_ρ'c' by (apply HΓA'; intuition).
      (on_all_hyp: fun H => destruct (H _ _ equiv_ρc_ρ'c')).
      destruct_conjs.
      destruct_by_head @rel_typ_unsorted.
      destruct_by_head @rel_exp.      
      econstructor; mauto.
  }
  exvar (relation (domain P))
    ltac:(fun R => assert ({{ DF Π r a0 ρ B' ≈ Π r a ρ' B' ∈ per_sort_elem pred_P s3 ↘ R }})).
  {
    per_sort_elem_econstructor; [econstructor | | | solve_refl].
    - etransitivity; [| symmetry]; mauto.
    - eapply rel_exp_pi_core; [| reflexivity].
      intros.
      assert {{ Dom ρ ↦ c ≈ ρ' ↦ c' ∈ cons_per_ctx_env env_relΓ head_relA' }} as equiv_ρc_ρ'c' by (apply HΓA'; intuition).
      assert {{ Dom ρ ↦ c ≈ ρ' ↦ c' ∈ cons_per_ctx_env env_relΓ head_rel }} as equiv_ρc_ρ'c'0 by (apply HΓA'0; intuition).
      simpl in *.
      (on_all_hyp: fun H => destruct (H _ _ equiv_ρc_ρ'c')).
      (on_all_hyp: fun H => destruct (H _ _ equiv_ρc_ρ'c'0)).
      econstructor; mauto.
  }

  exvar (relation (domain P))
    ltac:(fun R => assert ({{ DF Π r a3 ρ B ≈ Π r a2 ρ' B ∈ per_sort_elem pred_P s3 ↘ R }})).
  {
    intros.
    per_sort_elem_econstructor; [econstructor | mauto 2 | | solve_refl].
    - eapply rel_exp_pi_core; [| reflexivity].
      intros.
      assert {{ Dom ρ ↦ c ≈ ρ' ↦ c' ∈ cons_per_ctx_env env_relΓ head_relA' }} as equiv_ρc_ρ'c' by (apply HΓA'; intuition).
      simpl in *.
      (on_all_hyp: fun H => destruct (H _ _ equiv_ρc_ρ'c')).
      econstructor; mauto.
  }
  exvar (relation (domain P))
    ltac:(fun R => assert ({{ DF Π r a3 ρ B' ≈ Π r a2 ρ' B' ∈ per_sort_elem pred_P s3 ↘ R }})).
  {
    per_sort_elem_econstructor; [econstructor | mauto 2 | | solve_refl].
    - eapply rel_exp_pi_core; [| reflexivity].
      intros.
      assert {{ Dom ρ ↦ c ≈ ρ' ↦ c' ∈ cons_per_ctx_env env_relΓ head_relA' }} as equiv_ρc_ρ'c' by (apply HΓA'; intuition).
      assert {{ Dom ρ ↦ c ≈ ρ' ↦ c' ∈ cons_per_ctx_env env_relΓ head_rel }} as equiv_ρc_ρ'c'0 by (apply HΓA'0; intuition).
      simpl in *.
      (on_all_hyp: fun H => destruct (H _ _ equiv_ρc_ρ'c')).
      (on_all_hyp: fun H => destruct (H _ _ equiv_ρc_ρ'c'0)).
      econstructor; mauto.
  }
  
  do 2 eexists.
  repeat split; econstructor; mauto 2.
  do 2 econstructor;
  only 1: mauto;
  only 3-4: try (saturate_refl; mautosolve 2).
  - eauto using per_sort_elem_cumu.
  - intros.
    assert (cons_per_ctx_env env_relΓ head_relA' d{{{ ρ ↦ c }}} d{{{ ρ' ↦ c' }}}) as equiv_ρc_ρ'c' by (apply HΓA'; intuition).
    assert (cons_per_ctx_env env_relΓ head_rel d{{{ ρ ↦ c }}} d{{{ ρ' ↦ c' }}}) as equiv_ρc_ρ'c'0 by (apply HΓA'0; intuition).
    simpl in *.
    (on_all_hyp: fun H => destruct (H _ _ equiv_ρc_ρ'c')).
    (on_all_hyp: fun H => destruct (H _ _ equiv_ρc_ρ'c'0)).
    destruct_conjs.
    destruct_by_head @rel_mod_eval.
    destruct H42.
    handle_per_sort_elem_irrel.
    mauto using per_subtyp_sorted_cumu.
Admitted.
