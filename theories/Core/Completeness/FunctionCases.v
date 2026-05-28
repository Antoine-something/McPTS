From Coq Require Import Morphisms_Relations Relation_Definitions.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import LogicalRelation TermStructureCases SortCases.
Import Domain_Notations.

Lemma rel_exp_of_pi_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : Π r A B }} ->
    exists env_rel,
      {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} /\
        forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
        exists in_rel out_rel,
          rel_typ pred_P s1 A ρ A ρ' in_rel /\
            (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_typ pred_P s2 B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (out_rel c c' equiv_c_c')) /\
            rel_exp M ρ M' ρ'
              (fun f f' : domain P => forall (c c' : domain P) (equiv_c_c' : in_rel c c'), rel_mod_app f c f' c' (out_rel c c' equiv_c_c')).
Proof.
  intros * [env_relΓ].
  assert ((pred_rel pred_P s1 s3 \/ s1 = s3) /\ (pred_rel pred_P s2 s3 \/ s2 = s3)) by (eapply ord_ru_pi; mauto).
  destruct_conjs.
  exists env_relΓ.
  split; mauto.
  intros.
  assert (exists elem_rel : relation (domain P), rel_typ pred_P H2 {{{ Π r A B }}} ρ {{{ Π r A B }}} ρ' elem_rel /\ rel_exp M ρ M' ρ' elem_rel) by mauto.
  destruct_conjs.
  inversion_clear H5.
  assert (exists aρ, a = d{{{ Π r aρ ρ B }}}).
  {
    inversion H7.
    rewrite -> H16.
    exists a0.
    assert ({{ ⟦ Π r A B ⟧ ρ ↘ Π r a0 ρ B }}) by (econstructor; mauto).
    functional_eval_rewrite_clear.
    reflexivity.
  }
  assert (exists aρ', a' = d{{{ Π r aρ' ρ' B }}}).
  {
    inversion H8.
    rewrite -> H17.
    exists a0.
    assert ({{ ⟦ Π r A B ⟧ ρ' ↘ Π r a0 ρ' B }}) by (econstructor; mauto).
    functional_eval_rewrite_clear.
    reflexivity.
  }
  destruct_conjs; subst.
  rename H5 into a.
  rename H10 into a'.
  rename H2 into s4.
  invert_per_sort_elem H9.
  assert ((pred_rel pred_P s1 s4 \/ s1 = s4) /\ (pred_rel pred_P s2 s4 \/ s2 = s4)) by (eapply ord_ru_pi_sub; mauto).
  destruct H9.
  exists in_rel; exists out_rel.
  repeat split; mauto.
  - econstructor.
    + inversion H7; mauto.
    + inversion H8; mauto.
    + destruct equiv_a_a'.
      destruct H0.
      * destruct H9; mauto.
        subst; eapply H11; mauto.
      * rewrite -> H0.
        subst.
        destruct H9; mauto.
        subst; eapply H11; mauto.
  - intros.
    assert (rel_mod_eval
      (fun (R : relation (domain P)) (b b' : domain P) =>
       (s2 = s4 -> per_sort_elem pred_P s4 R b b') /\
       (pred_rel pred_P s2 s4 -> per_sort_elem pred_P s2 R b b')) B d{{{
      ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (out_rel c c' equiv_c_c')) by mauto.
    unfold rel_typ.
    inversion_clear H11.
    destruct_conjs.
    econstructor; mauto.
    destruct H1.
    + destruct H10; mauto.
      subst; eapply H11; mauto.
    + destruct H10; mauto.
      subst; eapply H11; mauto.
  - handle_per_sort_elem_irrel.
    eapply H6.
Qed.

Lemma rel_exp_of_pi {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ env_rel M M' s1 s2 s3 A B} {r : Ru P s1 s2 s3},
    {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} ->
	(forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      exists in_rel out_rel,
        rel_typ pred_P s1 A ρ A ρ' in_rel /\
          (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_typ pred_P s2 B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (out_rel c c' equiv_c_c')) /\
          rel_exp M ρ M' ρ'
            (fun f f' : domain P => forall (c c' : domain P) (equiv_c_c' : in_rel c c'), rel_mod_app f c f' c' (out_rel c c' equiv_c_c'))) ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : Π r A B }}.
Proof.
  intros.
  destruct_conjs.
  (* eexists_rel_exp_with (max i j). *)
  eexists_rel_exp_with s3.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_rel).
  match goal with
  | _: rel_typ pred_P s1 A ρ A ρ' ?x |- _ =>
      rename x into in_rel
  end.
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp P).
  exists (fun f f' : domain P =>
   forall (c c' : domain P) (equiv_c_c' : in_rel c c'),
   rel_mod_app f c f' c' (out_rel c c' equiv_c_c')); split; econstructor; mauto.
  per_sort_elem_econstructor; mauto.
  reflexivity.
Qed.

Ltac eexists_rel_exp_of_pi :=
  unshelve eapply (rel_exp_of_pi _); shelve_unifiable; [eassumption |].

#[local]
Ltac extract_output_info_with P ρ c ρ' c' env_rel :=
  let Hequiv := fresh "equiv" in
  (assert (Hequiv : {{ Dom ρ ↦ c ≈ ρ' ↦ c' ∈ env_rel }}) by (apply_relation_equivalence; mauto 4);
   apply_relation_equivalence;
   (on_all_hyp: fun H => destruct (H _ _ Hequiv));
   destruct_conjs;
   destruct_by_head (@rel_typ P);
   destruct_by_head (@rel_exp P)).

Lemma rel_exp_pi_core {P : PtsSig} {pred_P : PredicativeSig P} : forall {s o B o' B' R out_rel},
    (forall c c',
        R c c' ->
        rel_exp B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} (per_sort pred_P s)) ->
    (** We use the next equality to make unification on `out_rel` works *)
    (out_rel = fun c c' (equiv_c_c' : R c c') m m' =>
                 forall R',
                   rel_typ pred_P s B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} R' ->
                   R' m m') ->
    (forall c c' (equiv_c_c' : R c c'), rel_typ pred_P s B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} (out_rel c c' equiv_c_c')).
Proof with intuition.
  intros.
  subst.
  (on_all_hyp: destruct_rel_by_assumption R).
  econstructor; mauto.
  destruct_by_head (@per_sort P).
  apply -> per_sort_elem_morphism_iff; eauto.
  split; intros; destruct_by_head (@rel_typ P); handle_per_sort_elem_irrel...
  assert (rel_typ pred_P s B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} _) by mauto.
  intuition.
Qed.

Lemma rel_exp_unsorted_of_pi {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ env_rel M M' s1 s2 s3 A B} {r : Ru P s1 s2 s3},
    {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} ->
	(forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      exists in_rel out_rel,
        rel_typ pred_P s1 A ρ A ρ' in_rel /\
          (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_typ pred_P s2 B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (out_rel c c' equiv_c_c')) /\
          rel_exp M ρ M' ρ'
            (fun f f' : domain P => forall (c c' : domain P) (equiv_c_c' : in_rel c c'), rel_mod_app f c f' c' (out_rel c c' equiv_c_c'))) ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : Π r A B }}.
Proof.
  intros.
  assert ({{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : Π r A B }}) by (eapply rel_exp_of_pi; mauto).
  mauto.
Qed.

Ltac eexists_rel_exp_unsorted_of_pi :=
  unshelve eapply (rel_exp_unsorted_of_pi _); shelve_unifiable; [eassumption |].


Lemma rel_exp_unsorted_pi_cong {P} {pred_P : PredicativeSig P} : forall {s1 s2 s3 Γ A A' B B'} {r : Ru P s1 s2 s3},
    {{ ⟪ pred_P ⟫ Γ ⊨u A : Sort@s1 }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u A ≈ A' : Sort@s1 }} ->
    {{ ⟪ pred_P ⟫ Γ, A@s1 ⊨u B ≈ B' : Sort@s2 }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u Π r A B ≈ Π r A' B' : Sort@s3 }}.
Proof.
  intros * [env_relΓ]%rel_exp_unsorted_of_typ_inversion1 []%rel_exp_unsorted_of_typ_inversion1 [env_relΓA]%rel_exp_unsorted_of_typ_inversion1.
  destruct_conjs.
  invert_per_ctx_envs.
  handle_per_ctx_env_irrel.
  rename x into env_relΓ.

  eexists; split; [eassumption|].
  intros.
  assert (rel_exp A ρ A' ρ' (per_sort pred_P s1)) by mauto.
  assert (rel_typ_unsorted pred_P A ρ A ρ' (head_rel ρ ρ' equiv_ρ_ρ')) by mauto.
  destruct_by_head (@rel_exp P).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@per_sort P).
  functional_eval_rewrite_clear.
  handle_per_sort_elem_irrel.
  exists (per_sort pred_P s3); split.
  - econstructor; mauto.
    econstructor; mauto.
    reflexivity.
  - econstructor; mauto.
    econstructor; mauto.
    per_sort_elem_econstructor; mauto.
    + eapply rel_exp_pi_core; mauto; [|reflexivity].
      intros.
      eapply H2; mauto.
      econstructor; mauto.
      assert (per_typ_elem pred_P x m m') by mauto.
      handle_per_typ_elem_irrel.
      eassumption.
    + solve_refl.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_pi_cong : mcpts.



Lemma rel_exp_unsorted_pi_sub {P : PtsSig} {pred_P : PredicativeSig P} : forall {s1 s2 s3} {r : Ru P s1 s2 s3} {Γ σ Δ A B},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨u A : Sort@s1 }} ->
    {{ ⟪ pred_P ⟫ Δ, A@s1 ⊨u B : Sort@s2 }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u (Π r A B)[σ] ≈ Π r (A[σ]) (B[q σ]) : Sort@s3 }}.
Proof with mautosolve.
  intros * [env_relΓ] [env_relΔ]%rel_exp_unsorted_of_typ_inversion1 []%rel_exp_unsorted_of_typ_inversion1.
  destruct_conjs.
  pose env_relΔ.
  invert_per_ctx_envs.
  match goal with
  | _: _ <~> cons_per_ctx_env env_relΔ ?x |- _ =>
      rename x into elem_relA
  end.
  handle_per_ctx_env_irrel.
  eexists_rel_exp_of_sort.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  assert {{ Dom ρ'σ' ≈ ρ'σ' ∈ env_relΔ }} by (etransitivity; [symmetry |]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head (@per_sort P).
  handle_per_sort_elem_irrel.
  econstructor; mauto.
  eexists.
  assert (per_typ_elem pred_P (elem_relA ρσ ρ'σ' H7) a a) by mauto.
  assert (per_typ_elem pred_P (elem_relA ρσ ρ'σ' H7) a0 a) by mauto.
  handle_per_typ_elem_irrel.
  per_sort_elem_econstructor; eauto.
  - eapply rel_exp_pi_core; eauto; try reflexivity.
    intros.
    assert (Hequiv : {{ Dom ρσ ↦ c ≈ ρ'σ' ↦ c' ∈ (cons_per_ctx_env env_relΔ elem_relA) }}) by (econstructor; mauto; econstructor; mauto).
    apply_relation_equivalence;
      (on_all_hyp: fun H => destruct (H _ _ Hequiv));
      destruct_conjs;
      destruct_by_head (@rel_typ P);
      destruct_by_head (@rel_exp P).
    repeat (econstructor; mauto).
  - solve_refl.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_pi_sub : mcpts.


Lemma rel_exp_unsorted_fn_cong {P : PtsSig} {pred_P : PredicativeSig P} : forall {s1 s2 s3} {r : Ru P s1 s2 s3} {Γ A A' B M M'},
    {{ ⟪ pred_P ⟫ Γ ⊨u A ≈ A' : Sort@s1 }} ->
    {{ ⟪ pred_P ⟫ Γ, A@s1 ⊨u M ≈ M' : B }} ->
    {{ ⟪ pred_P ⟫ Γ, A@s1 ⊨u B : Sort@s2 }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u λ r A M ≈ λ r A' M' : Π r A B }}.
Proof with mautosolve.
  intros * [env_relΓ]%rel_exp_unsorted_of_typ_inversion1 [] [env_relΓA]%rel_exp_unsorted_of_typ_inversion1.
  destruct_conjs.
  invert_per_ctx_envs.

  match goal with
  | _: _ <~> cons_per_ctx_env env_relΓ ?x |- _ =>
      rename x into elem_relA
  end.
  handle_per_ctx_env_irrel.
  assert (forall ρ ρ' equiv_ρ_ρ', elem_relA ρ ρ' equiv_ρ_ρ' <~> head_rel ρ ρ' equiv_ρ_ρ').
  {
    intros.
    assert (rel_typ_unsorted pred_P A ρ A ρ' (head_rel ρ ρ' equiv_ρ_ρ')) by mauto.
    assert (rel_typ_unsorted pred_P A ρ A ρ' (elem_relA ρ ρ' equiv_ρ_ρ')) by mauto.
    destruct_by_head (@rel_typ_unsorted P).
    functional_eval_rewrite_clear.
    handle_per_typ_elem_irrel.
    reflexivity.
  }
  eexists_rel_exp_unsorted_of_pi.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@per_sort P).
  functional_eval_rewrite_clear.
  do 2 eexists.
  repeat split; [econstructor | | econstructor]; mauto.
  - eapply rel_exp_pi_core; eauto; try reflexivity.
    intros.
    assert (Hequiv : {{ Dom ρ ↦ c ≈ ρ' ↦ c' ∈ (cons_per_ctx_env env_relΓ elem_relA) }}).
    {
      assert (exists R'', per_sort_elem pred_P s1 R'' a a') by mauto.
      destruct_conjs.
      econstructor; mauto.
      simpl; mauto.
      handle_per_sort_elem_irrel.
      handle_per_typ_elem_irrel.
      apply_relation_equivalence.
      eapply H20; mauto.
    }
    apply_relation_equivalence;
      (on_all_hyp: fun H => destruct (H _ _ Hequiv));
      destruct_conjs;
      destruct_by_head (@rel_typ_unsorted P);
      destruct_by_head (@rel_exp P).

    econstructor; eauto.
    assert (rel_exp B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (per_sort pred_P s2)).
    {
      eapply H2.
      econstructor; mauto;
        econstructor; mauto.
    }
    destruct_by_head (@rel_exp P).

    destruct_by_head (@per_sort P).
    functional_eval_rewrite_clear.
    eexists; mauto.
  - intros.
    assert (Hequiv : {{ Dom ρ ↦ c ≈ ρ' ↦ c' ∈ (cons_per_ctx_env env_relΓ elem_relA) }}).
    {
      econstructor; mauto.
      simpl; mauto.
      handle_per_sort_elem_irrel.
      handle_per_typ_elem_irrel.
      apply_relation_equivalence.
      eapply H12; mauto.
    }
    extract_output_info_with P ρ c ρ' c' (cons_per_ctx_env env_relΓ elem_relA).


    assert (exists elem_rel : relation (domain P),
               rel_typ_unsorted pred_P B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} elem_rel /\ rel_exp M d{{{ ρ ↦ c }}} M' d{{{ ρ' ↦ c' }}} elem_rel) by mauto.

    destruct_conjs.
    destruct_by_head (@rel_exp).
    econstructor; mauto.

    intros.
    destruct_by_head (@rel_typ_unsorted P).
    destruct_by_head (@rel_typ P).
    handle_per_sort_elem_irrel.
    assert (per_typ_elem pred_P R' a1 a'1) by mauto.
    handle_per_typ_elem_irrel.
    mauto.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_fn_cong : mcpts.


Lemma rel_exp_unsorted_fn_sub {P : PtsSig} {pred_P : PredicativeSig P} : forall {s1 s2 s3} {r : Ru P s1 s2 s3} {Γ σ Δ A M B},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨u A : Sort@s1 }} ->
    {{ ⟪ pred_P ⟫ Δ, A@s1 ⊨u M : B }} ->
    {{ ⟪ pred_P ⟫ Δ, A@s1 ⊨u B : Sort@s2 }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u (λ r A M)[σ] ≈ λ r A[σ] M[q σ] : (Π r A B)[σ] }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΔ]]] [env_relΔ']%rel_exp_unsorted_of_typ_inversion1 [env_relΔA] [env_relΔA']%rel_exp_unsorted_of_typ_inversion1.
  destruct_conjs.
  pose env_relΔA.
  invert_per_ctx_envs.
  handle_per_ctx_env_irrel.
  eexists; split; [eassumption|].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ').
  simplify_evals.
  inversion_clear H19.

  assert (rel_typ_unsorted pred_P A ρσ A ρ'σ' (head_rel ρσ ρ'σ' H10)) by mauto.
  assert (rel_typ_unsorted pred_P A ρσ A ρ'σ' (head_rel0 ρσ ρ'σ' H10)) by mauto.
  destruct_by_head (@rel_typ_unsorted P).
  simplify_evals.
  handle_per_typ_elem_irrel.

  eexists.
  split; econstructor; mauto 4.
  - econstructor; mauto.
    per_sort_elem_econstructor; [| | apply Equivalence_Reflexive]; eauto.
    intros.
    eapply rel_exp_pi_core; eauto; try reflexivity.
    clear dependent c.
    clear dependent c'.
    intros.

    assert (per_sort_elem pred_P s1 (head_rel0 ρσ ρ'σ' H10) a a') by mauto.
    handle_per_sort_elem_irrel.
    assert (Hequiv : {{ Dom ρσ ↦ c ≈ ρ'σ' ↦ c' ∈ env_relΔA }}).
    {
      apply_relation_equivalence.
      econstructor; mauto.
      simpl; mauto.
      handle_per_typ_elem_irrel.
      eapply H18; mauto.
    }
    apply_relation_equivalence;
      (on_all_hyp: fun H => destruct (H _ _ Hequiv));
      destruct_conjs;
      destruct_by_head (@rel_typ P);
      destruct_by_head (@rel_typ_unsorted P);
      destruct_by_head (@rel_exp P).

    econstructor; eauto.

    assert (rel_exp B d{{{ ρσ ↦ c }}} B d{{{ ρ'σ' ↦ c' }}} (per_sort pred_P s2)) by mauto.
    destruct_by_head (@rel_exp P).
    functional_eval_rewrite_clear.
    assumption.

  - intros ? **.
    assert (per_sort_elem pred_P s1 (head_rel0 ρσ ρ'σ' H10) a a') by mauto.
    assert (Hequiv : {{ Dom ρσ ↦ c ≈ ρ'σ' ↦ c' ∈ env_relΔA }}).
    {
      apply_relation_equivalence.
      econstructor; mauto.
      simpl; mauto.
      handle_per_sort_elem_irrel.
      apply_relation_equivalence.
      eapply H17; mauto.
    }
    apply_relation_equivalence;
      (on_all_hyp: fun H => destruct (H _ _ Hequiv));
      destruct_conjs;
      destruct_by_head (@rel_typ P);
      destruct_by_head (@rel_typ_unsorted P);
      destruct_by_head (@rel_exp P).

    econstructor; mauto; [repeat (econstructor; mauto)|].
    intros.
    destruct_by_head (@rel_typ P).
    destruct_by_head (@rel_typ_unsorted P).
    assert (per_typ_elem pred_P R' a1 a'1) by mauto.
    functional_eval_rewrite_clear.
    handle_per_typ_elem_irrel...
Qed.

#[export]
Hint Resolve rel_exp_unsorted_fn_sub : mcpts.

Lemma rel_exp_unsorted_of_pi_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' A B s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : Π r A B }} ->
    exists env_rel,
      {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} /\
        forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
        exists in_rel out_rel,
          rel_typ pred_P s1 A ρ A ρ' in_rel /\
            (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_typ pred_P s2 B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (out_rel c c' equiv_c_c')) /\
            rel_exp M ρ M' ρ'
              (fun f f' : domain P => forall (c c' : domain P) (equiv_c_c' : in_rel c c'), rel_mod_app f c f' c' (out_rel c c' equiv_c_c')).
Proof.
  intros * [env_relΓ].
  assert ((pred_rel pred_P s1 s3 \/ s1 = s3) /\ (pred_rel pred_P s2 s3 \/ s2 = s3)) by (eapply ord_ru; mauto).
  destruct_conjs.
  exists env_relΓ.
  split; mauto.
  intros.
  assert (exists elem_rel : relation (domain P), rel_typ_unsorted pred_P {{{ Π r A B }}} ρ {{{ Π r A B }}} ρ' elem_rel /\ rel_exp M ρ M' ρ' elem_rel) by mauto.
  destruct_conjs.
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp).

  assert (exists aρ, a = d{{{ Π r aρ ρ B }}}).
  {
    inversion H4.
    exists a0.
    assert ({{ ⟦ Π r A B ⟧ ρ ↘ Π r a0 ρ B }}) by (econstructor; mauto).
    functional_eval_rewrite_clear.
    reflexivity.
  }
  assert (exists aρ', a' = d{{{ Π r aρ' ρ' B }}}).
  {
    inversion H6.
    exists a0.
    assert ({{ ⟦ Π r A B ⟧ ρ' ↘ Π r a0 ρ' B }}) by (econstructor; mauto).
    functional_eval_rewrite_clear.
    reflexivity.
  }
  destruct_conjs; subst.
  rename H10 into a.
  rename H11 into a'.
  inversion_clear H7.
  invert_per_sort_elems.
  exists in_rel; exists out_rel.
  repeat split; mauto.
  - econstructor.
    + inversion H4; mauto.
    + inversion H6; mauto.
    + destruct equiv_a_a'.
      destruct H0.
      * eapply H12; mauto.
      * rewrite -> H0.
        eapply H11; mauto.
  - intros.
    assert (rel_mod_eval
      (fun (R : relation (domain P)) (b b' : domain P) =>
       (s2 = s3 -> per_sort_elem pred_P s3 R b b') /\
       (pred_rel pred_P s2 s3 -> per_sort_elem pred_P s2 R b b')) B d{{{
      ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (out_rel c c' equiv_c_c')) by mauto.
    unfold rel_typ.
    inversion_clear H11.
    destruct_conjs.
    econstructor; mauto.
    destruct H1.
    + eapply H14; mauto.
    + rewrite -> H1.
      eapply H11; mauto.
  - handle_per_sort_elem_irrel.
    econstructor; mauto.
Qed.


Lemma rel_exp_unsorted_app_cong {P : PtsSig} {pred_P : PredicativeSig P} : forall {s1 s2 s3} {r : Ru P s1 s2 s3} {Γ M M' A B N N'},
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : Π r A B }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u N ≈ N' : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M N ≈ M' N' : B[Id,,N] }}.
Proof with intuition.
  intros * [env_relΓ]%rel_exp_unsorted_of_pi_inversion [].
  destruct_conjs.
  pose env_relΓ.
  handle_per_ctx_env_irrel.
  eexists; split; [eassumption |].
  intros.
  assert (equiv_p'_p' : env_relΓ ρ' ρ') by (etransitivity; [symmetry |]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  handle_per_sort_elem_irrel.
  assert (per_typ_elem pred_P in_rel0 a2 a2) by mauto.
  handle_per_typ_elem_irrel.
  assert (in_rel0 m1 m2) by (etransitivity; [| symmetry]; eassumption).
  assert (in_rel0 m1 m'2) by intuition.
  (on_all_hyp: destruct_rel_by_assumption in_rel0).
  handle_per_sort_elem_irrel.
  eexists.
  split; econstructor; mauto...
Qed.

#[export]
Hint Resolve rel_exp_unsorted_app_cong : mcpts.


Lemma rel_exp_unsorted_app_sub {P : PtsSig} {pred_P : PredicativeSig P} : forall {s1 s2 s3} {r : Ru P s1 s2 s3} {Γ σ Δ M A B N},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨u M : Π r A B }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨u N : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof with mautosolve.
  intros * [env_relΓ] [env_relΔ]%rel_exp_unsorted_of_pi_inversion [].
  destruct_conjs.
  pose env_relΓ.
  pose env_relΔ.
  handle_per_ctx_env_irrel.
  eexists; split; [eassumption|].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_typ_unsorted P).
  handle_per_sort_elem_irrel.
  assert (per_typ_elem pred_P in_rel a0 a'0) by mauto.
  handle_per_typ_elem_irrel.
  destruct_by_head (@rel_exp P).
  (on_all_hyp_rev: destruct_rel_by_assumption in_rel).
  eexists.
  split; econstructor...
Qed.

#[export]
Hint Resolve rel_exp_unsorted_app_sub : mcpts.


Lemma rel_exp_unsorted_pi_beta {P : PtsSig} {pred_P : PredicativeSig P} : forall {s1 s2 s3} {r : Ru P s1 s2 s3} {Γ A M B N},
    {{ ⟪ pred_P ⟫ Γ, A@s1 ⊨u M : B }} ->
    {{ ⟪ pred_P ⟫ Γ, A@s1 ⊨u B : Sort@s2 }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u N : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u (λ r A M) N ≈ M[Id,,N] : B[Id,,N] }}.
Proof with mautosolve.
  intros * [env_relΓA] [env_relΓA']%rel_exp_unsorted_of_typ_inversion1 [env_relΓ].
  destruct_conjs.
  pose env_relΓA.
  invert_per_ctx_envs.
  handle_per_ctx_env_irrel.
  eexists; split; [eassumption|].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_typ_unsorted P).
  handle_per_sort_elem_irrel.
  destruct_by_head (@rel_exp P).
  assert (per_typ_elem pred_P (head_rel ρ ρ' equiv_ρ_ρ') a a') by mauto.
  handle_per_typ_elem_irrel.
  rename m into n.
  rename m' into n'.
  assert (Hequiv : {{ Dom ρ ↦ n ≈ ρ' ↦ n' ∈ env_relΓA }}).
  {
    apply_relation_equivalence.
    econstructor; mauto; econstructor; mauto.
  }
  apply_relation_equivalence;
    (on_all_hyp: fun H => destruct (H _ _ Hequiv));
    destruct_conjs;
    destruct_by_head (@rel_typ P);
    destruct_by_head (@rel_typ_unsorted P);
    destruct_by_head (@rel_exp P).
  eexists.
  split; econstructor...
Qed.

#[export]
Hint Resolve rel_exp_unsorted_pi_beta : mcpts.


Lemma rel_exp_unsorted_pi_eta {P : PtsSig} {pred_P : PredicativeSig P} : forall {s1 s2 s3} {r : Ru P s1 s2 s3} {Γ M A B},
  {{ ⟪ pred_P ⟫ Γ ⊨u M : Π r A B }} ->
  {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ λ r A (M[Wk] #0) : Π r A B }}.
Proof with mautosolve.
  intros * [env_relΓ]%rel_exp_unsorted_of_pi_inversion.
  destruct_conjs.
  pose env_relΓ.
  eexists_rel_exp_unsorted_of_pi.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp P).
  do 2 eexists.
  repeat split; only 1,3: econstructor; mauto.
  intros.
  (on_all_hyp: destruct_rel_by_assumption in_rel).
  repeat (econstructor; mauto).
Qed.

#[export]
Hint Resolve rel_exp_unsorted_pi_eta : mcpts.
