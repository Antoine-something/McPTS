From Coq Require Import Morphisms_Relations Relation_Definitions.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import LogicalRelation TermStructureCases SortCases.
Import Domain_Notations.

#[local]
Ltac clear_pi_sort_eq_and_pred_rel1 :=
  match goal with
  | [r : Ru_pi ?P ?s1 _ ?s3,
     sub : st_subtyp ?s3 ?s,
     H1 : ?s1 = ?s -> ?Ps,
     H2 : pred_rel ?pred_P ?s1 ?s -> ?Ps1 |- _] => 
      assert Ps1 by (pose proof ord_ru_pi_sub pred_P r sub as [[] ?]; subst; mauto 2);
      clear H1 H2
  | [r : Ru_pi ?P ?s1 _ ?s3,
     sub : st_subtyp ?s3 ?s,
     H : (?s1 = ?s -> ?Ps) /\ (pred_rel ?pred_P ?s1 ?s -> ?Ps1) |- _] => 
      destruct H;
      assert Ps1 by (pose proof ord_ru_pi_sub pred_P r sub as [[] ?]; subst; mauto 2);
      clear H
  | [r : Ru_pi ?P _ ?s2 ?s3,
     sub : st_subtyp ?s3 ?s,
     H1 : ?s2 = ?s -> ?Ps,
     H2 : pred_rel ?pred_P ?s2 ?s -> ?Ps2 |- _] => 
      assert Ps2 by (pose proof ord_ru_pi_sub pred_P r sub as [? []]; subst; mauto 2);
      clear H1 H2
  | [r : Ru_pi ?P _ ?s2 ?s3,
     sub : st_subtyp ?s3 ?s,
     H : (?s2 = ?s -> ?Ps) /\ (pred_rel ?pred_P ?s2 ?s -> ?Ps2) |- _] => 
      destruct H;
      assert Ps2 by (pose proof ord_ru_pi_sub pred_P r sub as [? []]; subst; mauto 2);
      clear H
  end.

#[global]
Ltac clear_pi_sort_eq_and_pred_rel := repeat clear_pi_sort_eq_and_pred_rel1.

Lemma rel_exp_of_pi_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ M M' A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ M' : Π r A B }} ->
    exists env_rel,
      {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P Δ ↘ env_rel }} /\
        forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
        exists in_rel out_rel,
          rel_typ_unsorted pred_P Δ A ρ A ρ' in_rel /\
            (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_typ_unsorted pred_P Δ B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (out_rel c c' equiv_c_c')) /\
            rel_exp Δ M ρ M' ρ'
              (fun f f' : domain P => forall (c c' : domain P) (equiv_c_c' : in_rel c c'), rel_mod_app Δ f c f' c' (out_rel c c' equiv_c_c')).
Proof.
  intros * [env_relΓ []].
  exists env_relΓ.
  split; mauto 2.
  intros.
  pose proof (H0 _ _ equiv_ρ_ρ') as [elem_rel []].
  destruct_rel_typ_unsorted.
  simplify_evals.
  match_by_head (@per_typ_elem) ltac:(fun H => directed inversion_clear H).
  pose proof H5.
  match_by_head (@per_sort_elem) ltac:(fun H => invert_per_sort_elem H).
  clear_pi_sort_eq_and_pred_rel.
  handle_per_sort_elem_irrel.

  do 2 eexists; repeat split.
  - eexists; mauto 2.
  - intros.
    destruct_rel_mod_eval.
    simplify_evals.
    clear_pi_sort_eq_and_pred_rel.
    eexists; mauto 2.
  - destruct_by_head (@rel_exp).
    eexists; mauto 2.
Qed.

Lemma rel_exp_of_pi {P} {pred_P : PredicativeSig P} : forall {Δ Γ env_rel M M' A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P Δ ↘ env_rel }} ->
    (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      exists in_rel out_rel,
        rel_exp Δ A ρ A ρ' (per_sort pred_P Δ s1) /\
          rel_typ_unsorted pred_P Δ A ρ A ρ' in_rel /\
          (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
              rel_exp Δ B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (per_sort pred_P Δ s2) /\
                rel_typ_unsorted pred_P Δ B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (out_rel c c' equiv_c_c')) /\
          rel_exp Δ M ρ M' ρ' (fun f f' => forall c c' (equiv_c_c' : in_rel c c'), rel_mod_app Δ f c f' c' (out_rel c c' equiv_c_c'))) ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ M' : Π r A B }}.
Proof.
  intros * HΓ H.
  eexists; split; try eassumption.
  intros.
  pose proof (H _ _ equiv_ρ_ρ') as [in_rel [out_rel [HAs1 [HA [HB]]]]].
  destruct_rel_typ_unsorted.
  destruct_by_head (@rel_exp).
  simplify_evals.
  match_by_head (@per_sort) ltac:(fun H => destruct H).
  assert (per_typ_elem pred_P Δ x m0 m'0) by mauto 2.
  handle_per_typ_elem_irrel.
  
  pose (fun f f' => forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_mod_app Δ f c f' c' (out_rel c c' equiv_c_c')) as elem_rel.
  exists elem_rel.
  split; mauto 2.
  econstructor; mauto 3.
  econstructor.
  per_sort_elem_econstructor; try reflexivity; mauto 2.
  - intros.
    pose proof (HB _ _ equiv_c_c') as [HBs2 HB'].
    destruct_rel_typ_unsorted.
    destruct_by_head (@rel_exp).
    simplify_evals.
    match_by_head (@per_sort) ltac:(fun H => destruct H).
    assert (per_typ_elem pred_P Δ x m1 m'1) by mauto 2.
    handle_per_typ_elem_irrel.
    econstructor; mauto 2.
  - reflexivity.
Qed.

      
    
(* Lemma rel_exp_of_pi {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ env_rel M M' s1 s2 s3 A B} {r : Ru_pi P s1 s2 s3}, *)
(*     {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P Δ ↘ env_rel }} -> *)
(*     (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}), *)
(*       exists in_rel out_rel, *)
(*         rel_typ_unsorted pred_P Δ A ρ A ρ' in_rel /\ *)
(*           (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_typ_unsorted pred_P Δ B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (out_rel c c' equiv_c_c')) /\ *)
(*           rel_exp Δ M ρ M' ρ' *)
(*             (fun f f' : domain P => forall (c c' : domain P) (equiv_c_c' : in_rel c c'), rel_mod_app Δ f c f' c' (out_rel c c' equiv_c_c'))) -> *)
(*     {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ M' : Π r A B }}. *)
(* Proof. *)
(*   intros. *)
(*   eexists_rel_exp. *)
(*   pose proof (H0 _ _ equiv_ρ_ρ') as [in_rel [out_rel [? []]]]. *)
(*   split. *)
(*   - destruct_rel_typ_unsorted. *)
(*     eexists; mauto 3. *)
(*   destruct_conjs. *)
(*   (* eexists_rel_exp_with (max i j). *) *)
(*   eexists_rel_exp_with s3. *)
(*   intros. *)
(*   (on_all_hyp: destruct_rel_by_assumption env_rel). *)
(*   match goal with *)
(*   | _: rel_typ pred_P s1 A ρ A ρ' ?x |- _ => *)
(*       rename x into in_rel *)
(*   end. *)
(*   destruct_by_head (@rel_typ P). *)
(*   destruct_by_head (@rel_exp P). *)
(*   exists (fun f f' : domain P => *)
(*    forall (c c' : domain P) (equiv_c_c' : in_rel c c'), *)
(*    rel_mod_app f c f' c' (out_rel c c' equiv_c_c')); split; econstructor; mauto. *)
(*   per_sort_elem_econstructor; mauto. *)
(*   reflexivity. *)
(* Qed. *)

Ltac eexists_rel_exp_of_pi :=
  unshelve eapply (rel_exp_of_pi _); shelve_unifiable; [eassumption |].

#[local]
Ltac extract_output_info_with P ρ c ρ' c' env_rel :=
  let Hequiv := fresh "equiv" in
  (assert (Hequiv : {{ Dom ρ ↦ c ≈ ρ' ↦ c' ∈ env_rel }}) by (apply_relation_equivalence; mauto 4);
   apply_relation_equivalence;
   (on_all_hyp: fun H => destruct (H _ _ Hequiv));
   destruct_conjs;
   destruct_by_head (@rel_typ_unsorted P);
   destruct_by_head (@rel_exp P)).

Lemma rel_exp_pi_core {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ s o B o' B' R out_rel},
    (forall c c',
        R c c' ->
        rel_exp Δ B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} (per_sort pred_P Δ s)) ->
    (** We use the next equality to make unification on `out_rel` works *)
    (out_rel = fun c c' (equiv_c_c' : R c c') m m' =>
                 forall R',
                   rel_typ_unsorted pred_P Δ B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} R' ->
                   R' m m') ->
    (forall c c' (equiv_c_c' : R c c'), rel_typ_unsorted pred_P Δ B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} (out_rel c c' equiv_c_c')).
Proof with intuition.
  intros.
  subst.
  (on_all_hyp: destruct_rel_by_assumption R).
  econstructor; mauto.
  destruct_by_head (@per_sort P).
  assert (per_typ_elem pred_P Δ x m m') by mauto 2.
  apply -> per_typ_elem_morphism_iff; eauto.
  split; intros; destruct_by_head (@rel_typ_unsorted P); handle_per_typ_elem_irrel...
  assert (rel_typ_unsorted pred_P Δ B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} _) by mauto.
  intuition.
Qed.

Lemma rel_exp_pi_core' {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ s o B o' B' R out_rel},
    (forall c c',
        R c c' ->
        rel_exp Δ B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} (per_sort pred_P Δ s)) ->
    (** We use the next equality to make unification on `out_rel` works *)
    (out_rel = fun c c' (equiv_c_c' : R c c') m m' =>
                 forall R',
                   rel_typ_unsorted pred_P Δ B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} R' ->
                   R' m m') ->
    (forall c c' (equiv_c_c' : R c c'), rel_mod_eval (per_sort_elem pred_P Δ s) Δ B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} (out_rel c c' equiv_c_c')).
Proof.
  intros.
  assert (forall c c' (equiv_c_c' : R c c'), rel_typ_unsorted pred_P Δ B d{{{ o ↦ c }}} B' d{{{ o' ↦ c' }}} (out_rel c c' equiv_c_c')) by (eapply rel_exp_pi_core; mauto 2).

  specialize (H _ _ equiv_c_c').
  specialize (H1 _ _ equiv_c_c').
  destruct_by_head (@rel_exp).
  destruct_rel_typ_unsorted.
  simplify_evals.
  destruct_by_head (@per_sort).
  assert (per_typ_elem pred_P Δ x m m') by mauto 2.
  handle_per_typ_elem_irrel.
  econstructor; mauto 2.
Qed.

(* Lemma rel_exp_unsorted_of_pi {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ env_rel M M' s1 s2 s3 A B} {r : Ru_pi P s1 s2 s3}, *)
(*     {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} -> *)
(* 	(forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}), *)
(*       exists in_rel out_rel, *)
(*         rel_typ pred_P s1 A ρ A ρ' in_rel /\ *)
(*           (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_typ pred_P s2 B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (out_rel c c' equiv_c_c')) /\ *)
(*           rel_exp M ρ M' ρ' *)
(*             (fun f f' : domain P => forall (c c' : domain P) (equiv_c_c' : in_rel c c'), rel_mod_app f c f' c' (out_rel c c' equiv_c_c'))) -> *)
(*     {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : Π r A B }}. *)
(* Proof. *)
(*   intros. *)
(*   assert ({{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : Π r A B }}) by (eapply rel_exp_of_pi; mauto). *)
(*   mauto. *)
(* Qed. *)

(* Ltac eexists_rel_exp_unsorted_of_pi := *)
(*   unshelve eapply (rel_exp_unsorted_of_pi _); shelve_unifiable; [eassumption |]. *)


Lemma rel_exp_unsorted_pi_cong {P} {pred_P : PredicativeSig P} : forall {Δ s1 s2 s3 Γ A A' B B'} {r : Ru_pi P s1 s2 s3},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u A : Sort@s1 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u A ≈ A' : Sort@s1 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ, A ⊨u B ≈ B' : Sort@s2 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u Π r A B ≈ Π r A' B' : Sort@s3 }}.
Proof.
  intros * [env_relΓ]%rel_exp_unsorted_of_typ_inversion1 []%rel_exp_unsorted_of_typ_inversion1 [env_relΓA]%rel_exp_unsorted_of_typ_inversion1.
  destruct_conjs.
  pose proof H1.
  invert_per_ctx_env H1.
  handle_per_ctx_env_irrel.
  rename x into env_relΓ.

  eexists; split; [eassumption|].
  intros.
  assert (rel_exp Δ A ρ A' ρ' (per_sort pred_P Δ s1)) by mauto.
  assert (rel_typ_unsorted pred_P Δ A ρ A ρ' (head_rel ρ ρ' equiv_ρ_ρ')) by mauto.
  destruct_by_head (@rel_exp P).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@per_sort P).
  functional_eval_rewrite_clear.
  assert (per_typ_elem pred_P Δ x m m') by mauto 2.
  handle_per_typ_elem_irrel.
  exists (per_sort pred_P Δ s3); split.
  - econstructor; mauto.
    econstructor; mauto.
    reflexivity.
  - repeat eexists; mauto 2.
    per_sort_elem_econstructor; try reflexivity; mauto 2.
    + intros.
      eapply rel_exp_pi_core'; eauto; try reflexivity.
      intros.
      mauto 3.
    + solve_refl.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_pi_cong : mcpts.


(* STOPPED HERE *)
Lemma rel_exp_unsorted_pi_sub {P : PtsSig} {pred_P : PredicativeSig P} : forall {s1 s2 s3} {r : Ru_pi P s1 s2 s3} {Δ Γ Γ' σ A B},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s σ : Γ' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ' ⊨u A : Sort@s1 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ', A ⊨u B : Sort@s2 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u (Π r A B)[σ] ≈ Π r (A[σ]) (B[q σ]) : Sort@s3 }}.
Proof with mautosolve.
  intros * [env_relΓ] [env_relΓ']%rel_exp_unsorted_of_typ_inversion1 []%rel_exp_unsorted_of_typ_inversion1.
  destruct_conjs.
  pose env_relΓ'.
  invert_per_ctx_envs.
  match goal with
  | _: _ <~> cons_per_ctx_env env_relΓ' ?x |- _ =>
      rename x into elem_relA
  end.
  handle_per_ctx_env_irrel.
  eexists_rel_exp_of_sort.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  rename H7 into equiv_ρσ_ρ'σ'.
  assert {{ Dom ρ'σ' ≈ ρ'σ' ∈ env_relΓ' }} by (etransitivity; [symmetry |]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  destruct_by_head (@per_sort P).
  handle_per_sort_elem_irrel.
  econstructor; mauto.
  eexists.
  assert (per_typ_elem pred_P Δ x0 a a) by mauto.
  assert (per_typ_elem pred_P Δ x0 a0 a) by mauto.
  handle_per_typ_elem_irrel.
  per_sort_elem_econstructor; eauto.
  - econstructor.
  - intros.
    eapply rel_exp_pi_core'; eauto; try reflexivity.
    intros.
    assert (Hequiv : {{ Dom ρσ ↦ c0 ≈ ρ'σ' ↦ c'0 ∈ (cons_per_ctx_env env_relΓ' elem_relA) }}) by (econstructor; mauto; econstructor; mauto).
    apply_relation_equivalence;     
      (on_all_hyp: fun H => destruct (H _ _ Hequiv));
      destruct_conjs;
      destruct_by_head (@rel_typ_unsorted P);
      destruct_by_head (@rel_exp P).
    repeat (econstructor; mauto).        
  - solve_refl.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_pi_sub : mcpts.


Lemma rel_exp_unsorted_fn_cong {P : PtsSig} {pred_P : PredicativeSig P} : forall {s1 s2 s3} {r : Ru_pi P s1 s2 s3} {Δ Γ A A' B B' M M'},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u A ≈ A' : Sort@s1 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ, A ⊨u B ≈ B' : Sort@s2 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ, A ⊨u M ≈ M' : B }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u λ r A B M ≈ λ r A' B' M' : Π r A B }}.
Proof with mautosolve.
    intros * [env_relΓ]%rel_exp_unsorted_of_typ_inversion1 [env_relΓA]%rel_exp_unsorted_of_typ_inversion1 [] .
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
    assert (rel_typ_unsorted pred_P Δ A ρ A ρ' (head_rel ρ ρ' equiv_ρ_ρ')) by mauto.
    assert (rel_typ_unsorted pred_P Δ A ρ A ρ' (elem_relA ρ ρ' equiv_ρ_ρ')) by mauto.
    destruct_by_head (@rel_typ_unsorted P).
    functional_eval_rewrite_clear.
    handle_per_typ_elem_irrel.
    reflexivity.
  }
  eexists_rel_exp_of_pi.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@per_sort P).
  functional_eval_rewrite_clear.
  do 2 eexists.

  
  repeat split; [econstructor | econstructor | | | econstructor]; mauto.
    - destruct_rel_typ_unsorted.
      simplify_evals.
      assert (per_typ_elem pred_P Δ x a m') by mauto 2.
      handle_per_typ_elem_irrel.
      assert (cons_per_ctx_env env_relΓ head_rel d{{{ ρ ↦ c }}} d{{{ ρ' ↦ c'}}}) as equiv_ρc_ρ'c' by mauto 3.
      pose proof (H2 _ _ equiv_ρc_ρ'c') as [elem_relB []].
      destruct_rel_typ_unsorted.
      simplify_evals.
      eexists; mauto 2.
      assert (cons_per_ctx_env env_relΓ elem_relA d{{{ ρ ↦ c }}} d{{{ ρ' ↦ c'}}}) as equiv'_ρc_ρ'c'.
      {
        econstructor; mauto 3.
        apply H11; mauto 2.
      }
      pose proof (H3 _ _ equiv'_ρc_ρ'c').
      destruct_by_head (@rel_exp).
      simplify_evals.
      destruct_by_head (@per_sort).
      assert (per_sort_elem pred_P Δ s2 elem_relB a0 a'0) by mauto 2.
      eexists; mauto 2.

  - eapply rel_exp_pi_core; eauto; try reflexivity.
    intros.
    assert (Hequiv : {{ Dom ρ ↦ c0 ≈ ρ' ↦ c'0 ∈ (cons_per_ctx_env env_relΓ elem_relA) }}).
    {
      assert (exists R'', per_sort_elem pred_P Δ s1 R'' a a') by mauto.
      destruct_conjs.
      econstructor; mauto.
      simpl; mauto.
      handle_per_sort_elem_irrel.
      handle_per_typ_elem_irrel.
      apply_relation_equivalence.
      eapply H10; mauto.
    }
    assert (Hequiv' : {{ Dom ρ ↦ c0 ≈ ρ' ↦ c'0 ∈ (cons_per_ctx_env env_relΓ head_rel) }}).
    {
      assert (exists R'', per_sort_elem pred_P Δ s1 R'' a a') by mauto.
      destruct_conjs.
      econstructor; mauto.
    }
    apply_relation_equivalence;
      (on_all_hyp: fun H => destruct (H _ _ Hequiv));
      (on_all_hyp: fun H => destruct (H _ _ Hequiv'));
      destruct_conjs;
      destruct_by_head (@rel_typ_unsorted P);
      destruct_by_head (@rel_exp P);
      destruct_by_head (@per_sort P).
    
    handle_per_typ_elem_irrel.
    econstructor...
    
  - intros.
    assert (Hequiv : {{ Dom ρ ↦ c ≈ ρ' ↦ c' ∈ (cons_per_ctx_env env_relΓ elem_relA) }}).
    {
      econstructor; mauto.
      simpl; mauto.
      handle_per_sort_elem_irrel.
      handle_per_typ_elem_irrel.
      apply_relation_equivalence.
      eapply H9; mauto.
    }
    extract_output_info_with P ρ c ρ' c' (cons_per_ctx_env env_relΓ elem_relA).


    assert (exists elem_rel : relation (domain P),
               rel_typ_unsorted pred_P Δ B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} elem_rel /\ rel_exp Δ M d{{{ ρ ↦ c }}} M' d{{{ ρ' ↦ c' }}} elem_rel) by mauto.

    destruct_conjs.
    destruct_by_head (@rel_exp).
    econstructor; mauto.

    intros.
    destruct_by_head (@rel_typ_unsorted P).
    handle_per_sort_elem_irrel.
    handle_per_typ_elem_irrel.
    mauto 2.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_fn_cong : mcpts.


Lemma rel_exp_unsorted_fn_sub {P : PtsSig} {pred_P : PredicativeSig P} : forall {s1 s2 s3} {r : Ru_pi P s1 s2 s3} {Δ Γ Γ' σ A M B},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s σ : Γ' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ' ⊨u A : Sort@s1 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ', A ⊨u M : B }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ', A ⊨u B : Sort@s2 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u (λ r A B M)[σ] ≈ λ r A[σ] B[q σ] M[q σ] : (Π r A B)[σ] }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΓ']]] [env_relΓ'']%rel_exp_unsorted_of_typ_inversion1 [env_relΓ'A] [env_relΓ'A']%rel_exp_unsorted_of_typ_inversion1.
  destruct_conjs.
  pose env_relΓ'A.
  invert_per_ctx_envs.
  handle_per_ctx_env_irrel.
  eexists; split; [eassumption|].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ'').
  simplify_evals.
  inversion_clear H19.

  assert (rel_typ_unsorted pred_P Δ A ρσ A ρ'σ' (head_rel ρσ ρ'σ' H10)) by mauto.
  assert (rel_typ_unsorted pred_P Δ A ρσ A ρ'σ' (head_rel0 ρσ ρ'σ' H10)) by mauto.
  destruct_by_head (@rel_typ_unsorted P).
  simplify_evals.
  handle_per_typ_elem_irrel.

  eexists.
  split; econstructor; mauto 4.
  - econstructor; mauto.
    per_sort_elem_econstructor; [econstructor | | | apply Equivalence_Reflexive]; eauto.
    intros.
    eapply rel_exp_pi_core'; eauto; try reflexivity.
    clear dependent c.
    clear dependent c'.
    intros.

    assert (per_sort_elem pred_P Δ s1 (head_rel0 ρσ ρ'σ' H10) a a') by mauto.
    handle_per_sort_elem_irrel.
    assert (Hequiv : {{ Dom ρσ ↦ c ≈ ρ'σ' ↦ c' ∈ env_relΓ'A }}).
    {
      apply_relation_equivalence.
      econstructor; mauto.
      simpl; mauto.
      handle_per_typ_elem_irrel.
      eapply H17; mauto.
    }
    apply_relation_equivalence;
      (on_all_hyp: fun H => destruct (H _ _ Hequiv));
      destruct_conjs;
      destruct_by_head (@rel_typ_unsorted P);
      destruct_by_head (@rel_exp P).

    econstructor; eauto.

    assert (rel_exp Δ B d{{{ ρσ ↦ c }}} B d{{{ ρ'σ' ↦ c' }}} (per_sort pred_P Δ s2)) by mauto.
    destruct_by_head (@rel_exp P).
    functional_eval_rewrite_clear.
    assumption.

  - intros ? **.
    assert (per_sort_elem pred_P Δ s1 (head_rel0 ρσ ρ'σ' H10) a a') by mauto.
    assert (Hequiv : {{ Dom ρσ ↦ c ≈ ρ'σ' ↦ c' ∈ env_relΓ'A }}).
    {
      apply_relation_equivalence.
      econstructor; mauto.
      simpl; mauto.
      handle_per_sort_elem_irrel.
      apply_relation_equivalence.
      eapply H16; mauto.
    }
    apply_relation_equivalence;
      (on_all_hyp: fun H => destruct (H _ _ Hequiv));
      destruct_conjs;
      destruct_by_head (@rel_typ_unsorted P);
      destruct_by_head (@rel_exp P).

    econstructor; mauto; [repeat (econstructor; mauto)|].
    intros.
    destruct_by_head (@rel_typ_unsorted P).
    assert (per_typ_elem pred_P Δ R' a1 a'1) by mauto.
    functional_eval_rewrite_clear.
    handle_per_typ_elem_irrel...
Qed.

#[export]
Hint Resolve rel_exp_unsorted_fn_sub : mcpts.

Lemma pred_preserves_st {P : PtsSig} {pred_P : PredicativeSig P} : forall s s1 s2,
    st_subtyp s1 s2 ->
    pred_rel pred_P s s1 ->
    pred_rel pred_P s s2.
Proof.
  intros.
  assert (Transitive (pred_rel pred_P)) by (eapply (ord_rel pred_P)).
  specialize (ord_st_subtyp pred_P H) as ?.
  destruct H2; mauto.
  subst; mauto.
Qed.

#[local]
Hint Resolve pred_preserves_st : mcpts.

(* Lemma rel_exp_unsorted_of_pi_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' A B s1 s2 s3} {r : Ru_pi P s1 s2 s3}, *)
(*     {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ M' : Π r A B }} -> *)
(*     exists env_rel, *)
(*       {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} /\ *)
(*         forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}), *)
(*         exists in_rel out_rel, *)
(*           rel_typ pred_P s1 A ρ A ρ' in_rel /\ *)
(*             (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_typ pred_P s2 B d{{{ ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (out_rel c c' equiv_c_c')) /\ *)
(*             rel_exp M ρ M' ρ' *)
(*               (fun f f' : domain P => forall (c c' : domain P) (equiv_c_c' : in_rel c c'), rel_mod_app f c f' c' (out_rel c c' equiv_c_c')). *)
(* Proof. *)
(*   intros * [env_relΓ]. *)
(*   assert ((pred_rel pred_P s1 s3 \/ s1 = s3) /\ (pred_rel pred_P s2 s3 \/ s2 = s3)) by (eapply ord_ru_pi; mauto). *)
(*   destruct_conjs. *)
(*   exists env_relΓ. *)
(*   split; mauto. *)
(*   intros. *)
(*   assert (exists elem_rel : relation (domain P), rel_typ_unsorted pred_P {{{ Π r A B }}} ρ {{{ Π r A B }}} ρ' elem_rel /\ rel_exp M ρ M' ρ' elem_rel) by mauto. *)
(*   destruct_conjs. *)
(*   destruct_by_head (@rel_typ_unsorted P). *)
(*   destruct_by_head (@rel_exp). *)

(*   assert (exists aρ, a = d{{{ Π r aρ ρ B }}}). *)
(*   { *)
(*     inversion H4. *)
(*     exists a0. *)
(*     assert ({{ ⟦ Π r A B ⟧ ρ ↘ Π r a0 ρ B }}) by (econstructor; mauto). *)
(*     functional_eval_rewrite_clear. *)
(*     reflexivity. *)
(*   } *)
(*   assert (exists aρ', a' = d{{{ Π r aρ' ρ' B }}}). *)
(*   { *)
(*     inversion H6. *)
(*     exists a0. *)
(*     assert ({{ ⟦ Π r A B ⟧ ρ' ↘ Π r a0 ρ' B }}) by (econstructor; mauto). *)
(*     functional_eval_rewrite_clear. *)
(*     reflexivity. *)
(*   } *)
(*   destruct_conjs; subst. *)
(*   rename H10 into a. *)
(*   rename H11 into a'. *)
(*   inversion_clear H7. *)
(*   invert_per_sort_elems. *)
(*   exists in_rel; exists out_rel. *)
(*   repeat split; mauto. *)
(*   - econstructor. *)
(*     + inversion H4; mauto. *)
(*     + inversion H6; mauto. *)
(*     + destruct equiv_a_a'. *)
(*       destruct H0. *)
(*       * eapply H12; mauto. *)
(*       * specialize (ord_st_subtyp pred_P sub) as ?. *)
(*         destruct H13. *)
(*         ** eapply H12; subst; mauto. *)
(*         ** subst. *)
(*            eapply H11; reflexivity. *)
(*   - intros. *)
(*     assert (rel_mod_eval *)
(*       (fun (R : relation (domain P)) (b b' : domain P) => *)
(*        (s2 = s -> per_sort_elem pred_P s R b b') /\ *)
(*        (pred_rel pred_P s2 s -> per_sort_elem pred_P s2 R b b')) B d{{{ *)
(*             ρ ↦ c }}} B d{{{ ρ' ↦ c' }}} (out_rel c c' equiv_c_c')) by mauto. *)
(*     unfold rel_typ. *)
(*     inversion_clear H11. *)
(*     destruct_conjs. *)
(*     econstructor; mauto. *)
(*     destruct H1. *)
(*     + eapply H14; mauto. *)
(*     + specialize (ord_st_subtyp pred_P sub) as ?. *)
(*       destruct H17; subst; mauto. *)
(*   - handle_per_sort_elem_irrel. *)
(*     econstructor; mauto. *)
(* Qed. *)


Lemma rel_exp_unsorted_app_cong {P : PtsSig} {pred_P : PredicativeSig P} : forall {s1 s2 s3} {r : Ru_pi P s1 s2 s3} {Δ Γ M M' A B N N'},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ M' : Π r A B }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u N ≈ N' : A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M N ≈ M' N' : B[Id,,N] }}.
Proof with intuition.
  intros * [env_relΓ]%rel_exp_of_pi_inversion [].
  destruct_conjs.
  pose env_relΓ.
  handle_per_ctx_env_irrel.
  eexists; split; [eassumption |].
  intros.
  assert (equiv_p'_p' : env_relΓ ρ' ρ') by (etransitivity; [symmetry |]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  handle_per_sort_elem_irrel.
  (* assert (per_typ_elem pred_P Δ in_rel0 a2 a2) by mauto. *)
  handle_per_typ_elem_irrel.
  assert (in_rel0 m1 m2) by (etransitivity; [| symmetry]; eassumption).
  (* assert (in_rel0 m1 m'2) by intuition. *)
  (on_all_hyp: destruct_rel_by_assumption in_rel0).
  handle_per_typ_elem_irrel.

  destruct_rel_mod_app.
  destruct_rel_typ_unsorted.
  simplify_evals.
  handle_per_typ_elem_irrel.
  
  eexists.
  split; econstructor; mauto...
Qed.

#[export]
Hint Resolve rel_exp_unsorted_app_cong : mcpts.


Lemma rel_exp_unsorted_app_sub {P : PtsSig} {pred_P : PredicativeSig P} : forall {s1 s2 s3} {r : Ru_pi P s1 s2 s3} {Δ Γ σ Γ' M A B N},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s σ : Γ' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ' ⊨u M : Π r A B }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ' ⊨u N : A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof with mautosolve.
  intros * [env_relΓ] [env_relΓ']%rel_exp_of_pi_inversion [].
  destruct_conjs.
  pose env_relΓ.
  pose env_relΓ'.
  handle_per_ctx_env_irrel.
  eexists; split; [eassumption|].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  destruct_rel_typ_unsorted.
  handle_per_typ_elem_irrel.
  (* assert (per_typ_elem pred_P in_rel a0 a'0) by mauto. *)
  (* handle_per_typ_elem_irrel. *)
  destruct_by_head (@rel_exp P).
  (on_all_hyp_rev: destruct_rel_by_assumption in_rel).
  eexists.
  split; econstructor...
Qed.

#[export]
Hint Resolve rel_exp_unsorted_app_sub : mcpts.


Lemma rel_exp_unsorted_pi_beta {P : PtsSig} {pred_P : PredicativeSig P} : forall {s1 s2 s3} {r : Ru_pi P s1 s2 s3} {Δ Γ A M B N},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ, A ⊨u M : B }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ, A ⊨u B : Sort@s2 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u N : A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u (λ r A B M) N ≈ M[Id,,N] : B[Id,,N] }}.
Proof with mautosolve.
  intros * [env_relΓA] [env_relΓA']%rel_exp_unsorted_of_typ_inversion1 [env_relΓ].
  destruct_conjs.
  pose env_relΓA.
  invert_per_ctx_envs.
  handle_per_ctx_env_irrel.
  eexists; split; [eassumption|].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_rel_typ_unsorted.
  handle_per_sort_elem_irrel.
  handle_per_typ_elem_irrel.
  destruct_by_head (@rel_exp P).
  (* assert (per_typ_elem pred_P (head_rel ρ ρ' equiv_ρ_ρ') a a') by mauto. *)
  (* handle_per_typ_elem_irrel. *)
  rename m into n.
  rename m' into n'.
  assert (Hequiv : {{ Dom ρ ↦ n ≈ ρ' ↦ n' ∈ env_relΓA }}).
  {
    apply_relation_equivalence.
    econstructor; mauto 3.
    simpl.
    apply H9.
    mauto 2.
  }
  apply_relation_equivalence;
    (on_all_hyp: fun H => destruct (H _ _ Hequiv));
    destruct_conjs;
    destruct_by_head (@rel_typ_unsorted P);
    destruct_by_head (@rel_exp P).
  eexists.
  split; econstructor...
Qed.

#[export]
Hint Resolve rel_exp_unsorted_pi_beta : mcpts.


Lemma rel_exp_unsorted_pi_eta {P : PtsSig} {pred_P : PredicativeSig P} : forall {s1 s2 s3} {r : Ru_pi P s1 s2 s3} {Δ Γ M A B},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u A : Sort@s1 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ, A ⊨u B : Sort@s2 }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M : Π r A B }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M ≈ λ r A B (M[Wk] #0) : Π r A B }}.
Proof with mautosolve.
  intros * []%rel_exp_unsorted_of_typ_inversion1 [env_relΓA]%rel_exp_unsorted_of_typ_inversion1 [env_relΓ]%rel_exp_of_pi_inversion.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  rename x into env_relΓ.
  pose env_relΓ.
  eexists_rel_exp_of_pi.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_rel_typ_unsorted.

  pose proof (H4 _ _ equiv_ρ_ρ').
  destruct_by_head (@rel_exp P).
  simplify_evals.
  destruct_by_head (@per_sort).
  assert (per_sort_elem pred_P Δ s1 in_rel a a') by mauto 2.

  pose proof (H2 _ _ equiv_ρ_ρ') as [in_rel' [out_rel' [? []]]].
  
  do 2 eexists.
  repeat split; try solve [econstructor; mauto]; mauto 2.

  - eapply H3.
    invert_per_ctx_env H0.
    handle_per_ctx_env_irrel.
    destruct_rel_typ_unsorted.
    simplify_evals.
    handle_per_typ_elem_irrel.
    econstructor; mauto 3.
    simpl.
    apply H18.
    mauto 2.
  - destruct_by_head (@rel_exp).
    simplify_evals.
    econstructor; mauto 3.
    intros.
    destruct_rel_mod_app.
    econstructor; mauto 2.
    econstructor.
    econstructor; mauto 3.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_pi_eta : mcpts.
