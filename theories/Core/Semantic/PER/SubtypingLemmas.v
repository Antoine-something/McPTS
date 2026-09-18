From Coq Require Import Equivalence Lia Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Import System.
From McPTS.Core.Semantic Require Import PER.Definitions PER.CoreTactics PER.CoreLemmas PER.SortLemmas PER.TypeLemmas.
Import Domain_Notations.

(** * Lemmas related to semantic subtyping *)

(** Subtyping only applies to well-formed types *)
Lemma per_subtyp_sorted_to_sort_elem {P} {pred_P : PredicativeSig P} : forall a b,
    (* This is needed to find a sort for the neutral case *)
    (* It might be better to include a rule for neutrals directly in per_typ_elem, although this could potentially break functionality *)
    (exists s : P, True) ->
    {{ SubT a <: b ∈ per_subtyp pred_P }} ->
    exists R R',
      {{ DF a ≈ a ∈ per_typ_elem pred_P ↘ R }} /\
        {{ DF b ≈ b ∈ per_typ_elem pred_P ↘ R' }}.
Proof.
  intros * [s] [].
  - repeat eexists; econstructor; reflexivity.
  - repeat eexists; econstructor;
      per_sort_elem_econstructor; mauto 2; reflexivity.
  - repeat eexists; econstructor; try eassumption.
  - repeat eexists;
      unshelve econstructor; try eassumption; shelve_unifiable;
      per_sort_elem_econstructor; mauto 2; try reflexivity;
      etransitivity; try eassumption; symmetry; eassumption.
Qed.

(** Subtypes are represented as sub-relations *)
Lemma per_elem_subtyping {P} {pred_P : PredicativeSig P} : forall a b,
    {{ SubT a <: b ∈ per_subtyp pred_P }} ->
    forall R R' m n,
      {{ DF a ≈ a ∈ per_typ_elem pred_P ↘ R }} ->
      {{ DF b ≈ b ∈ per_typ_elem pred_P ↘ R' }} ->
      R m n ->
      R' m n.
Proof.
  induction 1; intros * Ha Hb.
  - assert (per_typ_elem pred_P (per_sort pred_P s1) d{{{ Sort@s1 }}} d{{{ Sort@s1 }}}) by (econstructor; try reflexivity).
    assert (per_typ_elem pred_P (per_sort pred_P s2) d{{{ Sort@s2 }}} d{{{ Sort@s2 }}}) by (econstructor; try reflexivity).
    handle_per_typ_elem_irrel.
    unfold per_sort; intros [R].
    assert (per_sort_elem pred_P s2 R m n) by mauto 2.
    mauto 2.

  - inversion_clear Ha; inversion_clear Hb.
    handle_per_sort_elem_irrel.
    mauto 2.
  - saturate_refl.
    handle_per_typ_elem_per_sort_elem_irrel.
    invert_per_sort_elems.
    destruct_conjs.
    clear_pi_sort_eq_and_pred_rel.
    handle_per_sort_elem_irrel.

    intros.
    rename equiv_n_n' into equiv0_n0_n'.
    assert (in_rel0 n0 n') as equiv_n0_n' by intuition.    
    destruct_rel_mod_eval.
    clear_pi_sort_eq_and_pred_rel.
    saturate_refl_for (@per_sort_elem P).

    destruct_rel_mod_app.
    econstructor; mauto 2.
    eapply H1; mauto 2.    
    
  - inversion_clear Ha; inversion_clear Hb.
    invert_per_sort_elems.
    apply_relation_equivalence.
    mauto 2.
Qed.

Lemma per_elem_subtyping_gen {P} {pred_P : PredicativeSig P} : forall a b a' b' R R' m n,
    {{ SubT a <: b ∈ per_subtyp pred_P }} ->
    {{ DF a ≈ a' ∈ per_typ_elem pred_P ↘ R }} ->
    {{ DF b ≈ b' ∈ per_typ_elem pred_P ↘ R' }} ->
    R m n ->
    R' m n.
Proof.
  intros.
  eapply per_elem_subtyping; saturate_refl; try eassumption.
Qed.

(** Subtyping is reflexive *)
Lemma per_subtyp_sorted_refl1 {P} {pred_P : PredicativeSig P} : forall s a b R,
    {{ DF a ≈ b ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ SubT a <: b ∈ per_subtyp pred_P }}.
Proof.  
  simpl; induction 1 using per_sort_elem_ind;
    subst;
    mauto;
    destruct_all.
  - assert ({{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P s_elem ↘ elem_rel }})
      by (per_sort_elem_econstructor; intuition; destruct_rel_mod_eval; mauto).
    saturate_refl_for (@per_sort_elem P).
    econstructor; eauto.
    intros;
      destruct_rel_mod_eval;
      functional_eval_rewrite_clear;
      trivial.
Qed.

#[export]
Hint Resolve per_subtyp_sorted_refl1 : mcpts.

Lemma per_subtyp_sorted_refl2 {P} {pred_P : PredicativeSig P} : forall s a b R,
    {{ DF a ≈ b ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ SubT b <: a ∈ per_subtyp pred_P }}.
Proof.
  intros.
  symmetry in H.
  eauto using per_subtyp_sorted_refl1.
Qed.

#[export]
Hint Resolve per_subtyp_sorted_refl2 : mcpts.

Lemma per_subtyp_refl1 {P} {pred_P : PredicativeSig P} : forall a b R,
    {{ DF a ≈ b ∈ per_typ_elem pred_P ↘ R }} ->
    {{ SubT a <: b ∈ per_subtyp pred_P }}.
Proof.
  destruct 1.
  - econstructor; reflexivity.
  - eapply per_subtyp_sorted_refl1; mauto 2.
Qed.

#[export]
Hint Resolve per_subtyp_refl1 : mcpts.

Lemma per_subtyp_refl2 {P} {pred_P : PredicativeSig P} : forall a b R,
    {{ DF a ≈ b ∈ per_typ_elem pred_P ↘ R }} ->
    {{ SubT b <: a ∈ per_subtyp pred_P }}.
Proof.
  intros.
  symmetry in H.
  eauto using per_subtyp_refl1.
Qed.

#[export]
Hint Resolve per_subtyp_refl2 : mcpts.

(** Subtyping is transitive *)
Lemma per_subtyp_trans {P} {pred_P : PredicativeSig P} : forall a1 a2,
    {{ SubT a1 <: a2 ∈ per_subtyp pred_P }} ->
    forall a3,
      {{ SubT a2 <: a3 ∈ per_subtyp pred_P }} ->
      {{ SubT a1 <: a3 ∈ per_subtyp pred_P }}.
Proof.
  induction 1; intros ? Hsub; simpl in *.
  1,2,4: progressive_inversion; mauto.
  - econstructor; mauto 2.
    transitivity s2; mauto 2.
  - dependent destruction Hsub; subst.
    handle_per_sort_elem_irrel.
    unshelve econstructor; only 4: auto; shelve_unifiable; eauto.
    + etransitivity; eassumption.
    + intros.
      saturate_refl_for (@per_sort_elem P).
      saturate_refl_for in_rel0.
      (on_all_hyp: fun H => directed invert_per_sort_elem H).
      destruct_conjs.
      clear_pi_sort_eq_and_pred_rel.
      handle_per_sort_elem_irrel.
      rename H21 into equiv3_c_c, H22 into equiv3_c'_c'.
      assert (in_rel c c) as equiv_c_c by intuition.
      assert (in_rel1 c c) as equiv1_c_c by intuition.
      assert (in_rel2 c c) as equiv2_c_c by intuition.
      assert (in_rel c' c') as equiv_c'_c' by intuition.
      assert (in_rel1 c' c') as equiv1_c'_c' by intuition.
      assert (in_rel2 c' c') as equiv2_c'_c' by intuition.
      destruct_rel_mod_eval.
      simplify_evals.
      clear_pi_sort_eq_and_pred_rel.
      
      assert (per_subtyp pred_P b a0) by mauto 2.
      assert (per_subtyp pred_P a0 b') by mauto 2.
      eapply (H1 c c' b a0); mauto 2.
    + pose proof (per_sort_elem_pi_lowering pred_P H2).
      mauto 2.
Qed.

#[export]
Hint Resolve per_subtyp_trans : mcpts.

#[export]
Instance per_subtyp_trans_ins {P} {pred_P : PredicativeSig P} : Transitive (per_subtyp pred_P).
Proof.
  eauto using per_subtyp_trans.
Qed.


(** Subtyping is stable under equality *)
Corollary per_subtyp_transp {P} {pred_P : PredicativeSig P} : forall a b a' b' R R',
    {{ SubT a <: b ∈ per_subtyp pred_P }} ->
    {{ DF a ≈ a' ∈ per_typ_elem pred_P ↘ R }} ->
    {{ DF b ≈ b' ∈ per_typ_elem pred_P ↘ R' }} ->
    {{ SubT a' <: b' ∈ per_subtyp pred_P }}.
Proof.
  mauto using per_subtyp_refl1, per_subtyp_refl2.
Qed.

#[export]
Hint Resolve per_subtyp_transp : mcpts.

(** ** Inversion principles for subtyping *)
Lemma per_subtyp_sort_inv_left {P} (pred_P : PredicativeSig P) : forall {s a},
    {{ SubT Sort@s <: a ∈ per_subtyp pred_P }} ->
    exists s', a = d{{{ Sort@s' }}} /\ st_subtyp s s'.
Proof.
  simpl.
  intros.
  do 2 (dependent destruction H; mauto).
Qed.

Lemma per_subtyp_sort_inv_right {P} (pred_P : PredicativeSig P) : forall {s a},
    {{ SubT a <: Sort@s ∈ per_subtyp pred_P }} ->
    exists s', a = d{{{ Sort@s' }}} /\ st_subtyp s' s.
Proof.
  simpl.
  intros.
  do 2 (dependent destruction H; mauto).
Qed.

Lemma per_subtyp_nat_inv_left {P} (pred_P : PredicativeSig P) : forall {a},
    {{ SubT ℕ <: a ∈ per_subtyp pred_P }} ->
    (a = d{{{ ℕ }}}).
Proof.
  intros.
  inversion_clear H.
  reflexivity.
Qed.

Lemma per_subtyp_nat_inv_right {P} (pred_P : PredicativeSig P) : forall {a},
    {{ SubT a <: ℕ ∈ per_subtyp pred_P }} ->
    a = d{{{ ℕ }}}.
Proof.
  intros.
  inversion_clear H.
  reflexivity.
Qed.

Lemma per_subtyp_pi_inv_left {P} (pred_P : PredicativeSig P) : forall {s1 s2 s3 c a ρ B} {r : Ru_pi P s1 s2 s3},
    {{ SubT Π r a ρ B <: c ∈ per_subtyp pred_P }} ->
    exists a' ρ' B', c = d{{{ Π r a' ρ' B' }}}.
Proof.
  simpl.
  intros.
  do 2 (dependent destruction H; mauto).
Qed.

Lemma per_subtyp_pi_inv_right {P} (pred_P : PredicativeSig P) : forall {s1 s2 s3 c a ρ B} {r : Ru_pi P s1 s2 s3},
    {{ SubT c <: Π r a ρ B ∈ per_subtyp pred_P }} ->
    exists a' ρ' B', c = d{{{ Π r a' ρ' B' }}}.
Proof.
  simpl.
  intros.
  do 2 (dependent destruction H; mauto).
Qed.

Lemma per_bot_var_inv {P : PtsSig} : forall {n n'},
    @per_bot P d{{{ !n }}} d{{{ !n' }}} ->
    n = n'.
Proof.
  intros.
  specialize (H (max n n' + 1)) as [L []].
  inversion H; subst.
  inversion H0; subst.
  lia.
Qed.

Lemma per_subtyp_var_inv_left {P} (pred_P : PredicativeSig P) : forall {a x n l},
    n < l ->
    {{ SubT ⇑! x n <: a ∈ per_subtyp pred_P }} ->
    exists x', a = d{{{ ⇑! x' n }}}.
Proof.
  intros * Hlt ?.
  inversion_clear H.
  pose proof H0.
  specialize (H0 l) as [M []].
  inversion H0; subst.
  inversion H1; subst.
  assert (x0 = n) by (eapply per_bot_var_inv; mauto 2).
  subst.
  eexists; reflexivity.
Qed.

Lemma per_subtyp_var_inv_right {P} (pred_P : PredicativeSig P) : forall {a x n l},
    n < l ->
    {{ SubT a <: ⇑! x n ∈ per_subtyp pred_P }} ->
    exists x', a = d{{{ ⇑! x' n }}}.
Proof.
  intros * Hlt ?.
  inversion_clear H.
  pose proof H0.
  specialize (H0 l) as [M []].
  inversion H1; subst.
  inversion H0; subst.
  assert (n = x0) by (eapply per_bot_var_inv; mauto 2).
  subst.
  eexists; reflexivity.
Qed.
