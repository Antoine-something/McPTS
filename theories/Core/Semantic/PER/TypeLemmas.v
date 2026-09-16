From Coq Require Import Equivalence Lia Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import System.
From McPTS.Core.Semantic Require Import PER.Definitions PER.CoreTactics PER.CoreLemmas PER.SortLemmas.
Import Domain_Notations.

(** ** Functionality of per_typ_elem *)
(** Main functionality result *)
Lemma per_typ_elem_right_irrel {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ a b b' R R',
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ DF a ≈ b' ∈ per_typ_elem pred_P Δ ↘ R' }} ->
    R <~> R'.
Proof.
  intros * Horig.
  induction Horig;
    intros Hright; dependent destruction Hright.
  - apply_relation_equivalence.
    reflexivity.
  - basic_invert_per_sort_elem H0.
    apply_relation_equivalence.
    reflexivity.
  - basic_invert_per_sort_elem H.
    apply_relation_equivalence.
    reflexivity.
  - eapply per_sort_elem_right_irrel; mauto.
Qed.

(** Main symmetry result of per_typ_elem *)
Lemma per_typ_elem_sym_main {P} {pred_P : PredicativeSig P} : forall {Δ R a b},
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ DF b ≈ a ∈ per_typ_elem pred_P Δ ↘ R }} /\
      (forall m m',
          {{ Dom m ≈ m' ∈ R }} ->
          {{ Dom m' ≈ m ∈ R }}).
Proof with mautosolve.
  simpl.
  induction 1; split.
  - econstructor; mauto.
  - apply_relation_equivalence.
    intros.
    symmetry; eauto.
  - symmetry in H.
    econstructor; mauto.
  - intros.
    symmetry; eauto.
Qed.

(** Other functionality results *)
Corollary per_typ_elem_left_irrel {P} {pred_P : PredicativeSig P} : forall Δ R a b R' a',
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ DF a' ≈ b ∈ per_typ_elem pred_P Δ ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ?%per_typ_elem_sym_main ?%per_typ_elem_sym_main.
  destruct_conjs.
  eauto using per_typ_elem_right_irrel.
Qed.

Corollary per_typ_elem_cross_irrel {P} {pred_P : PredicativeSig P} : forall Δ R a b R' b',
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ DF b' ≈ a ∈ per_typ_elem pred_P Δ ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ? ?%per_typ_elem_sym_main.
  destruct_conjs.
  eauto using per_typ_elem_right_irrel.
Qed.

(** Tactics to handle functionality of per_typ_elem *)
Ltac do_per_typ_elem_irrel_assert1 :=
  let tactic_error o1 o2 := fail 2 "per_typ_elem_irrel biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ DF ^?a ≈ ^_ ∈ per_typ_elem ?pred_P ?Δ ↘ ?R1 }},
      H2 : {{ DF ^?a ≈ ^_ ∈ per_typ_elem ?pred_P ?Δ ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_typ_elem_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ^_ ≈ ^?b ∈ per_typ_elem ?pred_P ?Δ ↘ ?R1 }},
      H2 : {{ DF ^_ ≈ ^?b ∈ per_typ_elem ?pred_P ?Δ ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_typ_elem_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ^?a ≈ ^_ ∈ per_typ_elem ?pred_P ?Δ ↘ ?R1 }},
      H2 : {{ DF ^_ ≈ ^?a ∈ per_typ_elem ?pred_P ?Δ ↘ ?R2 }} |- _ =>
      (** Order matters less here as H1 and H2 cannot be exchanged *)
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_typ_elem_cross_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  end.

Ltac do_per_typ_elem_irrel_assert :=
  repeat do_per_typ_elem_irrel_assert1.

Ltac handle_per_typ_elem_irrel :=
  functional_eval_rewrite_clear;
  do_per_typ_elem_irrel_assert;
  apply_relation_equivalence;
  clear_dups.


(** ** Hybrid functionality with per_sort_elem *)
#[local]
Ltac lift_per_sort_elem_to_per_typ_elem1 H :=
  match type of H with
  | {{ DF ^?a ≈ ^?b ∈ per_sort_elem ?pred_P ?Δ ?s ↘ ?R }} =>
      assert {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} by (econstructor; mauto 3)
  end.

#[global]
Ltac lift_per_sort_elem_to_per_typ_elem := (on_all_hyp: lift_per_sort_elem_to_per_typ_elem1).
 
Lemma per_typ_elem_per_sort_elem_right_irrel {P} {pred_P : PredicativeSig P} : forall Δ s a b b' R R',
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ DF a ≈ b' ∈ per_sort_elem pred_P Δ s ↘ R' }} ->
    R <~> R'.
Proof.
  intros.
  lift_per_sort_elem_to_per_typ_elem.
  handle_per_typ_elem_irrel.
  reflexivity.
Qed.

Lemma per_typ_elem_per_sort_elem_left_irrel {P} {pred_P : PredicativeSig P} : forall Δ s a a' b R R',
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ DF a' ≈ b ∈ per_sort_elem pred_P Δ s ↘ R' }} ->
    R <~> R'.
Proof.
  intros.
  lift_per_sort_elem_to_per_typ_elem.
  handle_per_typ_elem_irrel.
  reflexivity.
Qed.

Lemma per_typ_elem_per_sort_elem_cross_irrel1 {P} {pred_P : PredicativeSig P} : forall Δ s a b b' R R',
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ DF b' ≈ a ∈ per_sort_elem pred_P Δ s ↘ R' }} ->
    R <~> R'.
Proof.
  intros.
  lift_per_sort_elem_to_per_typ_elem.
  handle_per_typ_elem_irrel.
  reflexivity.
Qed.

Lemma per_typ_elem_per_sort_elem_cross_irrel2 {P} {pred_P : PredicativeSig P} : forall Δ s a a' b R R',
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ DF b ≈ a' ∈ per_sort_elem pred_P Δ s ↘ R' }} ->
    R <~> R'.
Proof.
  intros.
  lift_per_sort_elem_to_per_typ_elem.
  handle_per_typ_elem_irrel.
  reflexivity.
Qed.


(** Tactics to handle functionality of per_typ_elem *)
Ltac do_per_typ_elem_per_sort_elem_irrel_assert1 :=
  let tactic_error o1 o2 := fail 2 "per_typ_sort_elem_irrel biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ DF ^?a ≈ ^_ ∈ per_typ_elem ?pred_P ?Δ ↘ ?R1 }},
      H2 : {{ DF ^?a ≈ ^_ ∈ per_sort_elem ?pred_P ?s ?Δ ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_typ_elem_per_sort_elem_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ^_ ≈ ^?b ∈ per_typ_elem ?pred_P ?Δ ↘ ?R1 }},
      H2 : {{ DF ^_ ≈ ^?b ∈ per_sort_elem ?pred_P ?s ?Δ ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_typ_elem_per_sort_elem_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ^?a ≈ ^_ ∈ per_typ_elem ?pred_P ?Δ ↘ ?R1 }},
      H2 : {{ DF ^_ ≈ ^?a ∈ per_sort_elem ?pred_P ?Δ ?s ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_typ_elem_per_sort_elem_cross_irrel1; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ^_ ≈ ^?b ∈ per_typ_elem ?pred_P ?Δ ↘ ?R1 }},
      H2 : {{ DF ^?b ≈ ^_ ∈ per_sort_elem ?pred_P ?Δ ?s ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_typ_elem_per_sort_elem_cross_irrel2; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  end.

Ltac do_per_typ_elem_per_sort_elem_irrel_assert :=
  repeat do_per_typ_elem_per_sort_elem_irrel_assert1.

Ltac handle_per_typ_elem_per_sort_elem_irrel :=
  functional_eval_rewrite_clear;
  do_per_typ_elem_per_sort_elem_irrel_assert;
  apply_relation_equivalence;
  clear_dups.

(** ** PER instances related to per_typ_elem *)
Lemma per_typ_elem_trans_main {P} {pred_P : PredicativeSig P} : forall Δ R a1 a2,
    {{ DF a1 ≈ a2 ∈ per_typ_elem pred_P Δ ↘ R }} ->
    (forall a3,
        {{ DF a2 ≈ a3 ∈ per_typ_elem pred_P Δ ↘ R }} ->
        {{ DF a1 ≈ a3 ∈ per_typ_elem pred_P Δ ↘ R }}) /\
      (forall m1 m2 m3,
          R m1 m2 ->
          R m2 m3 ->
          R m1 m3).
Proof with mautosolve.
  simpl.
  induction 1.
  - split.
    + intros.
      mauto.
    + apply_relation_equivalence.
      eapply per_sort_trans; mauto.
  - split.
    + intros.
      dependent destruction H0.
      * apply_relation_equivalence.
        econstructor; mauto.
      * assert {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }} by (eapply per_sort_elem_trans; mauto).
        econstructor; mauto.
    + eapply per_sort_elem_trans_main; mauto.
Qed.

(** For per_typ_elem *)
#[export]
Instance per_typ_elem_PER {P} {pred_P : PredicativeSig P} {Δ R} : PER (per_typ_elem pred_P Δ R).
Proof.
  split.
  - intros x y H.
    eapply (per_typ_elem_sym_main H).
  - intros x y **.
    eapply (per_typ_elem_trans_main Δ R x _ ltac:(eassumption)); eassumption.
Qed.

(** For per_typ *)
Corollary per_typ_sym {P} {pred_P : PredicativeSig P} : forall Δ a b,
    {{ Dom a ≈ b ∈ per_typ pred_P Δ }} ->
    {{ Dom b ≈ a ∈ per_typ pred_P Δ }}.
Proof.
  intros * [? ?%per_typ_elem_sym_main].
  firstorder.
Qed.

Corollary per_typ_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ a1 a2 a3,
    {{ Dom a1 ≈ a2 ∈ per_typ pred_P Δ }} ->
    {{ Dom a2 ≈ a3 ∈ per_typ pred_P Δ }} ->
    {{ Dom a1 ≈ a3 ∈ per_typ pred_P Δ }}.
Proof.
  intros * [? ?] [? ?].
  handle_per_typ_elem_irrel.
  assert (per_typ_elem pred_P Δ x0 a1 a3) by (eapply (proj1 (per_typ_elem_trans_main Δ x0 a1 a2 H) a3 H0); mauto).
  mauto.
Qed.

#[export]
Instance per_typ_PER {P} {pred_P : PredicativeSig P} {Δ} : PER (per_typ pred_P Δ).
Proof.
  split.
  - intros x y H.
    eapply per_typ_sym; mauto.
  - intros x y z Hxy Hyz.
    eapply per_typ_trans; mauto.
Qed.

Corollary per_typ_elem_output_sym {P} {pred_P : PredicativeSig P} : forall {Δ a b R} m1 m2,
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    R m1 m2 ->
    R m2 m1.
Proof.
  intros * Hper H.
  pose proof (per_typ_elem_sym_main Hper) as [].
  mauto 2.
Qed.
  
Corollary per_typ_elem_output_trans {P} {pred_P : PredicativeSig P} : forall {Δ a b R} m1 m2 m3,
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    R m1 m2 ->
    R m2 m3 ->
    R m1 m3.
Proof.
  intros * Hper H12 H23.
  pose proof (per_typ_elem_trans_main _ _ _ _ Hper) as [].
  mauto 2.
Qed.

#[export]
Instance per_typ_elem_output_PER {P : PtsSig} {pred_P : PredicativeSig P} {Δ R a b} (H : per_typ_elem pred_P Δ R a b) : PER R.
Proof.
  split.
  - pose proof (fun m m' => per_typ_elem_output_sym m m' H); eauto.
  - pose proof (fun m1 m2 m3 => per_typ_elem_output_trans m1 m2 m3 H); eauto.
Qed.


(** Lowering for pi *)
Lemma per_typ_elem_pi_lowering {P} (pred_P : PredicativeSig P) : forall {Δ s1 s2 s3} {r : Ru_pi P s1 s2 s3} {elem_rel a ρ B a' ρ' B'},
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_typ_elem pred_P Δ ↘ elem_rel }} ->
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P Δ s3 ↘ elem_rel }}.
Proof.
  intros.
  inversion_clear H.
  eapply per_sort_elem_pi_lowering; mauto 2.
Qed.
