From Coq Require Import Equivalence Lia Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Import PER.CoreTactics PER.Definitions.
Import Domain_Notations.

Add Parametric Morphism {P} R0 `(R0_morphism : Proper _ ((@relation_equivalence (domain P)) ==> (@relation_equivalence (domain P))) R0) A ρ A' ρ' : (rel_mod_eval R0 A ρ A' ρ')
    with signature (@relation_equivalence (domain P)) ==> iff as rel_mod_eval_morphism.
Proof.
  split; intros []; econstructor; try eassumption;
    [> eapply R0_morphism; [symmetry + idtac |]; eassumption ..].
Qed.

Add Parametric Morphism {P} f a f' a' : (rel_mod_app f a f' a')
    with signature (@relation_equivalence (domain P)) ==> iff as rel_mod_app_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    apply HRR'; eassumption.
Qed.

Lemma per_bot_sym {P} : forall m n : domain_ne P,
    {{ Dom m ≈ n ∈ per_bot }} ->
    {{ Dom n ≈ m ∈ per_bot }}.
Proof with solve [eauto].
  intros * H s.
  pose proof H s.
  destruct_conjs...
Qed.

#[export]
Hint Resolve per_bot_sym : mcpts.

Lemma per_bot_trans {P} : forall m n l : domain_ne P,
    {{ Dom m ≈ n ∈ per_bot }} ->
    {{ Dom n ≈ l ∈ per_bot }} ->
    {{ Dom m ≈ l ∈ per_bot }}.
Proof with solve [eauto].
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_bot_trans : mcpts.

#[export]
Instance per_bot_PER {P} : PER (@per_bot P).
Proof.
  split.
  - eauto using per_bot_sym.
  - eauto using per_bot_trans.
Qed.

Lemma var_per_bot {P} : forall {n},
    {{ Dom !n ≈ !n ∈ @per_bot P }}.
Proof.
  intros ? ?. repeat econstructor.
Qed.

#[export]
Hint Resolve var_per_bot : mcpts.

Lemma per_top_sym {P} : forall m n : domain_nf P,
    {{ Dom m ≈ n ∈ per_top }} ->
    {{ Dom n ≈ m ∈ per_top }}.
Proof with solve [eauto].
  intros * H s.
  pose proof H s.
  destruct_conjs...
Qed.

#[export]
Hint Resolve per_top_sym : mcpts.

Lemma per_top_trans {P} : forall m n l : domain_nf P,
    {{ Dom m ≈ n ∈ per_top }} ->
    {{ Dom n ≈ l ∈ per_top }} ->
    {{ Dom m ≈ l ∈ per_top }}.
Proof with solve [eauto].
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_top_trans : mcpts.

#[export]
Instance per_top_PER {P} : PER (@per_top P).
Proof.
  split.
  - eauto using per_top_sym.
  - eauto using per_top_trans.
Qed.

Lemma per_bot_then_per_top {P} : forall (m : domain_ne P) m' a a' b b' c c',
    {{ Dom m ≈ m' ∈ per_bot }} ->
    {{ Dom ⇓ (⇑ a b) ⇑ c m ≈ ⇓ (⇑ a' b') ⇑ c' m' ∈ per_top }}.
Proof.
  intros * H s.
  pose proof H s.
  destruct_conjs.
  eexists; split; constructor; eassumption.
Qed.

#[export]
Hint Resolve per_bot_then_per_top : mcpts.

Lemma per_top_typ_sym {P} : forall m n : domain P,
    {{ Dom m ≈ n ∈ per_top_typ }} ->
    {{ Dom n ≈ m ∈ per_top_typ }}.
Proof with solve [eauto].
  intros * H s.
  pose proof H s.
  destruct_conjs...
Qed.

#[export]
Hint Resolve per_top_typ_sym : mcpts.

Lemma per_top_typ_trans {P} : forall m n l : domain P,
    {{ Dom m ≈ n ∈ per_top_typ }} ->
    {{ Dom n ≈ l ∈ per_top_typ }} ->
    {{ Dom m ≈ l ∈ per_top_typ }}.
Proof with solve [eauto].
  intros * Hmn Hnl s.
  pose proof (Hmn s, Hnl s).
  destruct_conjs.
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_top_typ_trans : mcpts.

#[export]
Instance per_top_typ_PER {P} : PER (@per_top_typ P).
Proof.
  split.
  - eauto using per_top_typ_sym.
  - eauto using per_top_typ_trans.
Qed.


Lemma per_ne_sym {P} : forall m n : domain P,
    {{ Dom m ≈ n ∈ per_ne }} ->
    {{ Dom n ≈ m ∈ per_ne }}.
Proof with mautosolve.
  intros * [].
  econstructor...
Qed.

#[export]
Hint Resolve per_ne_sym : mcpts.

Lemma per_ne_trans {P} : forall m n l : domain P,
    {{ Dom m ≈ n ∈ per_ne }} ->
    {{ Dom n ≈ l ∈ per_ne }} ->
    {{ Dom m ≈ l ∈ per_ne }}.
Proof with mautosolve.
  intros * [].
  inversion_clear 1.
  econstructor...
Qed.

#[export]
Hint Resolve per_ne_trans : mcpts.

#[export]
Instance per_ne_PER {P} : PER (@per_ne P).
Proof.
  split.
  - eauto using per_ne_sym.
  - eauto using per_ne_trans.
Qed.

Add Parametric Morphism {P} {pred_P : PredicativeSig P} s (per_sort_elem_rec : forall s', pred_rel pred_P s' s -> relation (domain P) -> relation (domain P)) : (per_sort_elem_core pred_P s per_sort_elem_rec)
    with signature (@relation_equivalence (domain P)) ==> eq ==> eq ==> iff as per_sort_elem_core_morphism_iff.
Proof with mautosolve.
  simpl.
  intros R R' HRR'.

  split; intros Horig; [gen R' | gen R];
    induction Horig;
    eauto;
    try (etransitivity; [symmetry + idtac|]; eassumption);
    intros;
    destruct_rel_mod_eval;
    econstructor; mauto 3.
  1-3: rewrite <- HRR'; mauto.
  all: rewrite HRR'; mauto.
Qed.

Add Parametric Morphism {P} {pred_P : PredicativeSig P} s : (per_sort_elem pred_P s)
    with signature (@relation_equivalence (domain P)) ==> eq ==> eq ==> iff as per_sort_elem_morphism_iff.
Proof with mautosolve.
  simp per_sort_elem.
  intros R R' HRR'.

  split; intros Horig; [gen R' | gen R];
  
    induction Horig;
    eauto;
    try (etransitivity; [symmetry + idtac|]; eassumption);
    intros;
    destruct_rel_mod_eval;
    econstructor; mauto 3.
  1-3: rewrite <- HRR'; mauto.
  all: rewrite HRR'; mauto.
Qed.


Add Parametric Morphism {P} {pred_P : PredicativeSig P} s per_sort_rec : (per_sort_elem_core pred_P s per_sort_rec)
    with signature (@relation_equivalence (domain P)) ==> (@relation_equivalence (domain P)) as per_sort_elem_core_morphism_relation_equivalence.
Proof with mautosolve.
  intros * H ? ?.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Add Parametric Morphism {P} {pred_P : PredicativeSig P} s : (per_sort_elem pred_P s)
    with signature (@relation_equivalence (domain P)) ==> (@relation_equivalence (domain P)) as per_sort_elem_morphism_relation_equivalence.
Proof with mautosolve.
  intros * H ? ?.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Add Parametric Morphism {P} {pred_P : PredicativeSig P} s A ρ A' ρ' : (rel_typ pred_P s A ρ A' ρ')
    with signature (@relation_equivalence (domain P)) ==> iff as rel_typ_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    [setoid_rewrite <- HRR' | setoid_rewrite HRR']; eassumption.
Qed.

Lemma domain_app_per {P} : forall (f : domain_ne P) f' a a',
  {{ Dom f ≈ f' ∈ per_bot }} ->
  {{ Dom a ≈ a' ∈ per_top }} ->
  {{ Dom f a ≈ f' a' ∈ per_bot }}.
Proof.
  intros. intros s.
  destruct (H s) as [? []].
  destruct (H0 s) as [? []].
  mauto.
Qed.

Ltac rewrite_relation_equivalence_left :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        try setoid_rewrite H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac rewrite_relation_equivalence_right :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        try setoid_rewrite <- H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite <- H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac clear_relation_equivalence :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        (unify R1 R2; clear H) + (is_var R1; clear R1 H) + (is_var R2; clear R2 H)
    end.

Ltac apply_relation_equivalence :=
  clear_relation_equivalence;
  rewrite_relation_equivalence_right;
  clear_relation_equivalence;
  rewrite_relation_equivalence_left;
  clear_relation_equivalence.

Lemma per_sort_elem_pi_arg_helper {P} {pred_P : PredicativeSig P} : forall {s_in s_out s a a' in_rel},
    Ru P s_in s_out s ->
    (s_in = s -> {{ DF a ≈ a' ∈ per_sort_elem pred_P s ↘ in_rel }}) /\ (pred_rel pred_P s_in s -> {{ DF a ≈ a' ∈ per_sort_elem pred_P s_in ↘ in_rel }}) <-> {{ DF a ≈ a' ∈ per_sort_elem pred_P s_in ↘ in_rel }}.
Proof.
  intros * r.
  split; [intros [Heq Hlt] | split; intros; subst; eauto].
  destruct (ord_ru pred_P r) as [[|] _]; subst; eauto.
Qed.

Lemma per_sort_elem_pi_ret_helper {P} {pred_P : PredicativeSig P} : forall {s_in s_out s ρ B ρ' B' in_rel} (out_rel : forall {n n'}, {{ Dom n ≈ n' ∈ in_rel }} -> relation (domain P)),
    Ru P s_in s_out s ->
    (forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
        rel_mod_eval (fun R b b' => (s_out = s -> {{ DF b ≈ b' ∈ per_sort_elem pred_P s ↘ R }}) /\ (pred_rel pred_P s_out s -> {{ DF b ≈ b' ∈ per_sort_elem pred_P s_out ↘ R }})) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) <->
      (forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
          rel_mod_eval (per_sort_elem pred_P s_out) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')).
Proof.
  intros * r.
  split;
    [ intros Hbare *; specialize (Hbare n n' equiv_n_n') as [? ? ? ? [Heq Hlt]]
    | intros Helab *; specialize (Helab n n' equiv_n_n') as []]; econstructor; eauto.
  - destruct (ord_ru pred_P r) as [_ [|]]; subst; eauto.
  - split; intros; subst; eauto.
Qed.

Lemma per_sort_elem_pi_left_inversion {P} {pred_P : PredicativeSig P} : forall {s_in s_out s s'} {r : Ru P s_in s_out s} {a ρ B c' elem_rel},
    {{ DF Π r a ρ B ≈ c' ∈ per_sort_elem pred_P s' ↘ elem_rel }} ->
    exists a' ρ' B' in_rel (out_rel : forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), relation (domain P)),
      s' = s /\
      c' = d{{{ Π r a' ρ' B' }}} /\
        {{ DF a ≈ a' ∈ per_sort_elem pred_P s_in ↘ in_rel }} /\
        (forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
            rel_mod_eval (per_sort_elem pred_P s_out) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) /\
        (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app f n f' n' (out_rel equiv_n_n')).
Proof.
  intros * H.
  basic_invert_per_sort_elem H.
  erewrite (per_sort_elem_pi_arg_helper r) in equiv_a_a'.
  erewrite (per_sort_elem_pi_ret_helper _ r) in H0.
  eexists a', ρ', B', in_rel, out_rel; eauto.
Qed.

#[local]
Ltac invert_per_sort_elem' H :=
  (unshelve eapply per_sort_elem_pi_left_inversion in H; shelve_unifiable; deex_in H; destruct H as [-> [-> [? []]]])
  + basic_invert_per_sort_elem H.

Lemma per_sort_elem_right_irrel {P} {pred_P : PredicativeSig P} : forall s s' R a b R' b',
    {{ DF a ≈ b ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ DF a ≈ b' ∈ per_sort_elem pred_P s' ↘ R' }} ->
    (R <~> R').
Proof with (destruct_rel_mod_eval; destruct_rel_mod_app; functional_eval_rewrite_clear; econstructor; intuition).
  simpl.
  intros * Horig.
  remember a as a' in |- *.
  gen s' a' b' R'.

  induction Horig using @per_sort_elem_ind; mauto; intros * ? ? Hright; subst;
    invert_per_sort_elem' Hright;
    apply_relation_equivalence;
    try reflexivity.
  assert (in_rel <~> in_rel0) by mauto 3.
  split; intros.
  - rename equiv_n_n' into equiv0_n_n'.
    assert (equiv_n_n' : in_rel n n') by firstorder...
  - assert (equiv0_n_n' : in_rel0 n n') by firstorder...
Qed.

#[local]
Ltac per_sort_elem_right_irrel_assert1 :=
  match goal with
  | H1 : {{ DF ^?a ≈ ^?b ∈ per_sort_elem ?pred_P ?s ↘ ?R1 }},
      H2 : {{ DF ^?a ≈ ^?b' ∈ per_sort_elem ?pred_P ?s ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_sort_elem_right_irrel; [apply H1 | apply H2])
      end
  end.
#[local]
Ltac per_sort_elem_right_irrel_assert := repeat per_sort_elem_right_irrel_assert1.

Lemma per_sort_elem_pi_econstructor {P} {pred_P : PredicativeSig P} : forall {s_in s_out s a ρ B a' ρ' B'} (r : Ru P s_in s_out s) {in_rel} (out_rel : forall {n n'}, {{ Dom n ≈ n' ∈ in_rel }} -> relation (domain P)) {elem_rel} (equiv_a_a' : {{ DF a ≈ a' ∈ per_sort_elem pred_P s_in ↘ in_rel }}),
    PER in_rel ->
    (forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
        rel_mod_eval (per_sort_elem pred_P s_out) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) ->
    (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app f n f' n' (out_rel equiv_n_n')) ->
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P s ↘ elem_rel }}.
Proof.
  intros.
  rewrite <- (per_sort_elem_pi_arg_helper r) in equiv_a_a'.
  rewrite <- (per_sort_elem_pi_ret_helper _ r) in H0.
  basic_per_sort_elem_econstructor; eauto.
Qed.

#[local]
Ltac per_sort_elem_econstructor' :=
  (repeat intro; hnf; (eapply per_sort_elem_pi_econstructor)) + basic_per_sort_elem_econstructor.

Lemma per_sort_elem_sym {P} {pred_P : PredicativeSig P} : forall {s R a b},
    {{ DF a ≈ b ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ DF b ≈ a ∈ per_sort_elem pred_P s ↘ R }} /\
      (forall m m',
          {{ Dom m ≈ m' ∈ R }} ->
          {{ Dom m' ≈ m ∈ R }}).
Proof with mautosolve.
  simpl.

  induction 1 using per_sort_elem_ind; subst.
  - split.
    + apply per_sort_elem_core_sort'; firstorder.
    + intros.
      rewrite H0 in *.
      destruct_by_head (per_sort pred_P).
      eexists.
      eapply proj1...
  (* - split. *)
  (*   + per_sort_elem_econstructor'; revgoals; mauto. *)
  (*   [per_sort_elem_econstructor' | intros; apply_relation_equivalence]... *)
  - destruct_conjs.
    split.
    + per_sort_elem_econstructor'; eauto.
      intros.
      assert (in_rel n' n) by eauto.
      assert (in_rel n n) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      econstructor; eauto.
      per_sort_elem_right_irrel_assert.
      apply_relation_equivalence.
      eassumption.
    + apply_relation_equivalence.
      intros.
      assert (in_rel n' n) by eauto.
      assert (in_rel n n) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      functional_eval_rewrite_clear.
      econstructor; eauto.
      per_sort_elem_right_irrel_assert.
      intuition.
  - destruct_conjs.
    split; [per_sort_elem_econstructor' | apply_relation_equivalence]; mauto 3.
Qed.

Corollary per_sort_sym {P} {pred_P : PredicativeSig P} : forall s R a b,
    {{ DF a ≈ b ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ DF b ≈ a ∈ per_sort_elem pred_P s ↘ R }}.
Proof.  
  intros * ?%per_sort_elem_sym.
  firstorder.
Qed.

Corollary per_sort_sym' {P} {pred_P : PredicativeSig P} : forall s a b,
    {{ Dom a ≈ b ∈ per_sort pred_P s }} ->
    {{ Dom b ≈ a ∈ per_sort pred_P s }}.
Proof.
  intros * [? ?%per_sort_elem_sym].
  firstorder.
Qed.

Corollary per_elem_sym {P} {pred_P : PredicativeSig P} : forall s R a b m m',
    {{ DF a ≈ b ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ Dom m ≈ m' ∈ R }} ->
    {{ Dom m' ≈ m ∈ R }}.
Proof.
  intros * ?%per_sort_elem_sym.
  firstorder.
Qed.

Corollary per_sort_elem_left_irrel {P} {pred_P : PredicativeSig P} : forall s s' R a b R' a',
    {{ DF a ≈ b ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ DF a' ≈ b ∈ per_sort_elem pred_P s' ↘ R' }} ->
    (R <~> R').
Proof.
  intros * ?%per_sort_sym ?%per_sort_sym.
  eauto using per_sort_elem_right_irrel.
Qed.

Corollary per_sort_elem_cross_irrel {P} {pred_P : PredicativeSig P} : forall s s' R a b R' b',
    {{ DF a ≈ b ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ DF b' ≈ a ∈ per_sort_elem pred_P s' ↘ R' }} ->
    (R <~> R').
Proof.
  intros * ? ?%per_sort_sym.
  eauto using per_sort_elem_right_irrel.
Qed.

Ltac do_per_sort_elem_irrel_assert1 :=
  let tactic_error o1 o2 := fail 2 "per_sort_elem_irrel biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ DF ^?a ≈ ^_ ∈ per_sort_elem ?pred_P ?s ↘ ?R1 }},
      H2 : {{ DF ^?a ≈ ^_ ∈ per_sort_elem ?pred_P ?s' ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_sort_elem_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ^_ ≈ ^?b ∈ per_sort_elem ?pred_P ?s ↘ ?R1 }},
      H2 : {{ DF ^_ ≈ ^?b ∈ per_sort_elem ?pred_P ?s' ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_sort_elem_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ^?a ≈ ^_ ∈ per_sort_elem ?pred_P ?s ↘ ?R1 }},
      H2 : {{ DF ^_ ≈ ^?a ∈ per_sort_elem ?pred_P ?s' ↘ ?R2 }} |- _ =>
      (** Order matters less here as H1 and H2 cannot be exchanged *)
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_sort_elem_cross_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  end.

Ltac do_per_sort_elem_irrel_assert :=
  repeat do_per_sort_elem_irrel_assert1.

Ltac handle_per_sort_elem_irrel :=
  functional_eval_rewrite_clear;
  do_per_sort_elem_irrel_assert;
  apply_relation_equivalence;
  clear_dups.

Lemma per_sort_elem_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall s R a1 a2,
    {{ DF a1 ≈ a2 ∈ per_sort_elem pred_P s ↘ R }} ->
    (forall s' a3,
        {{ DF a2 ≈ a3 ∈ per_sort_elem pred_P s' ↘ R }} ->
        {{ DF a1 ≈ a3 ∈ per_sort_elem pred_P s ↘ R }}) /\
      (forall m1 m2 m3,
          R m1 m2 ->
          R m2 m3 ->
          R m1 m3).
Proof with (per_sort_elem_econstructor'; mautosolve 4).
  simpl.
  induction 1 using per_sort_elem_ind;
    [> split;
     [ intros * HT2; invert_per_sort_elem' HT2
     | intros * HTR1 HTR2; apply_relation_equivalence ] ..]; subst; mauto.
  - (* sort case *)
    destruct HTR1, HTR2.
    handle_per_sort_elem_irrel.
    eexists.
    specialize (H1 _ _ _ H) as [].
    intuition.
  - (* pi case *)
    destruct_conjs.
    per_sort_elem_econstructor'; eauto.
    + handle_per_sort_elem_irrel.
      intuition.
    + intros.
      handle_per_sort_elem_irrel.
      assert (in_rel n n') by firstorder.
      assert (in_rel n n) by intuition.
      assert (in_rel0 n n') by intuition.
      destruct_rel_mod_eval.
      functional_eval_rewrite_clear.
      handle_per_sort_elem_irrel...
  - (* fun case *)
    intros.
    assert (in_rel n n) by intuition.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    handle_per_sort_elem_irrel.
    econstructor; eauto.
    intuition.
  - (* neut case *)
    idtac...
Qed.

Corollary per_sort_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall s s' R a1 a2 a3,
    per_sort_elem pred_P s R a1 a2 ->
    per_sort_elem pred_P s' R a2 a3 ->
    per_sort_elem pred_P s R a1 a3.
Proof.
  intros * ?%per_sort_elem_trans.
  firstorder.
Qed.

Corollary per_sort_trans' {P : PtsSig} {pred_P : PredicativeSig P} : forall s s' a1 a2 a3,
    {{ Dom a1 ≈ a2 ∈ per_sort pred_P s }} ->
    {{ Dom a2 ≈ a3 ∈ per_sort pred_P s' }} ->
    {{ Dom a1 ≈ a3 ∈ per_sort pred_P s }}.
Proof.
  intros * [? ?] [? ?].
  handle_per_sort_elem_irrel.
  firstorder mauto using per_sort_trans.
Qed.

Corollary per_elem_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall s R a1 a2 m1 m2 m3,
    per_sort_elem pred_P s R a1 a2 ->
    R m1 m2 ->
    R m2 m3 ->
    R m1 m3.
Proof.
  intros * ?% per_sort_elem_trans.
  firstorder.
Qed.

#[export]
Instance per_sort_PER {P : PtsSig} {pred_P : PredicativeSig P} {s R} : PER (per_sort_elem pred_P s R).
Proof.
  split.
  - auto using per_sort_sym.
  - eauto using per_sort_trans.
Qed.

#[export]
Instance per_sort_PER' {P : PtsSig} {pred_P : PredicativeSig P} {s} : PER (per_sort pred_P s).
Proof.
  split.
  - auto using per_sort_sym'.
  - eauto using per_sort_trans'.
Qed.

#[export]
Instance per_elem_PER {P : PtsSig} {pred_P : PredicativeSig P} {s R a b} (H : per_sort_elem pred_P s R a b) : PER R.
Proof.
  split.
  - pose proof (fun m m' => per_elem_sym _ _ _ _ m m' H). eauto.
  - pose proof (fun m0 m1 m2 => per_elem_trans _ _ _ _ m0 m1 m2 H); eauto.
Qed.

(** These lemmas get rid of the unnecessary PER premises. *)
Lemma per_sort_elem_pi' {P : PtsSig} {pred_P : PredicativeSig P} :
  forall s_in s_out s (r : Ru P s_in s_out s) a a' ρ B ρ' B'
    (in_rel : relation (domain P))
    (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), relation (domain P))
    elem_rel,
    {{ DF a ≈ a' ∈ per_sort_elem pred_P s_in ↘ in_rel}} ->
    (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
        rel_mod_eval (per_sort_elem pred_P s_out) B d{{{ ρ ↦ c }}} B' d{{{ ρ' ↦ c' }}} (out_rel equiv_c_c')) ->
    (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_mod_app f c f' c' (out_rel equiv_c_c')) ->
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P s ↘ elem_rel }}.
Proof.
  intros.
  per_sort_elem_econstructor'; eauto.
  typeclasses eauto.
Qed.

Ltac per_sort_elem_econstructor :=
  (repeat intro; hnf; (eapply per_sort_elem_pi')) + per_sort_elem_econstructor'.

#[export]
Hint Resolve per_sort_elem_pi' : mcpts.

Lemma per_sort_elem_pi_clean_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {s_in s_out s} {r : Ru P s_in s_out s} {a a' in_rel ρ ρ' B B' elem_rel},
    {{ DF a ≈ a' ∈ per_sort_elem pred_P s_in ↘ in_rel }} ->
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P s ↘ elem_rel }} ->
    exists (out_rel : forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), relation (domain P)),
      (forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
          rel_mod_eval (per_sort_elem pred_P s_out) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) /\
        (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app f n f' n' (out_rel equiv_n_n')).
Proof.
  intros * Ha HΠ.
  (unshelve eapply per_sort_elem_pi_left_inversion in HΠ; shelve_unifiable; deex_in HΠ; destruct HΠ as [_ [Heq [? []]]]; inversion Heq; subst).
  rename a'0 into a'.
  rename ρ'0 into ρ'.
  rename B'0 into B'.
  handle_per_sort_elem_irrel.
  eexists.
  split.
  - instantiate (1 := fun n n' (equiv_n_n' : in_rel n n') m m' =>
                        forall R,
                          rel_typ pred_P s_out B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} R ->
                          R m m').
    intros.
    assert (in_rel0 n n') by intuition.
    (on_all_hyp: destruct_rel_by_assumption in_rel0).
    econstructor; eauto.
    apply -> per_sort_elem_morphism_iff; eauto.
    split; intuition.
    destruct_by_head (rel_typ pred_P).
    handle_per_sort_elem_irrel.
    intuition.
  - split; intros;
      [assert (in_rel0 n n') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel0)
      | assert (in_rel n n') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel)];
      econstructor; intuition.
    destruct_by_head (rel_typ pred_P).
    handle_per_sort_elem_irrel.
    intuition.
Qed.

Ltac invert_per_sort_elem H :=
  (unshelve eapply (per_sort_elem_pi_clean_inversion _) in H; shelve_unifiable; [eassumption |]; destruct H as [? []])
  + invert_per_sort_elem' H.

Ltac invert_per_sort_elems := match_by_head per_sort_elem ltac:(fun H => directed invert_per_sort_elem H).


(* These are all lemmas about subtyping.  We might need to replace them with something else *)

(* Lemma per_subtyp_to_sort_elem : forall a b i, *)
(*     {{ Sub a <: b at i }} -> *)
(*     exists R R', *)
(*       {{ DF a ≈ a ∈ per_sort_elem i ↘ R }} /\ *)
(*         {{ DF b ≈ b ∈ per_sort_elem i ↘ R' }}. *)
(* Proof. *)
(*   destruct 1; do 2 eexists; mauto; *)
(*     split; *)
(*     try (etransitivity; try eassumption; symmetry; eassumption); *)
(*     per_sort_elem_econstructor; mauto 3; *)
(*     try apply Equivalence_Reflexive. *)

(*   lia. *)
(* Qed. *)

(* Lemma per_elem_subtyping : forall A B i, *)
(*     {{ Sub A <: B at i }} -> *)
(*     forall R R' a b, *)
(*       {{ DF A ≈ A ∈ per_sort_elem i ↘ R }} -> *)
(*       {{ DF B ≈ B ∈ per_sort_elem i ↘ R' }} -> *)
(*       R a b -> *)
(*       R' a b. *)
(* Proof. *)
(*   induction 1; intros; *)
(*     handle_per_sort_elem_irrel; *)
(*     saturate_refl; *)
(*     invert_per_sort_elems; *)
(*     handle_per_sort_elem_irrel; *)
(*     clear_refl_eqs; *)
(*     trivial. *)
(*   - firstorder mauto. *)
(*   - intros. *)
(*     handle_per_sort_elem_irrel. *)
(*     destruct_rel_mod_eval. *)
(*     saturate_refl_for per_sort_elem. *)
(*     destruct_rel_mod_app. *)
(*     simplify_evals. *)
(*     econstructor; eauto. *)
(*     intuition. *)
(* Qed. *)

(* Lemma per_elem_subtyping_gen : forall a b i a' b' R R' m n, *)
(*     {{ Sub a <: b at i }} -> *)
(*     {{ DF a ≈ a' ∈ per_sort_elem i ↘ R }} -> *)
(*     {{ DF b ≈ b' ∈ per_sort_elem i ↘ R' }} -> *)
(*     R m n -> *)
(*     R' m n. *)
(* Proof. *)
(*   intros. *)
(*   eapply per_elem_subtyping; saturate_refl; try eassumption. *)
(* Qed. *)

(* Lemma per_subtyp_refl1 : forall a b i R, *)
(*     {{ DF a ≈ b ∈ per_sort_elem i ↘ R }} -> *)
(*     {{ Sub a <: b at i }}. *)
(* Proof. *)
(*   simpl; induction 1 using per_sort_elem_ind; *)
(*     subst; *)
(*     mauto; *)
(*     destruct_all. *)
(*     assert ({{ DF Π a ρ B ≈ Π a' ρ' B' ∈ per_sort_elem i ↘ elem_rel }}) *)
(*       by (per_sort_elem_econstructor; intuition; destruct_rel_mod_eval; mauto). *)
(*     saturate_refl_for per_sort_elem. *)
(*     econstructor; eauto. *)
(*     intros; *)
(*       destruct_rel_mod_eval; *)
(*       functional_eval_rewrite_clear; *)
(*       trivial. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve per_subtyp_refl1 : mcpts. *)

(* Lemma per_subtyp_refl2 : forall a b i R, *)
(*     {{ DF a ≈ b ∈ per_sort_elem i ↘ R }} -> *)
(*     {{ Sub b <: a at i }}. *)
(* Proof. *)
(*   intros. *)
(*   symmetry in H. *)
(*   eauto using per_subtyp_refl1. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve per_subtyp_refl2 : mcpts. *)

(* Lemma per_subtyp_trans : forall a1 a2 i, *)
(*     {{ Sub a1 <: a2 at i }} -> *)
(*     forall a3, *)
(*       {{ Sub a2 <: a3 at i }} -> *)
(*       {{ Sub a1 <: a3 at i }}. *)
(* Proof. *)
(*   induction 1; intros ? Hsub; simpl in *. *)
(*   1,2,5: progressive_inversion; mauto. *)
(*   - econstructor; lia. *)
(*   - dependent destruction Hsub. *)
(*     handle_per_sort_elem_irrel. *)
(*     econstructor; eauto. *)
(*     + etransitivity; eassumption. *)
(*     + intros. *)
(*       invert_per_sort_elems. *)
(*       handle_per_sort_elem_irrel. *)
(*       saturate_refl_for in_rel1. *)
(*       destruct_rel_mod_eval. *)
(*       intuition. *)
(*   - dependent destruction Hsub. *)
(*     handle_per_sort_elem_irrel. *)
(*     econstructor; etransitivity; eauto. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve per_subtyp_trans : mcpts. *)

(* #[export] *)
(* Instance per_subtyp_trans_ins i : Transitive (per_subtyp i). *)
(* Proof. *)
(*   eauto using per_subtyp_trans. *)
(* Qed. *)

(* Lemma per_subtyp_transp : forall a b i a' b' R R', *)
(*     {{ Sub a <: b at i }} -> *)
(*     {{ DF a ≈ a' ∈ per_sort_elem i ↘ R }} -> *)
(*     {{ DF b ≈ b' ∈ per_sort_elem i ↘ R' }} -> *)
(*     {{ Sub a' <: b' at i }}. *)
(* Proof. *)
(*   mauto using per_subtyp_refl1, per_subtyp_refl2. *)
(* Qed. *)

(* Lemma per_subtyp_cumu : forall a1 a2 i, *)
(*     {{ Sub a1 <: a2 at i }} -> *)
(*     forall j, *)
(*       i <= j -> *)
(*       {{ Sub a1 <: a2 at j }}. *)
(* Proof. *)
(*   induction 1; intros; econstructor; mauto. *)
(*   lia. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve per_subtyp_cumu : mcpts. *)

(* Lemma per_subtyp_cumu_left : forall a1 a2 i j, *)
(*     {{ Sub a1 <: a2 at i }} -> *)
(*     {{ Sub a1 <: a2 at max i j }}. *)
(* Proof. *)
(*   intros. eapply per_subtyp_cumu; try eassumption. *)
(*   lia. *)
(* Qed. *)

(* Lemma per_subtyp_cumu_right : forall a1 a2 i j, *)
(*     {{ Sub a1 <: a2 at i }} -> *)
(*     {{ Sub a1 <: a2 at max j i }}. *)
(* Proof. *)
(*   intros. eapply per_subtyp_cumu; try eassumption. *)
(*   lia. *)
(* Qed. *)

Add Parametric Morphism {P : PtsSig} {pred_P : PredicativeSig P} : (per_typ_elem pred_P)
  with signature (@relation_equivalence (domain P)) ==> eq ==> eq ==> iff as per_typ_elem_morphism_iff.
Proof with mautosolve.
  intros R R' HRR'.  
  split; intro Horig; [gen R' | gen R];
    induction Horig; econstructor;
    apply_relation_equivalence; try reflexivity; try eassumption.
Qed.

Add Parametric Morphism {P : PtsSig} {pred_P : PredicativeSig P} : (per_typ_elem pred_P)
  with signature (@relation_equivalence (domain P)) ==> (@relation_equivalence (domain P)) as per_typ_elem_morphism_relation_equivalence.
Proof.
  intros * H ? ?.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma per_typ_elem_right_irrel {P : PtsSig} {pred_P : PredicativeSig P} : forall a b b' R R',
    {{ DF a ≈ b ∈ per_typ_elem pred_P ↘ R }} ->
    {{ DF a ≈ b' ∈ per_typ_elem pred_P ↘ R' }} ->
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


Lemma per_typ_elem_sym {P} {pred_P : PredicativeSig P} : forall {R a b},
    {{ DF a ≈ b ∈ per_typ_elem pred_P ↘ R }} ->
    {{ DF b ≈ a ∈ per_typ_elem pred_P ↘ R }} /\
      (forall m m',
          {{ Dom m ≈ m' ∈ R }} ->
          {{ Dom m' ≈ m ∈ R }}).
Proof with mautosolve.
  simpl.
  induction 1; split.
  - econstructor; mauto.
  - apply_relation_equivalence.
    intros.
    eapply per_sort_sym'; mauto.
  - assert (per_sort_elem pred_P s R b a) by (eapply per_sort_sym; mauto).
    econstructor; mauto.
  - intros.
    eapply per_elem_sym; mauto.
Qed.

Corollary per_typ_elem_left_irrel {P} {pred_P : PredicativeSig P} : forall R a b R' a',
    {{ DF a ≈ b ∈ per_typ_elem pred_P ↘ R }} ->
    {{ DF a' ≈ b ∈ per_typ_elem pred_P ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ?%per_typ_elem_sym ?%per_typ_elem_sym.
  destruct_conjs.
  eauto using per_typ_elem_right_irrel.
Qed.

Corollary per_typ_elem_cross_irrel {P} {pred_P : PredicativeSig P} : forall R a b R' b',
    {{ DF a ≈ b ∈ per_typ_elem pred_P ↘ R }} ->
    {{ DF b' ≈ a ∈ per_typ_elem pred_P ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ? ?%per_typ_elem_sym.
  destruct_conjs.
  eauto using per_typ_elem_right_irrel.
Qed.

Ltac do_per_typ_elem_irrel_assert1 :=
  let tactic_error o1 o2 := fail 2 "per_typ_elem_irrel biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ DF ^?a ≈ ^_ ∈ per_typ_elem ?pred_P ↘ ?R1 }},
      H2 : {{ DF ^?a ≈ ^_ ∈ per_typ_elem ?pred_P ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_typ_elem_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ^_ ≈ ^?b ∈ per_typ_elem ?pred_P ↘ ?R1 }},
      H2 : {{ DF ^_ ≈ ^?b ∈ per_typ_elem ?pred_P ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_typ_elem_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ^?a ≈ ^_ ∈ per_typ_elem ?pred_P ↘ ?R1 }},
      H2 : {{ DF ^_ ≈ ^?a ∈ per_typ_elem ?pred_P ↘ ?R2 }} |- _ =>
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


Lemma per_typ_elem_trans {P} {pred_P : PredicativeSig P} : forall R a1 a2,
    {{ DF a1 ≈ a2 ∈ per_typ_elem pred_P ↘ R }} ->
    (forall a3,
        {{ DF a2 ≈ a3 ∈ per_typ_elem pred_P ↘ R }} ->
        {{ DF a1 ≈ a3 ∈ per_typ_elem pred_P ↘ R }}) /\
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
      eapply per_sort_trans'; mauto.
  - split.
    + intros.
      dependent destruction H0.
      * apply_relation_equivalence.
        econstructor; mauto.
      * assert (per_sort_elem pred_P s R a b) by (eapply per_sort_trans; mauto).
        econstructor; mauto.
    + apply_relation_equivalence.
      eapply per_sort_elem_trans; mauto.
Qed.

#[export]
Instance per_typ_elem_PER {P} {pred_P : PredicativeSig P} {R} : PER (per_typ_elem pred_P R).
Proof.
  split.
  - intros x y H.
    eapply (per_typ_elem_sym H).
  - intros x y z Hxy Hyz.
    eapply (proj1 (per_typ_elem_trans R x y Hxy) z Hyz).
Qed.


Corollary per_typ_sym {P} {pred_P : PredicativeSig P} : forall a b,
    {{ Dom a ≈ b ∈ per_typ pred_P }} ->
    {{ Dom b ≈ a ∈ per_typ pred_P }}.
Proof.
  intros * [? ?%per_typ_elem_sym].
  firstorder.
Qed.

Corollary per_typ_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall a1 a2 a3,
    {{ Dom a1 ≈ a2 ∈ per_typ pred_P }} ->
    {{ Dom a2 ≈ a3 ∈ per_typ pred_P }} ->
    {{ Dom a1 ≈ a3 ∈ per_typ pred_P }}.
Proof.
  intros * [? ?] [? ?].
  handle_per_typ_elem_irrel.
  assert (per_typ_elem pred_P x0 a1 a3) by (eapply (proj1 (per_typ_elem_trans x0 a1 a2 H) a3 H0); mauto).
  mauto.
Qed.

#[export]
Instance per_typ_PER {P} {pred_P : PredicativeSig P} : PER (per_typ pred_P).
Proof.
  split.
  - intros x y H.
    eapply per_typ_sym; mauto.
  - intros x y z Hxy Hyz.
    eapply per_typ_trans; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} {pred_P : PredicativeSig P} : (per_ctx_env pred_P)
    with signature (@relation_equivalence (env P)) ==> eq ==> eq ==> iff as per_ctx_env_morphism_iff.
Proof with mautosolve.
  intros R R' HRR'.
  split; intro Horig; [gen R' | gen R];
    induction Horig; econstructor;
    apply_relation_equivalence; try reflexivity...
Qed.

Add Parametric Morphism {P : PtsSig} {pred_P : PredicativeSig P} : (per_ctx_env pred_P)
    with signature (@relation_equivalence (env P)) ==> (@relation_equivalence (ctx P)) as per_ctx_env_morphism_relation_equivalence.
Proof.
  intros * HRR' Γ Γ'.
  simpl.
  rewrite HRR'.
  reflexivity.
Qed.

Lemma per_ctx_env_right_irrel {P : PtsSig} {pred_P : PredicativeSig P} : forall Γ Δ Δ' R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env pred_P ↘ R }} ->
    {{ DF Γ ≈ Δ' ∈ per_ctx_env pred_P ↘ R' }} ->
    R <~> R'.
Proof with (destruct_rel_typ; handle_per_sort_elem_irrel; eexists; intuition).
  intros * Horig; gen Δ' R'.
  induction Horig; intros * Hright;
    inversion Hright; subst;
    apply_relation_equivalence;
    try reflexivity.
  specialize (IHHorig _ _ equiv_Γ_Γ'0).
  intros ρ ρ'.
  split; intros Hcons; dependent destruction Hcons.
  - assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel0 }} by intuition.
    assert (rel_typ_unsorted pred_P A _ A' _ (head_rel _ _ equiv_ρ_drop_ρ'_drop)) by mauto.
    assert (rel_typ_unsorted pred_P A _ A'0 _ (head_rel0 _ _ H5)) by mauto.
    inversion_clear H7.
    inversion_clear H8.
    simplify_evals.
    handle_per_typ_elem_irrel.
    econstructor; mauto; [econstructor; mauto | econstructor; mauto |].
    eapply H1.
    eassumption.

  - assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel }} by intuition.
    assert (rel_typ_unsorted pred_P A _ A' _ (head_rel _ _ H5)) by mauto.
    assert (rel_typ_unsorted pred_P A _ A'0 _ (head_rel0 _ _ equiv_ρ_drop_ρ'_drop)) by mauto.
    inversion_clear H7.
    inversion_clear H8.
    simplify_evals.
    handle_per_typ_elem_irrel.
    econstructor; mauto; [econstructor; mauto | econstructor; mauto |].
    eapply H1.
    eassumption.
Qed.

Lemma per_ctx_env_sym {P : PtsSig} {pred_P : PredicativeSig P} : forall Γ Δ R,
    {{ DF Γ ≈ Δ ∈ per_ctx_env pred_P ↘ R }} ->
    {{ DF Δ ≈ Γ ∈ per_ctx_env pred_P ↘ R }} /\
      (forall ρ ρ',
          {{ Dom ρ ≈ ρ' ∈ R }} ->
          {{ Dom ρ' ≈ ρ ∈ R }}).
Proof with solve [intuition].
  simpl.
  induction 1; split; simpl in *; destruct_conjs; try econstructor; intuition;
    pose proof (@relation_equivalence_pointwise (env P)).
  - assert (tail_rel ρ' ρ) by eauto.
    assert (tail_rel ρ ρ) by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    handle_per_typ_elem_irrel.
    econstructor; eauto.
    symmetry...
  - apply_relation_equivalence.
    destruct_by_head (@cons_per_ctx_env P).
    assert (tail_rel d{{{ ρ' ↯ }}} d{{{ ρ ↯ }}}) by eauto.
    assert (tail_rel d{{{ ρ ↯ }}} d{{{ ρ ↯ }}}) by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    handle_per_typ_elem_irrel.
    eexists; [eassumption | eassumption |].
    eapply H13.
    eapply (per_typ_elem_sym); mauto.
Qed.

Corollary per_ctx_sym {P : PtsSig} {pred_P : PredicativeSig P} : forall Γ Δ R,
    {{ DF Γ ≈ Δ ∈ per_ctx_env pred_P ↘ R }} ->
    {{ DF Δ ≈ Γ ∈ per_ctx_env pred_P ↘ R }}.
Proof.
  intros * ?%per_ctx_env_sym.
  firstorder.
Qed.

Corollary per_env_sym {P : PtsSig} {pred_P : PredicativeSig P} : forall Γ Δ R ρ ρ',
    {{ DF Γ ≈ Δ ∈ per_ctx_env pred_P ↘ R }} ->
    {{ Dom ρ ≈ ρ' ∈ R }} ->
    {{ Dom ρ' ≈ ρ ∈ R }}.
Proof.
  intros * ?%per_ctx_env_sym.
  firstorder.
Qed.

Corollary per_ctx_env_left_irrel {P : PtsSig} {pred_P : PredicativeSig P} : forall Γ Γ' Δ R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env pred_P ↘ R }} ->
    {{ DF Γ' ≈ Δ ∈ per_ctx_env pred_P ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ?%per_ctx_sym ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Corollary per_ctx_env_cross_irrel {P : PtsSig} {pred_P : PredicativeSig P} : forall Γ Δ Δ' R R',
    {{ DF Γ ≈ Δ ∈ per_ctx_env pred_P ↘ R }} ->
    {{ DF Δ' ≈ Γ ∈ per_ctx_env pred_P ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ? ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Ltac do_per_ctx_env_irrel_assert1 :=
  let tactic_error o1 o2 := fail 3 "per_ctx_env_irrel equality between" o1 "and" o2 "cannot be solved" in
  match goal with
    | H1 : {{ DF ^?Γ ≈ ^_ ∈ per_ctx_env ?pred_P ↘ ?R1 }},
        H2 : {{ DF ^?Γ ≈ ^_ ∈ per_ctx_env ?pred_P ↘ ?R2 }} |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : {{ DF ^_ ≈ ^?Δ ∈ per_ctx_env ?pred_P ↘ ?R1 }},
        H2 : {{ DF ^_ ≈ ^?Δ ∈ per_ctx_env ?pred_P ↘ ?R2 }} |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : {{ DF ^?Γ ≈ ^_ ∈ per_ctx_env ?pred_P ↘ ?R1 }},
        H2 : {{ DF ^_ ≈ ^?Γ ∈ per_ctx_env ?pred_P ↘ ?R2 }} |- _ =>
        (** Order matters less here as H1 and H2 cannot be exchanged *)
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_cross_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    end.

Ltac do_per_ctx_env_irrel_assert :=
  repeat do_per_ctx_env_irrel_assert1.

Ltac handle_per_ctx_env_irrel :=
  functional_eval_rewrite_clear;
  do_per_ctx_env_irrel_assert;
  apply_relation_equivalence;
  clear_dups.

Lemma per_ctx_env_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Γ1 Γ2 R,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env pred_P ↘ R }} ->
    (forall Γ3,
        {{ DF Γ2 ≈ Γ3 ∈ per_ctx_env pred_P ↘ R }} ->
        {{ DF Γ1 ≈ Γ3 ∈ per_ctx_env pred_P ↘ R }}) /\
      (forall ρ1 ρ2 ρ3,
          {{ Dom ρ1 ≈ ρ2 ∈ R }} ->
          {{ Dom ρ2 ≈ ρ3 ∈ R }} ->
          {{ Dom ρ1 ≈ ρ3 ∈ R }}).
Proof with solve [eauto using per_sort_trans].
  simpl.
  induction 1; subst;
    [> split;
     [ inversion 1; subst; eauto
     | intros; destruct_conjs; eauto] ..];
    pose proof (@relation_equivalence_pointwise (env P));
    handle_per_ctx_env_irrel;
    try solve [intuition].
  - econstructor; only 4: reflexivity; eauto.
    + apply_relation_equivalence. intuition.
    + intros.
      assert (tail_rel ρ ρ) by intuition.
      assert (tail_rel0 ρ ρ') by intuition.
      destruct_rel_typ_unsorted.
      handle_per_typ_elem_irrel.
      econstructor; mauto; intuition.
      (** This one cannot be replaced with `etransitivity` as we need different `i`s. *)
      do 3 (etransitivity; mauto).
      symmetry; mauto.
  - destruct_by_head (@cons_per_ctx_env P).
    assert (tail_rel d{{{ ρ ↯ }}} d{{{ ρ' ↯ }}}) by eauto.
    destruct_rel_typ_unsorted.
    handle_per_typ_elem_irrel.
    eexists; [eassumption | eassumption |].
    apply_relation_equivalence.
    
    eapply per_typ_elem_trans; mauto.
    + eapply H1; mauto.
    + eapply H15; mauto.
Qed.

Corollary per_ctx_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Γ1 Γ2 Γ3 R,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env pred_P ↘ R }} ->
    {{ DF Γ2 ≈ Γ3 ∈ per_ctx_env pred_P ↘ R }} ->
    {{ DF Γ1 ≈ Γ3 ∈ per_ctx_env pred_P ↘ R }}.
Proof.
  intros * ?% per_ctx_env_trans.
  firstorder.
Qed.

Corollary per_env_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Γ1 Γ2 R ρ1 ρ2 ρ3,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env pred_P ↘ R }} ->
    {{ Dom ρ1 ≈ ρ2 ∈ R }} ->
    {{ Dom ρ2 ≈ ρ3 ∈ R }} ->
    {{ Dom ρ1 ≈ ρ3 ∈ R }}.
Proof.
  intros * ?% per_ctx_env_trans.
  firstorder.
Qed.

#[export]
Instance per_ctx_PER {P : PtsSig} {pred_P : PredicativeSig P} {R} : PER (per_ctx_env pred_P R).
Proof.
  split.
  - auto using per_ctx_sym.
  - eauto using per_ctx_trans.
Qed.

#[export]
Instance per_env_PER {P : PtsSig} {pred_P : PredicativeSig P} {R Γ Δ} (H : per_ctx_env pred_P R Γ Δ) : PER R.
Proof.
  split.
  - pose proof (fun ρ ρ' => per_env_sym _ _ _ ρ ρ' H); auto.
  - pose proof (fun ρ0 ρ1 ρ2 => per_env_trans _ _ _ ρ0 ρ1 ρ2 H); eauto.
Qed.

(** This lemma removes the PER argument *)
Lemma per_ctx_env_cons' {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ Γ' A A' tail_rel}
                             (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}), relation (domain P))
                             env_rel,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P ↘ tail_rel }} ->
    (forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}),
        rel_typ_unsorted pred_P A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
    (env_rel <~> cons_per_ctx_env tail_rel (@head_rel)) ->
    {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env pred_P ↘ env_rel }}.
Proof.
  intros.
  econstructor; eauto.
  typeclasses eauto.
  
Qed.

#[export]
Hint Resolve per_ctx_env_cons' : mcpts.

Ltac per_ctx_env_econstructor :=
  (repeat intro; hnf; eapply per_ctx_env_cons') + econstructor.

Lemma per_ctx_env_cons_clean_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ Γ' env_relΓ A A' env_relΓA},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P ↘ env_relΓ }} ->
    {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env pred_P ↘ env_relΓA }} -> 
    exists (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}), relation (domain P)),
      (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
          rel_typ_unsorted pred_P A ρ A' ρ' (head_rel equiv_ρ_ρ')) /\
        (env_relΓA <~> cons_per_ctx_env env_relΓ (@head_rel)).
Proof with intuition.
  intros * HΓ HΓA.
  inversion HΓA; subst.
  handle_per_ctx_env_irrel.
  eexists.
  split; intros.
  - instantiate (1 := fun ρ ρ' (equiv_ρ_ρ' : env_relΓ ρ ρ') m m' =>
                        forall R,
                          rel_typ_unsorted pred_P A ρ A' ρ' R ->
                          {{ Dom m ≈ m' ∈ R }}).
    assert (tail_rel ρ ρ') by intuition.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    econstructor; eauto.
    apply -> per_typ_elem_morphism_iff; eauto.
    split; intros...
    destruct_by_head (@rel_typ_unsorted P).
    handle_per_typ_elem_irrel...
  - intros ρ ρ'.
    split; intros; destruct_by_head (@cons_per_ctx_env P);
    assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel }} by intuition;
      (on_all_hyp: destruct_rel_by_assumption tail_rel);
      unshelve (eexists; try eassumption); intros...
    destruct_by_head (@rel_typ_unsorted P).
    handle_per_typ_elem_irrel...
Qed.

Ltac invert_per_ctx_env H :=
  (unshelve eapply (per_ctx_env_cons_clean_inversion _) in H; [eassumption | |]; deex_in H; destruct H as [])
  + (inversion H; subst).

Ltac invert_per_ctx_envs := match_by_head per_ctx_env ltac:(fun H => directed invert_per_ctx_env H).

Ltac invert_per_ctx_envs_of pred_P rel := match_by_head (per_ctx_env pred_P rel) ltac:(fun H => directed invert_per_ctx_env H).

Lemma per_ctx_respects_length {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ Γ'},
    {{ Exp Γ ≈ Γ' ∈ per_ctx pred_P }} ->
    length Γ = length Γ'.
Proof.
  intros * [? H].
  induction H; simpl; congruence.
Qed.

Add Parametric Morphism {P} {pred_P : PredicativeSig P} A ρ A' ρ' : (rel_typ_unsorted pred_P A ρ A' ρ')
    with signature (@relation_equivalence (domain P)) ==> iff as rel_typ_unsorted_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    [setoid_rewrite <- HRR' | setoid_rewrite HRR']; eassumption.
Qed.

Lemma rel_typ_implies_rel_typ_unsorted {P} {pred_P : PredicativeSig P} : forall s A ρ A' ρ' R,
    rel_typ pred_P s A ρ A' ρ' R ->
    rel_typ_unsorted pred_P A ρ A' ρ' R.
Proof.
  intros * Hsorted.
  destruct Hsorted.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_typ_implies_rel_typ_unsorted : mcpts.


Lemma per_ctx_env_cons_clean_inversion_unsorted {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ Γ' env_relΓ A A' env_relΓA},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P ↘ env_relΓ }} ->
    {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env pred_P ↘ env_relΓA }} -> 
    exists (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}), relation (domain P)),
      (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
          rel_typ_unsorted pred_P A ρ A' ρ' (head_rel equiv_ρ_ρ')) /\
        (env_relΓA <~> cons_per_ctx_env env_relΓ (@head_rel)).
Proof with intuition.
  intros * HΓ HΓA.
  assert (exists (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}), relation (domain P)),
      (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
          rel_typ_unsorted pred_P A ρ A' ρ' (head_rel equiv_ρ_ρ')) /\
        (env_relΓA <~> cons_per_ctx_env env_relΓ (@head_rel))) by (eapply per_ctx_env_cons_clean_inversion; mauto).
  destruct_conjs.
  eexists.
  split; mauto.
Qed.

Ltac invert_per_ctx_env_unsorted H :=
  (unshelve eapply (per_ctx_env_cons_clean_inversion_unsorted _) in H; [eassumption | |]; deex_in H; destruct H as [])
  + (inversion H; subst).

Ltac invert_per_ctx_envs_unsorted := match_by_head per_ctx_env ltac:(fun H => directed invert_per_ctx_env_unsorted H).


Lemma per_typ_elem_and_per_sort_elem_implies_per_sort_elem {P} (pred_P : PredicativeSig P) : forall { a b c R R' s},
    {{ DF a ≈ b ∈ per_typ_elem pred_P ↘ R }} ->
    {{ DF a ≈ c ∈ per_sort_elem pred_P s ↘ R' }} ->
    {{ DF a ≈ b ∈ per_sort_elem pred_P s ↘ R }}.
Proof.
  intros * Hab.
  inversion_clear Hab; intros.
  - invert_per_sort_elem H0; mauto.
  - handle_per_sort_elem_irrel.
    assert (per_sort_elem pred_P s R c a) by (eapply (per_sort_elem_sym H0); mauto).
    assert (per_sort_elem pred_P s R c b) by (eapply (per_sort_elem_trans s R c a H1); eassumption).
    eapply (per_sort_elem_trans s R a c H0); eassumption.
Qed.

#[export]
Hint Resolve per_typ_elem_and_per_sort_elem_implies_per_sort_elem : mcpts.
