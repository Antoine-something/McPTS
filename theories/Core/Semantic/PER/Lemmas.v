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

Lemma per_nat_sym {P} : forall m n : domain P,
    {{ Dom m ≈ n ∈ per_nat }} ->
    {{ Dom n ≈ m ∈ per_nat }}.
Proof with mautosolve.
  induction 1; econstructor...
Qed.

#[export]
Hint Resolve per_nat_sym : mcpts.

Lemma per_nat_trans {P} : forall m n l : domain P,
    {{ Dom m ≈ n ∈ per_nat }} ->
    {{ Dom n ≈ l ∈ per_nat }} ->
    {{ Dom m ≈ l ∈ per_nat }}.
Proof with mautosolve.
  intros * H. gen l.
  induction H; inversion_clear 1; econstructor...
Qed.

#[export]
Hint Resolve per_nat_trans : mcpts.

#[export]
Instance per_nat_PER {P} : PER (@per_nat P).
Proof.
  split.
  - eauto using per_nat_sym.
  - eauto using per_nat_trans.
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
Proof with mautosolve 3.
  simpl.
  intros R R' HRR'.

  split; intros Horig; [gen R' | gen R];
    induction Horig;
    eauto;
    try (etransitivity; [symmetry + idtac|]; eassumption);
    intros;
    destruct_rel_mod_eval;
    econstructor; mauto 3.
  1-4: rewrite <- HRR'...
  all: rewrite HRR'...
Qed.

Add Parametric Morphism {P} {pred_P : PredicativeSig P} s : (per_sort_elem pred_P s)
    with signature (@relation_equivalence (domain P)) ==> eq ==> eq ==> iff as per_sort_elem_morphism_iff.
Proof with mautosolve 3.
  simp per_sort_elem.
  intros R R' HRR'.

  split; intros Horig; [gen R' | gen R];

    induction Horig;
    eauto;
    try (etransitivity; [symmetry + idtac|]; eassumption);
    intros;
    destruct_rel_mod_eval;
    econstructor; mauto 3.
  1-4: rewrite <- HRR'...
  all: rewrite HRR'...
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

Lemma per_sort_elem_pi_arg_helper {P} {pred_P : PredicativeSig P} : forall {s_in s_out s_pi s_elem a a' in_rel},
    Ru_pi P s_in s_out s_pi ->
    st_subtyp s_pi s_elem ->
    (s_in = s_elem -> {{ DF a ≈ a' ∈ per_sort_elem pred_P s_elem ↘ in_rel }}) /\ (pred_rel pred_P s_in s_elem -> {{ DF a ≈ a' ∈ per_sort_elem pred_P s_in ↘ in_rel }}) <-> {{ DF a ≈ a' ∈ per_sort_elem pred_P s_in ↘ in_rel }}.
Proof.
  intros * r sub.
  split; [intros [Heq Hlt] | split; intros; subst; eauto].
  destruct (ord_ru_pi_sub pred_P r sub) as [[|] _]; subst; eauto.
Qed.

Lemma per_sort_elem_pi_ret_helper {P} {pred_P : PredicativeSig P} : forall {s_in s_out s_pi s_elem ρ B ρ' B' in_rel} (out_rel : forall {n n'}, {{ Dom n ≈ n' ∈ in_rel }} -> relation (domain P)),
    Ru_pi P s_in s_out s_pi ->
    st_subtyp s_pi s_elem ->
    (forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
        rel_mod_eval (fun R b b' => (s_out = s_elem -> {{ DF b ≈ b' ∈ per_sort_elem pred_P s_elem ↘ R }}) /\ (pred_rel pred_P s_out s_elem -> {{ DF b ≈ b' ∈ per_sort_elem pred_P s_out ↘ R }})) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) <->
      (forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
          rel_mod_eval (per_sort_elem pred_P s_out) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')).
Proof.
  intros * r sub.
  split;
    [ intros Hbare *; specialize (Hbare n n' equiv_n_n') as [? ? ? ? [Heq Hlt]]
    | intros Helab *; specialize (Helab n n' equiv_n_n') as []]; econstructor; eauto.
  - destruct (ord_ru_pi_sub pred_P r sub) as [_ [|]]; subst; eauto.
  - split; intros; subst; eauto.
Qed.

Lemma per_sort_elem_pi_left_inversion {P} {pred_P : PredicativeSig P} : forall {s_in s_out s s'} {r : Ru_pi P s_in s_out s} {a ρ B c' elem_rel},
    {{ DF Π r a ρ B ≈ c' ∈ per_sort_elem pred_P s' ↘ elem_rel }} ->
    exists a' ρ' B' in_rel (out_rel : forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), relation (domain P)),
      st_subtyp s s' /\
      c' = d{{{ Π r a' ρ' B' }}} /\
        {{ DF a ≈ a' ∈ per_sort_elem pred_P s_in ↘ in_rel }} /\
        (forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
            rel_mod_eval (per_sort_elem pred_P s_out) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) /\
        (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app f n f' n' (out_rel equiv_n_n')).
Proof.
  intros * H.
  basic_invert_per_sort_elem H.
  erewrite (per_sort_elem_pi_arg_helper r sub) in equiv_a_a'.
  erewrite (per_sort_elem_pi_ret_helper _ r sub) in H0.
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
  assert (per_sort_elem pred_P s_in in_rel0 a a'0).
  {
    destruct equiv_a_a' as [equiv_a_a'_eq equiv_a_a'_rel].
    pose proof ord_ru_pi_sub pred_P r sub0 as [].
    destruct H2; subst; mauto 3.
  }
  assert (in_rel <~> in_rel0) by mauto 3.
  split; intros.
  - rename equiv_n_n' into equiv0_n_n'.
    specialize (H4 n n' equiv0_n_n').
    inversion_clear H4.
    assert (per_sort_elem pred_P s_out (out_rel0 n n' equiv0_n_n') a0 a'1).
    {
      destruct H9.
      pose proof ord_ru_pi_sub pred_P r sub0 as [].
      destruct H11; subst; mauto 3.
    }
    assert (equiv_n_n' : in_rel n n') by firstorder...
  - assert (equiv0_n_n' : in_rel0 n n') by firstorder.
    specialize (H4 n n' equiv0_n_n').
    inversion_clear H4.
    assert (per_sort_elem pred_P s_out (out_rel0 n n' equiv0_n_n') a0 a'1).
    {
      destruct H9.
      pose proof ord_ru_pi_sub pred_P r sub0 as [].
      destruct H11; subst; mauto 3.
    }
    idtac...
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

Lemma per_sort_elem_pi_econstructor {P} {pred_P : PredicativeSig P} : forall {s_in s_out s_pi s a ρ B a' ρ' B'} (r : Ru_pi P s_in s_out s_pi) (sub : st_subtyp s_pi s) {in_rel} (out_rel : forall {n n'}, {{ Dom n ≈ n' ∈ in_rel }} -> relation (domain P)) {elem_rel} (equiv_a_a' : {{ DF a ≈ a' ∈ per_sort_elem pred_P s_in ↘ in_rel }}),
    PER in_rel ->
    (forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
        rel_mod_eval (per_sort_elem pred_P s_out) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) ->
    (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app f n f' n' (out_rel equiv_n_n')) ->
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P s ↘ elem_rel }}.
Proof.
  intros.
  rewrite <- (per_sort_elem_pi_arg_helper r sub) in equiv_a_a'.
  rewrite <- (per_sort_elem_pi_ret_helper _ r sub) in H0.
  basic_per_sort_elem_econstructor; eauto.
Qed.

#[local]
Ltac per_sort_elem_econstructor' :=
  (repeat intro; hnf; eapply per_sort_elem_pi_econstructor) + basic_per_sort_elem_econstructor.

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
    + apply per_sort_elem_core_sort' with (s2 := s2); firstorder.
    + intros.
      rewrite_relation_equivalence_left.
      destruct_by_head (per_sort pred_P).
      eexists.
      eapply proj1...
  - destruct_conjs.
    split.
    + per_sort_elem_econstructor'; eauto.
      intros.
      assert (in_rel n' n) by eauto.
      assert (in_rel n n) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      simplify_evals.
      econstructor; eauto.
      per_sort_elem_right_irrel_assert.
      rewrite_relation_equivalence_left.
      eassumption.
    + apply_relation_equivalence.
      intros.
      assert (in_rel n' n) by eauto.
      assert (in_rel n n) by (etransitivity; eassumption).
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      simplify_evals.
      econstructor; eauto.
      per_sort_elem_right_irrel_assert.
      intuition.
  - split; [per_sort_elem_econstructor' | apply_relation_equivalence]; mauto 3.
  - split; [per_sort_elem_econstructor' | apply_relation_equivalence]; mauto 3.
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
    pose proof (ord_ru_pi_sub pred_P r sub0) as [ord_dom ord_im].
    assert (per_sort_elem pred_P s_in in_rel0 a' a'0) by (destruct ord_dom; subst; mauto 2).
    per_sort_elem_econstructor'; eauto.
    + handle_per_sort_elem_irrel.
      intuition.
    + intros.
      pose proof (H4 n n' equiv_n_n').
      inversion_clear H11.
      destruct_conjs.
      assert (per_sort_elem pred_P s_out (out_rel0 n n' equiv_n_n') a0 a'1) by (destruct ord_im; subst; mauto 2).
      handle_per_sort_elem_irrel.
      assert (in_rel n n') by firstorder.
      assert (in_rel n n) by intuition.
      assert (in_rel0 n n') by intuition.
      pose proof (H1 n n' H0).
      inversion_clear H18.
      pose proof (H1 n n H5).
      inversion_clear H18.
      destruct_conjs.
      functional_eval_rewrite_clear.
      handle_per_sort_elem_irrel.
      econstructor; mauto 2.
  - (* fun case *)
    intros.
    assert (in_rel n n) by intuition.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    handle_per_sort_elem_irrel.
    econstructor; eauto.
    intuition.
  - (* nat case *)
    per_sort_elem_econstructor'; [eapply r| |]; mauto 2.
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
  forall s_in s_out s_pi s (r : Ru_pi P s_in s_out s_pi) (sub : st_subtyp s_pi s) a a' ρ B ρ' B'
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

Lemma per_sort_elem_pi_clean_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {s_in s_out s_pi s} {r : Ru_pi P s_in s_out s_pi} {sub : st_subtyp s_pi s} {a a' in_rel ρ ρ' B B' elem_rel},
    {{ DF a ≈ a' ∈ per_sort_elem pred_P s_in ↘ in_rel }} ->
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P s ↘ elem_rel }} ->
    exists (out_rel : forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), relation (domain P)),
      (forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
          rel_mod_eval (per_sort_elem pred_P s_out) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) /\
        (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app f n f' n' (out_rel equiv_n_n')).
Proof.
  intros * sub * Ha HΠ.
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
    split; [| intuition].
    intros.
    destruct_by_head (@rel_typ P).
    handle_per_sort_elem_irrel.
    intuition.
  - split; intros;
      [assert (in_rel0 n n') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel0)
      | assert (in_rel n n') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel)];
      econstructor; intuition.
    destruct_by_head (@rel_typ P).
    handle_per_sort_elem_irrel.
    intuition.
Qed.

Ltac invert_per_sort_elem H :=
  (unshelve eapply (per_sort_elem_pi_clean_inversion _) in H; shelve_unifiable; [eassumption |]; destruct H as [? []])
  + invert_per_sort_elem' H.

Ltac invert_per_sort_elems := match_by_head per_sort_elem ltac:(fun H => directed invert_per_sort_elem H).


Lemma per_sort_elem_cumu {P} {pred_P : PredicativeSig P} : forall s1 s2 a b R,
    st_subtyp s1 s2 ->
    {{ DF a ≈ b ∈ per_sort_elem pred_P s1 ↘ R }} ->
    {{ DF a ≈ b ∈ per_sort_elem pred_P s2 ↘ R }}.
Proof.
  simpl.
  induction 2 using per_sort_elem_ind; subst.
  - eapply per_sort_elem_core_sort'; eauto.
    transitivity s_elem; eauto.
  - per_sort_elem_econstructor; eauto.    
    + transitivity s_elem; eauto.
    + intros.
      destruct_rel_mod_eval.
      econstructor; eauto.
  - per_sort_elem_econstructor; eauto.
    transitivity s_elem; mauto 2.
  - per_sort_elem_econstructor; eauto.
Qed.

#[export]
Hint Resolve per_sort_elem_cumu : mcpts.
 
Lemma per_subtyp_sorted_to_sort_elem {P} {pred_P : PredicativeSig P} : forall a b s,
    {{ ⟪ pred_P ⟫ Subs a <: b at s }} ->
    exists R R',
      {{ DF a ≈ a ∈ per_sort_elem pred_P s ↘ R }} /\
        {{ DF b ≈ b ∈ per_sort_elem pred_P s ↘ R' }}.
Proof.
  destruct 1;
    match_by_head @per_sort ltac:(fun H => destruct H);
    repeat eexists; mauto 2;
    per_sort_elem_econstructor; try reflexivity;
    etransitivity; try eassumption; symmetry; eassumption.
Qed.

Lemma per_elem_subtyping_sorted {P} {pred_P : PredicativeSig P} : forall A B s,
    {{ ⟪ pred_P ⟫ Subs A <: B at s }} ->
    forall R R' a b,
      {{ DF A ≈ A ∈ per_sort_elem pred_P s ↘ R }} ->
      {{ DF B ≈ B ∈ per_sort_elem pred_P s ↘ R' }} ->
      R a b ->
      R' a b.
Proof.  
  induction 1; intros;
    match_by_head (@per_sort) ltac:(fun H => destruct H);
    handle_per_sort_elem_irrel;
    saturate_refl;
    (on_all_hyp: fun H => directed invert_per_sort_elem H);
    handle_per_sort_elem_irrel;
    clear_refl_eqs;
    trivial.
  - unfold per_sort_rec in *.    
    firstorder mauto.
      
  - intros.
    destruct_conjs.
    pose proof (ord_ru_pi_sub pred_P r sub1) as [ord_dom ord_im].
    assert (per_sort_elem pred_P s1 in_rel1 a' a') by (destruct ord_dom; subst; mauto 2).
    assert (per_sort_elem pred_P s1 in_rel0 a a) by (destruct ord_dom; subst; mauto 2).
    handle_per_sort_elem_irrel.
    assert (in_rel0 n n') as equiv0_n_n' by (apply_relation_equivalence; mauto 2).
    clear ord_dom ord_im.
    destruct_rel_mod_eval.
    pose proof (ord_ru_pi_sub pred_P r sub1) as [ord_dom ord_im].
    assert (per_sort_elem pred_P s2 (out_rel0 n n' equiv_n_n') a1 a'0) by (destruct ord_im; subst; mauto 2).
    assert (per_sort_elem pred_P s2 (out_rel n n' equiv0_n_n') a2 a'1) by (destruct ord_im; subst; mauto 2).
    saturate_refl_for (@per_sort_elem P).
    clear ord_dom ord_im.
    handle_per_sort_elem_irrel.    
    destruct_rel_mod_app.
    simplify_evals.
    econstructor; intuition.
Qed.


Lemma per_elem_subtyping_sorted_gen {P} {pred_P : PredicativeSig P} : forall a b s a' b' R R' m n,
    {{ ⟪ pred_P ⟫ Subs a <: b at s }} ->
    {{ DF a ≈ a' ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ DF b ≈ b' ∈ per_sort_elem pred_P s ↘ R' }} ->
    R m n ->
    R' m n.
Proof.
  intros.
  eapply per_elem_subtyping_sorted; saturate_refl; try eassumption.
Qed.

Lemma per_subtyp_sorted_refl1 {P} {pred_P : PredicativeSig P} : forall a b s R,
    {{ DF a ≈ b ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ ⟪ pred_P ⟫ Subs a <: b at s }}.
Proof.
  simpl; induction 1 using per_sort_elem_ind;
    subst;
    mauto;
    destruct_all.
  - assert (st_subtyp s1' s1') by econstructor.
    econstructor; mauto 4.    
    
  - assert ({{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P s_elem ↘ elem_rel }})
      by (per_sort_elem_econstructor; intuition; destruct_rel_mod_eval; mauto).
    saturate_refl_for (@per_sort_elem P).
    econstructor; eauto.
    intros;
      destruct_rel_mod_eval;
      functional_eval_rewrite_clear;
      trivial.
  - econstructor; mauto 3.
    eexists.
    per_sort_elem_econstructor; eauto.
Qed.

#[export]
Hint Resolve per_subtyp_sorted_refl1 : mcpts.

Lemma per_subtyp_sorted_refl2 {P} {pred_P : PredicativeSig P} : forall a b s R,
    {{ DF a ≈ b ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ ⟪ pred_P ⟫ Subs b <: a at s }}.
Proof.
  intros.
  symmetry in H.
  eauto using per_subtyp_sorted_refl1.
Qed.

#[export]
Hint Resolve per_subtyp_sorted_refl2 : mcpts.

Lemma per_subtyp_sorted_trans {P} {pred_P : PredicativeSig P} : forall a1 a2 s,
    {{ ⟪ pred_P ⟫ Subs a1 <: a2 at s }} ->
    forall a3,
      {{ ⟪ pred_P ⟫ Subs a2 <: a3 at s }} ->
      {{ ⟪ pred_P ⟫ Subs a1 <: a3 at s }}.
Proof.
  induction 1; intros ? Hsub; simpl in *.
  (* Universe, nat and neutral cases *)
  1,2,4: progressive_inversion; mauto.
  - econstructor; mauto 2.
    transitivity s2; mauto 2.
  - dependent destruction Hsub; subst.
    handle_per_sort_elem_irrel.
    econstructor; eauto.
    + etransitivity; eassumption.
    + intros.
      (* (on_all_hyp: fun H => directed invert_per_sort_elem H).       *)
      saturate_refl_for (@per_sort_elem P).
      saturate_refl_for in_rel0.
      (on_all_hyp: fun H => directed invert_per_sort_elem H).
      destruct_conjs.
      assert (per_sort_elem pred_P s1 in_rel a a).
      {
        pose proof (ord_ru_pi_sub pred_P r sub) as [ord_dom ord_im].
        destruct ord_dom; subst; mauto 2.
      }
      assert (per_sort_elem pred_P s1 in_rel1 a' a').
      {
        pose proof (ord_ru_pi_sub pred_P r sub) as [ord_dom ord_im].
        destruct ord_dom; subst; mauto 2.
      }
      assert (per_sort_elem pred_P s1 in_rel2 a'0 a'0).
      {
        pose proof (ord_ru_pi_sub pred_P r sub) as [ord_dom ord_im].
        destruct ord_dom; subst; mauto 2.
      }
      handle_per_sort_elem_irrel.
      destruct_rel_mod_eval.
      handle_per_sort_elem_irrel.
      assert (per_sort_elem pred_P s2 (out_rel1 c' c' H19) b' b').
      {
        pose proof (ord_ru_pi_sub pred_P r sub2) as [ord_dom ord_im].
        destruct ord_im; subst; mauto 2.
      }
      assert (per_sort_elem pred_P s2 (out_rel1 c c' H13) a1 b').
      {
        pose proof (ord_ru_pi_sub pred_P r sub2) as [ord_dom ord_im].
        destruct ord_im; subst; mauto 2.
      }
      assert (per_sort_elem pred_P s2 (out_rel1 c c H18) a1 a1).
      {
        pose proof (ord_ru_pi_sub pred_P r sub2) as [ord_dom ord_im].
        destruct ord_im; subst; mauto 2.
      }
      handle_per_sort_elem_irrel.
      assert (in_rel c c') by (apply_relation_equivalence; eassumption).
      assert (in_rel1 c c') by (apply_relation_equivalence; eassumption).
      assert (PER in_rel).
      {
        split.
        - intros x y Hxy.
          eapply H29 in Hxy.
          eapply H29.
          symmetry.
          eassumption.
        - intros x y z Hxy Hyz.
          eapply H29.
          eapply H29 in Hxy.
          eapply H29 in Hyz.
          transitivity y; eassumption.
      }
      saturate_refl_for in_rel.
      saturate_refl_for in_rel1.
      destruct_rel_mod_eval.
      simplify_evals.
      
      assert {{ ⟪ pred_P ⟫ Subs b <: a5 at s2 }} by (eapply (H0 c c); mauto 3).
      assert {{ ⟪ pred_P ⟫ Subs a5 <: b' at s2 }} by (eapply (H6 c c'); mauto 3).
      eapply (H1 c c'); mauto 3.
Qed.

#[export]
Hint Resolve per_subtyp_sorted_trans : mcpts.

#[export]
Instance per_subtyp_sorted_trans_ins {P} {pred_P : PredicativeSig P} s : Transitive (per_subtyp_sorted pred_P s).
Proof.
  eauto using per_subtyp_sorted_trans.
Qed.

Lemma per_subtyp_sorted_transp {P} {pred_P : PredicativeSig P} : forall a b s a' b' R R',
    {{ ⟪ pred_P ⟫ Subs a <: b at s }} ->
    {{ DF a ≈ a' ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ DF b ≈ b' ∈ per_sort_elem pred_P s ↘ R' }} ->
    {{ ⟪ pred_P ⟫ Subs a' <: b' at s }}.
Proof.
  mauto using per_subtyp_sorted_refl1, per_subtyp_sorted_refl2.
Qed.

Lemma per_subtyp_sorted_cumu {P} {pred_P : PredicativeSig P} : forall a1 a2 s,
    {{ ⟪ pred_P ⟫ Subs a1 <: a2 at s }} ->
    forall s',
      st_subtyp s s' ->
      {{ ⟪ pred_P ⟫ Subs a1 <: a2 at s' }}.
Proof.
  induction 1; intros; econstructor; mauto;
    match_by_head (@per_sort P) ltac:(fun H => destruct H);
    only 4: (etransitivity; eassumption);
    eexists; mauto 2.
Qed.

#[export]
Hint Resolve per_subtyp_sorted_cumu : mcpts.


(** Lemmas for per_typ_elem and per_typ *)
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
  - assert {{ DF b ≈ a ∈ per_sort_elem pred_P s ↘ R }} by (eapply per_sort_sym; mauto).
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
      * assert {{ DF a ≈ b ∈ per_sort_elem pred_P s ↘ R }} by (eapply per_sort_trans; mauto).
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
  - intros x y **.
    eapply (per_typ_elem_trans R x y ltac:(eassumption)); eassumption.
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

(** Lemmas for per_ctx_env and per_ctx *)
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
  split; intros Hcons; dependent destruction Hcons;
    [ assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel0 }} by intuition
    | assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel }} by intuition ];
    assert (rel_typ pred_P s A _ A' _ (head_rel _ _ ltac:(eassumption))) by mauto 3;
    assert (rel_typ pred_P s A _ A'0 _ (head_rel0 _ _ ltac:(eassumption))) by mauto 3;
    inversion_clear_by_head (@rel_typ P);
    simplify_evals;
    handle_per_sort_elem_irrel;
    econstructor; mauto 3;
    intuition.
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
    handle_per_sort_elem_irrel.
    econstructor; eauto.
    symmetry...
  - apply_relation_equivalence.
    destruct_by_head (@cons_per_ctx_env P).
    assert (tail_rel d{{{ ρ' ↯ }}} d{{{ ρ ↯ }}}) by eauto.
    assert (tail_rel d{{{ ρ ↯ }}} d{{{ ρ ↯ }}}) by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    handle_per_sort_elem_irrel.
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
      destruct_rel_typ.
      handle_per_sort_elem_irrel.
      econstructor; mauto; intuition.
      (** This one cannot be replaced with `etransitivity` as we need different `i`s. *)
      do 3 (etransitivity; mauto).
      symmetry; mauto.
  - destruct_by_head (@cons_per_ctx_env P).
    assert (tail_rel d{{{ ρ ↯ }}} d{{{ ρ' ↯ }}}) by eauto.
    destruct_rel_typ.
    handle_per_sort_elem_irrel.
    eexists; [eassumption | eassumption |].
    apply_relation_equivalence.

    eapply per_sort_elem_trans; intuition.
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
Lemma per_ctx_env_cons' {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ Γ' A A' tail_rel s}
                             (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}), relation (domain P))
                             env_rel,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P ↘ tail_rel }} ->
    (forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}),
        rel_typ pred_P s A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
    (env_rel <~> cons_per_ctx_env tail_rel (@head_rel)) ->
    {{ EF Γ, A@s ≈ Γ', A'@s ∈ per_ctx_env pred_P ↘ env_rel }}.
Proof.
  intros.
  econstructor; eauto.
  typeclasses eauto.
Qed.

#[export]
Hint Resolve per_ctx_env_cons' : mcpts.

Ltac per_ctx_env_econstructor :=
  (repeat intro; hnf; eapply per_ctx_env_cons') + econstructor.

Lemma per_ctx_env_cons_clean_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ Γ' env_relΓ A A' env_relΓA s},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P ↘ env_relΓ }} ->
    {{ EF Γ, A@s ≈ Γ', A'@s ∈ per_ctx_env pred_P ↘ env_relΓA }} ->
    exists (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}), relation (domain P)),
      (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
          rel_typ pred_P s A ρ A' ρ' (head_rel equiv_ρ_ρ')) /\
        (env_relΓA <~> cons_per_ctx_env env_relΓ (@head_rel)).
Proof with intuition.
  intros * HΓ HΓA.
  inversion HΓA; subst.
  handle_per_ctx_env_irrel.
  eexists.
  split; intros.
  - instantiate (1 := fun ρ ρ' (equiv_ρ_ρ' : env_relΓ ρ ρ') m m' =>
                        forall R,
                          rel_typ pred_P s A ρ A' ρ' R ->
                          {{ Dom m ≈ m' ∈ R }}).
    assert (tail_rel ρ ρ') by intuition.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    econstructor; eauto.
    apply -> per_sort_elem_morphism_iff; eauto.
    split; intros...
    destruct_by_head (@rel_typ P).
    handle_per_sort_elem_irrel...
  - intros ρ ρ'.
    split; intros; destruct_by_head (@cons_per_ctx_env P);
    assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel }} by intuition;
      (on_all_hyp: destruct_rel_by_assumption tail_rel);
      unshelve (eexists; try eassumption); intros...
    destruct_by_head (@rel_typ P).
    handle_per_sort_elem_irrel...
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

Lemma per_ctx_subtyp_to_env {P : PtsSig} {pred_P : PredicativeSig P} : forall Γ Δ,
    {{ ⟪ pred_P ⟫ SubE Γ <: Δ }} ->
    exists R R',
      {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ R }} /\
        {{ EF Δ ≈ Δ ∈ per_ctx_env pred_P ↘ R' }}.
Proof.
  destruct 1; destruct_all.
  - repeat eexists; econstructor; apply Equivalence_Reflexive.
  - eauto.
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


Lemma per_ctx_env_cons_clean_inversion_unsorted {P : PtsSig} (pred_P : PredicativeSig P) : forall {Γ Γ' env_relΓ A A' env_relΓA s},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P ↘ env_relΓ }} ->
    {{ EF Γ, A@s ≈ Γ', A'@s ∈ per_ctx_env pred_P ↘ env_relΓA }} ->
    exists (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}), relation (domain P)),
      (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
          rel_typ pred_P s A ρ A' ρ' (head_rel equiv_ρ_ρ')) /\
        (env_relΓA <~> cons_per_ctx_env env_relΓ (@head_rel)).
Proof with intuition.
  intros * HΓ HΓA.
  assert (exists (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}), relation (domain P)),
      (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
          rel_typ pred_P s A ρ A' ρ' (head_rel equiv_ρ_ρ')) /\
        (env_relΓA <~> cons_per_ctx_env env_relΓ (@head_rel))) by (eapply per_ctx_env_cons_clean_inversion; mauto).
  destruct_conjs.
  eexists.
  split; mauto.
Qed.

Ltac invert_per_ctx_env_unsorted H :=
  (unshelve eapply (per_ctx_env_cons_clean_inversion_unsorted _ _) in H; [eassumption | |]; deex_in H; destruct H as [])
  + (inversion H; subst).

Ltac invert_per_ctx_envs_unsorted := match_by_head per_ctx_env ltac:(fun H => directed invert_per_ctx_env_unsorted H).
Ltac invert_per_ctx_envs_unsorted_of pred_P rel := match_by_head (per_ctx_env pred_P rel) ltac:(fun H => directed invert_per_ctx_env_unsorted H).

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



Lemma per_subtyp_to_typ_elem {P} {pred_P : PredicativeSig P} : forall a b,
    {{ ⟪ pred_P ⟫ Sub a <: b }} ->
    exists R R',
      {{ DF a ≈ a ∈ per_typ_elem pred_P ↘ R }} /\
        {{ DF b ≈ b ∈ per_typ_elem pred_P ↘ R' }}.
Proof.
  destruct 1.
  - repeat eexists; econstructor; reflexivity.
  - pose proof (per_subtyp_sorted_to_sort_elem a b s H).
    destruct_conjs.
    repeat eexists; econstructor; eassumption.
Qed.


Lemma per_elem_subtyping {P} {pred_P : PredicativeSig P} : forall A B,
    {{ ⟪ pred_P ⟫ Sub A <: B }} ->
    forall R R' a b,
      {{ DF A ≈ A ∈ per_typ_elem pred_P ↘ R }} ->
      {{ DF B ≈ B ∈ per_typ_elem pred_P ↘ R' }} ->
      R a b ->
      R' a b.
Proof.
  destruct 1.
  - intros.
    assert (per_typ_elem pred_P (per_sort pred_P s1) d{{{ Sort@s1 }}} d{{{ Sort@s1 }}}) by (econstructor; reflexivity).
    assert (per_typ_elem pred_P (per_sort pred_P s2) d{{{ Sort@s2 }}} d{{{ Sort@s2 }}}) by (econstructor; reflexivity).
    handle_per_typ_elem_irrel.
    destruct H2 as [R].
    eexists; mauto 2.
  - intros.
    pose proof (per_subtyp_sorted_to_sort_elem a b s H).
    destruct_conjs.
    assert (per_typ_elem pred_P H3 a a) by mauto 2.
    assert (per_typ_elem pred_P H4 b b) by mauto 2.
    handle_per_typ_elem_irrel.
    eapply per_elem_subtyping_sorted; mauto 2.
Qed.    


Lemma per_elem_subtyping_gen {P} {pred_P : PredicativeSig P} : forall a b a' b' R R' m n,
    {{ ⟪ pred_P ⟫ Sub a <: b }} ->
    {{ DF a ≈ a' ∈ per_typ_elem pred_P ↘ R }} ->
    {{ DF b ≈ b' ∈ per_typ_elem pred_P ↘ R' }} ->
    R m n ->
    R' m n.
Proof.
  intros.
  eapply per_elem_subtyping; saturate_refl; try eassumption.
Qed.

Lemma per_subtyp_refl1 {P} {pred_P : PredicativeSig P} : forall a b R,
    {{ DF a ≈ b ∈ per_typ_elem pred_P ↘ R }} ->
    {{ ⟪ pred_P ⟫ Sub a <: b }}.
Proof.
  simpl; destruct 1.
  - econstructor; mauto 2.
  - pose proof (per_subtyp_sorted_refl1 _ _ _ _ H).
    econstructor; mauto 2.
Qed.

#[export]
Hint Resolve per_subtyp_refl1 : mcpts.

Lemma per_subtyp_refl2 {P} {pred_P : PredicativeSig P} : forall a b R,
    {{ DF a ≈ b ∈ per_typ_elem pred_P ↘ R }} ->
    {{ ⟪ pred_P ⟫ Sub b <: a }}.
Proof.
  intros.
  symmetry in H.
  eauto using per_subtyp_refl1.
Qed.

#[export]
Hint Resolve per_subtyp_refl2 : mcpts.

    
Lemma per_subtyp_trans_helper {P} {pred_P : PredicativeSig P} : forall {a1 a2 s},
    {{ ⟪ pred_P ⟫ Subs a1 <: a2 at s }} ->
    forall a3 s',
      {{ ⟪ pred_P ⟫ Subs a2 <: a3 at s' }} ->
      {{ ⟪ pred_P ⟫ Sub a1 <: a3 }}.
Proof.
  induction 1; intros ? ? Hsub; simpl in *.
  - dependent destruction Hsub.
    assert (st_subtyp s1 s3) by (transitivity s2; eauto).
    econstructor; mauto 2.
  - econstructor; mauto 2.
  - dependent destruction Hsub.
    handle_per_sort_elem_irrel.
    assert (per_sort_elem pred_P s elem_rel'0 d{{{ Π r a'0 ρ'0 B'0 }}} d{{{ Π r a'0 ρ'0 B'0 }}}).
    {
      invert_per_sort_elem H7.
      
      per_sort_elem_econstructor; mauto 2.
      - pose proof (ord_ru_pi_sub pred_P r sub1) as [ord_dom ord_im].
        destruct_conjs.
        destruct ord_dom; subst; mauto 2.
      - intros.
        destruct_rel_mod_eval.
        pose proof (ord_ru_pi_sub pred_P r sub1) as [ord_dom ord_im].
        destruct_conjs.
        econstructor; mauto 2.
        destruct ord_im; subst; mauto 2.
    }
    eapply per_subtyp_from_sorted with (s := s).
    econstructor; mauto 2.
    + transitivity a'; eauto.
    + intros.      
      invert_per_sort_elem H3.
      assert (per_sort_elem pred_P s1 in_rel a' a').
      {
        pose proof (ord_ru_pi_sub pred_P r sub) as [ord_dom ord_im].
        destruct_conjs.
        destruct ord_dom; subst; mauto 2.
      }
      handle_per_sort_elem_irrel.
      destruct_rel_mod_eval.
      assert (per_sort_elem pred_P s2 (out_rel c c' H11) a0 a'1).
      {
        pose proof (ord_ru_pi_sub pred_P r sub0) as [ord_dom ord_im].
        destruct_conjs.
        destruct ord_im; subst; mauto 2.
      }
      assert (per_subtyp_sorted pred_P s2 a'1 a0) by mauto 3.
      assert (per_subtyp_sorted pred_P s2 b a'1) by mauto 3.
      assert (per_subtyp_sorted pred_P s2 a0 b') by mauto 3.
      transitivity a'1; eauto.
      transitivity a0; eauto.
  - econstructor; mauto 3.
Qed.

Lemma per_subtyp_trans {P} {pred_P : PredicativeSig P} : forall a1 a2,
    {{ ⟪ pred_P ⟫ Sub a1 <: a2 }} ->
    forall a3,
      {{ ⟪ pred_P ⟫ Sub a2 <: a3 }} ->
      {{ ⟪ pred_P ⟫ Sub a1 <: a3 }}.
Proof.
  destruct 1; intros ? Hsub; simpl in *; mauto 2.
  - assert {{ ⟪ pred_P ⟫ Sub Sort@s1 <: Sort@s2 }} by mauto 2.
    dependent destruction Hsub.
    + econstructor; mauto 2.
      transitivity s2; eauto.
    + dependent destruction H0.
      econstructor; mauto 2.
      transitivity s2; eauto.
  - destruct Hsub.
    + dependent destruction H.
      econstructor.
      etransitivity; eauto.
    + eapply per_subtyp_trans_helper; mauto 2.
Qed.
  
#[export]
Hint Resolve per_subtyp_trans : mcpts.

#[export]
Instance per_subtyp_trans_ins {P} {pred_P : PredicativeSig P} : Transitive (per_subtyp pred_P).
Proof.
  eauto using per_subtyp_trans.
Qed.

Lemma per_subtyp_transp {P} {pred_P : PredicativeSig P} : forall a b a' b' R R',
    {{ ⟪ pred_P ⟫ Sub a <: b }} ->
    {{ DF a ≈ a' ∈ per_typ_elem pred_P ↘ R }} ->
    {{ DF b ≈ b' ∈ per_typ_elem pred_P ↘ R' }} ->
    {{ ⟪ pred_P ⟫ Sub a' <: b' }}.
Proof.
  mauto using per_subtyp_refl1, per_subtyp_refl2.
Qed.

Lemma per_ctx_env_subtyping {P : PtsSig} {pred_P : PredicativeSig P} : forall Γ Δ,
    {{ ⟪ pred_P ⟫ SubE Γ <: Δ }} ->
    forall R R' ρ ρ',
      {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ R }} ->
      {{ EF Δ ≈ Δ ∈ per_ctx_env pred_P ↘ R' }} ->
      R ρ ρ' ->
      R' ρ ρ'.
Proof.
  induction 1; intros;
    handle_per_ctx_env_irrel;
    invert_per_ctx_envs;
    apply_relation_equivalence;
    trivial.

  inversion H6.
  assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel0 }} by intuition.
  eexists; try eassumption.
   
  destruct_rel_typ.
  eapply per_elem_subtyping; try eassumption.
  - eauto using per_subtyp_sorted_cumu.
  - saturate_refl.
    mauto.
  - saturate_refl.
    mauto.
Qed.

Lemma per_ctx_subtyp_refl1 {P : PtsSig} {pred_P : PredicativeSig P} : forall Γ Δ R,
    {{ EF Γ ≈ Δ ∈ per_ctx_env pred_P ↘ R }} ->
    {{ ⟪ pred_P ⟫ SubE Γ <: Δ }}.
Proof.
  induction 1; mauto.

  assert (exists R, {{ EF Γ , A@s ≈ Γ' , A'@s ∈ per_ctx_env pred_P ↘ R }}) by
    (eexists; eapply per_ctx_env_cons'; eassumption).
  destruct_all.
  econstructor; try solve [saturate_refl; mauto 2].
  intros.
  destruct_rel_typ.
  simplify_evals.
  mauto.
Qed.

Lemma per_ctx_subtyp_refl2 {P : PtsSig} {pred_P : PredicativeSig P} : forall Γ Δ R,
    {{ EF Γ ≈ Δ ∈ per_ctx_env pred_P ↘ R }} ->
    {{ ⟪ pred_P ⟫ SubE Δ <: Γ }}.
Proof.
  intros. symmetry in H. eauto using per_ctx_subtyp_refl1.
Qed.

Lemma per_ctx_subtyp_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Γ1 Γ2,
    {{ ⟪ pred_P ⟫ SubE Γ1 <: Γ2 }} ->
    forall Γ3,
      {{ ⟪ pred_P ⟫ SubE Γ2 <: Γ3 }} ->
      {{ ⟪ pred_P ⟫ SubE Γ1 <: Γ3 }}.
Proof.
  induction 1; intros;
    dir_inversion_by_head (@per_ctx_subtyp P); subst;
    repeat invert_per_ctx_envs;
    mauto 1; clear_PER.

  handle_per_ctx_env_irrel.
  econstructor; try eassumption.
  - firstorder.
  - intros.
    assert {{ Dom ρ ≈ ρ' ∈ tail_rel0 }}
      by (apply_relation_equivalence; eapply per_ctx_env_subtyping; revgoals; eassumption).
    saturate_refl_for tail_rel.
    destruct_rel_typ.
    handle_per_sort_elem_irrel.
    etransitivity; intuition mauto using per_subtyp_sorted_cumu.
  - econstructor; intuition.
    + typeclasses eauto.
    + solve_refl.
  - econstructor; mauto 3.
    + typeclasses eauto.
    + solve_refl.
Qed.

#[export]
Hint Resolve per_ctx_subtyp_trans : mcpts.

#[export]
Instance per_ctx_subtyp_trans_ins {P : PtsSig} {pred_P : PredicativeSig P} : Transitive (@per_ctx_subtyp P pred_P).
Proof.
  eauto using per_ctx_subtyp_trans.
Qed.
