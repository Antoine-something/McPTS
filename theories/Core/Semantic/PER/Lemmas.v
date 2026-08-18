From Coq Require Import Equivalence Lia Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import System.
From McPTS.Core.Semantic Require Import PER.CoreTactics PER.Definitions.
Import Domain_Notations.

Add Parametric Morphism {P} R0 `(R0_morphism : Proper _ ((@relation_equivalence (domain P)) ==> (@relation_equivalence (domain P))) R0) Δ A ρ A' ρ' : (rel_mod_eval R0 Δ A ρ A' ρ')
    with signature (@relation_equivalence (domain P)) ==> iff as rel_mod_eval_morphism.
Proof.
  split; intros []; econstructor; try eassumption;
    [> eapply R0_morphism; [symmetry + idtac |]; eassumption ..].
Qed.

Add Parametric Morphism {P} Δ f a f' a' : (rel_mod_app Δ f a f' a')
    with signature (@relation_equivalence (domain P)) ==> iff as rel_mod_app_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    apply HRR'; eassumption.
Qed.

Lemma per_bot_sym {P} : forall (Δ : gctx P) m n,
    {{ Dom m ≈ n ∈ per_bot Δ }} ->
    {{ Dom n ≈ m ∈ per_bot Δ }}.
Proof with solve [eauto].
  intros * H i.
  pose proof H i.
  destruct_conjs...
Qed.

#[export]
Hint Resolve per_bot_sym : mcpts.

Lemma per_bot_trans {P} : forall (Δ : gctx P) m n l,
    {{ Dom m ≈ n ∈ per_bot Δ }} ->
    {{ Dom n ≈ l ∈ per_bot Δ }} ->
    {{ Dom m ≈ l ∈ per_bot Δ }}.
Proof with solve [eauto].
  intros * Hmn Hnl i.
  pose proof (Hmn i, Hnl i).
  destruct_conjs.
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_bot_trans : mcpts.

#[export]
Instance per_bot_PER {P} {Δ : gctx P} : PER (per_bot Δ).
Proof.
  split.
  - eauto using per_bot_sym.
  - eauto using per_bot_trans.
Qed.

Lemma var_per_bot {P} : forall {Δ : gctx P} {n},
    {{ Dom !n ≈ !n ∈ per_bot Δ }}.
Proof.
  intros ? ?. repeat econstructor.
Qed.

#[export]
Hint Resolve var_per_bot : mcpts.

Lemma gvar_per_bot {P} : forall {Δ : gctx P} {x},
    {{ Dom `!x ≈ `!x ∈ per_bot Δ }}.
Proof.
  intros ? ?. repeat econstructor.
Qed.

#[export]
Hint Resolve gvar_per_bot : mcpts.

Lemma per_top_sym {P} : forall {Δ : gctx P} m n,
    {{ Dom m ≈ n ∈ per_top Δ }} ->
    {{ Dom n ≈ m ∈ per_top Δ }}.
Proof with solve [eauto].
  intros * H i.
  pose proof H i.
  destruct_conjs...
Qed.

#[export]
Hint Resolve per_top_sym : mcpts.

Lemma per_top_trans {P} : forall {Δ : gctx P} m n l,
    {{ Dom m ≈ n ∈ per_top Δ }} ->
    {{ Dom n ≈ l ∈ per_top Δ }} ->
    {{ Dom m ≈ l ∈ per_top Δ }}.
Proof with solve [eauto].
  intros * Hmn Hnl i.
  pose proof (Hmn i, Hnl i).
  destruct_conjs.
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_top_trans : mcpts.

#[export]
Instance per_top_PER {P} {Δ : gctx P} : PER (per_top Δ).
Proof.
  split.
  - eauto using per_top_sym.
  - eauto using per_top_trans.
Qed.

Lemma per_bot_then_per_top {P} : forall {Δ : gctx P} m m' a a' b b' c c',
    {{ Dom m ≈ m' ∈ per_bot Δ }} ->
    {{ Dom ⇓ (⇑ a b) ⇑ c m ≈ ⇓ (⇑ a' b') ⇑ c' m' ∈ per_top Δ }}.
Proof.
  intros * H i.
  pose proof H i.
  destruct_conjs.
  eexists; split; constructor; eassumption.
Qed.

#[export]
Hint Resolve per_bot_then_per_top : mcpts.

Lemma per_top_typ_sym {P} : forall {Δ : gctx P} m n,
    {{ Dom m ≈ n ∈ per_top_typ Δ }} ->
    {{ Dom n ≈ m ∈ per_top_typ Δ }}.
Proof with solve [eauto].
  intros * H i.
  pose proof H i.
  destruct_conjs...
Qed.

#[export]
Hint Resolve per_top_typ_sym : mcpts.

Lemma per_top_typ_trans {P} : forall {Δ : gctx P} m n l,
    {{ Dom m ≈ n ∈ per_top_typ Δ }} ->
    {{ Dom n ≈ l ∈ per_top_typ Δ }} ->
    {{ Dom m ≈ l ∈ per_top_typ Δ }}.
Proof with solve [eauto].
  intros * Hmn Hnl i.
  pose proof (Hmn i, Hnl i).
  destruct_conjs.
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_top_typ_trans : mcpts.

#[export]
  Instance per_top_typ_PER {P} {Δ : gctx P} : PER (per_top_typ Δ).
Proof.
  split.
  - eauto using per_top_typ_sym.
  - eauto using per_top_typ_trans.
Qed.


Lemma per_nat_sym {P} : forall {Δ : gctx P} m n,
    {{ Dom m ≈ n ∈ per_nat Δ }} ->
    {{ Dom n ≈ m ∈ per_nat Δ }}.
Proof with mautosolve.
  induction 1; econstructor...
Qed.

#[export]
Hint Resolve per_nat_sym : mcpts.

Lemma per_nat_trans {P} : forall {Δ : gctx P} m n l,
    {{ Dom m ≈ n ∈ per_nat Δ }} ->
    {{ Dom n ≈ l ∈ per_nat Δ }} ->
    {{ Dom m ≈ l ∈ per_nat Δ }}.
Proof with mautosolve.
  intros * H. gen l.
  induction H; inversion_clear 1; econstructor...
Qed.

#[export]
Hint Resolve per_nat_trans : mcpts.

#[export]
Instance per_nat_PER {P} {Δ : gctx P} : PER (per_nat Δ).
Proof.
  split.
  - eauto using per_nat_sym.
  - eauto using per_nat_trans.
Qed.


Lemma per_ne_sym {P} : forall {Δ : gctx P} m n,
    {{ Dom m ≈ n ∈ per_ne Δ }} ->
    {{ Dom n ≈ m ∈ per_ne Δ }}.
Proof with mautosolve.
  intros * [].
  econstructor...
Qed.

#[export]
Hint Resolve per_ne_sym : mcpts.

Lemma per_ne_trans {P} : forall {Δ : gctx P} m n l,
    {{ Dom m ≈ n ∈ per_ne Δ }} ->
    {{ Dom n ≈ l ∈ per_ne Δ }} ->
    {{ Dom m ≈ l ∈ per_ne Δ }}.
Proof with mautosolve.
  intros * [].
  inversion_clear 1.
  econstructor...
Qed.

#[export]
Hint Resolve per_ne_trans : mcpts.

#[export]
Instance per_ne_PER {P} {Δ : gctx P} : PER (per_ne Δ).
Proof.
  split.
  - eauto using per_ne_sym.
  - eauto using per_ne_trans.
Qed.

Add Parametric Morphism {P} {pred_P : PredicativeSig P} Δ s (per_sort_elem_rec : forall s', pred_rel pred_P s' s -> relation (domain P) -> relation (domain P)) : (per_sort_elem_core pred_P Δ s per_sort_elem_rec)
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

Add Parametric Morphism {P} {pred_P : PredicativeSig P} Δ s : (per_sort_elem pred_P Δ s)
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

Add Parametric Morphism {P} {pred_P : PredicativeSig P} Δ s per_sort_rec : (per_sort_elem_core pred_P Δ s per_sort_rec)
    with signature (@relation_equivalence (domain P)) ==> (@relation_equivalence (domain P)) as per_sort_elem_core_morphism_relation_equivalence.
Proof with mautosolve.
  intros * H ? ?.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Add Parametric Morphism {P} {pred_P : PredicativeSig P} Δ s : (per_sort_elem pred_P Δ s)
    with signature (@relation_equivalence (domain P)) ==> (@relation_equivalence (domain P)) as per_sort_elem_morphism_relation_equivalence.
Proof with mautosolve.
  intros * H ? ?.
  simpl.
  rewrite H.
  reflexivity.
Qed.

(* Add Parametric Morphism {P} {pred_P : PredicativeSig P} s Δ A ρ A' ρ' : (rel_typ pred_P s Δ A ρ A' ρ') *)
(*     with signature (@relation_equivalence (domain P)) ==> iff as rel_typ_morphism. *)
(* Proof. *)
(*   intros * HRR'. *)
(*   split; intros []; econstructor; try eassumption; *)
(*     [setoid_rewrite <- HRR' | setoid_rewrite HRR']; eassumption. *)
(* Qed. *)


Add Parametric Morphism {P} {pred_P : PredicativeSig P} Δ : (per_typ_elem pred_P Δ)
    with signature (@relation_equivalence (domain P)) ==> eq ==> eq ==> iff as per_typ_elem_morphism_iff.
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
  1-2: rewrite <- HRR'...
  all: rewrite HRR'...
Qed.

Add Parametric Morphism {P} {pred_P : PredicativeSig P} Δ : (per_typ_elem pred_P Δ)
    with signature (@relation_equivalence (domain P)) ==> (@relation_equivalence (domain P)) as per_sort_typ_morphism_relation_equivalence.
Proof with mautosolve.
  intros * H ? ?.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Add Parametric Morphism {P} {pred_P : PredicativeSig P} Δ A ρ A' ρ' : (rel_typ_unsorted pred_P Δ A ρ A' ρ')
    with signature (@relation_equivalence (domain P)) ==> iff as rel_typ_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    [setoid_rewrite <- HRR' | setoid_rewrite HRR']; eassumption.
Qed.


Lemma domain_app_per {P} : forall {Δ : gctx P}f f' a a',
  {{ Dom f ≈ f' ∈ per_bot Δ }} ->
  {{ Dom a ≈ a' ∈ per_top Δ }} ->
  {{ Dom f a ≈ f' a' ∈ per_bot Δ }}.
Proof.
  intros. intros i.
  destruct (H i) as [? []].
  destruct (H0 i) as [? []].
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

Lemma per_sort_elem_pi_arg_helper {P} {pred_P : PredicativeSig P} : forall {Δ s_in s_out s_pi s_elem a a' in_rel},
    Ru_pi P s_in s_out s_pi ->
    st_subtyp s_pi s_elem ->
    (s_in = s_elem -> {{ DF a ≈ a' ∈ per_sort_elem pred_P Δ s_elem ↘ in_rel }}) /\ (pred_rel pred_P s_in s_elem -> {{ DF a ≈ a' ∈ per_sort_elem pred_P Δ s_in ↘ in_rel }}) <-> {{ DF a ≈ a' ∈ per_sort_elem pred_P Δ s_in ↘ in_rel }}.
Proof.
  intros * r sub.
  split; [intros [Heq Hlt] | split; intros; subst; eauto].
  destruct (ord_ru_pi_sub pred_P r sub) as [[|] _]; subst; eauto.
Qed.

Lemma per_sort_elem_pi_ret_helper {P} {pred_P : PredicativeSig P} : forall {Δ s_in s_out s_pi s_elem ρ B ρ' B' in_rel} (out_rel : forall {n n'}, {{ Dom n ≈ n' ∈ in_rel }} -> relation (domain P)),
    Ru_pi P s_in s_out s_pi ->
    st_subtyp s_pi s_elem ->
    (forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
        rel_mod_eval (fun R b b' => (s_out = s_elem -> {{ DF b ≈ b' ∈ per_sort_elem pred_P Δ s_elem ↘ R }}) /\ (pred_rel pred_P s_out s_elem -> {{ DF b ≈ b' ∈ per_sort_elem pred_P Δ s_out ↘ R }})) Δ B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) <->
      (forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
          rel_mod_eval (per_sort_elem pred_P Δ s_out) Δ B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')).
Proof.
  intros * r sub.
  split;
    [ intros Hbare *; specialize (Hbare n n' equiv_n_n') as [? ? ? ? [Heq Hlt]]
    | intros Helab *; specialize (Helab n n' equiv_n_n') as []]; econstructor; eauto.
  - destruct (ord_ru_pi_sub pred_P r sub) as [_ [|]]; subst; eauto.
  - split; intros; subst; eauto.
Qed.

Lemma per_sort_elem_pi_left_inversion {P} {pred_P : PredicativeSig P} : forall {Δ s_in s_out s s'} {r : Ru_pi P s_in s_out s} {a ρ B c' elem_rel},
    {{ DF Π r a ρ B ≈ c' ∈ per_sort_elem pred_P Δ s' ↘ elem_rel }} ->
    exists a' ρ' B' in_rel (out_rel : forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), relation (domain P)),
      st_subtyp s s' /\
      c' = d{{{ Π r a' ρ' B' }}} /\
        {{ DF a ≈ a' ∈ per_sort_elem pred_P Δ s_in ↘ in_rel }} /\
        (forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
            rel_mod_eval (per_sort_elem pred_P Δ s_out) Δ B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) /\
        (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app Δ f n f' n' (out_rel equiv_n_n')).
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

Lemma per_sort_elem_right_irrel {P} {pred_P : PredicativeSig P} : forall Δ s s' R a b R' b',
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ DF a ≈ b' ∈ per_sort_elem pred_P Δ s' ↘ R' }} ->
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

  assert (per_sort_elem pred_P Δ s_in in_rel0 a a'0).
  {
    destruct equiv_a_a' as [equiv_a_a'_eq equiv_a_a'_rel].
    pose proof ord_ru_pi_sub pred_P r sub0 as [].
    destruct H2; subst; mauto 3.
  }
  assert (in_rel <~> in_rel0) by mauto 3.
  split; intros.
  - rename equiv_n_n' into equiv0_n_n'.
    assert (in_rel n n') as equiv_n_n' by intuition.
    destruct_rel_mod_eval.
    simplify_evals.
    
    (* specialize (H4 n n' equiv0_n_n'). *)
    (* inversion_clear H4. *)
    assert (per_sort_elem pred_P Δ s_out (out_rel0 n n' equiv0_n_n') a0 a'1).
    {
      pose proof ord_ru_pi_sub pred_P r sub0 as [? []]; subst; mauto 3.
    }
    idtac...
    
  - assert (equiv0_n_n' : in_rel0 n n') by firstorder.
    destruct_rel_mod_eval.
    assert (per_sort_elem pred_P Δ s_out (out_rel0 n n' equiv0_n_n') a0 a'1).
    {
      pose proof ord_ru_pi_sub pred_P r sub0 as [? []]; subst; mauto 3.
    }
    idtac...
Qed.

#[local]
Ltac per_sort_elem_right_irrel_assert1 :=
  match goal with
  | H1 : {{ DF ^?a ≈ ^?b ∈ per_sort_elem ?pred_P ?Δ ?s ↘ ?R1 }},
      H2 : {{ DF ^?a ≈ ^?b' ∈ per_sort_elem ?pred_P ?Δ ?s ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_sort_elem_right_irrel; [apply H1 | apply H2])
      end
  end.
#[local]
Ltac per_sort_elem_right_irrel_assert := repeat per_sort_elem_right_irrel_assert1.

Lemma per_sort_elem_pi_econstructor {P} {pred_P : PredicativeSig P} : forall {Δ s_in s_out s_pi s a ρ B a' ρ' B'} (r : Ru_pi P s_in s_out s_pi) (sub : st_subtyp s_pi s) {in_rel} (out_rel : forall {n n'}, {{ Dom n ≈ n' ∈ in_rel }} -> relation (domain P)) {elem_rel} (equiv_a_a' : {{ DF a ≈ a' ∈ per_sort_elem pred_P Δ s_in ↘ in_rel }}),
    PER in_rel ->
    (forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
        rel_mod_eval (per_sort_elem pred_P Δ s_out) Δ B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) ->
    (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app Δ f n f' n' (out_rel equiv_n_n')) ->
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P Δ s ↘ elem_rel }}.
Proof.
  intros.
  rewrite <- (per_sort_elem_pi_arg_helper r sub) in equiv_a_a'.
  rewrite <- (per_sort_elem_pi_ret_helper _ r sub) in H0.
  basic_per_sort_elem_econstructor; eauto.
Qed.

#[local]
Ltac per_sort_elem_econstructor' :=
  (repeat intro; hnf; eapply per_sort_elem_pi_econstructor) + basic_per_sort_elem_econstructor.

Lemma per_sort_elem_sym {P} {pred_P : PredicativeSig P} : forall {Δ s R a b},
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ DF b ≈ a ∈ per_sort_elem pred_P Δ s ↘ R }} /\
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

Corollary per_sort_sym {P} {pred_P : PredicativeSig P} : forall Δ s R a b,
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ DF b ≈ a ∈ per_sort_elem pred_P Δ s ↘ R }}.
Proof.
  intros * ?%per_sort_elem_sym.
  firstorder.
Qed.

Corollary per_sort_sym' {P} {pred_P : PredicativeSig P} : forall Δ s a b,
    {{ Dom a ≈ b ∈ per_sort pred_P Δ s }} ->
    {{ Dom b ≈ a ∈ per_sort pred_P Δ s }}.
Proof.
  intros * [? ?%per_sort_elem_sym].
  firstorder.
Qed.

Corollary per_elem_sym {P} {pred_P : PredicativeSig P} : forall Δ s R a b m m',
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ Dom m ≈ m' ∈ R }} ->
    {{ Dom m' ≈ m ∈ R }}.
Proof.
  intros * ?%per_sort_elem_sym.
  firstorder.
Qed.

Corollary per_sort_elem_left_irrel {P} {pred_P : PredicativeSig P} : forall Δ s s' R a b R' a',
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ DF a' ≈ b ∈ per_sort_elem pred_P Δ s' ↘ R' }} ->
    (R <~> R').
Proof.
  intros * ?%per_sort_sym ?%per_sort_sym.
  eauto using per_sort_elem_right_irrel.
Qed.

Corollary per_sort_elem_cross_irrel {P} {pred_P : PredicativeSig P} : forall Δ s s' R a b R' b',
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ DF b' ≈ a ∈ per_sort_elem pred_P Δ s' ↘ R' }} ->
    (R <~> R').
Proof.
  intros * ? ?%per_sort_sym.
  eauto using per_sort_elem_right_irrel.
Qed.

Ltac do_per_sort_elem_irrel_assert1 :=
  let tactic_error o1 o2 := fail 2 "per_sort_elem_irrel biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ DF ^?a ≈ ^_ ∈ per_sort_elem ?pred_P ?Δ ?s ↘ ?R1 }},
      H2 : {{ DF ^?a ≈ ^_ ∈ per_sort_elem ?pred_P ?Δ ?s' ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_sort_elem_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ^_ ≈ ^?b ∈ per_sort_elem ?pred_P ?Δ ?s ↘ ?R1 }},
      H2 : {{ DF ^_ ≈ ^?b ∈ per_sort_elem ?pred_P ?Δ ?s' ↘ ?R2 }} |- _ =>
      assert_fails (unify R1 R2);
      match goal with
      | H : R1 <~> R2 |- _ => fail 1
      | H : R2 <~> R1 |- _ => fail 1
      | _ => assert (R1 <~> R2) by (eapply per_sort_elem_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
      end
  | H1 : {{ DF ^?a ≈ ^_ ∈ per_sort_elem ?pred_P ?Δ ?s ↘ ?R1 }},
      H2 : {{ DF ^_ ≈ ^?a ∈ per_sort_elem ?pred_P ?Δ ?s' ↘ ?R2 }} |- _ =>
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

Lemma per_sort_elem_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ s R a1 a2,
    {{ DF a1 ≈ a2 ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    (forall s' a3,
        {{ DF a2 ≈ a3 ∈ per_sort_elem pred_P Δ s' ↘ R }} ->
        {{ DF a1 ≈ a3 ∈ per_sort_elem pred_P Δ s ↘ R }}) /\
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
    assert (per_sort_elem pred_P Δ s_in in_rel0 a' a'0) by (destruct ord_dom; subst; mauto 2).
    per_sort_elem_econstructor'; eauto.
    + handle_per_sort_elem_irrel.
      intuition.
    + intros.
      pose proof (H4 n n' equiv_n_n').
      inversion_clear H11.
      destruct_conjs.
      assert (per_sort_elem pred_P Δ s_out (out_rel0 n n' equiv_n_n') a0 a'1) by (destruct ord_im; subst; mauto 2).
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

Corollary per_sort_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ s s' R a1 a2 a3,
    per_sort_elem pred_P Δ s R a1 a2 ->
    per_sort_elem pred_P Δ s' R a2 a3 ->
    per_sort_elem pred_P Δ s R a1 a3.
Proof.
  intros * ?%per_sort_elem_trans.
  firstorder.
Qed.

Corollary per_sort_trans' {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ s s' a1 a2 a3,
    {{ Dom a1 ≈ a2 ∈ per_sort pred_P Δ s }} ->
    {{ Dom a2 ≈ a3 ∈ per_sort pred_P Δ s' }} ->
    {{ Dom a1 ≈ a3 ∈ per_sort pred_P Δ s }}.
Proof.
  intros * [? ?] [? ?].
  handle_per_sort_elem_irrel.
  firstorder mauto using per_sort_trans.
Qed.

Corollary per_elem_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ s R a1 a2 m1 m2 m3,
    per_sort_elem pred_P Δ s R a1 a2 ->
    R m1 m2 ->
    R m2 m3 ->
    R m1 m3.
Proof.
  intros * ?% per_sort_elem_trans.
  firstorder.
Qed.

#[export]
Instance per_sort_PER {P : PtsSig} {pred_P : PredicativeSig P} {Δ s R} : PER (per_sort_elem pred_P Δ s R).
Proof.
  split.
  - auto using per_sort_sym.
  - eauto using per_sort_trans.
Qed.

#[export]
Instance per_sort_PER' {P : PtsSig} {pred_P : PredicativeSig P} {Δ s} : PER (per_sort pred_P Δ s).
Proof.
  split.
  - auto using per_sort_sym'.
  - eauto using per_sort_trans'.
Qed.

#[export]
Instance per_elem_PER {P : PtsSig} {pred_P : PredicativeSig P} {Δ s R a b} (H : per_sort_elem pred_P Δ s R a b) : PER R.
Proof.
  split.
  - pose proof (fun m m' => per_elem_sym _ _ _ _ _ m m' H); eauto.
  - pose proof (fun m0 m1 m2 => per_elem_trans _ _ _ _ _ m0 m1 m2 H); eauto.
Qed.



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


Lemma per_typ_elem_sym {P} {pred_P : PredicativeSig P} : forall {Δ R a b},
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
    eapply per_sort_sym'; mauto.
  - assert {{ DF b ≈ a ∈ per_sort_elem pred_P Δ s ↘ R }} by (eapply per_sort_sym; mauto).
    econstructor; mauto.
  - intros.
    eapply per_elem_sym; mauto.
Qed.

Corollary per_typ_elem_left_irrel {P} {pred_P : PredicativeSig P} : forall Δ R a b R' a',
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ DF a' ≈ b ∈ per_typ_elem pred_P Δ ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ?%per_typ_elem_sym ?%per_typ_elem_sym.
  destruct_conjs.
  eauto using per_typ_elem_right_irrel.
Qed.

Corollary per_typ_elem_cross_irrel {P} {pred_P : PredicativeSig P} : forall Δ R a b R' b',
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ DF b' ≈ a ∈ per_typ_elem pred_P Δ ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ? ?%per_typ_elem_sym.
  destruct_conjs.
  eauto using per_typ_elem_right_irrel.
Qed.

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

Lemma per_typ_elem_trans {P} {pred_P : PredicativeSig P} : forall Δ R a1 a2,
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
      eapply per_sort_trans'; mauto.
  - split.
    + intros.
      dependent destruction H0.
      * apply_relation_equivalence.
        econstructor; mauto.
      * assert {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }} by (eapply per_sort_trans; mauto).
        econstructor; mauto.
    + eapply per_sort_elem_trans; mauto.
Qed.

#[export]
Instance per_typ_elem_PER {P} {pred_P : PredicativeSig P} {Δ R} : PER (per_typ_elem pred_P Δ R).
Proof.
  split.
  - intros x y H.
    eapply (per_typ_elem_sym H).
  - intros x y **.
    eapply (per_typ_elem_trans Δ R x _ ltac:(eassumption)); eassumption.
Qed.


Corollary per_typ_sym {P} {pred_P : PredicativeSig P} : forall Δ a b,
    {{ Dom a ≈ b ∈ per_typ pred_P Δ }} ->
    {{ Dom b ≈ a ∈ per_typ pred_P Δ }}.
Proof.
  intros * [? ?%per_typ_elem_sym].
  firstorder.
Qed.

Corollary per_typ_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ a1 a2 a3,
    {{ Dom a1 ≈ a2 ∈ per_typ pred_P Δ }} ->
    {{ Dom a2 ≈ a3 ∈ per_typ pred_P Δ }} ->
    {{ Dom a1 ≈ a3 ∈ per_typ pred_P Δ }}.
Proof.
  intros * [? ?] [? ?].
  handle_per_typ_elem_irrel.
  assert (per_typ_elem pred_P Δ x0 a1 a3) by (eapply (proj1 (per_typ_elem_trans Δ x0 a1 a2 H) a3 H0); mauto).
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


Lemma per_typ_elem_and_per_sort_elem_implies_per_sort_elem {P} (pred_P : PredicativeSig P) : forall {Δ a b c R R' s},
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ DF a ≈ c ∈ per_sort_elem pred_P Δ s ↘ R' }} ->
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }}.
Proof.
  intros * Hab.
  inversion_clear Hab; intros.
  - basic_invert_per_sort_elem H0; mauto.
  - handle_per_sort_elem_irrel.
    assert (per_sort_elem pred_P Δ s R c a) by (eapply (per_sort_elem_sym H0); mauto).
    assert (per_sort_elem pred_P Δ s R c b) by (eapply (per_sort_elem_trans Δ s R c a H1); eassumption).
    eapply (per_sort_elem_trans Δ s R a c H0); eassumption.
Qed.

#[export]
Hint Resolve per_typ_elem_and_per_sort_elem_implies_per_sort_elem : mcpts.


(** These lemmas get rid of the unnecessary PER premises. *)
Lemma per_sort_elem_pi' {P : PtsSig} {pred_P : PredicativeSig P} :
  forall Δ s_in s_out s_pi s (r : Ru_pi P s_in s_out s_pi) (sub : st_subtyp s_pi s) a a' ρ B ρ' B'
    (in_rel : relation (domain P))
    (out_rel : forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), relation (domain P))
    elem_rel,
    {{ DF a ≈ a' ∈ per_sort_elem pred_P Δ s_in ↘ in_rel}} ->
    (forall {c c'} (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}),
        rel_mod_eval (per_sort_elem pred_P Δ s_out) Δ B d{{{ ρ ↦ c }}} B' d{{{ ρ' ↦ c' }}} (out_rel equiv_c_c')) ->
    (elem_rel <~> fun f f' => forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ in_rel }}), rel_mod_app Δ f c f' c' (out_rel equiv_c_c')) ->
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P Δ s ↘ elem_rel }}.
Proof.
  intros.
  per_sort_elem_econstructor'; eauto.
  typeclasses eauto.
Qed.

Ltac per_sort_elem_econstructor :=
  (repeat intro; hnf; (eapply per_sort_elem_pi')) + per_sort_elem_econstructor'.

#[export]
Hint Resolve per_sort_elem_pi' : mcpts.

Lemma per_sort_elem_pi_clean_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ s_in s_out s_pi s} {r : Ru_pi P s_in s_out s_pi} {sub : st_subtyp s_pi s} {a a' in_rel ρ ρ' B B' elem_rel},
    {{ DF a ≈ a' ∈ per_sort_elem pred_P Δ s_in ↘ in_rel }} ->
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P Δ s ↘ elem_rel }} ->
    exists (out_rel : forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), relation (domain P)),
      (forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
          rel_mod_eval (per_sort_elem pred_P Δ s_out) Δ B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) /\
        (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app Δ f n f' n' (out_rel equiv_n_n')).
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
                          rel_typ_unsorted pred_P Δ B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} R ->
                          R m m').
    intros.
    assert (in_rel0 n n') by intuition.
    (on_all_hyp: destruct_rel_by_assumption in_rel0).
    econstructor; eauto.
    apply -> per_sort_elem_morphism_iff; eauto.
    split.
    + intros.
      destruct_by_head (@rel_typ_unsorted).
      simplify_evals.
      assert (per_sort_elem pred_P Δ s_out R a0 a'0) by mauto 2.
      handle_per_sort_elem_irrel.
      intuition.
    + intuition.
      eapply H6.
      econstructor; mauto 3.
  - split; intros;
      [assert (in_rel0 n n') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel0)
      | assert (in_rel n n') by intuition; (on_all_hyp: destruct_rel_by_assumption in_rel)];
      econstructor; intuition.
    + destruct_by_head (@rel_typ_unsorted P).
      simplify_evals.
      assert (per_sort_elem pred_P Δ s_out R a0 a'0) by mauto 2.
      handle_per_sort_elem_irrel.
      intuition.
    + destruct_rel_mod_app.
      destruct_rel_mod_eval.
      simplify_evals.
      eapply H9.
      econstructor; mauto 3.
Qed.

Ltac invert_per_sort_elem H :=
  (unshelve eapply (per_sort_elem_pi_clean_inversion _) in H; shelve_unifiable; [eassumption |]; destruct H as [? []])
  + invert_per_sort_elem' H.

Ltac invert_per_sort_elems := match_by_head per_sort_elem ltac:(fun H => directed invert_per_sort_elem H).


Lemma per_sort_elem_pi_lowering {P} (pred_P : PredicativeSig P) : forall {Δ s1 s2 s3 s} {r : Ru_pi P s1 s2 s3} {elem_rel a ρ B a' ρ' B'},
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P Δ s ↘ elem_rel }} ->
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P Δ s3 ↘ elem_rel }}.
Proof.
  intros.
  invert_per_sort_elem H.
  per_sort_elem_econstructor; mauto 3.
  - destruct_conjs.
    pose proof ord_ru_pi_sub pred_P r sub as [[] ?]; subst; mauto 2.
  - intros.
    destruct_rel_mod_eval.
    econstructor; mauto 3.
    pose proof ord_ru_pi_sub pred_P r sub as [? []]; subst; mauto 2.
Qed.

Lemma per_typ_elem_pi_lowering {P} (pred_P : PredicativeSig P) : forall {Δ s1 s2 s3} {r : Ru_pi P s1 s2 s3} {elem_rel a ρ B a' ρ' B'},
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_typ_elem pred_P Δ ↘ elem_rel }} ->
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P Δ s3 ↘ elem_rel }}.
Proof.
  intros.
  inversion_clear H.
  eapply per_sort_elem_pi_lowering; mauto 2.
Qed.


Lemma per_sort_elem_cumu {P} {pred_P : PredicativeSig P} : forall Δ s1 s2 a b R,
    st_subtyp s1 s2 ->
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s1 ↘ R }} ->
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s2 ↘ R }}.
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




(** * Lemmas related to semantic subtyping *)
Lemma per_subtyp_sorted_to_sort_elem {P} {pred_P : PredicativeSig P} : forall Δ a b,
    (exists s : P, True) ->
    {{ SubT a <: b ∈ per_subtyp pred_P Δ }} ->
    (* {{ ⟪ pred_P ⟫ Subs a <: b at s }} -> *)
    exists R R',
      {{ DF a ≈ a ∈ per_typ_elem pred_P Δ ↘ R }} /\
        {{ DF b ≈ b ∈ per_typ_elem pred_P Δ ↘ R' }}.
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

Lemma per_elem_subtyping {P} {pred_P : PredicativeSig P} : forall Δ a b,
    {{ SubT a <: b ∈ per_subtyp pred_P Δ }} ->
    forall R R' m n,
      {{ DF a ≈ a ∈ per_typ_elem pred_P Δ ↘ R }} ->
      {{ DF b ≈ b ∈ per_typ_elem pred_P Δ ↘ R' }} ->
      R m n ->
      R' m n.
Proof.
  induction 1; intros * Ha Hb.
  - assert (per_typ_elem pred_P Δ (per_sort pred_P Δ s1) d{{{ Sort@s1 }}} d{{{ Sort@s1 }}}) by (econstructor; try reflexivity).
    assert (per_typ_elem pred_P Δ (per_sort pred_P Δ s2) d{{{ Sort@s2 }}} d{{{ Sort@s2 }}}) by (econstructor; try reflexivity).
    handle_per_typ_elem_irrel.
    unfold per_sort; intros [R].
    assert (per_sort_elem pred_P Δ s2 R m n) by mauto 2.
    mauto 2.

  - inversion_clear Ha; inversion_clear Hb.
    handle_per_sort_elem_irrel.
    mauto 2.
  - saturate_refl.
    assert (per_typ_elem pred_P Δ elem_rel d{{{ Π r a ρ B }}} d{{{ Π r a ρ B }}}) by mauto 2.
    assert (per_typ_elem pred_P Δ elem_rel' d{{{ Π r a' ρ' B' }}} d{{{ Π r a' ρ' B' }}}) by mauto 2.
    handle_per_typ_elem_irrel.    
    invert_per_sort_elems.
    destruct_conjs.
    assert (per_sort_elem pred_P Δ s1 in_rel0 a a) by (pose proof ord_ru_pi_sub pred_P r sub0 as [[] ?]; subst; mauto 2).
    assert (per_sort_elem pred_P Δ s1 in_rel1 a' a') by (pose proof ord_ru_pi_sub pred_P r sub0 as [[] ?]; subst; mauto 2).    
    handle_per_sort_elem_irrel.

    intros.
    rename equiv_n_n' into equiv0_n0_n'.
    assert (in_rel0 n0 n') as equiv_n0_n' by intuition.    
    destruct_rel_mod_eval.
    assert (per_sort_elem pred_P Δ s2 (out_rel0 n0 n' equiv0_n0_n') a0 a'0) by (pose proof ord_ru_pi_sub pred_P r sub1 as [? []]; subst; mauto 2).
    assert (per_sort_elem pred_P Δ s2 (out_rel n0 n' equiv_n0_n') a1 a'1) by (pose proof ord_ru_pi_sub pred_P r sub1 as [? []]; subst; mauto 2).
    saturate_refl_for (@per_sort_elem P).

    destruct_rel_mod_app.
    econstructor; mauto 2.
    eapply H1; mauto 2.
    
  - inversion_clear Ha; inversion_clear Hb.
    invert_per_sort_elems.
    apply_relation_equivalence.
    mauto 2.
Qed.


Lemma per_elem_subtyping_gen {P} {pred_P : PredicativeSig P} : forall Δ a b a' b' R R' m n,
    {{ SubT a <: b ∈ per_subtyp pred_P Δ }} ->
    {{ DF a ≈ a' ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ DF b ≈ b' ∈ per_typ_elem pred_P Δ ↘ R' }} ->
    R m n ->
    R' m n.
Proof.
  intros.
  eapply per_elem_subtyping; saturate_refl; try eassumption.
Qed.

Lemma per_subtyp_sorted_refl1 {P} {pred_P : PredicativeSig P} : forall Δ s a b R,
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ SubT a <: b ∈ per_subtyp pred_P Δ }}.
Proof.  
  simpl; induction 1 using per_sort_elem_ind;
    subst;
    mauto;
    destruct_all.
  - assert ({{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P Δ s_elem ↘ elem_rel }})
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

Lemma per_subtyp_sorted_refl2 {P} {pred_P : PredicativeSig P} : forall Δ s a b R,
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ SubT b <: a ∈ per_subtyp pred_P Δ }}.
Proof.
  intros.
  symmetry in H.
  eauto using per_subtyp_sorted_refl1.
Qed.

#[export]
Hint Resolve per_subtyp_sorted_refl2 : mcpts.

Lemma per_subtyp_refl1 {P} {pred_P : PredicativeSig P} : forall Δ a b R,
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ SubT a <: b ∈ per_subtyp pred_P Δ }}.
Proof.
  destruct 1.
  - econstructor; reflexivity.
  - eapply per_subtyp_sorted_refl1; mauto 2.
Qed.

#[export]
Hint Resolve per_subtyp_refl1 : mcpts.

Lemma per_subtyp_refl2 {P} {pred_P : PredicativeSig P} : forall Δ a b R,
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ SubT b <: a ∈ per_subtyp pred_P Δ }}.
Proof.
  intros.
  symmetry in H.
  eauto using per_subtyp_refl1.
Qed.

#[export]
Hint Resolve per_subtyp_refl2 : mcpts.

Lemma per_subtyp_trans {P} {pred_P : PredicativeSig P} : forall Δ a1 a2,
    {{ SubT a1 <: a2 ∈ per_subtyp pred_P Δ }} ->
    forall a3,
      {{ SubT a2 <: a3 ∈ per_subtyp pred_P Δ }} ->
      {{ SubT a1 <: a3 ∈ per_subtyp pred_P Δ }}.
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
      assert (per_sort_elem pred_P Δ s1 in_rel a a) by (pose proof ord_ru_pi_sub pred_P r sub as [[] ?]; subst; mauto 2).
      assert (per_sort_elem pred_P Δ s1 in_rel1 a' a') by (pose proof ord_ru_pi_sub pred_P r sub as [[] ?]; subst; mauto 2).
      assert (per_sort_elem pred_P Δ s1 in_rel2 a' a') by (pose proof ord_ru_pi_sub pred_P r sub2 as [[] ?]; subst; mauto 2).
      assert (per_sort_elem pred_P Δ s1 in_rel3 a'0 a'0) by (pose proof ord_ru_pi_sub pred_P r sub2 as [[] ?]; subst; mauto 2).
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

      assert (per_subtyp pred_P Δ b a3) by mauto 2.
      assert (per_subtyp pred_P Δ a3 b') by mauto 2.
      eapply (H1 c c' b a3); mauto 2.
    + pose proof (per_sort_elem_pi_lowering pred_P H2).
      mauto 2.
Qed.

#[export]
Hint Resolve per_subtyp_trans : mcpts.

#[export]
Instance per_subtyp_trans_ins {P} {pred_P : PredicativeSig P} {Δ} : Transitive (per_subtyp pred_P Δ).
Proof.
  eauto using per_subtyp_trans.
Qed.

Lemma per_subtyp_transp {P} {pred_P : PredicativeSig P} : forall Δ a b a' b' R R',
    {{ SubT a <: b ∈ per_subtyp pred_P Δ }} ->
    {{ DF a ≈ a' ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ DF b ≈ b' ∈ per_typ_elem pred_P Δ ↘ R' }} ->
    {{ SubT a' <: b' ∈ per_subtyp pred_P Δ }}.
Proof.
  mauto using per_subtyp_refl1, per_subtyp_refl2.
Qed.

#[export]
Hint Resolve per_subtyp_transp : mcpts.
 
(* Lemma per_subtyp_sorted_cumu {P} {pred_P : PredicativeSig P} : forall a1 a2 s, *)
(*     {{ ⟪ pred_P ⟫ Subs a1 <: a2 at s }} -> *)
(*     forall s', *)
(*       st_subtyp s s' -> *)
(*       {{ ⟪ pred_P ⟫ Subs a1 <: a2 at s' }}. *)
(* Proof. *)
(*   induction 1; intros; econstructor; mauto; *)
(*     match_by_head (@per_sort P) ltac:(fun H => destruct H); *)
(*     only 4: (etransitivity; eassumption); *)
(*     eexists; mauto 2. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve per_subtyp_sorted_cumu : mcpts. *)


      
(** Lemmas for per_gctx *)
Lemma per_gctx_preserves_fresh {P} {pred_P : PredicativeSig P} : forall Δ Δ' x,
    {{ GC Δ ≈ Δ' ∈ per_gctx pred_P }} ->
    {{ `#x ∉ Δ }} ->
    {{ `#x ∉ Δ' }}.
Proof.
  induction 1; mauto 2.
  inversion_clear 1.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve per_gctx_preserves_fresh : mcpts. 

Lemma per_gctx_sym {P} {pred_P : PredicativeSig P} : forall Δ Δ',
    {{ GC Δ ≈ Δ' ∈ per_gctx pred_P }} ->
    {{ GC Δ' ≈ Δ ∈ per_gctx pred_P }}.
Proof.
  induction 1; mauto 2.
  destruct_rel_typ_unsorted.
  symmetry in H3.
  symmetry in H6.
  econstructor; mauto 2;
    econstructor; mauto 2.
Qed.

  
(* Lemma per_gctx_trans {P} {pred_P : PredicativeSig P} : forall Δ Δ', *)
(*     {{ GC Δ ≈ Δ' ∈ per_gctx pred_P }} -> *)
(*     forall Δ'', *)
(*       {{ GC Δ' ≈ Δ'' ∈ per_gctx pred_P }} -> *)
(*       {{ GC Δ ≈ Δ'' ∈ per_gctx pred_P }}. *)
(* Proof. *)
(*   intros * HΔΔ'. *)
(*   induction HΔΔ'; intros * HΔ'Δ''; *)
(*     dependent destruction HΔ'Δ''; *)
(*     mauto 2. *)

(*   destruct_rel_typ_unsorted. *)
(*   simplify_evals. *)
(*   econstructor; mauto 3. *)
(*   - econstructor; mauto 3. *)
(*     etransitivity; mauto 2. *)
(*     admit. *)
(*   - transitivity a'; mauto 2. *)
(* Qed. *)

(* #[export] *)
(* Instance per_gctx_PER {P} {pred_P : PredicativeSig P} : PER (per_gctx pred_P).  *)
(* Proof. *)
(*   split. *)
(*   - mauto 3 using per_gctx_sym. *)
(*   - mauto 3 using per_gctx_trans. *)
(* Qed. *)


(** Lemmas for per_ctx_env and per_ctx *)
Add Parametric Morphism {P : PtsSig} {pred_P : PredicativeSig P} {Δ} : (per_ctx_env pred_P Δ)
    with signature (@relation_equivalence (env P)) ==> eq ==> eq ==> iff as per_ctx_env_morphism_iff.
Proof with mautosolve.
  intros R R' HRR'.
  split; intro Horig; [gen R' | gen R];
    induction Horig; econstructor;
    apply_relation_equivalence; try reflexivity...
Qed.

Add Parametric Morphism {P : PtsSig} {pred_P : PredicativeSig P} {Δ} : (per_ctx_env pred_P Δ)
    with signature (@relation_equivalence (env P)) ==> (@relation_equivalence (ctx P)) as per_ctx_env_morphism_relation_equivalence.
Proof.
  intros * HRR' Γ Γ'.
  simpl.
  rewrite HRR'.
  reflexivity.
Qed.

Lemma per_ctx_env_implies_per_gctx {P} {pred_P : PredicativeSig P} : forall Δ Γ Γ' R,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ GC Δ ≈ Δ ∈ per_gctx pred_P }}.
Proof.
  induction 1; mauto 2.
Qed.

#[export]
Hint Resolve per_ctx_env_implies_per_gctx : mcpts.
 
  
  
Lemma per_ctx_env_right_irrel {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' Γ'' R R',
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ EF Γ ≈ Γ'' ∈ per_ctx_env pred_P Δ ↘ R' }} ->
    R <~> R'.
Proof with (destruct_rel_typ_unsorted; handle_per_typ_elem_irrel; eexists; intuition).
  intros * Horig; gen Γ'' R'.  
  induction Horig; intros * Hright;
    dependent destruction Hright; subst;
    apply_relation_equivalence; 
   try reflexivity.
  specialize (IHHorig _ _ equiv_Γ_Γ'0).
  intros ρ ρ'.
    split; intros Hcons; dependent destruction Hcons;
    [ assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel0 }} by intuition
    | assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel }} by intuition ];
    assert (rel_typ_unsorted pred_P _ A _ A' _ (head_rel _ _ ltac:(eassumption))) by mauto 3;
    assert (rel_typ_unsorted pred_P _ A _ A'0 _ (head_rel0 _ _ ltac:(eassumption))) by mauto 3;
    inversion_clear_by_head (@rel_typ_unsorted P);
    simplify_evals;
    handle_per_typ_elem_irrel;
    econstructor; mauto 3;
    intuition.
Qed.

    

Lemma per_ctx_env_sym {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' R,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ EF Γ' ≈ Γ ∈ per_ctx_env pred_P Δ ↘ R }} /\
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
    assert (tail_rel d{{{ ρ' ↯ }}} d{{{ ρ ↯ }}}) as equiv_ρ'_drop_ρ_drop by eauto.
    assert (tail_rel d{{{ ρ ↯ }}} d{{{ ρ ↯ }}}) as equiv_ρ_drop_ρ_drop by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    handle_per_typ_elem_irrel.
    eexists; try eassumption.
    eapply H11. (* equivalence   head_rel (ρ' ↯) (ρ ↯) <~> head_rel (ρ ↯) (ρ' ↯) *)
    eapply (per_typ_elem_sym); mauto.
Qed.

Corollary per_ctx_sym {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' R,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ EF Γ' ≈ Γ ∈ per_ctx_env pred_P Δ ↘ R }}.
Proof.
  intros * ?%per_ctx_env_sym.
  firstorder.
Qed.

Corollary per_env_sym {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' R ρ ρ',
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ Dom ρ ≈ ρ' ∈ R }} ->
    {{ Dom ρ' ≈ ρ ∈ R }}.
Proof.
  intros * ?%per_ctx_env_sym.
  firstorder.
Qed.

Corollary per_ctx_env_left_irrel {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' Γ'' R R',
    {{ EF Γ ≈ Γ'' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ EF Γ' ≈ Γ'' ∈ per_ctx_env pred_P Δ ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ?%per_ctx_sym ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Corollary per_ctx_env_cross_irrel {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' Γ'' R R',
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ EF Γ'' ≈ Γ ∈ per_ctx_env pred_P Δ ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ? ?%per_ctx_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Ltac do_per_ctx_env_irrel_assert1 :=
  let tactic_error o1 o2 := fail 3 "per_ctx_env_irrel equality between" o1 "and" o2 "cannot be solved" in
  match goal with
    | H1 : {{ EF ^?Γ ≈ ^_ ∈ per_ctx_env ?pred_P ?Δ ↘ ?R1 }},
        H2 : {{ EF ^?Γ ≈ ^_ ∈ per_ctx_env ?pred_P ?Δ ↘ ?R2 }} |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : {{ EF ^_ ≈ ^?Δ ∈ per_ctx_env ?pred_P ?Δ ↘ ?R1 }},
        H2 : {{ EF ^_ ≈ ^?Δ ∈ per_ctx_env ?pred_P ?Δ ↘ ?R2 }} |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : {{ DF ^?Γ ≈ ^_ ∈ per_ctx_env ?pred_P ?Δ ↘ ?R1 }},
        H2 : {{ DF ^_ ≈ ^?Γ ∈ per_ctx_env ?pred_P ?Δ ↘ ?R2 }} |- _ =>
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

Lemma per_ctx_env_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ1 Γ2 R,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env pred_P Δ ↘ R }} ->
    (forall Γ3,
        {{ DF Γ2 ≈ Γ3 ∈ per_ctx_env pred_P Δ ↘ R }} ->
        {{ DF Γ1 ≈ Γ3 ∈ per_ctx_env pred_P Δ ↘ R }}) /\
      (forall ρ1 ρ2 ρ3,
          {{ Dom ρ1 ≈ ρ2 ∈ R }} ->
          {{ Dom ρ2 ≈ ρ3 ∈ R }} ->
          {{ Dom ρ1 ≈ ρ3 ∈ R }}).
Proof with solve [eauto using per_typ_trans].
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
      do 3 (etransitivity; mauto).
      symmetry; mauto.
  - destruct_by_head (@cons_per_ctx_env P).
    assert (tail_rel d{{{ ρ ↯ }}} d{{{ ρ' ↯ }}}) by eauto.
    destruct_rel_typ_unsorted.
    handle_per_typ_elem_irrel.
    eexists; [eassumption | eassumption |].
    apply_relation_equivalence.
    eapply per_typ_elem_trans; intuition.
Qed.

Corollary per_ctx_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ1 Γ2 Γ3 R,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ DF Γ2 ≈ Γ3 ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ DF Γ1 ≈ Γ3 ∈ per_ctx_env pred_P Δ ↘ R }}.
Proof.
  intros * ?% per_ctx_env_trans.
  firstorder.
Qed.

Corollary per_env_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ1 Γ2 R ρ1 ρ2 ρ3,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ Dom ρ1 ≈ ρ2 ∈ R }} ->
    {{ Dom ρ2 ≈ ρ3 ∈ R }} ->
    {{ Dom ρ1 ≈ ρ3 ∈ R }}.
Proof.
  intros * ?% per_ctx_env_trans.
  firstorder.
Qed.

#[export]
Instance per_ctx_PER {P : PtsSig} {pred_P : PredicativeSig P} {Δ R} : PER (per_ctx_env pred_P Δ R).
Proof.
  split.
  - auto using per_ctx_sym.
  - eauto using per_ctx_trans.
Qed.

#[export]
Instance per_env_PER {P : PtsSig} {pred_P : PredicativeSig P} {Δ R Γ Γ'} (H : per_ctx_env pred_P Δ R Γ Γ') : PER R.
Proof.
  split.
  - pose proof (fun ρ ρ' => per_env_sym _ _ _ _ ρ ρ' H); auto.
  - pose proof (fun ρ0 ρ1 ρ2 => per_env_trans _ _ _ _ ρ0 ρ1 ρ2 H); eauto.
Qed.

(** This lemma removes the PER argument *)
Lemma per_ctx_env_cons' {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ Γ' A A' tail_rel}
                             (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}), relation (domain P))
                             env_rel,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ tail_rel }} ->
    (forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}),
        rel_typ_unsorted pred_P Δ A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
    (env_rel <~> cons_per_ctx_env tail_rel (@head_rel)) ->
    {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env pred_P Δ ↘ env_rel }}.
Proof.
  intros.
  econstructor; eauto.
  typeclasses eauto.
Qed.

#[export]
Hint Resolve per_ctx_env_cons' : mcpts.

Ltac per_ctx_env_econstructor :=
  (repeat intro; hnf; eapply per_ctx_env_cons') + econstructor.

Lemma per_ctx_env_cons_clean_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ Γ' env_relΓ A A' env_relΓA},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ env_relΓ }} ->
    {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env pred_P Δ ↘ env_relΓA }} ->
    exists (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}), relation (domain P)),
      (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
          rel_typ_unsorted pred_P Δ A ρ A' ρ' (head_rel equiv_ρ_ρ')) /\
        (env_relΓA <~> cons_per_ctx_env env_relΓ (@head_rel)).
Proof with intuition.
  intros * HΓ HΓA.
  inversion HΓA; subst.
  handle_per_ctx_env_irrel.
  eexists.
  split; intros.
  - instantiate (1 := fun ρ ρ' (equiv_ρ_ρ' : env_relΓ ρ ρ') m m' =>
                        forall R,
                          rel_typ_unsorted pred_P Δ A ρ A' ρ' R ->
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

Lemma per_ctx_respects_length {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ Γ'},
    {{ GC Γ ≈ Γ' ∈ per_ctx pred_P Δ }} ->
    length Γ = length Γ'.
Proof.
  intros * [? H].
  induction H; simpl; congruence.
Qed.


Lemma per_ctx_subtyp_implies_per_gctx {P} {pred_P : PredicativeSig P} : forall Δ Γ Γ',
    {{ SubC Γ <: Γ' ∈ per_ctx_subtyp pred_P Δ }} ->
    {{ GC Δ ≈ Δ ∈ per_gctx pred_P }}.
Proof.
  induction 1; mauto 2.
Qed.

#[export]
Hint Resolve per_ctx_subtyp_implies_per_gctx : mcpts.

Lemma per_ctx_subtyp_to_env {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ',
    {{ SubC Γ <: Γ' ∈ per_ctx_subtyp pred_P Δ }} ->
    exists R R',
      {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P Δ ↘ R }} /\
        {{ EF Γ' ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R' }}.
Proof.
  intros * HΓΓ'.
  assert {{ GC Δ ≈ Δ ∈ per_gctx pred_P }} by mauto 2.
  destruct HΓΓ'; destruct_all.
  - repeat eexists; econstructor; try apply Equivalence_Reflexive; try eassumption.
  - eauto.
Qed.

Add Parametric Morphism {P} {pred_P : PredicativeSig P} Δ A ρ A' ρ' : (rel_typ_unsorted pred_P Δ A ρ A' ρ')
    with signature (@relation_equivalence (domain P)) ==> iff as rel_typ_unsorted_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    [setoid_rewrite <- HRR' | setoid_rewrite HRR']; eassumption.
Qed.

(* Lemma rel_typ_implies_rel_typ_unsorted {P} {pred_P : PredicativeSig P} : forall s A ρ A' ρ' R, *)
(*     rel_typ pred_P s A ρ A' ρ' R -> *)
(*     rel_typ_unsorted pred_P A ρ A' ρ' R. *)
(* Proof. *)
(*   intros * Hsorted. *)
(*   destruct Hsorted. *)
(*   econstructor; mauto. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve rel_typ_implies_rel_typ_unsorted : mcpts. *)


Lemma per_ctx_env_cons_clean_inversion_unsorted {P : PtsSig} (pred_P : PredicativeSig P) : forall {Δ Γ Γ' env_relΓ A A' env_relΓA},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ env_relΓ }} ->
    {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env pred_P Δ ↘ env_relΓA }} ->
    exists (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}), relation (domain P)),
      (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
          rel_typ_unsorted pred_P Δ A ρ A' ρ' (head_rel equiv_ρ_ρ')) /\
        (env_relΓA <~> cons_per_ctx_env env_relΓ (@head_rel)).
Proof with intuition.
  intros * HΓ HΓA.
  assert (exists (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}), relation (domain P)),
      (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
          rel_typ_unsorted pred_P Δ A ρ A' ρ' (head_rel equiv_ρ_ρ')) /\
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


Lemma per_ctx_env_subtyping {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ',
    {{ SubC Γ <: Γ' ∈ per_ctx_subtyp pred_P Δ }} ->
    forall R R' ρ ρ',
      {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P Δ ↘ R }} ->
      {{ EF Γ' ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R' }} ->
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
   
  destruct_rel_typ_unsorted.
  eapply per_elem_subtyping; try eassumption.
  - eauto.
  - saturate_refl.
    mauto.
  - saturate_refl.
    mauto.
Qed.

Lemma per_ctx_subtyp_refl1 {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' R,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ SubC Γ <: Γ' ∈ per_ctx_subtyp pred_P Δ }}.
Proof.
  induction 1; mauto.

  assert (exists R, {{ EF Γ , A ≈ Γ' , A' ∈ per_ctx_env pred_P Δ ↘ R }}) by
    (eexists; eapply per_ctx_env_cons'; eassumption).
  destruct_all.
  econstructor; try solve [saturate_refl; mauto 2].
  intros.
  destruct_rel_typ_unsorted.
  simplify_evals.
  mauto.
Qed.

Lemma per_ctx_subtyp_refl2 {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' R,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ SubC Γ' <: Γ ∈ per_ctx_subtyp pred_P Δ }}.
Proof.
  intros. symmetry in H. eauto using per_ctx_subtyp_refl1.
Qed.

Lemma per_ctx_subtyp_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ1 Γ2,
    {{ SubC Γ1 <: Γ2 ∈ per_ctx_subtyp pred_P Δ }} ->
    forall Γ3,
      {{ SubC Γ2 <: Γ3 ∈ per_ctx_subtyp pred_P Δ }} ->
      {{ SubC Γ1 <: Γ3 ∈ per_ctx_subtyp pred_P Δ }}.
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
    destruct_rel_typ_unsorted.
    handle_per_typ_elem_irrel.
    etransitivity; intuition mauto.
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
Instance per_ctx_subtyp_trans_ins {P : PtsSig} {pred_P : PredicativeSig P} {Δ} : Transitive (per_ctx_subtyp pred_P Δ).
Proof.
  eauto using per_ctx_subtyp_trans.
Qed.



(* Lemma per_subtyp_implies_per_subtyp_sorted {P} {pred_P : PredicativeSig P} : forall b b', *)
(*     {{ ⟪ pred_P ⟫ Sub b <: b' }} -> *)
(*     forall s s1 s2, *)
(*       {{ Dom b ≈ b ∈ per_sort pred_P s1 }} -> *)
(*       {{ Dom b' ≈ b' ∈ per_sort pred_P s2 }} -> *)
(*       st_subtyp s1 s -> *)
(*       st_subtyp s2 s -> *)
(*       {{ ⟪ pred_P ⟫ Subs b <: b' at s }}. *)
(* Proof. *)
(*   intros * H. *)
(*   destruct H. *)
(*   - intros. *)
(*     destruct_by_head @per_sort. *)
(*     econstructor; mauto. *)
(*   - induction H. *)
(*     + intros. *)
(*       destruct_by_head @per_sort. *)
(*       handle_per_sort_elem_irrel. *)
(*       econstructor; mauto. *)
(*     + mauto. *)
(*     + intros. *)
(*       destruct_by_head @per_sort. *)
(*       handle_per_sort_elem_irrel. *)
(*       assert (per_sort_elem pred_P s0 elem_rel d{{{ Π r a ρ B }}} d{{{ Π r a ρ B }}}) by mauto. *)
(*       invert_per_sort_elem H8. *)
(*       econstructor; mauto. *)
(*     + mauto. *)
(* Qed. *)

Lemma per_subtyp_sort_inv_left {P} (pred_P : PredicativeSig P) : forall {Δ s a},
    {{ SubT Sort@s <: a ∈ per_subtyp pred_P Δ }} ->
    exists s', a = d{{{ Sort@s' }}} /\ st_subtyp s s'.
Proof.
  simpl.
  intros.
  do 2 (dependent destruction H; mauto).
Qed.

Lemma per_subtyp_sort_inv_right {P} (pred_P : PredicativeSig P) : forall {Δ s a},
    {{ SubT a <: Sort@s ∈ per_subtyp pred_P Δ }} ->
    exists s', a = d{{{ Sort@s' }}} /\ st_subtyp s' s.
Proof.
  simpl.
  intros.
  do 2 (dependent destruction H; mauto).
Qed.

Lemma per_subtyp_nat_inv_left {P} (pred_P : PredicativeSig P) : forall {Δ a},
    {{ SubT ℕ <: a ∈ per_subtyp pred_P Δ }} ->
    (a = d{{{ ℕ }}}).
Proof.
  intros.
  inversion_clear H.
  reflexivity.
Qed.

Lemma per_subtyp_nat_inv_right {P} (pred_P : PredicativeSig P) : forall {Δ a},
    {{ SubT a <: ℕ ∈ per_subtyp pred_P Δ }} ->
    a = d{{{ ℕ }}}.
Proof.
  intros.
  inversion_clear H.
  reflexivity.
Qed.

Lemma per_subtyp_pi_inv_left {P} (pred_P : PredicativeSig P) : forall {Δ s1 s2 s3 c a ρ B} {r : Ru_pi P s1 s2 s3},
    {{ SubT Π r a ρ B <: c ∈ per_subtyp pred_P Δ }} ->
    exists a' ρ' B', c = d{{{ Π r a' ρ' B' }}}.
Proof.
  simpl.
  intros.
  do 2 (dependent destruction H; mauto).
Qed.

Lemma per_subtyp_pi_inv_right {P} (pred_P : PredicativeSig P) : forall {Δ s1 s2 s3 c a ρ B} {r : Ru_pi P s1 s2 s3},
    {{ SubT c <: Π r a ρ B ∈ per_subtyp pred_P Δ }} ->
    exists a' ρ' B', c = d{{{ Π r a' ρ' B' }}}.
Proof.
  simpl.
  intros.
  do 2 (dependent destruction H; mauto).
Qed.

Lemma per_bot_var_inv {P : PtsSig} : forall {Δ : gctx P} {n n'},
    per_bot Δ d{{{ !n }}} d{{{ !n' }}} ->
    n = n'.
Proof.
  intros.
  specialize (H (max n n' + 1)) as [L []].
  inversion H; subst.
  inversion H0; subst.
  lia.
Qed.

Lemma per_subtyp_var_inv_left {P} (pred_P : PredicativeSig P) : forall {Δ a x n l},
    n < l ->
    {{ SubT ⇑! x n <: a ∈ per_subtyp pred_P Δ}} ->
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

Lemma per_subtyp_var_inv_right {P} (pred_P : PredicativeSig P) : forall {Δ a x n l},
    n < l ->
    {{ SubT a <: ⇑! x n ∈ per_subtyp pred_P Δ }} ->
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


Lemma per_bot_gvar_inv {P : PtsSig} : forall {Δ : gctx P} {x x'},
    per_bot Δ d{{{ `!x }}} d{{{ `!x' }}} ->
    x = x'.
Proof.
  intros.
  specialize (H 0) as [L []].
  inversion H; subst.
  inversion H0; subst.
  reflexivity.
Qed.

Lemma per_subtyp_gvar_inv_left {P} (pred_P : PredicativeSig P) : forall {Δ x a b},
    {{ SubT ⇑`! a x <: b ∈ per_subtyp pred_P Δ }} ->
    exists a', b = d{{{ ⇑`! a' x }}}.
Proof.
  intros * H.
  inversion_clear H.
  specialize (H0 0) as [M []].
  inversion H; subst.
  inversion H0; subst.
  eexists; reflexivity.
Qed.

Lemma per_subtyp_gvar_inv_right {P} (pred_P : PredicativeSig P) : forall {Δ x a b},
    {{ SubT b <: ⇑`! a x ∈ per_subtyp pred_P Δ }} ->
    exists a', b = d{{{ ⇑`! a' x }}}.
Proof.
  intros * H.
  inversion_clear H.
  specialize (H0 0) as [M []].
  inversion H0; subst.
  inversion H; subst.
  eexists; reflexivity.
Qed.
