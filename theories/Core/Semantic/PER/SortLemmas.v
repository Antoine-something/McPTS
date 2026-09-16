From Coq Require Import Equivalence Lia Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import System.
From McPTS.Core.Semantic Require Import PER.Definitions PER.CoreTactics PER.CoreLemmas.
Import Domain_Notations.

(** ** Properties/tools related to 'per_sort_elem' and 'per_sort' *)
(* The main results are the following:
   1. Functionality: The relations produced are unique up to relational equivalence
   2. 'per_sort[_elem]' really is a PER
   3. Inversion principles
   4. Optimized constructors
   These are entangled and must be proved together
 *)

(** Provides rewrite rules to go between to pred_rel/equal formulation of per_pi and the more direct formulation *)
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


(** Basic inversion principle for per_pi *)
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

(** Main functionality result *)
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

  clear_pi_sort_eq_and_pred_rel.
  assert (in_rel <~> in_rel0) by mauto 3.
  split; intros.
  - rename equiv_n_n' into equiv0_n_n'.
    assert (in_rel n n') as equiv_n_n' by intuition.
    destruct_rel_mod_eval.
    simplify_evals.
    clear_pi_sort_eq_and_pred_rel.
    idtac...
    
  - assert (equiv0_n_n' : in_rel0 n n') by firstorder.
    destruct_rel_mod_eval.
    clear_pi_sort_eq_and_pred_rel.
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

(** Symmetry for per_sort_elem and per_sort *)
Lemma per_sort_elem_sym_main {P} {pred_P : PredicativeSig P} : forall {Δ s R a b},
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

Corollary per_sort_elem_sym {P} {pred_P : PredicativeSig P} : forall Δ s R a b,
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ DF b ≈ a ∈ per_sort_elem pred_P Δ s ↘ R }}.
Proof.
  intros * ?%per_sort_elem_sym_main.
  firstorder.
Qed.

Corollary per_sort_sym {P} {pred_P : PredicativeSig P} : forall Δ s a b,
    {{ Dom a ≈ b ∈ per_sort pred_P Δ s }} ->
    {{ Dom b ≈ a ∈ per_sort pred_P Δ s }}.
Proof.
  intros * [? ?%per_sort_elem_sym].
  firstorder.
Qed.

Corollary per_sort_elem_output_sym {P} {pred_P : PredicativeSig P} : forall Δ s R a b m m',
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ Dom m ≈ m' ∈ R }} ->
    {{ Dom m' ≈ m ∈ R }}.
Proof.
  intros * ?%per_sort_elem_sym_main.
  firstorder.
Qed.

(** More forms of functionality *)
Corollary per_sort_elem_left_irrel {P} {pred_P : PredicativeSig P} : forall Δ s s' R a b R' a',
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ DF a' ≈ b ∈ per_sort_elem pred_P Δ s' ↘ R' }} ->
    (R <~> R').
Proof.
  intros * ?%per_sort_elem_sym ?%per_sort_elem_sym.
  eauto using per_sort_elem_right_irrel.
Qed.

Corollary per_sort_elem_cross_irrel {P} {pred_P : PredicativeSig P} : forall Δ s s' R a b R' b',
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ DF b' ≈ a ∈ per_sort_elem pred_P Δ s' ↘ R' }} ->
    (R <~> R').
Proof.
  intros * ? ?%per_sort_elem_sym.
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


(** Tansitivity for per_sort_elem and per_sort *)
Lemma per_sort_elem_trans_main {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ s R a1 a2,
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
    clear_pi_sort_eq_and_pred_rel.
    per_sort_elem_econstructor'; eauto.
    + handle_per_sort_elem_irrel.
      intuition.
    + intros.
      destruct_rel_mod_eval.
      clear_pi_sort_eq_and_pred_rel.
      handle_per_sort_elem_irrel.
      (* Some of this should not be necessary: handling irrelevance should remove one of the two relations *)
      assert (in_rel n n') by firstorder.
      assert (in_rel n n) by intuition.
      assert (in_rel0 n n') by intuition.      
      destruct_rel_mod_eval.
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

Corollary per_sort_elem_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ s s' R a1 a2 a3,
    per_sort_elem pred_P Δ s R a1 a2 ->
    per_sort_elem pred_P Δ s' R a2 a3 ->
    per_sort_elem pred_P Δ s R a1 a3.
Proof.
  intros * ?%per_sort_elem_trans_main.
  firstorder.
Qed.

Corollary per_sort_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ s s' a1 a2 a3,
    {{ Dom a1 ≈ a2 ∈ per_sort pred_P Δ s }} ->
    {{ Dom a2 ≈ a3 ∈ per_sort pred_P Δ s' }} ->
    {{ Dom a1 ≈ a3 ∈ per_sort pred_P Δ s }}.
Proof.
  intros * [? ?] [? ?].
  handle_per_sort_elem_irrel.
  firstorder mauto using per_sort_elem_trans.
Qed.

Corollary per_sort_elem_output_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ s R a1 a2 m1 m2 m3,
    per_sort_elem pred_P Δ s R a1 a2 ->
    R m1 m2 ->
    R m2 m3 ->
    R m1 m3.
Proof.
  intros * ?% per_sort_elem_trans_main.
  firstorder.
Qed.

(** PER instances for per_sort_elem *)
#[export]
Instance per_sort_elem_PER {P : PtsSig} {pred_P : PredicativeSig P} {Δ s R} : PER (per_sort_elem pred_P Δ s R).
Proof.
  split.
  - auto using per_sort_elem_sym.
  - eauto using per_sort_elem_trans.
Qed.

#[export]
Instance per_sort_PER {P : PtsSig} {pred_P : PredicativeSig P} {Δ s} : PER (per_sort pred_P Δ s).
Proof.
  split.
  - auto using per_sort_sym.
  - eauto using per_sort_trans.
Qed.

#[export]
Instance per_sort_elem_output_PER {P : PtsSig} {pred_P : PredicativeSig P} {Δ s R a b} (H : per_sort_elem pred_P Δ s R a b) : PER R.
Proof.
  split.
  - pose proof (fun m m' => per_sort_elem_output_sym _ _ _ _ _ m m' H); eauto.
  - pose proof (fun m0 m1 m2 => per_sort_elem_output_trans _ _ _ _ _ m0 m1 m2 H); eauto.
Qed.


(** This lemma gets rid of the unnecessary PER premises, providing and optimized consructor *)
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


(** ** Lowering principles *)
(** Any relation in per_typ can be lowered to per_sort if one of the element is related in per_sort *)
Lemma per_typ_elem_and_per_sort_elem_lowering {P} (pred_P : PredicativeSig P) : forall {Δ a b c R R' s},
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ DF a ≈ c ∈ per_sort_elem pred_P Δ s ↘ R' }} ->
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }}.
Proof.
  intros * Hab.
  inversion_clear Hab; intros.
  - basic_invert_per_sort_elem H0; mauto.
  - handle_per_sort_elem_irrel.
    assert (per_sort_elem pred_P Δ s R c a) by (eapply (per_sort_elem_sym_main H0); mauto).
    assert (per_sort_elem pred_P Δ s R c b) by (eapply (per_sort_elem_trans_main Δ s R c a H1); eassumption).
    eapply (per_sort_elem_trans_main Δ s R a c H0); eassumption.
Qed.

#[export]
Hint Resolve per_typ_elem_and_per_sort_elem_lowering : mcpts.

(** Any related function space is related in the output sort of its formation rule *)
Lemma per_sort_elem_pi_lowering {P} (pred_P : PredicativeSig P) : forall {Δ s1 s2 s3 s} {r : Ru_pi P s1 s2 s3} {elem_rel a ρ B a' ρ' B'},
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P Δ s ↘ elem_rel }} ->
    {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P Δ s3 ↘ elem_rel }}.
Proof.
  intros.
  basic_invert_per_sort_elem H.
  per_sort_elem_econstructor; mauto 3.
  - clear_pi_sort_eq_and_pred_rel.
    mauto 2.
  - intros.
    destruct_rel_mod_eval.
    clear_pi_sort_eq_and_pred_rel.
    econstructor; mauto 3.    
Qed.


(** Inversion principle for pi case *)
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


(** Cumulativity of per_sort_elem *)
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

Corollary per_sort_cumu {P} {pred_P : PredicativeSig P} : forall Δ s1 s2 a b,
    st_subtyp s1 s2 ->
    {{ Dom a ≈ b ∈ per_sort pred_P Δ s1 }} ->
    {{ Dom a ≈ b ∈ per_sort pred_P Δ s2 }}.
Proof.
  intros * ? [].
  eexists; mauto 2.
Qed.

#[export]
Hint Resolve per_sort_cumu : mcpts.
