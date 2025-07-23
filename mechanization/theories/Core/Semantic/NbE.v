From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export System.
From McPTS.Core.Semantic Require Export Domain Evaluation Readback.
Import Domain_Notations.

Generalizable All Variables.

Inductive initial_env {P : PtsSig} : ctx P -> env P -> Prop :=
| initial_env_nil : initial_env nil empty_env
| initial_env_cons :
  `( initial_env Γ ρ ->
     {{ ⟦ A ⟧ ρ ↘ a }} ->
     initial_env ({{{ Γ, A::Sort@s }}}) d{{{ ρ ↦ ⇑! a (length Γ) }}}).

#[export]
Hint Constructors initial_env : mcpts.

Lemma functional_initial_env {P : PtsSig} : forall (Γ : ctx P) ρ,
    initial_env Γ ρ ->
    forall ρ',
      initial_env Γ ρ' ->
      ρ = ρ'.
Proof.
  induction 1; intros ? Hother; inversion_clear Hother; eauto.
  erewrite IHinitial_env in *; try eassumption;
    functional_eval_rewrite_clear;
    eauto.
Qed.

#[export]
Hint Resolve functional_initial_env : mcpts.

(** In the following spec, we do not care (for now)
    whether [a] is the evaluation result of A or not.
    If we want to specify that as well, we need a generalized
    version of [drop_env] that can drop [x] elements. *)
Lemma initial_env_spec {P : PtsSig} : forall x (Γ : ctx P) ρ A s,
    initial_env Γ ρ ->
    {{ #x : A :: Sort@s ∈ Γ }} ->
    exists m a, {{ ρ[x] ↘ m }} /\ m = d{{{ ⇑! a (length Γ - x - 1) }}}.
Proof.
  induction x; intros * Hinit Hlookup;
    dependent destruction Hlookup; dependent destruction Hinit; simpl; mauto 3.
  eexists; eexists; repeat f_equal; split.
Admitted.

#[export]
Hint Resolve initial_env_spec : mcpts.

Ltac functional_initial_env_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_initial_env equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : initial_env ?G ?ρ, H2 : initial_env ?G ?ρ' |- _ =>
      clean replace ρ' with ρ by first [solve [mauto 2] | tactic_error ρ' ρ]; clear H2
  end.
Ltac functional_initial_env_rewrite_clear := repeat functional_initial_env_rewrite_clear1.

Inductive nbe {P : PtsSig} : ctx P -> exp P -> typ P -> nf P -> Prop :=
| nbe_run :
  `( initial_env Γ ρ ->
     {{ ⟦ A ⟧ ρ ↘ a }} ->
     {{ ⟦ M ⟧ ρ ↘ m }} ->
     {{ Rnf ⇓ a m in (length Γ) ↘ w }} ->
     nbe Γ M A w ).

#[export]
Hint Constructors nbe : mcpts.

Lemma functional_nbe {P : PtsSig} : forall (Γ : ctx P) M A w w',
    nbe Γ M A w ->
    nbe Γ M A w' ->
    w = w'.
Proof.
  intros.
  inversion_clear H; inversion_clear H0;
    functional_initial_env_rewrite_clear;
  functional_eval_rewrite_clear;
  functional_read_rewrite_clear;
  reflexivity.
Qed.

#[export]
Hint Resolve functional_nbe : mcpts.

Inductive nbe_ty {P : PtsSig} : ctx P -> typ P -> nf P -> Prop :=
| nbe_ty_run :
  `( initial_env Γ ρ ->
     {{ ⟦ M ⟧ ρ ↘ m }} ->
     {{ Rtyp m in (length Γ) ↘ W }} ->
     nbe_ty Γ M W ).

#[export]
Hint Constructors nbe_ty : mcpts.

Lemma functional_nbe_ty {P : PtsSig} : forall (Γ : ctx P) M w w',
    nbe_ty Γ M w ->
    nbe_ty Γ M w' ->
    w = w'.
Proof.
  intros.
  inversion_clear H; inversion_clear H0;
    functional_initial_env_rewrite_clear;
  functional_eval_rewrite_clear;
  functional_read_rewrite_clear;
  reflexivity.
Qed.

Lemma nbe_type_to_nbe_ty {P : PtsSig} : forall (Γ : ctx P) M s w,
    nbe Γ M {{{ Sort@s }}} w ->
    nbe_ty Γ M w.
Proof.
  intros. progressive_inversion.
  mauto.
Qed.

#[export]
Hint Resolve functional_nbe_ty nbe_type_to_nbe_ty : mcpts.

Ltac functional_nbe_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_nbe equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : nbe ?G ?M ?A ?W, H2 : nbe ?G ?M ?A ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]; clear H2
  | H1 : nbe ?G ?A {{{ Sort@?s }}} ?W, H2 : nbe ?G ?A {{{ Sort@?s }}} ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]
  | H1 : nbe_ty ?G ?M ?W, H2 : nbe_ty ?G ?M ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]; clear H2
  end.
Ltac functional_nbe_rewrite_clear := repeat functional_nbe_rewrite_clear1.
