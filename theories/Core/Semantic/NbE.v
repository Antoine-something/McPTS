From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export System.
From McPTS.Core.Semantic Require Export Domain Evaluation Readback.
Import Domain_Notations.

Generalizable All Variables.

Inductive initial_env {P : PtsSig} : gctx P -> ctx P -> env P -> Prop :=
| initial_env_nil :
  `( initial_env Δ nil empty_env )
| initial_env_cons :
  `( initial_env Δ Γ ρ ->
     {{ Δ ▶ ⟦ A ⟧ ρ ↘ a }} ->
     initial_env Δ ({{{ Γ, A }}}) d{{{ ρ ↦ ⇑! a (length Γ) }}}).

#[export]
Hint Constructors initial_env : mcpts.

Lemma functional_initial_env {P : PtsSig} : forall (Δ : gctx P) Γ ρ,
    initial_env Δ Γ ρ ->
    forall ρ',
      initial_env Δ Γ ρ' ->
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
Lemma initial_env_spec {P : PtsSig} : forall x (Δ : gctx P) Γ ρ A,
    initial_env Δ Γ ρ ->
    {{ #x : A ∈ Γ }} ->
    exists m a, {{ #| ρ[x] |↘ m }} /\ m = d{{{ ⇑! a (length Γ - x - 1) }}}.
Proof.
  induction x; intros * Hinit Hlookup;
    dependent destruction Hlookup; dependent destruction Hinit; simpl; mauto.
  - eexists; eexists; repeat f_equal; split; mauto.
    assert (length Γ0 - 0 = length Γ0) by lia.
    rewrite -> H0.
    econstructor; mauto.
  - assert (exists m a, {{ #| ρ0[x] |↘ m}} /\ (m = d{{{ ⇑! a (length Γ0 - x - 1) }}})) by mauto.
    destruct_conjs.
    subst.
    assert (length Γ0 - x - 1 = length Γ0 - (S x)) by lia.
    rewrite -> H0.
    rewrite -> H0 in H2.
    eexists; eexists; repeat f_equal; split; mauto.
Qed.

#[export]
Hint Resolve initial_env_spec : mcpts.

Lemma initial_env_spec_subst {P} : forall x (Δ : gctx P) Γ ρ A,
    initial_env Δ Γ ρ ->
    {{ #x : A ∈ Γ }} ->
    exists a, {{ #| ρ[x] |↘ ⇑! a (length Γ - x - 1) }}.
Proof.
  intros.
  eapply initial_env_spec in H0; eauto.
  destruct_conjs.
  subst.  
  eexists; mauto 2.
Qed.

#[export]
Hint Resolve initial_env_spec_subst : mcpts.

Ltac functional_initial_env_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_initial_env equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : initial_env ?Δ ?Γ ?ρ, H2 : initial_env ?Δ ?Γ ?ρ' |- _ =>
      clean replace ρ' with ρ by first [solve [mauto 2] | tactic_error ρ' ρ]; clear H2
  end.
Ltac functional_initial_env_rewrite_clear := repeat functional_initial_env_rewrite_clear1.

Inductive nbe {P : PtsSig} : gctx P -> ctx P -> exp P -> typ P -> nf P -> Prop :=
| nbe_run :
  `( initial_env Δ Γ ρ ->
     {{ Δ ▶ ⟦ A ⟧ ρ ↘ a }} ->
     {{ Δ ▶ ⟦ M ⟧ ρ ↘ m }} ->
     {{ Δ ▶ Rnf ⇓ a m in (length Γ) ↘ W }} ->
     nbe Δ Γ M A W ).

#[export]
Hint Constructors nbe : mcpts.

Lemma functional_nbe {P : PtsSig} : forall (Δ : gctx P) Γ M A W W',
    nbe Δ Γ M A W ->
    nbe Δ Γ M A W' ->
    W = W'.
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

Inductive nbe_ty {P : PtsSig} : gctx P -> ctx P -> typ P -> nf P -> Prop :=
| nbe_ty_run :
  `( initial_env Δ Γ ρ ->
     {{ Δ ▶ ⟦ M ⟧ ρ ↘ m }} ->
     {{ Δ ▶ Rtyp m in (length Γ) ↘ W }} ->
     nbe_ty Δ Γ M W ).

#[export]
Hint Constructors nbe_ty : mcpts.

Lemma functional_nbe_ty {P : PtsSig} : forall (Δ : gctx P) Γ M W W',
    nbe_ty Δ Γ M W ->
    nbe_ty Δ Γ M W' ->
    W = W'.
Proof.
  intros.
  inversion_clear H; inversion_clear H0;
    functional_initial_env_rewrite_clear;
  functional_eval_rewrite_clear;
  functional_read_rewrite_clear;
  reflexivity.
Qed.

#[export]
Hint Resolve functional_nbe_ty : mcpts.
  
Lemma nbe_type_to_nbe_ty {P : PtsSig} : forall (Δ : gctx P) Γ M s W,
    nbe Δ Γ M {{{ Sort@s }}} W ->
    nbe_ty Δ Γ M W.
Proof.
  intros. progressive_inversion.
  mauto.
Qed.

#[export]
Hint Resolve nbe_type_to_nbe_ty : mcpts.

Lemma function_nbe_nbe_ty {P : PtsSig} : forall (Δ : gctx P) Γ A s W W',
    nbe Δ Γ A {{{ Sort@s }}} W ->
    nbe_ty Δ Γ A W' ->
    W = W'.
Proof.
  intros * ?%nbe_type_to_nbe_ty ?.
  mauto 2.
Qed.

Ltac functional_nbe_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_nbe equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : nbe ?Δ ?Γ ?M ?A ?W, H2 : nbe ?Δ ?Γ ?M ?A ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]; clear H2
  | H1 : nbe ?Δ ?Γ ?A {{{ Sort@?s }}} ?W, H2 : nbe ?Δ ?Γ ?A {{{ Sort@?s }}} ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]; clear H2
  | H1 : nbe_ty ?Δ ?Γ ?M ?W, H2 : nbe_ty ?Δ ?Γ ?M ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]; clear H2
  | H1 : nbe ?Δ ?Γ ?A {{{ Sort@?s }}} ?W, H2 : nbe_ty ?Δ ?Γ ?A ?W' |- _ =>
      clean replace W' with W by first [solve [mauto 2] | tactic_error W' W]
  end.
Ltac functional_nbe_rewrite_clear := repeat functional_nbe_rewrite_clear1.
