From Coq Require Import Lia PeanoNat Relations Logic.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic.Evaluation Require Import Definitions.
Import Domain_Notations.

Section functional_eval.
  Lemma env_lookup_functional {P : PtsSig} : forall (ρ : env P) x m1,
      {{ #| ρ[x] |↘ m1 }} ->
      forall m2,
        {{ #| ρ[x] |↘ m2 }} ->
        m1 = m2.
  Proof with ((on_all_hyp: fun H => erewrite H in *; eauto); solve [eauto]) using.
    intros * H1.
    dependent induction H1;
      intros * H2; inversion H2; mauto 2.
  Qed.

  Lemma functional_eval {P : PtsSig} :
    (forall (M : exp P) ρ m1,
        {{ ⟦ M ⟧ ρ ↘ m1 }} ->
        forall m2,
          {{ ⟦ M ⟧ ρ ↘ m2 }} ->
          m1 = m2) /\
      (forall (m : domain P) n e1,
          {{ $| m & n |↘ e1 }} ->
          forall e2,
            {{ $| m & n |↘ e2 }} ->
            e1 = e2) /\
      (forall (A : exp P) MZ MS m ρ e1,
          {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e1 }} ->
          forall e2,
            {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e2 }} ->
            e1 = e2) /\
      (forall (σ : sub P) ρ ρσ1,
          {{ ⟦ σ ⟧s ρ ↘ ρσ1 }} ->
          forall ρσ2,
            {{ ⟦ σ ⟧s ρ ↘ ρσ2 }} ->
            ρσ1 = ρσ2).
  Proof with ((on_all_hyp: fun H => erewrite H in *; eauto); solve [eauto]) using.
    apply eval_mut_ind; intros.

    1,5-9,10,13-19: progressive_inversion; do 2 f_equal; try reflexivity...

    - progressive_inversion.
      eapply env_lookup_functional; mauto 2.

    (** 'progressive_inversion' does not work well with functions because of the rule annotations
        use 'progressive_invert' on the relevant assumption instead *)
    - progressive_invert H0.
      assert (a = a0) by mauto.
      congruence.

    - progressive_invert H.
      reflexivity.
    - progressive_invert H0.
      mauto.
    - progressive_invert H0.
      rewrite <- (H _ H0).
      mauto.
  Qed.

  Corollary functional_eval_exp {P : PtsSig} : forall (M : exp P) ρ m1 m2,
      {{ ⟦ M ⟧ ρ ↘ m1 }} ->
      {{ ⟦ M ⟧ ρ ↘ m2 }} ->
      m1 = m2.
  Proof.
    pose proof @functional_eval P; firstorder.
  Qed.

  Corollary functional_eval_app {P : PtsSig} : forall (m : domain P) n e1 e2,
      {{ $| m & n |↘ e1 }} ->
      {{ $| m & n |↘ e2 }} ->
      e1 = e2.
  Proof.
    pose proof @functional_eval P; intuition.
    eapply H; mauto 2.
  Qed.

  Corollary functional_eval_natrec {P : PtsSig} : forall (A : exp P) MZ MS m ρ e1 e2,
      {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e1 }} ->
      {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e2 }} ->
      e1 = e2.
  Proof.
    pose proof @functional_eval P; intuition.
  Qed.

  Corollary functional_eval_sub {P : PtsSig} : forall (σ : sub P) ρ ρσ1 ρσ2,
      {{ ⟦ σ ⟧s ρ ↘ ρσ1 }} ->
      {{ ⟦ σ ⟧s ρ ↘ ρσ2 }} ->
      ρσ1 = ρσ2.
  Proof.
    pose proof @functional_eval P; firstorder.
  Qed.
End functional_eval.

#[export]
Hint Resolve env_lookup_functional functional_eval_exp functional_eval_app functional_eval_sub : mcpts.

Ltac functional_eval_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_eval equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : {{ #| ^?ρ[?n] |↘ ^?m1 }},
      H2 : {{ #| ^?ρ[?n] |↘ ^?m2 }} |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  | H1 : {{ ⟦ ^?M ⟧ ^?ρ ↘ ^?m1 }},
      H2 : {{ ⟦ ^?M ⟧ ^?ρ ↘ ^?m2 }} |- _ =>
      clean replace m2 with m1 by first [solve [mauto 2] | tactic_error m2 m1]; clear H2
  | H1 : {{ $| ^?m & ^?n |↘ ^?e1 }},
      H2 : {{ $| ^?m & ^?n |↘ ^?e2 }} |- _ =>
      clean replace e2 with e1 by first [solve [mauto 2] | tactic_error e2 e1]; clear H2
  | H1 : {{ rec ^?m ⟦return ^?A | zero -> ^?MZ | succ -> ^?MS end⟧ ^?ρ ↘ ^?e1 }},
      H2 : {{ rec ^?m ⟦return ^?A | zero -> ^?MZ | succ -> ^?MS end⟧ ^?ρ ↘ ^?e2 }} |- _ =>
      clean replace e2 with e1 by first [solve [mauto 2] | tactic_error e2 e1]; clear H2
  | H1 : {{ ⟦ ^?σ ⟧s ^?ρ ↘ ^?ρσ1 }},
      H2 : {{ ⟦ ^?σ ⟧s ^?ρ ↘ ^?ρσ2 }} |- _ =>
      clean replace ρσ2 with ρσ1 by first [solve [mauto 2] | tactic_error ρσ2 ρσ1]; clear H2
  end.
Ltac functional_eval_rewrite_clear := repeat functional_eval_rewrite_clear1.


