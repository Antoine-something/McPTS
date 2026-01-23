From Coq Require Import Lia PeanoNat Relations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Import Evaluation.
From McPTS.Core.Semantic.Readback Require Import Definitions.
Import Domain_Notations.

Section functional_read.
  Lemma functional_read {P : PtsSig} :
    (forall i (m : domain_nf P) M1,
        {{ Rnf m in i ↘ M1 }} ->
        forall M2,
          {{ Rnf m in i ↘ M2 }} ->
          M1 = M2) /\
      (forall i (e : domain_ne P) E1,
          {{ Rne e in i ↘ E1 }} ->
          forall E2,
            {{ Rne e in i ↘ E2 }} ->
            E1 = E2) /\
      (forall i (a : domain P) A1,
          {{ Rtyp a in i ↘ A1 }} ->
          forall A2,
            {{ Rtyp a in i ↘ A2 }} ->
            A1 = A2).
  Proof with (functional_eval_rewrite_clear; f_equal; solve [eauto]) using.
    apply read_mut_ind; intros.
    all: progressive_inversion...
    
    (* 1, 3-9,10,12,13: progressive_inversion... *)
    (* - progressive_invert H1. *)
    (*   assert (A = A0) by mauto. *)
    (*   assert (b = b0) by (eapply functional_eval_exp; mauto). *)
    (*   assert (m' = m'0) by (eapply functional_eval_app; mauto). *)
    (*   subst.       *)
    (*   assert (M = M0) by mauto. *)
    (*   subst. *)
    (*   reflexivity. *)
    (* - progressive_invert H1. *)
    (*   assert (A = A0) by mauto. *)
    (*   assert (b = b0) by (eapply functional_eval_exp; mauto). *)
    (*   subst. *)
    (*   assert (B' = B'0) by mauto. *)
    (*   subst. *)
    (*   reflexivity. *)
  Qed.

  Corollary functional_read_nf {P : PtsSig} : forall i (v : domain_nf P) V1 V2,
      {{ Rnf v in i ↘ V1 }} ->
      {{ Rnf v in i ↘ V2 }} ->
      V1 = V2.
  Proof.
    pose proof @functional_read P; firstorder.
  Qed.

  Lemma functional_read_ne {P : PtsSig} : forall i (e : domain_ne P) E1 E2,
      {{ Rne e in i ↘ E1 }} ->
      {{ Rne e in i ↘ E2 }} ->
      E1 = E2.
  Proof.
    pose proof @functional_read P; firstorder.
  Qed.

  Lemma functional_read_typ {P : PtsSig} : forall i (a : domain P) A1 A2,
      {{ Rtyp a in i ↘ A1 }} ->
      {{ Rtyp a in i ↘ A2 }} ->
      A1 = A2.
  Proof.
    pose proof @functional_read P; firstorder.
  Qed.
End functional_read.

#[export]
Hint Resolve functional_read_nf functional_read_ne functional_read_typ : mcpts.

Ltac functional_read_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_read equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : {{ Rnf ^?m in ?s ↘ ^?M1 }}, H2 : {{ Rnf ^?m in ?s ↘ ^?M2 }} |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : {{ Rne ^?m in ?s ↘ ^?M1 }}, H2 : {{ Rne ^?m in ?s ↘ ^?M2 }} |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : {{ Rtyp ^?m in ?s ↘ ^?M1 }}, H2 : {{ Rtyp ^?m in ?s ↘ ^?M2 }} |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  end.
Ltac functional_read_rewrite_clear := repeat functional_read_rewrite_clear1.
