From Coq Require Import Lia PeanoNat Relations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import System.
From McPTS.Core.Semantic Require Import Evaluation.
From McPTS.Core.Semantic.Readback Require Import Definitions.
Import Domain_Notations.

Section functional_read.
  Lemma functional_read {P : PtsSig} :
    (forall (Δ : gctx P) i m M1,
        {{ Δ ▶ Rnf m in i ↘ M1 }} ->
        forall M2,
          {{ Δ ▶ Rnf m in i ↘ M2 }} ->
          M1 = M2) /\
      (forall (Δ : gctx P) i e E1,
          {{ Δ ▶ Rne e in i ↘ E1 }} ->
          forall E2,
            {{ Δ ▶ Rne e in i ↘ E2 }} ->
            E1 = E2) /\
      (forall (Δ : gctx P) i a A1,
          {{ Δ ▶ Rtyp a in i ↘ A1 }} ->
          forall A2,
            {{ Δ ▶ Rtyp a in i ↘ A2 }} ->
            A1 = A2).
  Proof with (functional_eval_rewrite_clear; f_equal; solve [eauto]) using.
    apply read_mut_ind; intros.
    1,3-11,13,14: progressive_inversion...

    (* 1,3-9,10,12,13: progressive_inversion... *)

    - progressive_invert H2.
      assert (A = A0) by mauto.
      assert (b = b0) by (eapply functional_eval_exp; mauto).
      assert (m' = m'0) by (eapply functional_eval_app; mauto).
      subst.
      assert (B' = B'0) by mauto.
      assert (M = M0) by mauto.
      subst.
      reflexivity.
    - progressive_invert H1.
      assert (A = A0) by mauto.
      assert (b = b0) by (eapply functional_eval_exp; mauto).
      subst.
      assert (B' = B'0) by mauto.
      subst.
      reflexivity.
  Qed.

  Corollary functional_read_nf {P : PtsSig} : forall (Δ : gctx P) i v V1 V2,
      {{ Δ ▶ Rnf v in i ↘ V1 }} ->
      {{ Δ ▶ Rnf v in i ↘ V2 }} ->
      V1 = V2.
  Proof.
    pose proof @functional_read P; firstorder.
  Qed.

  Lemma functional_read_ne {P : PtsSig} : forall (Δ : gctx P) i e E1 E2,
      {{ Δ ▶ Rne e in i ↘ E1 }} ->
      {{ Δ ▶ Rne e in i ↘ E2 }} ->
      E1 = E2.
  Proof.
    pose proof @functional_read P; firstorder.
  Qed.

  Lemma functional_read_typ {P : PtsSig} : forall (Δ : gctx P) i a A1 A2,
      {{ Δ ▶ Rtyp a in i ↘ A1 }} ->
      {{ Δ ▶ Rtyp a in i ↘ A2 }} ->
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
  | H1 : {{ Δ ▶ Rnf ^?m in ?s ↘ ^?M1 }}, H2 : {{ Δ ▶ Rnf ^?m in ?s ↘ ^?M2 }} |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : {{ Δ ▶ Rne ^?m in ?s ↘ ^?M1 }}, H2 : {{ Δ ▶ Rne ^?m in ?s ↘ ^?M2 }} |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : {{ Δ ▶ Rtyp ^?m in ?s ↘ ^?M1 }}, H2 : {{ Δ ▶ Rtyp ^?m in ?s ↘ ^?M2 }} |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  end.
Ltac functional_read_rewrite_clear := repeat functional_read_rewrite_clear1.

Section gctx_weakening_readback.
  Lemma gctx_weakening_readback {P} :
    (forall (Δ : gctx P) i w W, {{ Δ ▶ Rnf w in i ↘ W }} -> forall x B, {{ `#x ∉ Δ }} -> {{ Δ, x:B ▶ Rnf w in i ↘ W }}) /\
      (forall (Δ : gctx P) i e E, {{ Δ ▶ Rne e in i ↘ E }} -> forall x B, {{ `#x ∉ Δ }} -> {{ Δ, x:B ▶ Rne e in i ↘ E }}) /\
      (forall (Δ : gctx P) i a A, {{ Δ ▶ Rtyp a in i ↘ A }} -> forall x B, {{ `#x ∉ Δ }} -> {{ Δ, x:B ▶ Rtyp a in i ↘ A }}).
  Proof.
    apply read_mut_ind;
      intros; mauto;
      econstructor; mauto 3.
  Qed.

  #[local]
  Ltac solve_gctx_weakening_readback P := pose proof (@gctx_weakening_readback P); destruct_conjs; intros; mauto 3.
  
  Corollary gctx_weakening_readback_nf {P} : forall {Δ : gctx P} {i w W x B},
      {{ Δ ▶ Rnf w in i ↘ W }} ->
      {{ `#x ∉ Δ }} ->
      {{ Δ, x:B ▶ Rnf w in i ↘ W }}.
  Proof. solve_gctx_weakening_readback P. Qed.

  Corollary gctx_weakening_readback_ne {P} : forall {Δ : gctx P} {i e E x B},
      {{ Δ ▶ Rne e in i ↘ E }} ->
      {{ `#x ∉ Δ }} ->
      {{ Δ, x:B ▶ Rne e in i ↘ E }}.
  Proof. solve_gctx_weakening_readback P. Qed.

  Corollary gctx_weakening_readback_typ {P} : forall {Δ : gctx P} {i a A x B},
      {{ Δ ▶ Rtyp a in i ↘ A }} ->
      {{ `#x ∉ Δ }} ->
      {{ Δ, x:B ▶ Rtyp a in i ↘ A }}.
  Proof. solve_gctx_weakening_readback P. Qed.
End gctx_weakening_readback.

#[export]
Hint Resolve gctx_weakening_readback_nf gctx_weakening_readback_ne gctx_weakening_readback_typ : mcpts.
 
