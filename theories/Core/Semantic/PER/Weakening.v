From Coq Require Import Equivalence Lia Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import System.
From McPTS.Core.Semantic Require Import PER.Definitions PER.CoreTactics PER.CoreLemmas PER.SortLemmas PER.TypeLemmas PER.SubtypingLemmas PER.CtxLemmas.
Import Domain_Notations.

(** ** All PERs are stable under weakening of global contexts *)
(* This is not currently true, cannot prove the pi case for per_sort_elem *)
Lemma gctx_weaken_per_bot {P} : forall {Δ : gctx P} {e e' x B},
    {{ Dom e ≈ e' ∈ per_bot Δ }} ->
    {{ `#x ∉ Δ }} ->
    {{ Dom e ≈ e' ∈ per_bot ((x, B) :: Δ) }}.
Proof.
  intros * Hbot Hfresh i;
    specialize (Hbot i) as [E []];
    repeat eexists; mauto 2.
Qed.

Lemma gctx_weaken_per_top {P} : forall {Δ : gctx P} {w w' x B},
    {{ Dom w ≈ w' ∈ per_top Δ }} ->
    {{ `#x ∉ Δ }} ->
    {{ Dom w ≈ w' ∈ per_top ((x, B) :: Δ) }}.
Proof.
  intros * Htop Hfresh i;
    specialize (Htop i) as [W []];
    repeat eexists; mauto 2.
Qed.

Lemma gctx_weaken_per_top_typ {P} : forall {Δ : gctx P} {a a' x B},
    {{ Dom a ≈ a' ∈ per_top_typ Δ }} ->
    {{ `#x ∉ Δ }} ->
    {{ Dom a ≈ a' ∈ per_top_typ ((x, B) :: Δ) }}.
Proof.
  intros * Htop_typ Hfresh i;
    specialize (Htop_typ i) as [A []];
    repeat eexists; mauto 2.
Qed.

#[export]
Hint Resolve gctx_weaken_per_bot gctx_weaken_per_top gctx_weaken_per_top_typ : mcpts.
 
Lemma gctx_weaken_per_nat {P} : forall {Δ : gctx P} {n n' x B},
    {{ Dom n ≈ n' ∈ per_nat Δ }} ->
    {{ `#x ∉ Δ }} ->
    {{ Dom n ≈ n' ∈ per_nat ((x, B) :: Δ) }}.
Proof.
  induction 1; intros; mauto 3.
Qed.

#[export]
Hint Resolve gctx_weaken_per_nat : mcpts.

Lemma gctx_weaken_per_ne {P} : forall {Δ : gctx P} {m m' x B},
    {{ Dom m ≈ m' ∈ per_ne Δ }} ->
    {{ `#x ∉ Δ }} ->
    {{ Dom m ≈ m' ∈ per_ne ((x, B) :: Δ) }}.
Proof.
  induction 1; intros; mauto 3.
Qed.

#[export]
Hint Resolve gctx_weaken_per_ne : mcpts.

Lemma gctx_weaken_per_sort_elem {P} {pred_P : PredicativeSig P} : forall {Δ : gctx P} {x B a a' s R},
    {{ `#x ∉ Δ }} ->
    {{ DF a ≈ a' ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    exists R',
      {{ DF a ≈ a' ∈ per_sort_elem pred_P ((x, B) :: Δ) s ↘ R' }}.
Proof.
  simpl.
  intros * Hfresh.
  induction 1 using per_sort_elem_ind.
  - eexists; (unshelve per_sort_elem_econstructor; mauto 2).
    reflexivity.
  - destruct IHper_sort_elem as [in_rel'].
    admit.
  - eexists; per_sort_elem_econstructor; mauto 2.
    reflexivity.
  - eexists; per_sort_elem_econstructor; mauto 2.
    reflexivity.
Abort.      
