From Coq Require Import Equivalence Lia Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import System.
From McPTS.Core.Semantic Require Import PER.Definitions PER.CoreTactics PER.CoreLemmas PER.SortLemmas PER.TypeLemmas PER.SubtypingLemmas.
Import Domain_Notations.

(** ** Lemmas for per_gctx *)

(** Equivalent global contexts have the same fresh variables *)
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

(** per_gctx really is a PER *)
(* The current formulation must be wrong because transitivity does (appear to) not hold *)
Lemma per_gctx_sym {P} {pred_P : PredicativeSig P} : forall Δ Δ',
    {{ GC Δ ≈ Δ' ∈ per_gctx pred_P }} ->
    {{ GC Δ' ≈ Δ ∈ per_gctx pred_P }}.
Proof.
  induction 1; mauto 2.
  destruct_rel_typ_unsorted.
  symmetry in H2.
  symmetry in H5.
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
