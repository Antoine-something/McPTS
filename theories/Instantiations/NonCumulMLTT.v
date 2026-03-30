From Coq Require Import Arith Orders Relation_Definitions RelationClasses.
From Coq.Arith Require Import PeanoNat.
From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core.Syntactic Require Import Syntax System Presup.
From McPTS.Core Require Import Base Completeness Soundness.
Import Domain_Notations.

Section NonCumulSig.
  (** Definition of the signature *)
  Definition St_nc : Set := nat.

  Definition Ax_nc : St_nc -> St_nc -> Prop := lt.

  Variant Ru_nc : St_nc -> St_nc -> St_nc -> Set :=
    | mk_ru_cumul : forall i j, Ru_nc i j (max i j)
  .

  Variant Ru_nat_nc : St_nc -> Set :=
    | mk_ru_nat_nc : forall i, Ru_nat_nc i
  .

  Definition Sig_nc : PtsSig :=
    mkPtsSig St_nc Ax_nc Ru_nc Ru_nat_nc.


  (** Proof of predicativity *)
  Definition pred_rel_nc : relation St_nc := lt.
  Arguments pred_rel_nc /.

  Lemma ord_rel_nc : StrictOrder pred_rel_nc.
  Proof.
    apply Nat.lt_strorder.
  Qed.

  Lemma wf_rel_nc : well_founded pred_rel_nc.
  Proof.
    apply Wf_nat.lt_wf.
  Qed.

  Lemma ord_ax_nc : forall (s1 s2 : St Sig_nc), Ax Sig_nc s1 s2 -> pred_rel_nc s1 s2.
  Proof. trivial. Qed.

  Lemma ord_ru_nc : forall (s1 s2 s3 : St Sig_nc), Ru Sig_nc s1 s2 s3 -> (pred_rel_nc s1 s3 \/ s1 = s3) /\ (pred_rel_nc s2 s3 \/ s2 = s3).
  Proof.
    simpl.
    inversion 1; subst; lia.
  Qed.

  Definition pred_Sig_cumul : PredicativeSig Sig_nc :=
    mkPredicativeSig Sig_nc pred_rel_nc ord_rel_nc wf_rel_nc ord_ax_nc ord_ru_nc
  .
End NonCumulSig.
