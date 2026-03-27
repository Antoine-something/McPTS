From Coq Require Import Arith Orders Relation_Definitions RelationClasses.
From Coq.Arith Require Import PeanoNat.
From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core.Syntactic Require Import Syntax System Presup.
From McPTS.Core Require Import Base Completeness Soundness.
Import Domain_Notations.


Section CumulSig.
  (** Definition of the signature *)
  Definition St_cumul : Set := nat.

  Definition Ax_cumul : St_cumul -> St_cumul -> Prop := lt.

  Variant Ru_cumul : St_cumul -> St_cumul -> St_cumul -> Set :=
    | mk_ru_cumul : forall i j k, i <= j -> j <= k -> Ru_cumul i j k
  .
  
  Variant Ru_nat_cumul : St_cumul -> Set :=
    | mk_ru_nat_cumul : forall i, Ru_nat_cumul i
  .    

  Definition Sig_cumul : PtsSig :=
    mkPtsSig St_cumul Ax_cumul Ru_cumul Ru_nat_cumul.


  (** Proof of predicativity *)
  Definition pred_rel_cumul : relation St_cumul := lt.

  Lemma ord_rel_cumul : StrictOrder pred_rel_cumul.
  Proof.
    split.
    - intros x Hx.
      unfold pred_rel_cumul in Hx.
      eapply lt_irrefl in Hx.
      eassumption.
    - intros x y z Hxy Hyz.
      unfold pred_rel_cumul in *.
      eapply lt_trans; eauto.
  Qed.

  Lemma wf_rel_cumul : well_founded pred_rel_cumul.
  Proof.
    intros a.
    induction a.
    - econstructor; intros.
      unfold pred_rel_cumul in H.
      inversion H.
    - econstructor.
      intros.
      unfold pred_rel_cumul in H.
      inversion_clear H; [eassumption|].
      eapply IHa.
      inversion_clear H0; econstructor; eauto.
  Qed.

  Lemma ord_ax_cumul : forall (s1 s2 : St Sig_cumul), Ax Sig_cumul s1 s2 -> pred_rel_cumul s1 s2.
  Proof. trivial. Qed.

  Lemma ord_ru_cumul : forall (s1 s2 s3 : St Sig_cumul), Ru Sig_cumul s1 s2 s3 -> (pred_rel_cumul s1 s3 \/ s1 = s3) /\ (pred_rel_cumul s2 s3 \/ s2 = s3).
  Proof.
    intros.
    inversion H; subst.
    destruct H0; destruct H1; split.
    1,2,6: right; reflexivity.
    all: left; eapply Nat.le_lt_trans; eauto.
  Qed.

  Definition pred_Sig_cumul : PredicativeSig Sig_cumul :=
    mkPredicativeSig Sig_cumul pred_rel_cumul ord_rel_cumul wf_rel_cumul ord_ax_cumul ord_ru_cumul
  .
End CumulSig.
