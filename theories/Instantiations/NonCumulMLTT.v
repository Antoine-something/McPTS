From Coq Require Import Arith Orders Relation_Definitions RelationClasses.
From Coq.Arith Require Import PeanoNat.
From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core.Syntactic Require Import Syntax System Presup.
From McPTS.Core Require Import Base Completeness Soundness.
Import Domain_Notations.
Import Nat.

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

  Lemma ord_rel_nc : StrictOrder pred_rel_nc.
  Proof.
    split.
    - intros x Hx.
      unfold pred_rel_nc in Hx.
      eapply lt_irrefl in Hx.
      eassumption.
    - intros x y z Hxy Hyz.
      unfold pred_rel_nc in *.
      eapply lt_trans; eauto.
  Qed.

  Lemma wf_rel_nc : well_founded pred_rel_nc.
  Proof.
    intros a.
    induction a.
    - econstructor; intros.
      unfold pred_rel_nc in H.
      inversion H.
    - econstructor.
      intros.
      unfold pred_rel_nc in H.
      inversion_clear H; [eassumption|].
      eapply IHa.
      inversion_clear H0; econstructor; eauto.
  Qed.

  Lemma ord_ax_nc : forall (s1 s2 : St Sig_nc), Ax Sig_nc s1 s2 -> pred_rel_nc s1 s2.
  Proof. trivial. Qed.

  Lemma ord_ru_nc : forall (s1 s2 s3 : St Sig_nc), Ru Sig_nc s1 s2 s3 -> (pred_rel_nc s1 s3 \/ s1 = s3) /\ (pred_rel_nc s2 s3 \/ s2 = s3).
  Proof.
    intros.
    inversion H; subst.
    destruct s1, s2; split.
    1,2,4,5: right; reflexivity.
    1,2: left; eapply le_lt_trans; eauto; eapply lt_0_succ.
    - simpl.
      destruct (le_max_l s1 s2).
      + right; reflexivity.
      + left; eapply le_lt_trans; eauto.
        do 2 (eapply le_n_S); eauto.
    - simpl.
      destruct (le_max_r s1 s2).
      + right; reflexivity.
      + left; eapply le_lt_trans; eauto.
        do 2 (eapply le_n_S); eauto.
  Qed.

  Definition pred_Sig_cumul : PredicativeSig Sig_nc :=
    mkPredicativeSig Sig_nc pred_rel_nc ord_rel_nc wf_rel_nc ord_ax_nc ord_ru_nc
  .
End NonCumulSig.
