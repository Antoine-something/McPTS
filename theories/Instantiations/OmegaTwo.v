From Coq Require Import Arith Orders Relation_Definitions RelationClasses.
From Coq.Arith Require Import PeanoNat.
From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core.Syntactic Require Import Syntax System Presup.
From McPTS.Core Require Import Base Completeness Soundness.
Import Domain_Notations.


Section OmegaSig.
  (** Definition of the signature *)
  Inductive St_om : Set :=
  | fin : forall (i : nat), St_om
  | infin : forall (i : nat), St_om
  .

  Inductive Ax_om : St_om -> St_om -> Prop :=
  | ax_fin_succ : forall i, Ax_om (fin i) (fin (S i))
  | ax_infin_succ : forall i, Ax_om (infin i) (infin (S i))
  (* | ax_fin_omega : forall i, Ax_om (fin i) (infin 0) *)
  .

  Inductive Ru_om : St_om -> St_om -> St_om -> Prop :=
  | ru_fin_fin : forall i j, Ru_om (fin i) (fin j) (fin (max i j))
  | ru_infin_infin : forall i j, Ru_om (infin i) (infin j) (infin (max i j))
  | ru_fin_infin : forall i j, Ru_om (fin i) (infin j) (infin j)
  .

  Inductive Ru_nat_om : St_om -> Prop :=
  | ru_nat_zero : Ru_nat_om (fin 0)
  .

  Definition Sig_om : PtsSig :=
    mkPtsSig St_om Ax_om Ru_om Ru_nat_om
  .


  (** Proof of predicativity *)
  Inductive pred_rel_om : relation St_om :=
  | pr_fin_fin : forall i j, i < j -> pred_rel_om (fin i) (fin j)
  | pr_infin_infin : forall i j, i < j -> pred_rel_om (infin i) (infin j)
  | pr_fin_infin : forall i j, pred_rel_om (fin i) (infin j)
  .

  Lemma ord_rel_om : StrictOrder pred_rel_om.
  Proof.
    split.
    - intros x Hx.
      dependent destruction Hx;
        eapply lt_irrefl in H; eassumption.
    - intros x y z Hxy.
      gen z.
      induction Hxy;
        intros z Hyz; inversion Hyz; subst.
      1,3: assert (i < j0) by (eapply lt_trans; eauto).
      all: econstructor; eauto.
  Qed.

  Lemma wf_rel_om_fin : forall i, Acc pred_rel_om (fin i).
  Proof.
    intros i.
    induction i.
    - econstructor.
      intros.
      inversion H; subst.
      dependent destruction H2.
    - econstructor.
      intros.
      inversion H; subst.
      inversion H2; subst; eauto.      
      assert (pred_rel_om (fin i0) (fin i)) by (econstructor; lia).
      eapply IHi; eauto.
  Qed.

  Lemma wf_rel_om_infin : forall i, Acc pred_rel_om (infin i).  
  Proof.
    intros i.
    induction i.
    - econstructor.
      intros.
      inversion H; subst.
      + dependent destruction H2.
      + eapply wf_rel_om_fin; eauto.
    - econstructor.
      intros.
      inversion H; subst.
      + inversion H2; subst; eauto.      
        assert (pred_rel_om (infin i0) (infin i)) by (econstructor; lia).
        eapply IHi; eauto.
      + eapply wf_rel_om_fin.
  Qed.        
      
    
  Lemma wf_rel_om : well_founded pred_rel_om.
  Proof.
    intros x.
    destruct x.
    - eapply wf_rel_om_fin.
    - eapply wf_rel_om_infin.
  Qed.

  Lemma ord_ax_om : forall (s1 s2 : St Sig_om), Ax Sig_om s1 s2 -> pred_rel_om s1 s2.
  Proof.
    intros.
    destruct H;
      enough (i < S i) by (econstructor; eauto);
      econstructor.
  Qed.

  Lemma ord_ru_om_helper : forall i j, i < j \/ i = j \/ j < i.
  Proof.
    intros i.
    induction i.
    - intros.
      destruct j; eauto.
      left; lia.
    - intros.
      destruct j.
      + right; right; lia.
      + specialize (IHi j).
        destruct IHi; [left; lia |].
        destruct H; right; [left | right]; eauto.
        lia.
  Qed.
  
  Lemma ord_ru_om : forall (s1 s2 s3 : St Sig_om), Ru Sig_om s1 s2 s3 -> (pred_rel_om s1 s3 \/ s1 = s3) /\ (pred_rel_om s2 s3 \/ s2 = s3).
  Proof.
    intros.
    inversion H; subst.
    - assert (i < j \/ i = j \/ j < i) by (eapply ord_ru_om_helper; eauto).
      destruct H0; [| destruct H0].
      + assert (Init.Nat.max i j = j) as -> by lia.
        split.        
        * left.
          econstructor; eassumption.
        * right.
          reflexivity.
      + subst.
        assert (Init.Nat.max j j = j) as -> by lia.
        split; right; reflexivity.
      + assert (Init.Nat.max i j = i) as -> by lia.
        split.        
        * right.
          reflexivity.
        * left.
          econstructor; eassumption.

    - assert (i < j \/ i = j \/ j < i) by (eapply ord_ru_om_helper; eauto).
      destruct H0; [| destruct H0].
      + assert (Init.Nat.max i j = j) as -> by lia.
        split.        
        * left.
          econstructor; eassumption.
        * right.
          reflexivity.
      + subst.
        assert (Init.Nat.max j j = j) as -> by lia.
        split; right; reflexivity.
      + assert (Init.Nat.max i j = i) as -> by lia.
        split.        
        * right.
          reflexivity.
        * left.
          econstructor; eassumption.

    - split; [left; econstructor | right; reflexivity].
  Qed.

  Definition pred_Sig_om : PredicativeSig Sig_om :=
    mkPredicativeSig Sig_om pred_rel_om ord_rel_om wf_rel_om ord_ax_om ord_ru_om
  .
End OmegaSig.


