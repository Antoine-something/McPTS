From Coq Require Import Orders Relation_Definitions RelationClasses Program.Equality Arith.
From Equations Require Import Equations.

From McPTS Require Import LibTactics PtsSignature.

Section MLTTCumulSig.
  Inductive MLTTCumul_St : Set :=
  | s_univ : nat -> MLTTCumul_St.

  Inductive MLTTCumul_Ax_typ : MLTTCumul_St -> MLTTCumul_St -> Prop :=
  | at_univ_suc : forall i, MLTTCumul_Ax_typ (s_univ i) (s_univ (S i)).

  Inductive MLTTCumul_Ax_sub : MLTTCumul_St -> MLTTCumul_St -> Prop :=
  | as_univ_suc : forall i, MLTTCumul_Ax_sub (s_univ i) (s_univ (S i)).

  Inductive MLTTCumul_Ru_pi : MLTTCumul_St -> MLTTCumul_St -> MLTTCumul_St -> Set :=
  | f_max : forall i j, MLTTCumul_Ru_pi (s_univ i) (s_univ j) (s_univ (max i j)).

  Inductive MLTTCumul_Ru_nat : MLTTCumul_St -> Set :=
  | n_zero : MLTTCumul_Ru_nat (s_univ 0).

  Definition MLTTCumul_Sig : PtsSig :=
    mkPtsSig MLTTCumul_St MLTTCumul_Ax_typ MLTTCumul_Ax_sub MLTTCumul_Ru_pi MLTTCumul_Ru_nat.
End MLTTCumulSig.             

Definition P := MLTTCumul_Sig.

Section MLTTCumulPredicative.
  Inductive MLTTCumul_pred_rel : relation P :=
  | pr_lt : forall i j, i < j -> MLTTCumul_pred_rel (s_univ i) (s_univ j).

  Lemma MLTTCumul_ord_rel : StrictOrder MLTTCumul_pred_rel.
  Proof.    
    pose proof Nat.lt_strorder as [].
    split.
    - intros [] H.
      dependent destruction H.
      eapply StrictOrder_Irreflexive; eauto 2.
    - intros [i] [j] [k] Hij Hjk;
        dependent destruction Hij;
        dependent destruction Hjk.
      econstructor; eapply StrictOrder_Transitive; eauto 2.
  Qed.

  Lemma MLTTCumul_wf_rel : well_founded MLTTCumul_pred_rel.
  Proof.
    pose proof Wf_nat.lt_wf.
    unfold well_founded in *.
    intros [].
    induction n.
    - econstructor; intros y Hy.
      dependent destruction Hy.
      inversion H0.
    - econstructor; intros y Hy.
      dependent destruction Hy.
      inversion_clear H0; try eassumption.
      eapply IHn; econstructor; auto.
  Qed.

  Lemma MLTTCumul_ord_ax_typ : forall (s1 s2 : P), Ax_typ P s1 s2 -> MLTTCumul_pred_rel s1 s2.
  Proof.
    intros * []; econstructor; auto.
  Qed.

  Lemma MLTTCumul_ord_ax_sub : forall (s1 s2 : P), Ax_sub P s1 s2 -> MLTTCumul_pred_rel s1 s2.
  Proof.
    intros * []; econstructor; auto.
  Qed.

  Lemma MLTTCumul_ord_ru_pi : forall (s1 s2 s3 : P), Ru_pi P s1 s2 s3 -> (MLTTCumul_pred_rel s1 s3 \/ s1 = s3) /\ (MLTTCumul_pred_rel s2 s3 \/ s2 = s3).
  Proof.
    intros * [].    
    split.
    - assert (i <= max i j) as [] by lia;
        [ right; reflexivity
          | left; econstructor; lia].
    - assert (j <= max i j) as [] by lia;
        [ right; reflexivity
          | left; econstructor; lia].
  Qed.

  Definition MLTTCumul_Predicative : PredicativeSig P :=
    mkPredicativeSig P MLTTCumul_pred_rel MLTTCumul_ord_rel MLTTCumul_wf_rel MLTTCumul_ord_ax_typ MLTTCumul_ord_ax_sub MLTTCumul_ord_ru_pi.
End MLTTCumulPredicative.

Section MLTTCumulFunctional.
  Lemma MLTTCumul_Func_ax_typ : forall s1 s2 s2', Ax_typ P s1 s2 -> Ax_typ P s1 s2' -> s2 = s2'.
  Proof.
    intros * [] H; inversion_clear H;
      reflexivity.
  Qed.

  Lemma MLTTCumul_Func_ru_pi : forall s1 s2 s3 s3', Ru_pi P s1 s2 s3 -> Ru_pi P s1 s2 s3' -> s3 = s3'.
  Proof.
    intros * [] H; inversion_clear H;
      reflexivity.
  Qed.

  Lemma MLTTCumul_Func_ru_nat : forall s s', Ru_nat P s -> Ru_nat P s' -> s = s'.
  Proof.
    intros * [] []; reflexivity.
  Qed.

  Definition MLTTCumul_Functional : FunctionalSig P :=
    mkFunctionalSig P MLTTCumul_Func_ax_typ MLTTCumul_Func_ru_pi MLTTCumul_Func_ru_nat.
End MLTTCumulFunctional.

Section MLTTCumulDecidable.
  Lemma MLTTCumul_dec_st_eq : forall (s s' : P), ({s = s'} + {s <> s'})%type.
  Proof.
    intros [] [].
    assert ({n = n0} + {n <> n0}) as [] by eapply eq_dec;
      [left | right; inversion 1]; auto.
  Qed.

  Lemma MLTTCumul_dec_ax_typ : forall (s : P), ( {s' & Ax_typ P s s'} + {forall s', ~Ax_typ P s s'} )%type.
  Proof.
    intros [i]; left; eexists; econstructor.
  Qed.

  Lemma MLTTCumul_dec_st_sub_help : forall i j, @st_subtyp P (s_univ i) (s_univ j) <-> i <= j.
  Proof.
    split.
    - intros H; dependent induction H; [lia |].
      destruct s2 as [k].
      inversion H; subst.
      assert (S i <= j) by auto.
      lia.
    - intros H; dependent induction H.
      reflexivity.
      transitivity (s_univ m); auto.
      enough (MLTTCumul_Ax_sub (s_univ m) (s_univ (S m))) by (econstructor; [eauto | reflexivity]).
      econstructor.
  Qed.
  
  Lemma MLTTCumul_dec_st_sub : forall (s s' : P), ({st_subtyp s s'} + {~ st_subtyp s s'})%type.
  Proof.
    intros [] [].
    assert ({n <= n0} + {~ n <= n0 }) as [] by eapply le_dec.
    left; eapply MLTTCumul_dec_st_sub_help; eassumption.
    right; intros H%(MLTTCumul_dec_st_sub_help); auto.
  Qed.

  Lemma MLTTCumul_dec_ru_pi : forall (s1 s2 : P), ({s3 & Ru_pi P s1 s2 s3} + {forall s3, Ru_pi P s1 s2 s3 -> False})%type.
  Proof.
    intros [i] [j]; left; eexists; econstructor.
  Qed.
  
  Lemma MLTTCumul_dec_ru_pi_eq : forall (s1 s2 s3 : P) (r : Ru_pi P s1 s2 s3) (r' : Ru_pi P s1 s2 s3),
      ( { r = r'} + {r <> r'} )%type.
  Proof.
    simpl.
    intros s1 s2 s3 [] r'.
    dependent destruction r'.
    left; reflexivity.
  Qed.

  Lemma MLTTCumul_dec_ru_nat : ({s & Ru_nat P s} + {forall s, Ru_nat P s -> False})%type.
  Proof.
    left; eexists; econstructor.
  Qed.
  
  Definition MLTTCumul_Decidable : DecidableSig P :=
    mkDecidableSig MLTTCumul_Sig MLTTCumul_dec_st_eq MLTTCumul_dec_ax_typ MLTTCumul_dec_st_sub MLTTCumul_dec_ru_pi MLTTCumul_dec_ru_pi_eq MLTTCumul_dec_ru_nat.
End MLTTCumulDecidable.
