From Stdlib Require Import Orders Relation_Definitions RelationClasses Program.Equality Arith.
From Equations Require Import Equations.

From McPTS Require Import LibTactics PtsSignature.

Section MLTTNonCumulSig.
  Inductive MLTTNonCumul_St : Set :=
  | s_univ : nat -> MLTTNonCumul_St.

  Inductive MLTTNonCumul_Ax_typ : MLTTNonCumul_St -> MLTTNonCumul_St -> Prop :=
  | at_univ_suc : forall i, MLTTNonCumul_Ax_typ (s_univ i) (s_univ (S i)).

  Inductive MLTTNonCumul_Ax_sub : MLTTNonCumul_St -> MLTTNonCumul_St -> Prop :=.

  Inductive MLTTNonCumul_Ru_pi : MLTTNonCumul_St -> MLTTNonCumul_St -> MLTTNonCumul_St -> Set :=
  | f_max : forall i j, MLTTNonCumul_Ru_pi (s_univ i) (s_univ j) (s_univ (max i j)).

  Inductive MLTTNonCumul_Ru_nat : MLTTNonCumul_St -> Set :=
  | n_zero : MLTTNonCumul_Ru_nat (s_univ 0).

  Definition MLTTNonCumul_Sig : PtsSig :=
    mkPtsSig MLTTNonCumul_St MLTTNonCumul_Ax_typ MLTTNonCumul_Ax_sub MLTTNonCumul_Ru_pi MLTTNonCumul_Ru_nat.
End MLTTNonCumulSig.             

Definition P := MLTTNonCumul_Sig.

Section MLTTNonCumulPredicative.
  Inductive MLTTNonCumul_pred_rel : relation P :=
  | pr_lt : forall i j, i < j -> MLTTNonCumul_pred_rel (s_univ i) (s_univ j).

  Lemma MLTTNonCumul_ord_rel : StrictOrder MLTTNonCumul_pred_rel.
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

  Lemma MLTTNonCumul_wf_rel : well_founded MLTTNonCumul_pred_rel.
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

  Lemma MLTTNonCumul_ord_ax_typ : forall (s1 s2 : P), Ax_typ P s1 s2 -> MLTTNonCumul_pred_rel s1 s2.
  Proof.
    intros * []; econstructor; auto.
  Qed.

  Lemma MLTTNonCumul_ord_ax_sub : forall (s1 s2 : P), Ax_sub P s1 s2 -> MLTTNonCumul_pred_rel s1 s2.
  Proof.
    intros * []; econstructor; auto.
  Qed.

  Lemma MLTTNonCumul_ord_ru_pi : forall (s1 s2 s3 : P), Ru_pi P s1 s2 s3 -> (MLTTNonCumul_pred_rel s1 s3 \/ s1 = s3) /\ (MLTTNonCumul_pred_rel s2 s3 \/ s2 = s3).
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

  Definition MLTTNonCumul_Predicative : PredicativeSig P :=
    mkPredicativeSig P MLTTNonCumul_pred_rel MLTTNonCumul_ord_rel MLTTNonCumul_wf_rel MLTTNonCumul_ord_ax_typ MLTTNonCumul_ord_ax_sub MLTTNonCumul_ord_ru_pi.
End MLTTNonCumulPredicative.

Section MLTTNonCumulFunctional.
  Lemma MLTTNonCumul_Func_ax_typ : forall s1 s2 s2', Ax_typ P s1 s2 -> Ax_typ P s1 s2' -> s2 = s2'.
  Proof.
    intros * [] H; inversion_clear H;
      reflexivity.
  Qed.

  Lemma MLTTNonCumul_Func_ru_pi : forall s1 s2 s3 s3', Ru_pi P s1 s2 s3 -> Ru_pi P s1 s2 s3' -> s3 = s3'.
  Proof.
    intros * [] H; inversion_clear H;
      reflexivity.
  Qed.

  Lemma MLTTNonCumul_Func_ru_nat : forall s s', Ru_nat P s -> Ru_nat P s' -> s = s'.
  Proof.
    intros * [] []; reflexivity.
  Qed.

  Definition MLTTNonCumul_Functional : FunctionalSig P :=
    mkFunctionalSig P MLTTNonCumul_Func_ax_typ MLTTNonCumul_Func_ru_pi MLTTNonCumul_Func_ru_nat.
End MLTTNonCumulFunctional.

Section MLTTNonCumulDecidable.
  Lemma MLTTNonCumul_dec_st_eq : forall (s s' : P), ({s = s'} + {s <> s'})%type.
  Proof.
    intros [] [].
    assert ({n = n0} + {n <> n0}) as [] by eapply eq_dec;
      [left | right; inversion 1]; auto.
  Qed.

  Lemma MLTTNonCumul_dec_ax_typ : forall (s : P), ( {s' & Ax_typ P s s'} + {forall s', ~Ax_typ P s s'} )%type.
  Proof.
    intros [i]; left; eexists; econstructor.
  Qed.

  Lemma MLTTNonCumul_dec_st_sub_help : forall i j, @st_subtyp P (s_univ i) (s_univ j) <-> i = j.
  Proof.
    split.
    - intros H; dependent induction H; [lia |].
      destruct s2 as [k].
      inversion H; subst.
    - intros H; dependent induction H.
      reflexivity.
  Qed.
  
  Lemma MLTTNonCumul_dec_st_sub : forall (s s' : P), ({st_subtyp s s'} + {~ st_subtyp s s'})%type.
  Proof.
    intros [] [].
    assert ({n = n0} + {~ n = n0 }) as [] by eapply eq_dec.
    left; eapply MLTTNonCumul_dec_st_sub_help; eassumption.
    right; intros H%(MLTTNonCumul_dec_st_sub_help); auto.
  Qed.

  Lemma MLTTNonCumul_dec_ru_pi : forall (s1 s2 : P), ({s3 & Ru_pi P s1 s2 s3} + {forall s3, Ru_pi P s1 s2 s3 -> False})%type.
  Proof.
    intros [i] [j]; left; eexists; econstructor.
  Qed.
  
  Lemma MLTTNonCumul_dec_ru_pi_eq : forall (s1 s2 s3 : P) (r : Ru_pi P s1 s2 s3) (r' : Ru_pi P s1 s2 s3),
      ( { r = r'} + {r <> r'} )%type.
  Proof.
    simpl.
    intros s1 s2 s3 [] r'.
    dependent destruction r'.
    left; reflexivity.
  Qed.

  Lemma MLTTNonCumul_dec_ru_nat : ({s & Ru_nat P s} + {forall s, Ru_nat P s -> False})%type.
  Proof.
    left; eexists; econstructor.
  Qed.
  
  Definition MLTTNonCumul_Decidable : DecidableSig P :=
    mkDecidableSig MLTTNonCumul_Sig MLTTNonCumul_dec_st_eq MLTTNonCumul_dec_ax_typ MLTTNonCumul_dec_st_sub MLTTNonCumul_dec_ru_pi MLTTNonCumul_dec_ru_pi_eq MLTTNonCumul_dec_ru_nat.
End MLTTNonCumulDecidable.
