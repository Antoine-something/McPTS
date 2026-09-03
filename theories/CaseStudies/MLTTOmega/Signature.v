From Stdlib Require Import Orders Relation_Definitions RelationClasses Program.Equality Arith.
From Equations Require Import Equations.

From McPTS Require Import LibTactics PtsSignature.

Section MLTTOmegaSig.
  Inductive MLTTOmega_St : Set :=
  | s_univ : nat -> MLTTOmega_St
  | s_omega : MLTTOmega_St.
  
  Inductive MLTTOmega_Ax_typ : MLTTOmega_St -> MLTTOmega_St -> Prop :=
  | at_univ_suc : forall i, MLTTOmega_Ax_typ (s_univ i) (s_univ (S i)).

  Inductive MLTTOmega_Ax_sub : MLTTOmega_St -> MLTTOmega_St -> Prop :=
  | as_univ_suc : forall i, MLTTOmega_Ax_sub (s_univ i) (s_univ (S i))
  | as_univ_omega : forall i, MLTTOmega_Ax_sub (s_univ i) s_omega.
  
  Inductive MLTTOmega_Ru_pi : MLTTOmega_St -> MLTTOmega_St -> MLTTOmega_St -> Set :=
  | f_max : forall i j, MLTTOmega_Ru_pi (s_univ i) (s_univ j) (s_univ (max i j))
  | f_omega: MLTTOmega_Ru_pi s_omega s_omega s_omega.

  Inductive MLTTOmega_Ru_nat : MLTTOmega_St -> Set :=
  | n_zero : MLTTOmega_Ru_nat (s_univ 0).

  Definition MLTTOmega_Sig : PtsSig :=
    mkPtsSig MLTTOmega_St MLTTOmega_Ax_typ MLTTOmega_Ax_sub MLTTOmega_Ru_pi MLTTOmega_Ru_nat.
End MLTTOmegaSig.             

Definition P := MLTTOmega_Sig.

Section MLTTOmegaPredicative.
  Inductive MLTTOmega_pred_rel : relation P :=
  | pr_lt : forall i j, i < j -> MLTTOmega_pred_rel (s_univ i) (s_univ j)
  | pr_omega: forall i, MLTTOmega_pred_rel (s_univ i) s_omega.

  Lemma MLTTOmega_ord_rel : StrictOrder MLTTOmega_pred_rel.
  Proof.    
    pose proof Nat.lt_strorder as [].
    split.
    - intros [] H;
      dependent destruction H;
      eapply StrictOrder_Irreflexive; eauto 2.
    - intros i j k Hij Hjk.
        dependent destruction Hij;
        dependent destruction Hjk;
          econstructor; eapply StrictOrder_Transitive; eauto 2.
  Qed.

  Lemma MLTTOmega_wf_rel_helper : forall (n : nat), Acc MLTTOmega_pred_rel (s_univ n).
  Proof.
    induction n.
    - econstructor; intros y Hy.
      dependent destruction Hy.
      inversion H.
    - econstructor; intros y Hy.
      dependent destruction Hy.
      inversion_clear H; try eassumption.
      eapply IHn; econstructor; auto.
  Qed.       
  Lemma MLTTOmega_wf_rel : well_founded MLTTOmega_pred_rel.
  Proof.
    pose proof Wf_nat.lt_wf.
    unfold well_founded in *.
    intros [].
    - eapply MLTTOmega_wf_rel_helper.
    - econstructor; intros; dependent destruction H0.
      eapply MLTTOmega_wf_rel_helper.
  Qed.

  Lemma MLTTOmega_ord_ax_typ : forall (s1 s2 : P), Ax_typ P s1 s2 -> MLTTOmega_pred_rel s1 s2.
  Proof.
    intros * []; econstructor; auto.
  Qed.

  Lemma MLTTOmega_ord_ax_sub : forall (s1 s2 : P), Ax_sub P s1 s2 -> MLTTOmega_pred_rel s1 s2.
  Proof.
    intros * []; econstructor; auto.
  Qed.

  Lemma MLTTOmega_ord_ru_pi : forall (s1 s2 s3 : P), Ru_pi P s1 s2 s3 -> (MLTTOmega_pred_rel s1 s3 \/ s1 = s3) /\ (MLTTOmega_pred_rel s2 s3 \/ s2 = s3).
  Proof.
    intros * [].    
    split.
    - assert (i <= max i j) as [] by lia;
        [ right; reflexivity
          | left; econstructor; lia].
    - assert (j <= max i j) as [] by lia;
        [ right; reflexivity
        | left; econstructor; lia].
    - split; right; reflexivity.
  Qed.

  Definition MLTTOmega_Predicative : PredicativeSig P :=
    mkPredicativeSig P MLTTOmega_pred_rel MLTTOmega_ord_rel MLTTOmega_wf_rel MLTTOmega_ord_ax_typ MLTTOmega_ord_ax_sub MLTTOmega_ord_ru_pi.
End MLTTOmegaPredicative.

Section MLTTOmegaFunctional.
  Lemma MLTTOmega_Func_ax_typ : forall s1 s2 s2', Ax_typ P s1 s2 -> Ax_typ P s1 s2' -> s2 = s2'.
  Proof.
    intros * [] H; inversion_clear H;
      reflexivity.
  Qed.

  Lemma MLTTOmega_Func_ru_pi : forall s1 s2 s3 s3', Ru_pi P s1 s2 s3 -> Ru_pi P s1 s2 s3' -> s3 = s3'.
  Proof.
    intros * [] H; inversion_clear H;
      reflexivity.
  Qed.

  Lemma MLTTOmega_Func_ru_nat : forall s s', Ru_nat P s -> Ru_nat P s' -> s = s'.
  Proof.
    intros * [] []; reflexivity.
  Qed.

  Definition MLTTOmega_Functional : FunctionalSig P :=
    mkFunctionalSig P MLTTOmega_Func_ax_typ MLTTOmega_Func_ru_pi MLTTOmega_Func_ru_nat.
End MLTTOmegaFunctional.

Section MLTTOmegaDecidable.
  Lemma MLTTOmega_dec_st_eq : forall (s s' : P), ({s = s'} + {s <> s'})%type.
  Proof.
    intros [] []; only 2,3: (right; intros H; inversion H).
    - assert ({n = n0} + {n <> n0}) as [] by eapply eq_dec;
        [left | right; inversion 1]; auto.
    - left; reflexivity.
  Qed.

  Lemma MLTTOmega_dec_ax_typ : forall (s : P), ( {s' & Ax_typ P s s'} + {forall s', ~Ax_typ P s s'} )%type.
  Proof.
    intros [].
    - left; eexists; econstructor.
    - right; intros; intros H; inversion H.
  Qed.

  Lemma MLTTOmega_dec_st_sub_help : forall i j, @st_subtyp P (s_univ i) (s_univ j) <-> i <= j.
  Proof.
    split.
    - intros H; dependent induction H; [lia |].
      destruct s2.
      + inversion H; subst.
        assert (S i <= j) by auto.
        lia.
      + inversion H0; inversion H1.
    - intros H; dependent induction H.
      reflexivity.
      transitivity (s_univ m); auto.
      enough (MLTTOmega_Ax_sub (s_univ m) (s_univ (S m))) by (econstructor; [eauto | reflexivity]).
      econstructor.
  Qed.
    
  Lemma MLTTOmega_dec_st_sub : forall (s s' : P), ({st_subtyp s s'} + {~ st_subtyp s s'})%type.
  Proof.
    intros [] [].
    - assert ({n <= n0} + {~ n <= n0 }) as [] by eapply le_dec.
      left; eapply MLTTOmega_dec_st_sub_help; eassumption.
      right; intros H%(MLTTOmega_dec_st_sub_help); auto.
    - left; econstructor; only 1: eapply as_univ_omega; econstructor.
    - right. intros H. inversion H; subst. inversion H; subst. inversion H0.
    - left; econstructor.
  Qed.

  Lemma MLTTOmega_dec_ru_pi : forall (s1 s2 : P), ({s3 & Ru_pi P s1 s2 s3} + {forall s3, Ru_pi P s1 s2 s3 -> False})%type.
  Proof.
    intros [i|] [j|]; only 2,3: (right; intros; inversion H).
    - left; eexists; econstructor.
    - left; eexists; econstructor.
  Qed.
  
  Lemma MLTTOmega_dec_ru_pi_eq : forall (s1 s2 s3 : P) (r : Ru_pi P s1 s2 s3) (r' : Ru_pi P s1 s2 s3),
      ( { r = r'} + {r <> r'} )%type.
  Proof.
    simpl.
    intros s1 s2 s3 [] r';
      dependent destruction r';
      left; reflexivity.
  Qed.

  Lemma MLTTOmega_dec_ru_nat : ({s & Ru_nat P s} + {forall s, Ru_nat P s -> False})%type.
  Proof.
    left; eexists; econstructor.
  Qed.
  
  Definition MLTTOmega_Decidable : DecidableSig P :=
    mkDecidableSig MLTTOmega_Sig MLTTOmega_dec_st_eq MLTTOmega_dec_ax_typ MLTTOmega_dec_st_sub MLTTOmega_dec_ru_pi MLTTOmega_dec_ru_pi_eq MLTTOmega_dec_ru_nat.
End MLTTOmegaDecidable.
