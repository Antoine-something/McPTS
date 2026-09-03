From Stdlib Require Import Orders Relation_Definitions RelationClasses Program.Equality.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature.

Section MiniMLSig.
  Inductive MiniML_St : Set :=
  | s_typ : MiniML_St.

  Inductive MiniML_Ax_typ : MiniML_St -> MiniML_St -> Prop :=.

  Inductive MiniML_Ax_sub : MiniML_St -> MiniML_St -> Prop :=.

  Inductive MiniML_Ru_pi : MiniML_St -> MiniML_St -> MiniML_St -> Prop :=
  | f_simple : MiniML_Ru_pi s_typ s_typ s_typ.

  Inductive MiniML_Ru_nat : MiniML_St -> Prop :=
  | n_typ : MiniML_Ru_nat s_typ.

  Definition MiniML_Sig : PtsSig :=
    mkPtsSig MiniML_St MiniML_Ax_typ MiniML_Ax_sub MiniML_Ru_pi MiniML_Ru_nat.
End MiniMLSig.             

Definition P := MiniML_Sig.

Section MiniMLPredicative.
  Inductive MiniML_pred_rel : relation P :=.

  Lemma MiniML_ord_rel : StrictOrder MiniML_pred_rel.
  Proof.
    split; inversion 1.
  Qed.

  Lemma MiniML_wf_rel : well_founded MiniML_pred_rel.
  Proof.
    split; inversion 1.
  Qed.

  Lemma MiniML_ord_ax_typ : forall (s1 s2 : P), Ax_typ P s1 s2 -> MiniML_pred_rel s1 s2.
  Proof.
    inversion 1.
  Qed.

  Lemma MiniML_ord_ax_sub : forall (s1 s2 : P), Ax_sub P s1 s2 -> MiniML_pred_rel s1 s2.
  Proof.
    inversion 1.
  Qed.

  Lemma MiniML_ord_ru_pi : forall (s1 s2 s3 : P), Ru_pi P s1 s2 s3 -> (MiniML_pred_rel s1 s3 \/ s1 = s3) /\ (MiniML_pred_rel s2 s3 \/ s2 = s3).
  Proof.
    inversion_clear 1.
    split; right; reflexivity.
  Qed.

  Definition MiniML_Predicative : PredicativeSig P :=
    mkPredicativeSig P MiniML_pred_rel MiniML_ord_rel MiniML_wf_rel MiniML_ord_ax_typ MiniML_ord_ax_sub MiniML_ord_ru_pi.
End MiniMLPredicative.

Section MiniMLFunctional.
  Lemma MiniML_Func_ax_typ : forall s1 s2 s2', Ax_typ P s1 s2 -> Ax_typ P s1 s2' -> s2 = s2'.
  Proof.
    inversion 1.
  Qed.

  Lemma MiniML_Func_ru_pi : forall s1 s2 s3 s3', Ru_pi P s1 s2 s3 -> Ru_pi P s1 s2 s3' -> s3 = s3'.
  Proof.
    intros * [] []; reflexivity.
  Qed.

  Lemma MiniML_Func_ru_nat : forall s s', Ru_nat P s -> Ru_nat P s' -> s = s'.
  Proof.
    intros * [] []; reflexivity.
  Qed.

  Definition MiniML_Functional : FunctionalSig P :=
    mkFunctionalSig P MiniML_Func_ax_typ MiniML_Func_ru_pi MiniML_Func_ru_nat.
End MiniMLFunctional.

Section MiniMLDecidable.
  Lemma MiniML_dec_st_eq : forall (s s' : P), ({s = s'} + {s <> s'})%type.
  Proof.
    intros [] []; left; reflexivity.
  Qed.

  Lemma MiniML_dec_ax_typ : forall (s : P), ( {s' & Ax_typ P s s'} + {forall s', ~Ax_typ P s s'} )%type.
  Proof.
    right; inversion 1.
  Qed.

  Lemma MiniML_dec_st_sub : forall (s s' : P), ({st_subtyp s s'} + {~ st_subtyp s s'})%type.
  Proof.
    intros [] [].
    left; reflexivity.
  Qed.

  Lemma MiniML_dec_ru_pi : forall (s1 s2 : P), ({s3 & Ru_pi P s1 s2 s3} + {forall s3, Ru_pi P s1 s2 s3 -> False})%type.
  Proof.
    intros [] []; left; eexists; econstructor.
  Qed.
  
  Lemma MiniML_dec_ru_pi_eq : forall (s1 s2 s3 : P) (r : Ru_pi P s1 s2 s3) (r' : Ru_pi P s1 s2 s3),
      ( { r = r'} + {r <> r'} )%type.
  Proof.
    simpl.
    intros s1 s2 s3 [] r'.
    dependent destruction r'.
    left; reflexivity.
  Qed.

  Lemma MiniML_dec_ru_nat : ({s & Ru_nat P s} + {forall s, Ru_nat P s -> False})%type.
  Proof.
    left; eexists; econstructor.
  Qed.

  Definition MiniML_Decidable : DecidableSig P :=
    mkDecidableSig MiniML_Sig MiniML_dec_st_eq MiniML_dec_ax_typ MiniML_dec_st_sub MiniML_dec_ru_pi MiniML_dec_ru_pi_eq MiniML_dec_ru_nat.
End MiniMLDecidable.
