From Stdlib Require Import Orders Relation_Definitions RelationClasses Program.Equality.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature.

Section STLCSig.
  Inductive STLC_St : Set :=
  | s_typ : STLC_St.

  Inductive STLC_Ax_typ : STLC_St -> STLC_St -> Prop :=.

  Inductive STLC_Ax_sub : STLC_St -> STLC_St -> Prop :=.

  Inductive STLC_Ru_pi : STLC_St -> STLC_St -> STLC_St -> Set :=
  | f_simple : STLC_Ru_pi s_typ s_typ s_typ.

  Inductive STLC_Ru_nat : STLC_St -> Set :=.

  Definition STLC_Sig : PtsSig :=
    mkPtsSig STLC_St STLC_Ax_typ STLC_Ax_sub STLC_Ru_pi STLC_Ru_nat.
End STLCSig.

Definition P := STLC_Sig.

Section STLCPredicative.
  Inductive STLC_pred_rel : relation P :=.

  Lemma STLC_ord_rel : StrictOrder STLC_pred_rel.
  Proof.
    split; inversion_clear 1.
  Qed.

  Lemma STLC_wf_rel : well_founded STLC_pred_rel.
  Proof.
    intros []; econstructor; intros [] [].
  Qed.

  Lemma STLC_ord_ax_typ : forall (s1 s2 : P), Ax_typ P s1 s2 -> STLC_pred_rel s1 s2.
  Proof.
    inversion 1.
  Qed.

  Lemma STLC_ord_ax_sub : forall (s1 s2 : P), Ax_sub P s1 s2 -> STLC_pred_rel s1 s2.
  Proof.
    inversion 1.
  Qed.
 
  Lemma STLC_ord_ru_pi : forall (s1 s2 s3 : P), Ru_pi P s1 s2 s3 -> (STLC_pred_rel s1 s3 \/ s1 = s3) /\ (STLC_pred_rel s2 s3 \/ s2 = s3).
  Proof.
    inversion_clear 1; split;
      try solve [right; reflexivity].
  Qed.

  Definition STLC_Predicative : PredicativeSig P :=
    mkPredicativeSig P STLC_pred_rel STLC_ord_rel STLC_wf_rel STLC_ord_ax_typ STLC_ord_ax_sub STLC_ord_ru_pi.
End STLCPredicative.


Section STLCFunctional.
  Lemma STLC_Func_ax_typ : forall s1 s2 s2', Ax_typ P s1 s2 -> Ax_typ P s1 s2' -> s2 = s2'.
  Proof.
    inversion_clear 1.
  Qed.

  Lemma STLC_Func_ru_pi : forall s1 s2 s3 s3', Ru_pi P s1 s2 s3 -> Ru_pi P s1 s2 s3' -> s3 = s3'.
  Proof.
    intros * [] []; reflexivity.
  Qed.

  Lemma STLC_Func_ru_nat : forall s s', Ru_nat P s -> Ru_nat P s' -> s = s'.
  Proof.
    inversion_clear 1.
  Qed.

  Definition STLC_Functional : FunctionalSig P :=
    mkFunctionalSig P STLC_Func_ax_typ STLC_Func_ru_pi STLC_Func_ru_nat.
End STLCFunctional.

Section STLCDecidable.
  Lemma STLC_dec_st_eq : forall (s s' : P), ({s = s'} + {s <> s'})%type.
  Proof.
    intros [] []; left; reflexivity.
  Qed.

  Lemma STLC_dec_ax_typ : forall (s : P), ( {s' & Ax_typ P s s'} + {forall s', ~Ax_typ P s s'} )%type.
  Proof.
    intros []; right; inversion 1.
  Qed.

  Lemma STLC_dec_st_sub : forall (s s' : P), ({st_subtyp s s'} + {~ st_subtyp s s'})%type.
  Proof.
    intros [] []; left; reflexivity.
  Qed.

  Lemma STLC_dec_ru_pi : forall (s1 s2 : P), ({s3 & Ru_pi P s1 s2 s3} + {forall s3, Ru_pi P s1 s2 s3 -> False})%type.
  Proof.
    intros [] [];
      only 1: (left; eexists; econstructor);
      right; intros * H; inversion H.
  Qed.
  
  Lemma STLC_dec_ru_pi_eq : forall (s1 s2 s3 : P) (r : Ru_pi P s1 s2 s3) (r' : Ru_pi P s1 s2 s3),
      ( { r = r'} + {r <> r'} )%type.
  Proof.
    simpl.
    intros s1 s2 s3 [] r';
      dependent destruction r';
      left; reflexivity.
  Qed.

  Lemma STLC_dec_ru_nat : ({s & Ru_nat P s} + {forall s, Ru_nat P s -> False})%type.
  Proof.
    right; inversion 1.
  Qed.
  
  Definition STLC_Decidable : DecidableSig P :=
    mkDecidableSig STLC_Sig STLC_dec_st_eq STLC_dec_ax_typ STLC_dec_st_sub STLC_dec_ru_pi STLC_dec_ru_pi_eq STLC_dec_ru_nat .
End STLCDecidable.
