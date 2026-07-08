From Coq Require Import Orders Relation_Definitions RelationClasses Program.Equality.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature.

Section LFSig.
  Inductive LF_St : Set :=
  | s_typ : LF_St
  | s_knd : LF_St.

  Inductive LF_Ax_typ : LF_St -> LF_St -> Prop :=
  | at_typ_knd : LF_Ax_typ s_typ s_knd.

  Inductive LF_Ax_sub : LF_St -> LF_St -> Prop :=.

  Inductive LF_Ru_pi : LF_St -> LF_St -> LF_St -> Set :=
  | f_simple : LF_Ru_pi s_typ s_typ s_typ
  | f_dep : LF_Ru_pi s_typ s_knd s_knd
  | f_def : LF_Ru_pi s_knd s_knd s_knd.

  Inductive LF_Ru_nat : LF_St -> Set :=.

  Definition LF_Sig : PtsSig :=
    mkPtsSig LF_St LF_Ax_typ LF_Ax_sub LF_Ru_pi LF_Ru_nat.
End LFSig.

Definition P := LF_Sig.

Section LFPredicative.
  Inductive LF_pred_rel : relation P :=
  | pr_typ_knd : LF_pred_rel s_typ s_knd.

  Lemma LF_ord_rel : StrictOrder LF_pred_rel.
  Proof.
    split; inversion_clear 1.
    inversion 1.
  Qed.

  Lemma LF_wf_rel : well_founded LF_pred_rel.
  Proof.
    intros x; induction x;
      econstructor; inversion_clear 1.
    econstructor; inversion_clear 1.
  Qed.

  Lemma LF_ord_ax_typ : forall (s1 s2 : P), Ax_typ P s1 s2 -> LF_pred_rel s1 s2.
  Proof.
    inversion 1; econstructor.
  Qed.

  Lemma LF_ord_ax_sub : forall (s1 s2 : P), Ax_sub P s1 s2 -> LF_pred_rel s1 s2.
  Proof.
    inversion 1.
  Qed.
 
  Lemma LF_ord_ru_pi : forall (s1 s2 s3 : P), Ru_pi P s1 s2 s3 -> (LF_pred_rel s1 s3 \/ s1 = s3) /\ (LF_pred_rel s2 s3 \/ s2 = s3).
  Proof.
    inversion_clear 1; split;
      try solve [right; reflexivity].
    left; econstructor.
  Qed.

  Definition LF_Predicative : PredicativeSig P :=
    mkPredicativeSig P LF_pred_rel LF_ord_rel LF_wf_rel LF_ord_ax_typ LF_ord_ax_sub LF_ord_ru_pi.
End LFPredicative.


Section LFFunctional.
  Lemma LF_Func_ax_typ : forall s1 s2 s2', Ax_typ P s1 s2 -> Ax_typ P s1 s2' -> s2 = s2'.
  Proof.
    inversion_clear 1;
      inversion_clear 1; reflexivity.
  Qed.

  Lemma LF_Func_ru_pi : forall s1 s2 s3 s3', Ru_pi P s1 s2 s3 -> Ru_pi P s1 s2 s3' -> s3 = s3'.
  Proof.
    intros * [] []; reflexivity.
  Qed.

  Lemma LF_Func_ru_nat : forall s s', Ru_nat P s -> Ru_nat P s' -> s = s'.
  Proof.
    inversion_clear 1.
  Qed.

  Definition LF_Functional : FunctionalSig P :=
    mkFunctionalSig P LF_Func_ax_typ LF_Func_ru_pi LF_Func_ru_nat.
End LFFunctional.

Section LFDecidable.
  Lemma LF_dec_st : forall (s s' : P), ({s = s'} + {s <> s'})%type.
  Proof.
    intros [] [];
      only 1,4: (left; reflexivity);
      right; inversion 1.
  Qed.

  Lemma LF_dec_ru_pi: forall (s1 s2 s3 : P) (r : Ru_pi P s1 s2 s3) (r' : Ru_pi P s1 s2 s3),
      ( { r = r'} + {r <> r'} )%type.
  Proof.
    simpl.
    intros s1 s2 s3 [] r';
      dependent destruction r';
      left; reflexivity.
  Qed.

  Lemma LF_dec_st_sub : forall (s s' : P), ({st_subtyp s s'} + {~ st_subtyp s s'})%type.
  Proof.
    intros [] [];
      only 1,4: (left; reflexivity);
      right; inversion_clear 1; inversion H0.    
  Qed.

  Lemma LF_dec_ru_nat : ({s & Ru_nat P s} + {forall s, Ru_nat P s -> False})%type.
  Proof.
    right; inversion 1.
  Qed.
  
  Lemma LF_dec_ax_typ : forall (s : P), ( {s' & Ax_typ P s s'} + {forall s', ~Ax_typ P s s'} )%type.
  Proof.
    intros s; destruct s.
    - left; eexists; econstructor.
    - right; inversion 1.
  Qed.

  Definition LF_Decidable : DecidableSig P :=
    mkDecidableSig LF_Sig LF_dec_st LF_dec_ru_pi LF_dec_st_sub LF_dec_ru_nat LF_dec_ax_typ.
End LFDecidable.
