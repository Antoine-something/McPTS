From Stdlib Require Import Relation_Definitions RelationClasses.
From McPTS.PtsSignature Require Import Signatures.

From Equations Require Import Equations.

Record PredicativeSig (P : PtsSig) : Type :=
  mkPredicativeSig {
      pred_rel : relation P;
      ord_rel : StrictOrder pred_rel;
      wf_rel : well_founded pred_rel;
      ord_ax_typ : forall {s1 s2 : P}, Ax_typ P s1 s2 -> pred_rel s1 s2;
      ord_ax_sub : forall {s1 s2 : P}, Ax_sub P s1 s2 -> pred_rel s1 s2;
      ord_ru_pi : forall {s1 s2 s3 : P}, Ru_pi P s1 s2 s3 -> (pred_rel s1 s3 \/ s1 = s3) /\ (pred_rel s2 s3 \/ s2 = s3);
    }.
Arguments pred_rel {_}.
Arguments ord_rel {_}.
Arguments wf_rel {_}.
Arguments ord_ax_typ {_} _ {_ _}.
Arguments ord_ru_pi {_} _ {_ _ _}.
Arguments ord_ax_sub {_} _ {_ _}.

Lemma ord_st_subtyp {P} (pred_P : PredicativeSig P) : forall {s1 s2 : P}, st_subtyp s1 s2 -> (pred_rel pred_P s1 s2 \/ s1 = s2).
Proof.
  induction 1.
  - right; reflexivity.
  - assert (pred_rel pred_P s1 s2) by (eapply ord_ax_sub; eauto).
    assert (Transitive (pred_rel pred_P)) by (eapply (ord_rel pred_P)).
    left.
    destruct IHst_subtyp; [transitivity s2 | subst]; eauto.
Qed.

Lemma ord_ax_typ_sub {P} (pred_P : PredicativeSig P) : forall {s1 s2 s3 : P}, Ax_typ P s1 s2 -> st_subtyp s2 s3 -> pred_rel pred_P s1 s3.
Proof.
  intros.
  assert (Transitive (pred_rel pred_P)) by (eapply (ord_rel pred_P)).
  assert (pred_rel pred_P s1 s2) by (eapply ord_ax_typ; eauto).
  assert (pred_rel pred_P s2 s3 \/ s2 = s3) by (eapply ord_st_subtyp; eauto).
  destruct H3.
  - transitivity s2; eauto.
  - subst; eauto.
Qed.

Lemma ord_ru_pi_sub {P} (pred_P : PredicativeSig P) : forall {s1 s2 s3 s3'}, Ru_pi P s1 s2 s3 -> st_subtyp s3 s3' -> (pred_rel pred_P s1 s3' \/ s1 = s3') /\ (pred_rel pred_P s2 s3' \/ s2 = s3').
Proof.
  intros.
  assert (Transitive (pred_rel pred_P)) by (eapply (ord_rel pred_P)).
  eapply (ord_ru_pi pred_P) in H as [].
  eapply (ord_st_subtyp pred_P) in H0.
  split.
  - destruct H; destruct H0.
    + left; transitivity s3; eauto.
    + left; subst; eauto.
    + left; subst; eauto.
    + right; subst; eauto.
  - destruct H2; destruct H0.
    + left; transitivity s3; eauto.
    + left; subst; eauto.
    + left; subst; eauto.
    + right; subst; eauto.
Qed.

Section OrderProperties.
  Context {P : PtsSig} (pred_P : PredicativeSig P).

  Instance pred_rel_StrictOrder : StrictOrder (pred_rel pred_P) := ord_rel pred_P.
  Opaque pred_rel_StrictOrder.

  Instance pred_rel_WellFounded : WellFounded (pred_rel pred_P) := wf_rel pred_P.
  Opaque pred_rel_WellFounded.

  Instance pred_rel_Asymmetric : Asymmetric (pred_rel pred_P).
  Proof using.
    typeclasses eauto.
  Qed.

  Let clos_refl_rel := fun s1 s2 => pred_rel pred_P s1 s2 \/ s1 = s2.

  Instance clos_refl_rel_Reflexive : Reflexive clos_refl_rel.
  Proof using.
    solve [do 2 constructor].
  Qed.

  Instance clos_refl_rel_Transitive : Transitive clos_refl_rel.
  Proof using.
    intros ? * [] []; subst; try solve [do 2 constructor]; constructor; eauto.
    etransitivity; eauto.
  Qed.

  Lemma ord_clos_refl_rel : order P clos_refl_rel.
    constructor.
    - intro. reflexivity.
    - intros ? **.
      etransitivity; eassumption.
    - intros ? * [] Hyx; inversion_clear Hyx; subst; eauto.
      exfalso. eapply pred_rel_Asymmetric; eassumption.
  Qed.
End OrderProperties.
