From Coq Require Import Orders Relation_Definitions RelationClasses.

From Equations Require Import Equations.

Record PtsSig : Type :=
  mkPtsSig {
      St :> Set;
      Ax : St -> St -> Set;
      Ru : St -> St -> St -> Set;
      Ru_nat : St -> Set;
    }.

Record PredicativeSig (P : PtsSig) : Type :=
  mkPredicativeSig {
      pred_rel : relation P;
      pred_irrel : forall {s1 s2 : P} (lt lt' : pred_rel s1 s2), lt = lt';
      ord_rel : StrictOrder pred_rel;
      wf_rel : well_founded pred_rel;
      ord_ax : forall {s1 s2 : P}, Ax P s1 s2 -> pred_rel s1 s2;
      ord_ru : forall {s1 s2 s3 : P}, Ru P s1 s2 s3 -> (pred_rel s1 s3 \/ s1 = s3) /\ (pred_rel s2 s3 \/ s2 = s3);
    }.
Arguments pred_rel {_}.
Arguments pred_irrel {_} _ {_ _}.
Arguments ord_rel {_}.
Arguments wf_rel {_}.
Arguments ord_ax {_} _ {_ _}.
Arguments ord_ru {_} _ {_ _ _}.

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
