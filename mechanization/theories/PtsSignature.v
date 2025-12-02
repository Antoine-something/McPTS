From Coq Require Import Orders Relation_Definitions RelationClasses.

From Equations Require Import Equations.

Record PtsSig : Type :=
  mkPtsSig {
      St :> Set;
      Ax : St -> St -> Set;
      Ru : St -> St -> St -> Set;
    }.

Record PredicativeSig (P : PtsSig) : Type :=
  mkPredicativeSig {
      pred_rel : relation P;
      (* pred_irrel : forall {s1 s2 : P} (lt lt' : pred_rel s1 s2), lt = lt'; *)
      ord_rel : StrictOrder pred_rel;
      wf_rel : well_founded pred_rel;
      ord_ax : forall {s1 s2 : P}, Ax P s1 s2 -> pred_rel s1 s2;
      ord_ru : forall {s1 s2 s3 : P}, Ru P s1 s2 s3 -> (pred_rel s1 s3 \/ s1 = s3) /\ (pred_rel s2 s3 \/ s2 = s3);
    }.
Arguments pred_rel {_}.
(* Arguments pred_irrel {_} _ {_ _}. *)
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


Section SignatureExtension.
  Context (P : PtsSig) (pred_P : PredicativeSig P).

  (* Defining a new signature *)
  Inductive eSt : Set :=
  | st_P : St P -> eSt
  | st_ext : nat -> eSt.

  Inductive eAx : eSt -> eSt -> Set :=
  | ax_P : forall {s1 s2 : St P}, Ax P s1 s2 -> eAx (st_P s1) (st_P s2)
  | ax_ext : forall {n : nat}, eAx (st_ext n) (st_ext (S n))
  | ax_cross : forall {s : St P}, eAx (st_P s) (st_ext 0).

  Inductive eRu : eSt -> eSt -> eSt -> Set :=
  | ru_P : forall {s1 s2 s3 : St P}, Ru P s1 s2 s3 -> eRu (st_P s1) (st_P s2) (st_P s3).

  Definition eP : PtsSig := mkPtsSig eSt eAx eRu.


  (* Proof that the extended signature is still predicative *)
  Inductive epred_rel : relation eP :=
  | pr_P : forall {s1 s2 : St P}, pred_rel pred_P s1 s2 -> epred_rel (st_P s1) (st_P s2)
  | pr_ext : forall {i j : nat}, i < j -> epred_rel (st_ext i) (st_ext j)
  | pr_cross : forall {s : St P} {i : nat}, epred_rel (st_P s) (st_ext i).
    
  
  Lemma eord_rel : StrictOrder epred_rel.
  Proof using Type.
    assert (StrictOrder (pred_rel pred_P)) by (eapply ord_rel).
    destruct H.
    split.
    - intros x Hx.
      inversion_clear Hx.
      + eapply StrictOrder_Irreflexive; eauto.
      + unfold lt in H.
        induction i.
        * inversion H.
        * eapply IHi.
          eapply le_S_n; assumption.
    - intros x y z Hxy.
      inversion_clear Hxy; intros Hyz.
      + inversion_clear Hyz.
        * assert (pred_rel pred_P s1 s3) by (eapply StrictOrder_Transitive; eauto).
          econstructor; auto.
        * econstructor; auto.
      + inversion_clear Hyz.
        assert (i < j0) by (etransitivity; eauto).
        econstructor; auto.
      + inversion_clear Hyz.
        econstructor; auto.
  Qed.

  Lemma epred_rel_wf : well_founded epred_rel.
  Proof.
    (* Don't understand how to prove this *)
  Admitted.
  
  Lemma eord_ax : forall (s1 s2 : eP), Ax eP s1 s2 -> epred_rel s1 s2.
  Proof using Type.
    intros.
    inversion_clear H; econstructor; auto.
    eapply ord_ax; assumption.
  Qed.

  Lemma eord_ru : forall (s1 s2 s3 : eP), Ru eP s1 s2 s3 -> (epred_rel s1 s3 \/ s1 = s3) /\ (epred_rel s2 s3 \/ s2 = s3).
  Proof using Type.
    intros.
    inversion H; subst.
    assert (((pred_rel pred_P s0 s5) \/ (s0 = s5)) /\ ((pred_rel pred_P s4 s5) \/ (s4 =s5))) by (apply ord_ru; auto).
    destruct H1.
    split.
    - destruct H1.
      + left.
        econstructor; auto.
      + right.
        subst; reflexivity.
    - destruct H2.
      + left.
        econstructor; auto.
      + right.
        subst; reflexivity.
  Qed.


  Definition epred_P : PredicativeSig eP :=
    mkPredicativeSig eP epred_rel eord_rel epred_rel_wf eord_ax eord_ru.
End SignatureExtension.
