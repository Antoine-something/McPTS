From Coq Require Import Orders Relation_Definitions RelationClasses.
From Coq Require Import Program.Equality.

From Equations Require Import Equations.

Record PtsSig : Type :=
  mkPtsSig {
      St :> Set;
      (** Typing and subtyping axioms *)
      Ax_typ : St -> St -> Prop;
      Ax_sub : St -> St -> Prop;
      (** Rules for type constructors *)
      Ru_pi : St -> St -> St -> Set;
      Ru_nat : St -> Set;
    }.

Inductive st_subtyp {P : PtsSig} : P -> P -> Prop :=
| st_subtyp_refl : forall s, st_subtyp s s
| st_subtyp_trans : forall s1 s2 s3, Ax_sub P s1 s2 -> st_subtyp s2 s3 ->
                                st_subtyp s1 s3.
#[export]
Hint Constructors st_subtyp : mcpts.

#[export]
Instance st_Subtyp_reflexive {P} : Reflexive (@st_subtyp P).
Proof.
  intros x; econstructor.
Qed.

#[export]
Instance st_subtyp_transtive {P} : Transitive (@st_subtyp P).
Proof.
  induction 1; intros; eauto.
  econstructor; eauto.
Qed.

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

Record DecidableSig (P : PtsSig) : Type :=
  mkDecidableSig {
      dec_st : forall (s s' : P), ( {s = s'} + {s <> s'} )%type;
      dec_pi: forall (s1 s2 s3 : P) (r : Ru_pi P s1 s2 s3) (r' : Ru_pi P s1 s2 s3),
        ( { r = r'} + {r <> r'} )%type
    }.
Arguments dec_st {_}.
Arguments dec_pi {_}.

Section DecidableProperties.
  Context {P : PtsSig} (dec_P : DecidableSig P).

  Definition strong_equality : forall (s1 s1' s2 s2' s3 s3' : P) (r : Ru_pi P s1 s2 s3) (r' : Ru_pi P s1' s2' s3'),
      (s1 = s1') /\ (s2 = s2') /\ (s3 = s3') /\ (r ~= r').
    
    
  Lemma strong_decidable_pi : forall (s1 s1' s2 s2' s3 s3' : P) (r : Ru_pi P s1 s2 s3) (r' : Ru_pi P s1' s2' s3').
  


(* Definition FullSig (P : PtsSig) : Type := forall s, exists s', Ax P s s'. *)


(* Section SignatureExtension. *)
(*   Context (P : PtsSig) (pred_P : PredicativeSig P). *)

(*   (** Defining a new signature *) *)
(*   Inductive eSt : Set := *)
(*   | st_P : St P -> eSt *)
(*   | st_ext : nat -> eSt. *)

(*   Inductive eAx : eSt -> eSt -> Prop := *)
(*   | ax_P : forall {s1 s2 : St P}, Ax P s1 s2 -> eAx (st_P s1) (st_P s2) *)
(*   | ax_ext : forall {n : nat}, eAx (st_ext n) (st_ext (S n)) *)
(*   | ax_cross : forall {s : St P}, eAx (st_P s) (st_ext 0). *)

(*   Inductive eRu : eSt -> eSt -> eSt -> Set := *)
(*   | ru_P : forall {s1 s2 s3 : St P}, Ru P s1 s2 s3 -> eRu (st_P s1) (st_P s2) (st_P s3). *)

(*   Inductive eRu_nat : eSt -> Set := *)
(*   | runat_P : forall {s : St P}, Ru_nat P s -> eRu_nat (st_P s). *)

(*   Definition eP : PtsSig := mkPtsSig eSt eAx eRu eRu_nat. *)


(*   (** Proof that the extended signature is still predicative *) *)
(*   Inductive epred_rel : relation eP := *)
(*   | pr_P : forall {s1 s2 : St P}, pred_rel pred_P s1 s2 -> epred_rel (st_P s1) (st_P s2) *)
(*   | pr_ext : forall {i j : nat}, i < j -> epred_rel (st_ext i) (st_ext j) *)
(*   | pr_cross : forall {s : St P} {i : nat}, epred_rel (st_P s) (st_ext i). *)


(*   Lemma eord_rel : StrictOrder epred_rel. *)
(*   Proof using Type. *)
(*     assert (StrictOrder (pred_rel pred_P)) by (eapply ord_rel). *)
(*     destruct H. *)
(*     split. *)
(*     - intros x Hx. *)
(*       inversion_clear Hx. *)
(*       + eapply StrictOrder_Irreflexive; eauto. *)
(*       + unfold lt in H. *)
(*         induction i. *)
(*         * inversion H. *)
(*         * eapply IHi. *)
(*           eapply le_S_n; assumption. *)
(*     - intros x y z Hxy. *)
(*       inversion_clear Hxy; intros Hyz. *)
(*       + inversion_clear Hyz. *)
(*         * assert (pred_rel pred_P s1 s3) by (eapply StrictOrder_Transitive; eauto). *)
(*           econstructor; auto. *)
(*         * econstructor; auto. *)
(*       + inversion_clear Hyz. *)
(*         assert (i < j0) by (etransitivity; eauto). *)
(*         econstructor; auto. *)
(*       + inversion_clear Hyz. *)
(*         econstructor; auto. *)
(*   Qed. *)

(*   Lemma wf_acc_orig : forall (s : P), Acc (pred_rel pred_P) s -> Acc epred_rel (st_P s). *)
(*   Proof using Type. *)
(*     intros. *)
(*     induction H. *)
(*     constructor. *)
(*     intros. *)
(*     assert (exists s' : P, y = (st_P s') /\ pred_rel pred_P s' x). *)
(*     { *)
(*       inversion H1; subst. *)
(*       exists s1; split; auto. *)
(*     } *)
(*     destruct H2 as [s' []]. *)
(*     rewrite H2. *)
(*     apply H0. *)
(*     assumption. *)
(*   Qed. *)

(*   Lemma wf_acc_nat : forall (i : nat), Acc lt i -> Acc epred_rel (st_ext i). *)
(*   Proof using Type. *)
(*     intros. *)
(*     induction H. *)
(*     constructor. *)
(*     intros. *)
(*     inversion H1; subst. *)
(*     - apply H0; auto. *)
(*     - apply wf_acc_orig. *)
(*       apply (wf_rel pred_P). *)
(*   Qed. *)

(*   Lemma wf_acc_lt : forall (i : nat), Acc lt i. *)
(*   Proof using Type. *)
(*     intros i. *)
(*     induction i; *)
(*       constructor; intros. *)
(*     - unfold lt in H. *)
(*       inversion H. *)
(*     - inversion H; auto. *)
(*       destruct IHi; auto. *)
(*   Qed. *)

(*   Lemma epred_rel_wf : well_founded epred_rel. *)
(*   Proof using Type. *)
(*     assert (Hwf : well_founded (pred_rel pred_P)) by (apply wf_rel). *)
(*     intros a. *)
(*     constructor. *)
(*     intros b H. *)
(*     inversion_clear H. *)
(*     - apply wf_acc_orig. *)
(*       apply Hwf. *)
(*     - apply wf_acc_nat. *)
(*       apply wf_acc_lt. *)
(*     - apply wf_acc_orig. *)
(*       apply Hwf. *)
(*   Qed. *)

(*   Lemma eord_ax : forall (s1 s2 : eP), Ax eP s1 s2 -> epred_rel s1 s2. *)
(*   Proof using Type. *)
(*     intros. *)
(*     inversion_clear H; econstructor; auto. *)
(*     eapply ord_ax; assumption. *)
(*   Qed. *)

(*   Lemma eord_ru : forall (s1 s2 s3 : eP), Ru eP s1 s2 s3 -> (epred_rel s1 s3 \/ s1 = s3) /\ (epred_rel s2 s3 \/ s2 = s3). *)
(*   Proof using Type. *)
(*     intros. *)
(*     inversion H; subst. *)
(*     assert (((pred_rel pred_P s0 s5) \/ (s0 = s5)) /\ ((pred_rel pred_P s4 s5) \/ (s4 =s5))) by (apply ord_ru; auto). *)
(*     destruct H1. *)
(*     split. *)
(*     - destruct H1. *)
(*       + left. *)
(*         econstructor; auto. *)
(*       + right. *)
(*         subst; reflexivity. *)
(*     - destruct H2. *)
(*       + left. *)
(*         econstructor; auto. *)
(*       + right. *)
(*         subst; reflexivity. *)
(*   Qed. *)


(*   Definition epred_P : PredicativeSig eP := *)
(*     mkPredicativeSig eP epred_rel eord_rel epred_rel_wf eord_ax eord_ru. *)

(*   (** Proof that the extended signature is full *) *)
(*   Lemma full_eP : FullSig eP. *)
(*   Proof using Type. *)
(*     intros s. *)
(*     destruct s. *)
(*     - exists (st_ext 0). *)
(*       econstructor. *)

(*     - exists (st_ext (S n)). *)
(*       econstructor. *)
(*   Qed. *)
(* End SignatureExtension. *)

(* Arguments st_P {P} s. *)
(* Arguments st_ext {P} i. *)
(* Arguments ax_P {P} {s1} {s2} ax. *)
(* Arguments ax_ext {P} {n}. *)
(* Arguments ax_cross {P} {s}. *)
(* Arguments ru_P {P} {s1} {s2} {s3} ru. *)

(* Arguments pr_P {P} {pred_P} {s1} {s2} pr. *)
(* Arguments pr_ext {P} {pred_P} {i} {j} lt. *)
(* Arguments pr_cross {P} {pred_P} {s} {i}. *)
