From Coq Require Import Orders Relation_Definitions RelationClasses.
From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core.Syntactic Require Import Syntax System Presup.
From McPTS.Core Require Import Base Completeness Soundness.
Import Domain_Notations.

Section LFSig.
  (** Definition of the PTS signature *)
  Inductive St_lf : Set :=
  | star : St_lf
  | square : St_lf
  .

  Inductive Ax_lf : St_lf -> St_lf -> Prop :=
  | ax_star_square : Ax_lf star square
  .

  Inductive Ru_lf : St_lf -> St_lf -> St_lf -> Set :=
  | r_simple : Ru_lf star star star
  | r_dep : Ru_lf star square square
  .

  Inductive Ru_nat_lf : St_lf -> Set :=
    (** Empty relation to show how we can get ordinary PTSs *)
  .

  Definition Sig_lf : PtsSig :=
    mkPtsSig St_lf Ax_lf Ru_lf Ru_nat_lf
  .


  (** Proof of predicativity *)
  Definition pred_rel : relation (St Sig_lf) := Ax_lf.

  Lemma ord_rel : StrictOrder pred_rel.
  Proof.
    split.
    - intros x Hx.
      inversion_clear Hx.
    - intros x y z.
      do 2 inversion_clear 1.
  Qed.

  Lemma wf_rel : well_founded pred_rel.
  Proof.
    intros a.
    do 2 (econstructor; inversion_clear 1).
  Qed.

  Lemma ord_ax : forall (s1 s2 : St Sig_lf), Ax Sig_lf s1 s2 -> pred_rel s1 s2.
  Proof.
    trivial.
  Qed.

  Lemma ord_ru : forall (s1 s2 s3 : St Sig_lf), Ru Sig_lf s1 s2 s3 -> (pred_rel s1 s3 \/ s1 = s3) /\ (pred_rel s2 s3 \/ s2 = s3).
  Proof.
    inversion_clear 1; split; intuition.
    left; econstructor.
  Qed.

  Definition pred_Sig : PredicativeSig Sig_lf :=
    mkPredicativeSig Sig_lf pred_rel ord_rel wf_rel ord_ax ord_ru.
End LFSig.

(** Instantiations of the main results *)
Definition completeness_stlc : forall {Γ : ctx Sig_lf} {M M' A},
    {{ Γ ⊢ M ≈ M' : A }} ->
    exists W, nbe Γ M A W /\ nbe Γ M' A W :=
  @completeness Sig_lf pred_Sig.

Definition soundness_stlc : forall {Γ : ctx Sig_lf} {M A},
    {{ Γ ⊢ M : A }} ->
    exists W, nbe Γ M A W /\ {{ Γ ⊢ M ≈ W : A }} :=
  @soundness Sig_lf pred_Sig.


(** Proof that we cannot form natural numbers in pure LF *)
Theorem no_nats : forall {Γ : ctx Sig_lf} {M},
    {{ Γ ⊢ M : ℕ }} -> False.
Proof.
  intros.
  gen_presups.
  inversion_clear HAwf.
  eapply wf_nat_inversion in H0.
  destruct_conjs.
  destruct H1.
Qed.
