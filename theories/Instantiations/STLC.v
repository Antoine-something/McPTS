From Coq Require Import Orders Relation_Definitions RelationClasses.
From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core.Syntactic Require Import Syntax System Presup.
From McPTS.Core Require Import Base Completeness Soundness.
Import Domain_Notations.


Section STLCSig.
  (** Definition of the PTS signature *)
  Inductive St_stlc : Set :=
  | star : St_stlc
  | square : St_stlc
  .

  Inductive Ax_stlc : St_stlc -> St_stlc -> Prop :=
  | ax_star_square : Ax_stlc star square
  .

  Inductive Ru_stlc : St_stlc -> St_stlc -> St_stlc -> Set :=
  | r_simple : Ru_stlc star star star
  .

  Inductive Ru_nat_stlc : St_stlc -> Set :=
  | rn_star : Ru_nat_stlc star
  .

  Definition Sig_stlc : PtsSig :=
    mkPtsSig St_stlc Ax_stlc Ru_stlc Ru_nat_stlc
  .


  (** Proof of predicativity *)
  Definition pred_rel : relation (St Sig_stlc) := Ax_stlc.

  Lemma ord_rel : StrictOrder pred_rel.
  Proof.
    split.
    - intros x Hx.
      inversion_clear Hx.
    - intros x y z Hxy Hyz.
      inversion_clear Hxy.
      inversion_clear Hyz.
      econstructor.
  Qed.

  Lemma wf_rel : well_founded pred_rel.
  Proof.
    intros a.
    econstructor.
    intros.
    inversion_clear H.
    econstructor.
    intros.
    inversion_clear H.
  Qed.

  Lemma ord_ax : forall (s1 s2 : St Sig_stlc), Ax Sig_stlc s1 s2 -> pred_rel s1 s2.
  Proof.
    trivial.
  Qed.

  Lemma ord_ru : forall (s1 s2 s3 : St Sig_stlc), Ru Sig_stlc s1 s2 s3 -> (pred_rel s1 s3 \/ s1 = s3) /\ (pred_rel s2 s3 \/ s2 = s3).
  Proof.
    intros.
    inversion_clear H.
    split; right; reflexivity.
  Qed.

  Definition pred_Sig : PredicativeSig Sig_stlc :=
    mkPredicativeSig Sig_stlc pred_rel ord_rel wf_rel ord_ax ord_ru.
End STLCSig.

#[local]
Hint Resolve pred_Sig : mcpts.

Definition exp_stlc := exp Sig_stlc.
Definition sub_stlc := exp Sig_stlc.

Definition wf_exp_stlc := @wf_exp Sig_stlc.

Definition presup_exp_eq_stlc : forall {Γ : ctx Sig_stlc} {M M' A},
    {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ M : A }} /\ {{ Γ ⊢ M' : A }} /\ {{ Γ ⊢ A }}
  := @presup_exp_eq Sig_stlc.

Definition completeness_stlc : forall {Γ : ctx Sig_stlc} {M M' A},
    {{ Γ ⊢ M ≈ M' : A }} ->
    exists W, nbe Γ M A W /\ nbe Γ M' A W :=
  @completeness Sig_stlc pred_Sig.

Definition soundness_stlc : forall {Γ : ctx Sig_stlc} {M A},
    {{ Γ ⊢ M : A }} ->
    exists W, nbe Γ M A W /\ {{ Γ ⊢ M ≈ W : A }} :=
  @soundness Sig_stlc pred_Sig.
