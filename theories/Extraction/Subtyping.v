From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Algorithmic Require Export Subtyping.
From McPTS.Extraction Require Import NbE PseudoMonadic.
From Equations Require Import Equations.
Import Domain_Notations.

#[local]
Ltac subtyping_tac :=
  intros;
  lazymatch goal with
  | |- {{ ⊢anf ^_ ⊆ ^_ }} =>
      subst;
      mauto 4;
      try congruence;
      econstructor; simpl; trivial
  | |- ~ {{ ⊢anf ^_ ⊆ ^_ }} =>
      let H := fresh "H" in
      intro H; dependent destruction H; simpl in *;
      try lia;
      try congruence
  end.


#[tactic="subtyping_tac",derive(equations=no,eliminator=no)]
Equations subtyping_nf_impl {P : PtsSig} (dec_P : DecidableSig P) (A : nf P) B : { {{ ⊢anf A ⊆ B }} } + {~ {{ ⊢anf A ⊆ B }} } :=
| dec_P, n{{{ Sort@s }}}, n{{{ Sort@s' }}} =>
    let*b _ := dec_st_sub dec_P s s' while _ in
    pureb _
| dec_P, (@nf_pi P s1 s2 s3 r A B), (@nf_pi P s1' s2' s3' r' A' B') =>
    let*b _ := dec_st dec_P s1 s1' while _ in
    let*b _ := dec_st dec_P s2 s2' while _ in
    let*b _ := dec_st dec_P s3 s3' while _ in
    let*b _ := strong_dec_pi dec_P s1 s1' s2 s2' s3 s3' r r' while _ in
    let*b _ := nf_eq_dec dec_P A A' while _ in
    let*b _ := subtyping_nf_impl dec_P B B' while _ in
    pureb _
(** Pseudo-monadic syntax for the next catch-all branch
    generates some unsolved obligations, so we directly match on
    [nf_eq_dec A B] here. *)
| dec_P, A, B with nf_eq_dec dec_P A B => {
  | left _ => left _
  | right _ => right _
  }.
Next Obligation.
assert (r = r').
{
  dependent destruction H0; reflexivity.
}
subst.
unfold strong_ru_pi_eq in H.
eapply H.
repeat split; try reflexivity.
Qed.
Next Obligation.
unfold strong_ru_pi_eq in s.
destruct_conjs; subst.
mauto 2.
Qed.
  
(** The definitions of [subtyping_nf_impl] already come with soundness proofs,
    as well as obvious completeness. *)

Theorem subtyping_nf_impl_complete {P} (dec_P : DecidableSig P) : forall (A B : nf P),
    {{ ⊢anf A ⊆ B }} ->
    exists H, subtyping_nf_impl dec_P A B = left H.
Proof.
  intros; dec_complete.
Qed.

Inductive subtyping_order {P} (Γ : ctx P) A B :=
| subtyping_order_run :
  nbe_ty_order Γ A ->
  nbe_ty_order Γ B ->
  subtyping_order Γ A B.
#[local]
Hint Constructors subtyping_order : mcpts.

Lemma subtyping_order_sound {P} : forall (Γ : ctx P) A B,
    {{ Γ ⊢a A ⊆ B }} ->
    subtyping_order Γ A B.
Proof.
  intros * H.
  dependent destruction H.
  mauto using nbe_ty_order_sound.
Qed.

#[local]
Ltac subtyping_impl_tac1 :=
  match goal with
  | H : subtyping_order _ _ _ |- _ => progressive_invert H
  | H : nbe_ty_order _ _ |- _ => progressive_invert H
  end.

#[local]
Ltac subtyping_impl_tac :=
  repeat subtyping_impl_tac1; try econstructor; mauto.

#[tactic="subtyping_impl_tac",derive(equations=no,eliminator=no)]
Equations subtyping_impl {P} (dec_P : DecidableSig P) (Γ : ctx P) A B (H : subtyping_order Γ A B) :
  { {{ Γ ⊢a A ⊆ B }} } + { ~ {{ Γ ⊢a A ⊆ B }} } :=
| dec_P, Γ, A, B, H =>
    let (a, Ha) := nbe_ty_impl Γ A _ in
    let (b, Hb) := nbe_ty_impl Γ B _ in
    let*b _ := subtyping_nf_impl dec_P a b while _ in
    pureb _.
Next Obligation.
  progressive_inversion.
  functional_nbe_rewrite_clear.
  contradiction.
Qed.

(** Similar for [subtyping_impl]. *)

Theorem subtyping_impl_complete' {P} (dec_P : DecidableSig P) : forall (Γ : ctx P) A B,
    {{Γ ⊢a A ⊆ B}} ->
    forall (H : subtyping_order Γ A B),
      exists H', subtyping_impl dec_P Γ A B H = left H'.
Proof.
  intros; dec_complete.
Qed.

#[local]
Hint Resolve subtyping_order_sound subtyping_impl_complete' : mcpts.

Theorem subtyping_impl_complete {P} (dec_P : DecidableSig P) : forall (Γ : ctx P) A B,
    {{ Γ ⊢a A ⊆ B }} ->
    exists H H', subtyping_impl dec_P Γ A B H = left H'.
Proof.
  repeat unshelve mauto.
Qed.
