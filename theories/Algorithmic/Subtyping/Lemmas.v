From McPTS Require Import PtsSignature LibTactics.
From McPTS.Algorithmic.Subtyping Require Import Definitions.
From McPTS.Core Require Import Base Soundness.
From McPTS.Core.Syntactic Require Import SystemOpt.
From McPTS.Core.Completeness.Consequences Require Import Rules.
Import Domain_Notations.

#[local]
Ltac apply_subtyping :=
  repeat match goal with
    | H : {{ ^?Γ ⊢ ^?M : ^?A }},
        H1 : {{ ^?Γ ⊢ ^?A ⊆ ^?B }} |- _ =>
        assert {{ Γ ⊢ M : B }} by mauto; clear H
    end.

Lemma alg_subtyping_nf_sound {P} : forall (A : nf P) B,
    {{ ⊢anf A ⊆ B }} ->
    forall Γ,
      {{ Γ ⊢ A }} ->
      {{ Γ ⊢ B }} ->
      {{ Γ ⊢ A ⊆ B }}.
Proof.
  induction 1; intros; subst; simpl in *; mauto 3.

  on_all_hyp: fun H => apply wf_typ_pi_inversion in H; destruct H as [? ?].
  destruct_all.
  gen_presups.
  pose proof (wf_typ_exp _ _ _ H2).
  pose proof (wf_typ_exp _ _ _ H3).
  epose proof (IHalg_subtyping_nf _ H4 H1).
  mauto 3.
Qed.

Lemma alg_subtyping_nf_trans {P} : forall (A0 : nf P) A1 A2,
    {{ ⊢anf A0 ⊆ A1 }} ->
    {{ ⊢anf A1 ⊆ A2 }} ->
    {{ ⊢anf A0 ⊆ A2 }}.
Proof.
  intros * H1; gen A2.
  induction H1; subst; intros ? H2;
    dependent destruction H2; mauto 3.

  eapply asnf_sort.
  induction H; mauto 3.
Qed.

Lemma alg_subtyping_nf_refl {P} : forall (A : nf P),
    {{ ⊢anf A ⊆ A }}.
Proof.
  induction A;
    try solve [constructor; simpl; trivial].
  assert (st_subtyp s s) by mauto 3.
  mauto 2.
Qed.

#[local]
Hint Resolve alg_subtyping_nf_trans alg_subtyping_nf_refl : mcpts.

Lemma alg_subtyping_trans {P} : forall (Γ : ctx P) A0 A1 A2,
    {{ Γ ⊢a A0 ⊆ A1 }} ->
    {{ Γ ⊢a A1 ⊆ A2 }} ->
    {{ Γ ⊢a A0 ⊆ A2 }}.
Proof.
  intros. progressive_inversion.
  functional_nbe_rewrite_clear.
  mauto 3.
Qed.

#[local]
  Hint Resolve alg_subtyping_trans : mcpts.

#[local]
Ltac progressive_invert_once H n :=
  let T := type of H in
  lazymatch T with
  | __mark__ _ _ => fail
  | forall _, _ => fail
  | _ => idtac
  end;
  lazymatch type of T with
  | Prop => idtac
  | Type => idtac
  end;
  directed inversion H;
  simplify_eqs;
  clear_refl_eqs;
  clear_dups;
  try mark_with H n.

#[global]
Ltac progressive_inversion :=
  clear_dups;
  repeat match goal with
    | H : _ |- _ =>
        progressive_invert_once H 1000
    end;
  unmark_all_with 1000.


Lemma alg_subtyping_complete {P} (pred_P : PredicativeSig P): forall (Γ : ctx P) A B,
    {{ Γ ⊢ A ⊆ B }} ->
    {{ Γ ⊢a A ⊆ B }}.
Proof.
  induction 1; mauto.
  - apply (@completeness_typ_unsorted P pred_P) in H as [W [? ?]].
    econstructor; mauto.
  - assert {{ Γ ⊢ Sort@s1 ⊆ Sort@s2 }} by mauto 2.
    gen_presups.
    on_all_hyp: fun H => apply (@soundness_ty P pred_P) in H.
    destruct_all.
    econstructor; mauto 2.
    progressive_inversion.
    mauto.
  - assert {{ ⊢ Γ , A@s1 ≈ Γ , A'@s1 }} by mauto.
    eapply (@ctxeq_nbe_eq P pred_P) in H5; [ |eassumption].
    match goal with
    | H : _ |- _ => apply (@completeness P pred_P) in H
    end.
    assert {{ Γ ⊢ Π r A B : Sort@s3 }} as ?%(@soundness P pred_P) by mauto.
    assert {{ Γ ⊢ Π r A' B' : Sort@s3 }} as ?%(@soundness P pred_P) by mauto.
    destruct_all.
    econstructor; mauto 2.

    progressive_invert IHwf_subtyp.
    dir_inversion_clear_by_head @nbe.
    dir_inversion_clear_by_head @nbe_ty.
    dir_inversion_by_head @initial_env; subst.
    functional_initial_env_rewrite_clear.
    invert_rel_typ_body.
    dir_inversion_clear_by_head @read_nf.
    match_by_head @read_typ ltac:(fun H => progressive_invert H).
    functional_eval_rewrite_clear.
    functional_read_rewrite_clear.
    eapply asnf_pi; mauto 3.
Qed.

Lemma alg_subtyping_sound {P} (pred_P : PredicativeSig P): forall (Γ : ctx P) A B,
    {{ Γ ⊢a A ⊆ B }} ->
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ A ⊆ B }}.
Proof.
  intros. destruct H.
  on_all_hyp: fun H => apply (@soundness_ty P pred_P) in H.
  destruct_all.
  functional_nbe_rewrite_clear.
  gen_presups.
  assert {{ Γ ⊢ A' ⊆ B' }} by mauto 3 using alg_subtyping_nf_sound.
  transitivity A'; [mauto |].
  transitivity B'; [eassumption |].
  mauto.
Qed.
