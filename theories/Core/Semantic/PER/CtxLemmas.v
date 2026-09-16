From Coq Require Import Equivalence Lia Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import System.
From McPTS.Core.Semantic Require Import PER.Definitions PER.CoreTactics PER.CoreLemmas PER.SortLemmas PER.TypeLemmas PER.SubtypingLemmas.
Import Domain_Notations.


(** ** Lemmas for per_gctx *)

(** Equivalent global contexts have the same fresh variables *)
Lemma per_gctx_preserves_fresh {P} {pred_P : PredicativeSig P} : forall Δ Δ' x,
    {{ GC Δ ≈ Δ' ∈ per_gctx pred_P }} ->
    {{ `#x ∉ Δ }} ->
    {{ `#x ∉ Δ' }}.
Proof.
  induction 1; mauto 2.
  inversion_clear 1.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve per_gctx_preserves_fresh : mcpts. 

(** per_gctx really is a PER *)
(* The current formulation must be wrong because transitivity does (appear to) not hold *)
Lemma per_gctx_sym {P} {pred_P : PredicativeSig P} : forall Δ Δ',
    {{ GC Δ ≈ Δ' ∈ per_gctx pred_P }} ->
    {{ GC Δ' ≈ Δ ∈ per_gctx pred_P }}.
Proof.
  induction 1; mauto 2.
  destruct_rel_typ_unsorted.
  symmetry in H2.
  symmetry in H5.
  econstructor; mauto 2;
    econstructor; mauto 2.
Qed.


(* Lemma per_gctx_trans {P} {pred_P : PredicativeSig P} : forall Δ Δ', *)
(*     {{ GC Δ ≈ Δ' ∈ per_gctx pred_P }} -> *)
(*     forall Δ'', *)
(*       {{ GC Δ' ≈ Δ'' ∈ per_gctx pred_P }} -> *)
(*       {{ GC Δ ≈ Δ'' ∈ per_gctx pred_P }}. *)
(* Proof. *)
(*   intros * HΔΔ'. *)
(*   induction HΔΔ'; intros * HΔ'Δ''; *)
(*     dependent destruction HΔ'Δ''; *)
(*     mauto 2. *)

(*   destruct_rel_typ_unsorted. *)
(*   simplify_evals. *)
(*   econstructor; mauto 3. *)
(*   - econstructor; mauto 3. *)
(*     etransitivity; mauto 2. *)
(*     admit. *)
(*   - transitivity a'; mauto 2. *)
(* Qed. *)

(* #[export] *)
(* Instance per_gctx_PER {P} {pred_P : PredicativeSig P} : PER (per_gctx pred_P).  *)
(* Proof. *)
(*   split. *)
(*   - mauto 3 using per_gctx_sym. *)
(*   - mauto 3 using per_gctx_trans. *)
(* Qed. *)

(** * Lemmas for local contexts *)
(** ** Basic properties *)
(** Global contexts in per_ctx_env are always well-formed *)
Lemma per_ctx_env_implies_per_gctx {P} {pred_P : PredicativeSig P} : forall Δ Γ Γ' R,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ GC Δ ≈ Δ ∈ per_gctx pred_P }}.
Proof.
  induction 1; mauto 2.
Qed.

#[export]
Hint Resolve per_ctx_env_implies_per_gctx : mcpts.

Lemma per_ctx_implies_per_gctx {P} {pred_P : PredicativeSig P} : forall Δ Γ Γ',
    {{ GC Γ ≈ Γ' ∈ per_ctx pred_P Δ }} ->
    {{ GC Δ ≈ Δ ∈ per_gctx pred_P }}.
Proof.
  intros * [].
  mauto 2.
Qed.

#[export]
Hint Resolve per_ctx_implies_per_gctx : mcpts.

Lemma per_ctx_respects_length {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ Γ'},
    {{ GC Γ ≈ Γ' ∈ per_ctx pred_P Δ }} ->
    length Γ = length Γ'.
Proof.
  intros * [? H].
  induction H; simpl; congruence.
Qed.


(** ** Functionality and PER properties *)
(** Main functionality result for per_ctx_env *)
Lemma per_ctx_env_right_irrel {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' Γ'' R R',
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ EF Γ ≈ Γ'' ∈ per_ctx_env pred_P Δ ↘ R' }} ->
    R <~> R'.
Proof with (destruct_rel_typ_unsorted; handle_per_typ_elem_irrel; eexists; intuition).
  intros * Horig; gen Γ'' R'.  
  induction Horig; intros * Hright;
    dependent destruction Hright; subst;
    apply_relation_equivalence; 
   try reflexivity.
  specialize (IHHorig _ _ equiv_Γ_Γ'0).
  intros ρ ρ'.
    split; intros Hcons; dependent destruction Hcons;
    [ assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel0 }} by intuition
    | assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel }} by intuition ];
    assert (rel_typ_unsorted pred_P _ A _ A' _ (head_rel _ _ ltac:(eassumption))) by mauto 3;
    assert (rel_typ_unsorted pred_P _ A _ A'0 _ (head_rel0 _ _ ltac:(eassumption))) by mauto 3;
    inversion_clear_by_head (@rel_typ_unsorted P);
    simplify_evals;
    handle_per_typ_elem_irrel;
    econstructor; mauto 3;
    intuition.
Qed.

(** Symmetry of per_ctx_env *)
Lemma per_ctx_env_sym_main {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' R,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ EF Γ' ≈ Γ ∈ per_ctx_env pred_P Δ ↘ R }} /\
      (forall ρ ρ',
          {{ Dom ρ ≈ ρ' ∈ R }} ->
          {{ Dom ρ' ≈ ρ ∈ R }}).
Proof with solve [intuition].
  simpl.
  induction 1; split; simpl in *; destruct_conjs; try econstructor; intuition;
    pose proof (@relation_equivalence_pointwise (env P)).
  - assert (tail_rel ρ' ρ) by eauto.
    assert (tail_rel ρ ρ) by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    handle_per_typ_elem_irrel.
    econstructor; eauto.
    symmetry...
  - apply_relation_equivalence.
    destruct_by_head (@cons_per_ctx_env P).
    assert (tail_rel d{{{ ρ' ↯ }}} d{{{ ρ ↯ }}}) as equiv_ρ'_drop_ρ_drop by eauto.
    assert (tail_rel d{{{ ρ ↯ }}} d{{{ ρ ↯ }}}) as equiv_ρ_drop_ρ_drop by (etransitivity; eassumption).
    destruct_rel_mod_eval.
    handle_per_typ_elem_irrel.
    eexists; try eassumption.
    eapply H11. (* equivalence   head_rel (ρ' ↯) (ρ ↯) <~> head_rel (ρ ↯) (ρ' ↯) *)
    eapply per_typ_elem_sym_main; mauto.
Qed.

Corollary per_ctx_env_sym {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' R,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ EF Γ' ≈ Γ ∈ per_ctx_env pred_P Δ ↘ R }}.
Proof.
  intros * ?%per_ctx_env_sym_main.
  firstorder.
Qed.

Corollary per_ctx_env_output_sym {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' R ρ ρ',
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ Dom ρ ≈ ρ' ∈ R }} ->
    {{ Dom ρ' ≈ ρ ∈ R }}.
Proof.
  intros * ?%per_ctx_env_sym_main.
  firstorder.
Qed.

(** Other functionality results *)
Corollary per_ctx_env_left_irrel {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' Γ'' R R',
    {{ EF Γ ≈ Γ'' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ EF Γ' ≈ Γ'' ∈ per_ctx_env pred_P Δ ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ?%per_ctx_env_sym ?%per_ctx_env_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Corollary per_ctx_env_cross_irrel {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' Γ'' R R',
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ EF Γ'' ≈ Γ ∈ per_ctx_env pred_P Δ ↘ R' }} ->
    R <~> R'.
Proof.
  intros * ? ?%per_ctx_env_sym.
  eauto using per_ctx_env_right_irrel.
Qed.

Ltac do_per_ctx_env_irrel_assert1 :=
  let tactic_error o1 o2 := fail 3 "per_ctx_env_irrel equality between" o1 "and" o2 "cannot be solved" in
  match goal with
    | H1 : {{ EF ^?Γ ≈ ^_ ∈ per_ctx_env ?pred_P ?Δ ↘ ?R1 }},
        H2 : {{ EF ^?Γ ≈ ^_ ∈ per_ctx_env ?pred_P ?Δ ↘ ?R2 }} |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_right_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : {{ EF ^_ ≈ ^?Δ ∈ per_ctx_env ?pred_P ?Δ ↘ ?R1 }},
        H2 : {{ EF ^_ ≈ ^?Δ ∈ per_ctx_env ?pred_P ?Δ ↘ ?R2 }} |- _ =>
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_left_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    | H1 : {{ DF ^?Γ ≈ ^_ ∈ per_ctx_env ?pred_P ?Δ ↘ ?R1 }},
        H2 : {{ DF ^_ ≈ ^?Γ ∈ per_ctx_env ?pred_P ?Δ ↘ ?R2 }} |- _ =>
        (** Order matters less here as H1 and H2 cannot be exchanged *)
        assert_fails (unify R1 R2);
        match goal with
        | H : R1 <~> R2 |- _ => fail 1
        | H : R2 <~> R1 |- _ => fail 1
        | _ => assert (R1 <~> R2) by (eapply per_ctx_env_cross_irrel; [apply H1 | apply H2]) || tactic_error R1 R2
        end
    end.

Ltac do_per_ctx_env_irrel_assert :=
  repeat do_per_ctx_env_irrel_assert1.

Ltac handle_per_ctx_env_irrel :=
  functional_eval_rewrite_clear;
  do_per_ctx_env_irrel_assert;
  apply_relation_equivalence;
  clear_dups.

(** Transitivity of per_ctx_env *)
Lemma per_ctx_env_trans_main {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ1 Γ2 R,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env pred_P Δ ↘ R }} ->
    (forall Γ3,
        {{ DF Γ2 ≈ Γ3 ∈ per_ctx_env pred_P Δ ↘ R }} ->
        {{ DF Γ1 ≈ Γ3 ∈ per_ctx_env pred_P Δ ↘ R }}) /\
      (forall ρ1 ρ2 ρ3,
          {{ Dom ρ1 ≈ ρ2 ∈ R }} ->
          {{ Dom ρ2 ≈ ρ3 ∈ R }} ->
          {{ Dom ρ1 ≈ ρ3 ∈ R }}).
Proof with solve [eauto using per_typ_trans].
  simpl.
  induction 1; subst;
    [> split;
     [ inversion 1; subst; eauto
     | intros; destruct_conjs; eauto] ..];
    pose proof (@relation_equivalence_pointwise (env P));
    handle_per_ctx_env_irrel;
    try solve [intuition].
  - econstructor; only 4: reflexivity; eauto.
    + apply_relation_equivalence. intuition.
    + intros.
      assert (tail_rel ρ ρ) by intuition.
      assert (tail_rel0 ρ ρ') by intuition.
      destruct_rel_typ_unsorted.
      handle_per_typ_elem_irrel.
      econstructor; mauto; intuition.
      do 3 (etransitivity; mauto).
      symmetry; mauto.
  - destruct_by_head (@cons_per_ctx_env P).
    assert (tail_rel d{{{ ρ ↯ }}} d{{{ ρ' ↯ }}}) by eauto.
    destruct_rel_typ_unsorted.
    handle_per_typ_elem_irrel.
    eexists; [eassumption | eassumption |].
    apply_relation_equivalence.
    eapply per_typ_elem_output_trans; intuition.
Qed.

Corollary per_ctx_env_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ1 Γ2 Γ3 R,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ DF Γ2 ≈ Γ3 ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ DF Γ1 ≈ Γ3 ∈ per_ctx_env pred_P Δ ↘ R }}.
Proof.
  intros * ?% per_ctx_env_trans_main.
  firstorder.
Qed.

Corollary per_ctx_env_output_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ1 Γ2 R ρ1 ρ2 ρ3,
    {{ DF Γ1 ≈ Γ2 ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ Dom ρ1 ≈ ρ2 ∈ R }} ->
    {{ Dom ρ2 ≈ ρ3 ∈ R }} ->
    {{ Dom ρ1 ≈ ρ3 ∈ R }}.
Proof.
  intros * ?% per_ctx_env_trans_main.
  firstorder.
Qed.

(** PER instances for per_ctx_env and its outputs *)
#[export]
Instance per_ctx_PER {P : PtsSig} {pred_P : PredicativeSig P} {Δ R} : PER (per_ctx_env pred_P Δ R).
Proof.
  split.
  - auto using per_ctx_env_sym.
  - eauto using per_ctx_env_trans.
Qed.

#[export]
Instance per_env_PER {P : PtsSig} {pred_P : PredicativeSig P} {Δ R Γ Γ'} (H : per_ctx_env pred_P Δ R Γ Γ') : PER R.
Proof.
  split.
  - pose proof (fun ρ ρ' => per_ctx_env_output_sym _ _ _ _ ρ ρ' H); auto.
  - pose proof (fun ρ0 ρ1 ρ2 => per_ctx_env_output_trans _ _ _ _ ρ0 ρ1 ρ2 H); eauto.
Qed.


(** ** Optimized constructors *)
(** Remove the PER argument for context extensions *)
Lemma per_ctx_env_cons' {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ Γ' A A' tail_rel}
                             (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}), relation (domain P))
                             env_rel,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ tail_rel }} ->
    (forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}),
        rel_typ_unsorted pred_P Δ A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
    (env_rel <~> cons_per_ctx_env tail_rel (@head_rel)) ->
    {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env pred_P Δ ↘ env_rel }}.
Proof.
  intros.
  econstructor; eauto.
  typeclasses eauto.
Qed.

#[export]
Hint Resolve per_ctx_env_cons' : mcpts.

Ltac per_ctx_env_econstructor :=
  (repeat intro; hnf; eapply per_ctx_env_cons') + econstructor.


(** ** Inversion principles *)
Lemma per_ctx_env_cons_clean_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ Γ' env_relΓ A A' env_relΓA},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ env_relΓ }} ->
    {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env pred_P Δ ↘ env_relΓA }} ->
    exists (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}), relation (domain P)),
      (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
          rel_typ_unsorted pred_P Δ A ρ A' ρ' (head_rel equiv_ρ_ρ')) /\
        (env_relΓA <~> cons_per_ctx_env env_relΓ (@head_rel)).
Proof with intuition.
  intros * HΓ HΓA.
  inversion HΓA; subst.
  handle_per_ctx_env_irrel.
  eexists.
  split; intros.
  - instantiate (1 := fun ρ ρ' (equiv_ρ_ρ' : env_relΓ ρ ρ') m m' =>
                        forall R,
                          rel_typ_unsorted pred_P Δ A ρ A' ρ' R ->
                          {{ Dom m ≈ m' ∈ R }}).
    assert (tail_rel ρ ρ') by intuition.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    econstructor; eauto.
    apply -> per_typ_elem_morphism_iff; eauto.
    split; intros...
    destruct_by_head (@rel_typ_unsorted P).
    handle_per_typ_elem_irrel...
  - intros ρ ρ'.
    split; intros; destruct_by_head (@cons_per_ctx_env P);
    assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel }} by intuition;
      (on_all_hyp: destruct_rel_by_assumption tail_rel);
      unshelve (eexists; try eassumption); intros...
    destruct_by_head (@rel_typ_unsorted P).
    handle_per_typ_elem_irrel...
Qed.

Ltac invert_per_ctx_env H :=
  (unshelve eapply (per_ctx_env_cons_clean_inversion _) in H; [eassumption | |]; deex_in H; destruct H as [])
  + (inversion H; subst).

Ltac invert_per_ctx_envs := match_by_head per_ctx_env ltac:(fun H => directed invert_per_ctx_env H).

Ltac invert_per_ctx_envs_of pred_P Δ rel := match_by_head (per_ctx_env pred_P Δ rel) ltac:(fun H => directed invert_per_ctx_env H).


(** ** Lemmas for context subtyping *)
(** Global contexts used for context subtyping are well-formed *)
Lemma per_ctx_subtyp_implies_per_gctx {P} {pred_P : PredicativeSig P} : forall Δ Γ Γ',
    {{ SubC Γ <: Γ' ∈ per_ctx_subtyp pred_P Δ }} ->
    {{ GC Δ ≈ Δ ∈ per_gctx pred_P }}.
Proof.
  induction 1; mauto 2.
Qed.

#[export]
Hint Resolve per_ctx_subtyp_implies_per_gctx : mcpts.

(** Context subtyping relates only well-formed contexts *)
Lemma per_ctx_subtyp_to_env {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ',
    {{ SubC Γ <: Γ' ∈ per_ctx_subtyp pred_P Δ }} ->
    exists R R',
      {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P Δ ↘ R }} /\
        {{ EF Γ' ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R' }}.
Proof.
  intros * HΓΓ'.
  assert {{ GC Δ ≈ Δ ∈ per_gctx pred_P }} by mauto 2.
  destruct HΓΓ'; destruct_all.
  - repeat eexists; econstructor; try apply Equivalence_Reflexive; try eassumption.
  - eauto.
Qed.

(** Context subtypes produce subrelations *)
Lemma per_ctx_env_subtyping {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ',
    {{ SubC Γ <: Γ' ∈ per_ctx_subtyp pred_P Δ }} ->
    forall R R' ρ ρ',
      {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P Δ ↘ R }} ->
      {{ EF Γ' ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R' }} ->
      R ρ ρ' ->
      R' ρ ρ'.
Proof.
  induction 1; intros;
    handle_per_ctx_env_irrel;
    invert_per_ctx_envs;
    apply_relation_equivalence;
    trivial.

  inversion H6.
  assert {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel0 }} by intuition.
  eexists; try eassumption.
   
  destruct_rel_typ_unsorted.
  eapply per_elem_subtyping; try eassumption.
  - eauto.
  - saturate_refl.
    mauto.
  - saturate_refl.
    mauto.
Qed.

(** Context subtyping is reflexive with respect to context equality *)
Lemma per_ctx_subtyp_refl1 {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' R,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ SubC Γ <: Γ' ∈ per_ctx_subtyp pred_P Δ }}.
Proof.
  induction 1; mauto.

  assert (exists R, {{ EF Γ , A ≈ Γ' , A' ∈ per_ctx_env pred_P Δ ↘ R }}) by
    (eexists; eapply per_ctx_env_cons'; eassumption).
  destruct_all.
  econstructor; try solve [saturate_refl; mauto 2].
  intros.
  destruct_rel_typ_unsorted.
  simplify_evals.
  mauto.
Qed.

Lemma per_ctx_subtyp_refl2 {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' R,
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ R }} ->
    {{ SubC Γ' <: Γ ∈ per_ctx_subtyp pred_P Δ }}.
Proof.
  intros. symmetry in H. eauto using per_ctx_subtyp_refl1.
Qed.

(** Context subtyping is transitive *)
Lemma per_ctx_subtyp_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ1 Γ2,
    {{ SubC Γ1 <: Γ2 ∈ per_ctx_subtyp pred_P Δ }} ->
    forall Γ3,
      {{ SubC Γ2 <: Γ3 ∈ per_ctx_subtyp pred_P Δ }} ->
      {{ SubC Γ1 <: Γ3 ∈ per_ctx_subtyp pred_P Δ }}.
Proof.
  induction 1; intros;
    dir_inversion_by_head (@per_ctx_subtyp P); subst;
    repeat invert_per_ctx_envs;
    mauto 1; clear_PER.

  handle_per_ctx_env_irrel.
  econstructor; try eassumption.
  - firstorder.
  - intros.
    assert {{ Dom ρ ≈ ρ' ∈ tail_rel0 }}
      by (apply_relation_equivalence; eapply per_ctx_env_subtyping; revgoals; eassumption).
    saturate_refl_for tail_rel.
    destruct_rel_typ_unsorted.
    handle_per_typ_elem_irrel.
    etransitivity; intuition mauto.
  - econstructor; intuition.
    + typeclasses eauto.
    + solve_refl.
  - econstructor; mauto 3.
    + typeclasses eauto.
    + solve_refl.
Qed.

#[export]
Hint Resolve per_ctx_subtyp_trans : mcpts.

#[export]
Instance per_ctx_subtyp_trans_ins {P : PtsSig} {pred_P : PredicativeSig P} {Δ} : Transitive (per_ctx_subtyp pred_P Δ).
Proof.
  eauto using per_ctx_subtyp_trans.
Qed.
