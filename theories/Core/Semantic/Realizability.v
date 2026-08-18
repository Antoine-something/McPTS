From Coq Require Import Lia Morphisms_Relations PeanoNat Relation_Definitions.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Export NbE PER.
Import Domain_Notations.

Lemma per_nat_then_per_top {P} : forall {Δ : gctx P} {n m},
    {{ Dom n ≈ m ∈ per_nat Δ }} ->
    {{ Dom ⇓ ℕ n ≈ ⇓ ℕ m ∈ per_top Δ }}.
Proof with solve [destruct_conjs; eexists; repeat econstructor; eauto].
  induction 1; simpl in *; intros s;
    try specialize (IHper_nat s);
    try specialize (H s)...
Qed.
#[export]
Hint Resolve per_nat_then_per_top : mcpts.

Lemma realize_per_sort_elem_gen {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ s a a' R},
    {{ DF a ≈ a' ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ Dom a ≈ a' ∈ per_top_typ Δ }}
    /\ (forall {c c'}, {{ Dom c ≈ c' ∈ per_bot Δ }} -> {{ Dom ⇑ a c ≈ ⇑ a' c' ∈ R }})
    /\ (forall {b b'}, {{ Dom b ≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top Δ }}).
Proof with (solve [try (try (eexists; split); econstructor); mauto]).
  intros * Hsortelem. simpl in Hsortelem.
  induction Hsortelem using per_sort_elem_ind; repeat split; intros;
    apply_relation_equivalence; mauto.
  - subst; repeat econstructor.
  - subst.
    eexists.
    per_sort_elem_econstructor...
  - subst.
    destruct_by_head (@per_sort P).
    specialize (H1 _ _ _ H).
    destruct_conjs.
    intro i.
    specialize (H0 i) as [? []]...
  - destruct IHHsortelem as [? []].
    intro i.
    assert {{ Dom ⇑! a i ≈ ⇑! a' i ∈ in_rel }} by eauto using var_per_bot.
    destruct_rel_mod_eval.
    specialize (H9 (S i)) as [? []].
    specialize (H2 i) as [? []]...
  - intros c0 c0' equiv_c0_c0'.
    destruct_conjs.
    destruct_rel_mod_eval.
    econstructor; try solve [econstructor; eauto].
    enough ({{ Dom c ⇓ a c0 ≈ c' ⇓ a' c0' ∈ per_bot Δ }}) by eauto.
    intro i.
    specialize (H3 i) as [? []].
    specialize (H5 _ _ equiv_c0_c0' i) as [? []]...
  - destruct_conjs.
    intro i.
    assert {{ Dom ⇑! a i ≈ ⇑! a' i ∈ in_rel }} by eauto using var_per_bot.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    match goal with
    | _: {{ ^?Δ ▶ $| ^?f0 & ⇑! a i |↘ ^_ }},
        _: {{ ^?Δ ▶ $| ^?f0' & ⇑! a' i |↘ ^_ }},
          _: {{ ^?Δ ▶ ⟦ B ⟧ ρ ↦ ⇑! a i ↘ ^?b0 }},
            _: {{ ^?Δ ▶ ⟦ B' ⟧ ρ' ↦ ⇑! a' i ↘ ^?b0' }} |- _ =>
        rename f0 into f;
        rename f0' into f';
        rename b0 into b;
        rename b0' into b'
    end.
    assert {{ Dom ⇓ b fa ≈ ⇓ b' f'a' ∈ per_top Δ }} by eauto.
    specialize (H2 i) as [? []].
    specialize (H10 (S i)) as [? []].
    specialize (H16 (S i)) as [? []]...
  - intro i.
    (on_all_hyp: fun H => destruct (H i) as [? []])...
  - intro i.
    inversion_clear_by_head (@per_ne P).
    (on_all_hyp: fun H => specialize (H i) as [? []])...
Qed.

Corollary per_sort_then_per_top_typ {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ s a a' R},
    {{ DF a ≈ a' ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ Dom a ≈ a' ∈ per_top_typ Δ }}.
Proof.
  intros * ?%realize_per_sort_elem_gen; firstorder.
Qed.

#[export]
Hint Resolve per_sort_then_per_top_typ : mcpts.

Corollary per_bot_then_per_elem {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ s a a' R c c'},
    {{ DF a ≈ a' ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ Dom c ≈ c' ∈ per_bot Δ }} -> {{ Dom ⇑ a c ≈ ⇑ a' c' ∈ R }}.
Proof.
  intros * ?%realize_per_sort_elem_gen; firstorder.
Qed.

(** We cannot add [per_bot_then_per_elem] as a hint
    because we don't know what "R" is (i.e. the pattern becomes higher-order.)
    In fact, Coq complains it cannot add one if we try. *)
Corollary per_elem_then_per_top {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ s a a' R b b'},
    {{ DF a ≈ a' ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ Dom b ≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top Δ }}.
Proof.
  intros * ?%realize_per_sort_elem_gen; firstorder.
Qed.

#[export]
Hint Resolve per_elem_then_per_top : mcpts.


(* Realizability for per_typ_elem *)
Lemma realize_per_typ_elem_gen {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ a a' R},
    {{ DF a ≈ a' ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ Dom a ≈ a' ∈ per_top_typ Δ }}
    /\ (forall {c c'}, {{ Dom c ≈ c' ∈ per_bot Δ }} -> {{ Dom ⇑ a c ≈ ⇑ a' c' ∈ R }})
    /\ (forall {b b'}, {{ Dom b ≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top Δ }}).
Proof with (solve [try (try (eexists; split); econstructor); mauto]).
  intros * Htypelem. simpl in Htypelem.
  induction Htypelem.
  - repeat split.
    + econstructor; mauto.
    + intros.
      apply_relation_equivalence.
      exists (per_ne Δ).
      per_sort_elem_econstructor; mauto.
      reflexivity.
    + intros.
      apply_relation_equivalence.
      unfold per_sort in H0.
      destruct_conjs.
      assert ({{ Dom b ≈ b' ∈ per_top_typ Δ }}) by mauto.
      intros n.
      specialize (H1 n) as [M []].
      econstructor; mauto.
  - eapply realize_per_sort_elem_gen; mauto.
Qed.

Corollary per_typ_elem_then_per_top_typ {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ a a' R},
    {{ DF a ≈ a' ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ Dom a ≈ a' ∈ per_top_typ Δ }}.
Proof.
  intros * ?%realize_per_typ_elem_gen; firstorder.
Qed.

#[export]
Hint Resolve per_typ_elem_then_per_top_typ : mcpts.

Corollary per_bot_then_per_typ_elem {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ a a' R c c'},
    {{ DF a ≈ a' ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ Dom c ≈ c' ∈ per_bot Δ }} -> {{ Dom ⇑ a c ≈ ⇑ a' c' ∈ R }}.
Proof.
  intros * ?%realize_per_typ_elem_gen; firstorder.
Qed.

(** We cannot add [per_bot_then_per_elem] as a hint
    because we don't know what "R" is (i.e. the pattern becomes higher-order.)
    In fact, Coq complains it cannot add one if we try. *)
Corollary per_typ_elem_then_per_top {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ a a' R b b'},
    {{ DF a ≈ a' ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ Dom b ≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top Δ }}.
Proof.
  intros * ?%realize_per_typ_elem_gen; firstorder.
Qed.

#[export]
Hint Resolve per_typ_elem_then_per_top : mcpts.

Lemma per_ctx_then_per_env_initial_env {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ Γ' env_rel},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P Δ ↘ env_rel }} ->
    exists ρ ρ', initial_env Δ Γ ρ /\ initial_env Δ Γ' ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_rel }}.
Proof.
  induction 1.
  - do 2 eexists; intuition.
  - destruct_conjs.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    do 2 eexists; repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    econstructor; mauto.
    eapply per_bot_then_per_typ_elem; eauto.
    erewrite per_ctx_respects_length; mauto.
    eexists; eauto.
Qed.

Lemma var_per_elem {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ a b s R} n,
    {{ DF a ≈ b ∈ per_sort_elem pred_P Δ s ↘ R }} ->
    {{ Dom ⇑! a n ≈ ⇑! b n ∈ R }}.
Proof.
  intros.
  eapply per_bot_then_per_elem; mauto.
Qed.

Lemma var_per_typ_elem {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ a b R} n,
    {{ DF a ≈ b ∈ per_typ_elem pred_P Δ ↘ R }} ->
    {{ Dom ⇑! a n ≈ ⇑! b n ∈ R }}.
Proof.
  intros.
  eapply per_bot_then_per_typ_elem; mauto.
Qed.
