From Coq Require Import Lia Morphisms_Relations PeanoNat Relation_Definitions.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Export NbE PER.
Import Domain_Notations.

Lemma realize_per_sort_elem_gen {P : PtsSig} {pred_P : PredicativeSig P} : forall {s a a' R},
    {{ DF a ≈ a' ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ Dom a ≈ a' ∈ per_top_typ }}
    /\ (forall {c c'}, {{ Dom c ≈ c' ∈ per_bot }} -> {{ Dom ⇑ a c ≈ ⇑ a' c' ∈ R }})
    /\ (forall {b b'}, {{ Dom b ≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top }}).
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
    intro s.
    specialize (H0 s) as [? []]...
  - destruct IHHsortelem as [? []].
    intro s.
    assert {{ Dom ⇑! a s ≈ ⇑! a' s ∈ in_rel }} by eauto using var_per_bot.
    destruct_rel_mod_eval.
    specialize (H9 (S s)) as [? []].
    specialize (H2 s) as [? []]...
  - intros c0 c0' equiv_c0_c0'.
    destruct_conjs.
    destruct_rel_mod_eval.
    econstructor; try solve [econstructor; eauto].
    enough ({{ Dom c ⇓ a c0 ≈ c' ⇓ a' c0' ∈ per_bot }}) by eauto.
    intro s.
    specialize (H3 s) as [? []].
    specialize (H5 _ _ equiv_c0_c0' s) as [? []]...
  - destruct_conjs.
    intro s.
    assert {{ Dom ⇑! a s ≈ ⇑! a' s ∈ in_rel }} by eauto using var_per_bot.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    match goal with
    | _: {{ $| ^?f0 & ⇑! a s |↘ ^_ }},
        _: {{ $| ^?f0' & ⇑! a' s |↘ ^_ }},
          _: {{ ⟦ B ⟧ ρ ↦ ⇑! a s ↘ ^?b0 }},
            _: {{ ⟦ B' ⟧ ρ' ↦ ⇑! a' s ↘ ^?b0' }} |- _ =>
        rename f0 into f;
        rename f0' into f';
        rename b0 into b;
        rename b0' into b'
    end.
    assert {{ Dom ⇓ b fa ≈ ⇓ b' f'a' ∈ per_top }} by eauto.
    specialize (H2 s) as [? []].
    specialize (H16 (S s)) as [? []]...
  (* - intros s. *)
  (*   destruct_conjs. *)
  (*   (* assert {{ Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top }} by mauto 3. *) *)
  (*   (* assert {{ Dom ⇓ a m2 ≈ ⇓ a' m2' ∈ per_top }} by mauto 3. *) *)
  (*   (on_all_hyp: fun H => destruct (H s) as [? []])... *)
  (* - intros s. *)
  (*   destruct_conjs. *)
  (*   inversion_clear_by_head per_eq. *)
  (*   + assert {{ Dom ⇓ a n ≈ ⇓ a' n' ∈ per_top }} by mauto 3. *)
  (*     (on_all_hyp: fun H => destruct (H s) as [? []])... *)
  (*   + (on_all_hyp: fun H => destruct (H s) as [? []])... *)
  - intro s.
    (on_all_hyp: fun H => destruct (H s) as [? []])...
  - intro s.
    inversion_clear_by_head (@per_ne P).
    (on_all_hyp: fun H => specialize (H s) as [? []])...
Qed.

Corollary per_sort_then_per_top_typ {P : PtsSig} {pred_P : PredicativeSig P} : forall {s a a' R},
    {{ DF a ≈ a' ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ Dom a ≈ a' ∈ per_top_typ }}.
Proof.
  intros * ?%realize_per_sort_elem_gen; firstorder.
Qed.

#[export]
Hint Resolve per_sort_then_per_top_typ : mcpts.

Corollary per_bot_then_per_elem {P : PtsSig} {pred_P : PredicativeSig P} : forall {s a a' R c c'},
    {{ DF a ≈ a' ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ Dom c ≈ c' ∈ per_bot }} -> {{ Dom ⇑ a c ≈ ⇑ a' c' ∈ R }}.
Proof.
  intros * ?%realize_per_sort_elem_gen; firstorder.
Qed.

(** We cannot add [per_bot_then_per_elem] as a hint
    because we don't know what "R" is (i.e. the pattern becomes higher-order.)
    In fact, Coq complains it cannot add one if we try. *)

Corollary per_elem_then_per_top {P : PtsSig} {pred_P : PredicativeSig P} : forall {s a a' R b b'},
    {{ DF a ≈ a' ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ Dom b ≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top }}.
Proof.
  intros * ?%realize_per_sort_elem_gen; firstorder.
Qed.

#[export]
Hint Resolve per_elem_then_per_top : mcpts.

Lemma per_ctx_then_per_env_initial_env {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ Γ' env_rel},
    {{ EF Γ ≈ Γ' ∈ per_ctx_env pred_P ↘ env_rel }} ->
    exists ρ ρ', initial_env Γ ρ /\ initial_env Γ' ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_rel }}.
Proof.
  induction 1.
  - do 2 eexists; intuition.
  - destruct_conjs.
    (on_all_hyp: destruct_rel_by_assumption tail_rel).
    do 2 eexists; repeat split; only 1-2: econstructor; eauto.
    apply_relation_equivalence.
    eexists.
    econstructor; mauto.
    econstructor; mauto.
    eapply per_bot_then_per_elem; eauto.
    erewrite per_ctx_respects_length; mauto.
    eexists; eauto.
Qed.

Lemma var_per_elem {P : PtsSig} {pred_P : PredicativeSig P} : forall {a b s R} n,
    {{ DF a ≈ b ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ Dom ⇑! a n ≈ ⇑! b n ∈ R }}.
Proof.
  intros.
  eapply per_bot_then_per_elem; mauto.
Qed.



(* Realizability for per_typ_elem *)
Lemma realize_per_typ_elem_gen {P : PtsSig} {pred_P : PredicativeSig P} : forall {a a' R},
    {{ DF a ≈ a' ∈ per_typ_elem pred_P ↘ R }} ->
    {{ Dom a ≈ a' ∈ per_top_typ }}
    /\ (forall {c c'}, {{ Dom c ≈ c' ∈ per_bot }} -> {{ Dom ⇑ a c ≈ ⇑ a' c' ∈ R }})
    /\ (forall {b b'}, {{ Dom b ≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top }}).
Proof with (solve [try (try (eexists; split); econstructor); mauto]).
  intros * Htypelem. simpl in Htypelem.
  induction Htypelem.     
  - repeat split.
    + econstructor; mauto.
    + intros.
      apply_relation_equivalence.
      exists per_ne.     
      per_sort_elem_econstructor; mauto.
      reflexivity.
    + intros.
      apply_relation_equivalence.
      unfold per_sort in H0.
      destruct_conjs.
      assert ({{ Dom b ≈ b' ∈ (@per_top_typ P) }}) by mauto.
      simpl in H1.
      intros n.
      assert (exists C : nf P, {{ Rtyp b in n ↘ C }} /\ {{ Rtyp b' in n ↘ C }}) by mauto.
      destruct_conjs.
      econstructor; mauto.  
  - eapply realize_per_sort_elem_gen; mauto.
Qed.

Corollary per_typ_elem_then_per_top_typ {P : PtsSig} {pred_P : PredicativeSig P} : forall {a a' R},
    {{ DF a ≈ a' ∈ per_typ_elem pred_P ↘ R }} ->
    {{ Dom a ≈ a' ∈ per_top_typ }}.
Proof.
  intros * ?%realize_per_typ_elem_gen; firstorder.
Qed.

#[export]
Hint Resolve per_typ_elem_then_per_top_typ : mcpts.

Corollary per_bot_then_per_typ_elem {P : PtsSig} {pred_P : PredicativeSig P} : forall {a a' R c c'},
    {{ DF a ≈ a' ∈ per_typ_elem pred_P ↘ R }} ->
    {{ Dom c ≈ c' ∈ per_bot }} -> {{ Dom ⇑ a c ≈ ⇑ a' c' ∈ R }}.
Proof.
  intros * ?%realize_per_typ_elem_gen; firstorder.
Qed.

(** We cannot add [per_bot_then_per_elem] as a hint
    because we don't know what "R" is (i.e. the pattern becomes higher-order.)
    In fact, Coq complains it cannot add one if we try. *)

Corollary per_typ_elem_then_per_top {P : PtsSig} {pred_P : PredicativeSig P} : forall {a a' R b b'},
    {{ DF a ≈ a' ∈ per_typ_elem pred_P ↘ R }} ->
    {{ Dom b ≈ b' ∈ R }} -> {{ Dom ⇓ a b ≈ ⇓ a' b' ∈ per_top }}.
Proof.
  intros * ?%realize_per_typ_elem_gen; firstorder.
Qed.

#[export]
Hint Resolve per_typ_elem_then_per_top : mcpts.
