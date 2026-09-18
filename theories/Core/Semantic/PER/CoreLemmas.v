From Coq Require Import Equivalence Lia Morphisms Morphisms_Prop Morphisms_Relations PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Import System.
From McPTS.Core.Semantic Require Import PER.Definitions PER.CoreTactics.
Import Domain_Notations.

(** ** Proofs that all the basic relations really are PERs *)
(* We cannot do the cases for per_sort, per_typ, and per_ctx yet, as they require additional lemmas *)

(** For per_bot *)
Lemma per_bot_sym {P} : forall (m : domain_ne P) n,
    {{ Dom m ≈ n ∈ per_bot }} ->
    {{ Dom n ≈ m ∈ per_bot }}.
Proof with solve [eauto].
  intros * H i.
  pose proof H i.
  destruct_conjs...
Qed.

#[export]
Hint Resolve per_bot_sym : mcpts.

Lemma per_bot_trans {P} : forall (m : domain_ne P) n l,
    {{ Dom m ≈ n ∈ per_bot }} ->
    {{ Dom n ≈ l ∈ per_bot }} ->
    {{ Dom m ≈ l ∈ per_bot }}.
Proof with solve [eauto].
  intros * Hmn Hnl i.
  pose proof (Hmn i, Hnl i).
  destruct_conjs.
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_bot_trans : mcpts.

#[export]
Instance per_bot_PER {P} : PER (@per_bot P).
Proof.
  split; eauto using per_bot_sym, per_bot_trans.
Qed.


(** For per_top *)
Lemma per_top_sym {P} : forall (m : domain_nf P) n,
    {{ Dom m ≈ n ∈ per_top }} ->
    {{ Dom n ≈ m ∈ per_top }}.
Proof with solve [eauto].
  intros * H i.
  pose proof H i.
  destruct_conjs...
Qed.

#[export]
Hint Resolve per_top_sym : mcpts.

Lemma per_top_trans {P} : forall (m : domain_nf P) n l,
    {{ Dom m ≈ n ∈ per_top }} ->
    {{ Dom n ≈ l ∈ per_top }} ->
    {{ Dom m ≈ l ∈ per_top }}.
Proof with solve [eauto].
  intros * Hmn Hnl i.
  pose proof (Hmn i, Hnl i).
  destruct_conjs.
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_top_trans : mcpts.

#[export]
Instance per_top_PER {P} : PER (@per_top P).
Proof.
  split; eauto using per_top_sym, per_top_trans.
Qed.

(** For per_top_typ *)
Lemma per_top_typ_sym {P} : forall (m : domain P) n,
    {{ Dom m ≈ n ∈ per_top_typ }} ->
    {{ Dom n ≈ m ∈ per_top_typ }}.
Proof with solve [eauto].
  intros * H i.
  pose proof H i.
  destruct_conjs...
Qed.

#[export]
Hint Resolve per_top_typ_sym : mcpts.

Lemma per_top_typ_trans {P} : forall (m : domain P) n l,
    {{ Dom m ≈ n ∈ per_top_typ }} ->
    {{ Dom n ≈ l ∈ per_top_typ }} ->
    {{ Dom m ≈ l ∈ per_top_typ }}.
Proof with solve [eauto].
  intros * Hmn Hnl i.
  pose proof (Hmn i, Hnl i).
  destruct_conjs.
  functional_read_rewrite_clear...
Qed.

#[export]
Hint Resolve per_top_typ_trans : mcpts.

#[export]
Instance per_top_typ_PER {P} : PER (@per_top_typ P).
Proof.
  split; eauto using per_top_typ_sym, per_top_typ_trans.
Qed.

(** For per_nat *)
Lemma per_nat_sym {P} : forall (m : domain P) n,
    {{ Dom m ≈ n ∈ per_nat }} ->
    {{ Dom n ≈ m ∈ per_nat }}.
Proof with mautosolve.
  induction 1; econstructor...
Qed.

#[export]
Hint Resolve per_nat_sym : mcpts.

Lemma per_nat_trans {P} : forall (m : domain P) n l,
    {{ Dom m ≈ n ∈ per_nat }} ->
    {{ Dom n ≈ l ∈ per_nat }} ->
    {{ Dom m ≈ l ∈ per_nat }}.
Proof with mautosolve.
  intros * H. gen l.
  induction H; inversion_clear 1; econstructor...
Qed.

#[export]
Hint Resolve per_nat_trans : mcpts.

#[export]
Instance per_nat_PER {P} : PER (@per_nat P).
Proof.
  split; eauto using per_nat_sym, per_nat_trans.
Qed.

(** For per_ne *)
Lemma per_ne_sym {P} : forall (m : domain P) n,
    {{ Dom m ≈ n ∈ per_ne }} ->
    {{ Dom n ≈ m ∈ per_ne }}.
Proof with mautosolve.
  intros * [].
  econstructor...
Qed.

#[export]
Hint Resolve per_ne_sym : mcpts.

Lemma per_ne_trans {P} : forall (m : domain P) n l,
    {{ Dom m ≈ n ∈ per_ne }} ->
    {{ Dom n ≈ l ∈ per_ne }} ->
    {{ Dom m ≈ l ∈ per_ne }}.
Proof with mautosolve.
  intros * [].
  inversion_clear 1.
  econstructor...
Qed.

#[export]
Hint Resolve per_ne_trans : mcpts.

#[export]
Instance per_ne_PER {P} : PER (@per_ne P).
Proof.
  split; eauto using per_ne_sym, per_ne_trans.
Qed.


(** ** Some core properties of the basic PERs *)

(** Variables are in the least PER *)
Lemma var_per_bot {P} : forall {n},
    {{ Dom !n ≈ !n ∈ @per_bot P }}.
Proof.
  intros ? ?. repeat econstructor.
Qed.

#[export]
Hint Resolve var_per_bot : mcpts.

(** All related neutrals can be reified to related normals *)
Lemma per_bot_then_per_top {P} : forall (m : domain_ne P) m' a a' b b' c c',
    {{ Dom m ≈ m' ∈ per_bot }} ->
    {{ Dom ⇓ (⇑ a b) ⇑ c m ≈ ⇓ (⇑ a' b') ⇑ c' m' ∈ per_top }}.
Proof.
  intros * H i.
  pose proof H i.
  destruct_conjs.
  eexists; split; constructor; eassumption.
Qed.

#[export]
Hint Resolve per_bot_then_per_top : mcpts.

(** Applying related neutrals to related normals gives a related neutral *)
Lemma domain_app_per {P} : forall (f : domain_ne P) f' a a',
  {{ Dom f ≈ f' ∈ per_bot }} ->
  {{ Dom a ≈ a' ∈ per_top }} ->
  {{ Dom f a ≈ f' a' ∈ per_bot }}.
Proof.
  intros. intros i.
  destruct (H i) as [? []].
  destruct (H0 i) as [? []].
  mauto.
Qed.

    
(** ** Basic rewrite rules *)
(** Rewrite equivalent relations in rel_mod_eval *)
Add Parametric Morphism {P} R0 `(R0_morphism : Proper _ ((@relation_equivalence (domain P)) ==> (@relation_equivalence (domain P))) R0) A ρ A' ρ' : (rel_mod_eval R0 A ρ A' ρ')
    with signature (@relation_equivalence (domain P)) ==> iff as rel_mod_eval_morphism.
Proof.
  split; intros []; econstructor; try eassumption;
    [> eapply R0_morphism; [symmetry + idtac |]; eassumption ..].
Qed.

(** Rewrite equivalent relations in rel_mod_app *)
Add Parametric Morphism {P} f a f' a' : (rel_mod_app f a f' a')
    with signature (@relation_equivalence (domain P)) ==> iff as rel_mod_app_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    apply HRR'; eassumption.
Qed.

(** Rewrite equivalent relations in per_sort_elem_core *)
Add Parametric Morphism {P} {pred_P : PredicativeSig P} s (per_sort_elem_rec : forall s', pred_rel pred_P s' s -> relation (domain P) -> relation (domain P)) : (per_sort_elem_core pred_P s per_sort_elem_rec)
    with signature (@relation_equivalence (domain P)) ==> eq ==> eq ==> iff as per_sort_elem_core_morphism_iff.
Proof with mautosolve 3.
  simpl.
  intros R R' HRR'.

  split; intros Horig; [gen R' | gen R];
    induction Horig;
    eauto;
    try (etransitivity; [symmetry + idtac|]; eassumption);
    intros;
    destruct_rel_mod_eval;
    econstructor; mauto 3.
  1-4: rewrite <- HRR'...
  all: rewrite HRR'...
Qed.

Add Parametric Morphism {P} {pred_P : PredicativeSig P} s per_sort_rec : (per_sort_elem_core pred_P s per_sort_rec)
    with signature (@relation_equivalence (domain P)) ==> (@relation_equivalence (domain P)) as per_sort_elem_core_morphism_relation_equivalence.
Proof with mautosolve.
  intros * H ? ?.
  simpl.
  rewrite H.
  reflexivity.
Qed.

(** Rewrite equivalent relations in per_sort_elem *)
Add Parametric Morphism {P} {pred_P : PredicativeSig P} s : (per_sort_elem pred_P s)
    with signature (@relation_equivalence (domain P)) ==> eq ==> eq ==> iff as per_sort_elem_morphism_iff.
Proof with mautosolve 3.
  simp per_sort_elem.
  intros R R' HRR'.

  split; intros Horig; [gen R' | gen R];
    induction Horig;
    eauto;
    try (etransitivity; [symmetry + idtac|]; eassumption);
    intros;
    destruct_rel_mod_eval;
    econstructor; mauto 3.
  1-4: rewrite <- HRR'...
  all: rewrite HRR'...
Qed.

Add Parametric Morphism {P} {pred_P : PredicativeSig P} s : (per_sort_elem pred_P s)
    with signature (@relation_equivalence (domain P)) ==> (@relation_equivalence (domain P)) as per_sort_elem_morphism_relation_equivalence.
Proof with mautosolve.
  intros * H ? ?.
  simpl.
  rewrite H.
  reflexivity.
Qed.

(** Rewrite equivalent relations in per_typ_elem *)
Add Parametric Morphism {P} {pred_P : PredicativeSig P} : (per_typ_elem pred_P)
    with signature (@relation_equivalence (domain P)) ==> eq ==> eq ==> iff as per_typ_elem_morphism_iff.
Proof with mautosolve 3.
  simp per_sort_elem.
  intros R R' HRR'.

  split; intros Horig; [gen R' | gen R];
    induction Horig;
    eauto;
    try (etransitivity; [symmetry + idtac|]; eassumption);
    intros;
    destruct_rel_mod_eval;
    econstructor; mauto 3.
  1-2: rewrite <- HRR'...
  all: rewrite HRR'...
Qed.

Add Parametric Morphism {P} {pred_P : PredicativeSig P} : (per_typ_elem pred_P)
    with signature (@relation_equivalence (domain P)) ==> (@relation_equivalence (domain P)) as per_sort_typ_morphism_relation_equivalence.
Proof with mautosolve.
  intros * H ? ?.
  simpl.
  rewrite H.
  reflexivity.
Qed.

(** Rewrite equivalent relations in rel_typ_unsorted *)
Add Parametric Morphism {P} {pred_P : PredicativeSig P} A ρ A' ρ' : (rel_typ_unsorted pred_P A ρ A' ρ')
    with signature (@relation_equivalence (domain P)) ==> iff as rel_typ_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    [setoid_rewrite <- HRR' | setoid_rewrite HRR']; eassumption.
Qed.

Add Parametric Morphism {P} {pred_P : PredicativeSig P} A ρ A' ρ' : (rel_typ_unsorted pred_P A ρ A' ρ')
    with signature (@relation_equivalence (domain P)) ==> iff as rel_typ_unsorted_morphism.
Proof.
  intros * HRR'.
  split; intros []; econstructor; try eassumption;
    [setoid_rewrite <- HRR' | setoid_rewrite HRR']; eassumption.
Qed.

(** Rewrite equivalent relations in per_ctx_env *)
Add Parametric Morphism {P : PtsSig} {pred_P : PredicativeSig P} : (per_ctx_env pred_P)
    with signature (@relation_equivalence (env P)) ==> eq ==> eq ==> iff as per_ctx_env_morphism_iff.
Proof with mautosolve.
  intros R R' HRR'.
  split; intro Horig; [gen R' | gen R];
    induction Horig; econstructor;
    apply_relation_equivalence; try reflexivity...
Qed.

Add Parametric Morphism {P : PtsSig} {pred_P : PredicativeSig P} : (per_ctx_env pred_P)
    with signature (@relation_equivalence (env P)) ==> (@relation_equivalence (ctx P)) as per_ctx_env_morphism_relation_equivalence.
Proof.
  intros * HRR' Γ Γ'.
  simpl.
  rewrite HRR'.
  reflexivity.
Qed.
