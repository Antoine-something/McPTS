From Coq Require Import Morphisms_Relations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import System.
From McPTS.Core.Completeness Require Import LogicalRelation SortCases.
Import Domain_Notations.

(** ** Global context cases *)
Proposition valid_gctx_empty {P} {pred_P : PredicativeSig P} :
  {{ ⟪ pred_P ⟫ ▶ ⋅ }}.
Proof. mauto 2. Qed.

Proposition rel_gctx_empty {P} {pred_P : PredicativeSig P} :
  {{ ⟪ pred_P ⟫ ▶ ⋅ ≈ ⋅ }}.
Proof. mauto 2. Qed.

Proposition rel_gctx_subtyp_empty {P} {pred_P : PredicativeSig P} :
  {{ SubG ⋅ <: ⋅ ∈ per_gctx_subtyp pred_P }}.
Proof. econstructor. Qed.

#[export]
Hint Resolve valid_gctx_empty rel_gctx_empty rel_gctx_subtyp_empty : mcpts.
    
Proposition rel_gctx_extend {P} {pred_P : PredicativeSig P} : forall {Δ Δ' x A A'},
    {{ ⟪ pred_P ⟫ ▶ Δ ≈ Δ' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ ⋅ ⊨ A ≈ A' }} ->
    {{ ⟪ pred_P ⟫ Δ' ▶ ⋅ ⊨ A ≈ A' }} ->
    {{ `#x ∉ Δ }} -> 
    {{ ⟪ pred_P ⟫ ▶ Δ, x:A ≈ Δ', x:A' }}.
Proof.
  intros * ? [env_rel []] [env_rel' []] ?.
  inversion H0; subst.
  inversion H2; subst.
  assert (env_rel d{{{ ⋅ }}} d{{{ ⋅ }}}) as equiv_env_rel by (apply_relation_equivalence; mauto 2).
  assert (env_rel' d{{{ ⋅ }}} d{{{ ⋅ }}}) as equiv_env_rel' by intuition. 
  pose proof (H1 _ _ equiv_env_rel) as [elem_rel].
  pose proof (H3 _ _ equiv_env_rel') as [elem_rel'].
  econstructor; mauto 2; try reflexivity.
Qed.

Proposition valid_gctx_extend {P} {pred_P : PredicativeSig P} : forall {Δ x A},
    {{ ⟪ pred_P ⟫ ▶ Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ ⋅ ⊨ A }} ->
    {{ `#x ∉ Δ }} -> 
    {{ ⟪ pred_P ⟫ ▶ Δ, x:A }}.
Proof.
  intros.
  eapply rel_gctx_extend; mauto 2.
Qed.

Proposition rel_gctx_subtyp_extend {P} {pred_P : PredicativeSig P} : forall {Δ Δ' x A A'},
    {{ SubG Δ <: Δ' ∈ per_gctx_subtyp pred_P }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ ⋅ ⊨ A }} ->
    {{ ⟪ pred_P ⟫ Δ' ▶ ⋅ ⊨ A' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ ⋅ ⊨ A ⊆ A' }} ->
    {{ `#x ∉ Δ }} ->
    {{ SubG Δ, x:A <: Δ', x:A' ∈ per_gctx_subtyp pred_P }}.
Proof.
  intros * ? [env_rel []] [env_rel' []] [env_rel'' []] ?.
  invert_per_ctx_envs.
  apply_relation_equivalence.
  specialize (H1 d{{{ ⋅ }}} d{{{ ⋅ }}} ltac:(auto)) as [elem_rel].
  specialize (H3 d{{{ ⋅ }}} d{{{ ⋅ }}} ltac:(auto)) as [elem_rel'].
  specialize (H5 d{{{ ⋅ }}} d{{{ ⋅ }}} ltac:(auto)) as [R [R' [? []]]].

  destruct_rel_typ_unsorted.
  destruct_by_head (@rel_exp).
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve rel_gctx_extend valid_gctx_extend rel_gctx_subtyp_extend : mcpts.


(** ** Local context cases *)
Proposition valid_ctx_empty {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ},
    {{ ⟪ pred_P ⟫ ▶ Δ }} -> 
    {{ ⟪ pred_P ⟫ Δ ▶ ⋅ }}.
Proof.
  do 2 econstructor; mauto 2.
  apply Equivalence_Reflexive.
Qed.

Lemma rel_ctx_empty {P} {pred_P : PredicativeSig P} : forall {Δ},
  {{ ⟪ pred_P ⟫ ▶ Δ }} -> 
  {{ ⟪ pred_P ⟫ Δ ▶ ⋅ ≈ ⋅ }}.
Proof.
  do 2 econstructor; mauto 2.
  apply Equivalence_Reflexive.
Qed.


#[export]
Hint Resolve valid_ctx_empty rel_ctx_empty : mcpts.


Lemma rel_ctx_extend {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ Γ' A A'},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ≈ Γ' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A ≈ A' }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ, A ≈ Γ', A' }}.
Proof with intuition.
  intros * [] [env_relΓ]%rel_exp_of_typ_unsorted_inversion1.
  pose env_relΓ.
  destruct_conjs.
  handle_per_ctx_env_irrel.
  eexists.
  per_ctx_env_econstructor; eauto.
  - instantiate (1 := fun ρ ρ' (equiv_ρ_ρ' : env_relΓ ρ ρ') m m' =>
                        forall R,
                          rel_typ_unsorted pred_P Δ A ρ A' ρ' R ->
                          R m m').
    intros.
    (on_all_hyp: destruct_rel_by_assumption env_relΓ).
    match_by_head (@per_typ P) ltac:(fun H => destruct H as [elem_relA]).
    econstructor; eauto.
    apply -> per_typ_elem_morphism_iff; eauto.
    split; intros; destruct_by_head (@rel_typ_unsorted P); handle_per_typ_elem_irrel...
    assert (rel_typ_unsorted pred_P Δ A ρ A' ρ' elem_relA) by mauto.
    intuition.
  - apply Equivalence_Reflexive.
Qed.

(* Lemma rel_ctx_extend_het {P} {pred_P : PredicativeSig P} : forall {Γ Δ A A'}, *)
(*     {{ ⟪ pred_P ⟫ ⊨ Γ ≈ Δ }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ ⊨ A }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ ⊨ A' }} -> *)
(*     {{ ⟪ pred_P ⟫ Δ ⊨ A }} -> *)
(*     {{ ⟪ pred_P ⟫ Δ ⊨ A' }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ ⊨ A ≈ A' }} -> *)
(*     {{ ⟪ pred_P ⟫ Δ ⊨ A ≈ A' }} -> *)
(*     {{ ⟪ pred_P ⟫ ⊨ Γ, A ≈ Δ, A' }}. *)
(* Proof. *)
(*   intros * [] [env_relΓ]%rel_exp_of_typ_unsorted_inversion1 []%rel_exp_of_typ_unsorted_inversion1 *)
(*              [env_relΔ]%rel_exp_of_typ_unsorted_inversion1 []%rel_exp_of_typ_unsorted_inversion1 *)
(*              []%rel_exp_of_typ_unsorted_inversion1 []%rel_exp_of_typ_unsorted_inversion1. *)
(*   destruct_conjs. *)
(*   handle_per_ctx_env_irrel. *)
(*   eexists. *)
(*   per_ctx_env_econstructor; eauto. *)
(*   - instantiate (1 := fun ρ ρ' (equiv_ρ_ρ' : x ρ ρ') m m' => *)
(*                         forall R, *)
(*                           rel_typ_unsorted pred_P A ρ A' ρ' R -> *)
(*                           R m m'). *)
(*     intros. *)
(*     (on_all_hyp: destruct_rel_by_assumption x). *)
(*     match_by_head (@per_typ P) ltac:(fun H => destruct H as [elem_relA]). *)
(*     econstructor; eauto. *)
(*     destruct_by_head (@per_typ P). *)
(*     simplify_evals. *)
(*     handle_per_typ_elem_irrel. *)
(*     apply -> per_typ_elem_morphism_iff; [apply H2 | reflexivity | reflexivity |]. *)
(*     split; intros; destruct_by_head (@rel_typ_unsorted P); handle_per_typ_elem_irrel; *)
(*       assert (rel_typ_unsorted pred_P A ρ A' ρ' x1) by mauto; *)
(*       intuition. *)

(*   - apply Equivalence_Reflexive. *)
(* Qed. *)

Lemma valid_ctx_extend {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ A},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ, A }}.
Proof.
  intros.
  eapply rel_ctx_extend; eauto.
  destruct H as [? []].
  eexists. eassumption.
Qed.

#[export]
Hint Resolve rel_ctx_extend valid_ctx_extend : mcpts.

Lemma rel_ctx_sub_empty {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ},
    {{ ⟪ pred_P ⟫ ▶ Δ }} -> 
    {{ SubC ⋅ <: ⋅ ∈ per_ctx_subtyp pred_P Δ }}.
Proof. mauto. Qed.

Lemma rel_ctx_sub_extend {P : PtsSig} {pred_P : PredicativeSig P} : forall Δ Γ Γ' A A',
  {{ SubC Γ <: Γ' ∈ per_ctx_subtyp pred_P Δ }} ->
  {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A }} ->
  {{ ⟪ pred_P ⟫ Δ ▶ Γ' ⊨ A' }} ->
  {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨ A ⊆ A' }} ->
  {{ SubC Γ , A <: Γ' , A' ∈ per_ctx_subtyp pred_P Δ }}.
Proof.
  intros * ? []%valid_ctx_extend []%valid_ctx_extend [env_relΓ].
  pose env_relΓ.
  destruct_conjs.
  
  econstructor; try eassumption.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_exp P).
  simplify_evals.
  eassumption.
Qed.

#[export]
Hint Resolve rel_ctx_sub_empty rel_ctx_sub_extend : mcpts.
