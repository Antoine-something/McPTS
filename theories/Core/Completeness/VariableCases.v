From Coq Require Import Morphisms_Relations.

From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import LogicalRelation.
From McPTS.Core.Syntactic Require Import SystemOpt.
Import Domain_Notations.

(** ** Cases for global variables *)
Lemma valid_exp_gvar {P} {pred_P : PredicativeSig P} : forall {Δ Γ σ A x},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s σ : ⋅ }} ->
    {{ `#x : A ∈ Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u `#x : A[σ] }}.
Proof.
  intros * [env_relΓ [? [env_rel []]]] HxinΔ.
  eexists_rel_exp.
  assert (rel_sub Δ σ ρ σ ρ' env_rel) as [] by mauto 2.
  split.
  - econstructor.
    econstructor; mauto 2.
Abort.

Lemma valid_glookup {P} {pred_P : PredicativeSig P} : forall {Δ x A},
    {{ GC Δ ≈ Δ ∈ per_gctx pred_P }} ->
    {{ `#x : A ∈ Δ }} ->
    exists elem_rel,
      rel_typ_unsorted pred_P Δ A d{{{ ⋅ }}} A d{{{ ⋅ }}} elem_rel /\ rel_exp Δ {{{ `#x }}} d{{{ ⋅ }}} {{{ `#x }}} d{{{ ⋅ }}} elem_rel.
Proof.
  intros * HΔΔ'.
  gen x A.
  induction HΔΔ'; intros * HxinΔ;
    inversion HxinΔ; subst.

    
(** ** Cases for local variables *)
Lemma valid_lookup {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ Γ x A env_relΓ}
                        (equiv_Γ_Γ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P Δ ↘ env_relΓ }}),
    {{ #x : A ∈ Γ }} ->
    forall ρ ρ' (equiv_p_p' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
    exists elem_rel,
      rel_typ_unsorted pred_P Δ A ρ A ρ' elem_rel /\ rel_exp Δ {{{ #x }}} ρ {{{ #x }}} ρ' elem_rel.
Proof with solve [split; mauto].
  intros * ? HxinΓ.
  assert {{ #x : A ∈ Γ }} as HxinΓ' by mauto.
  remember Γ as Γ' eqn:HΓ'Γ in HxinΓ', equiv_Γ_Γ at 2. clear HΓ'Γ. rename equiv_Γ_Γ into equiv_Γ_Γ'.
  remember A as A' eqn:HAA' in HxinΓ' |- * at 2. clear HAA'.
  gen Γ' A' env_relΓ.

  induction HxinΓ; intros * equiv_Γ_Γ' HxinΓ0; inversion HxinΓ0; subst; clear HxinΓ0; inversion_clear equiv_Γ_Γ'; subst; apply_relation_equivalence.
  - intros ? ? [];
      (on_all_hyp: destruct_rel_by_assumption tail_rel); destruct_conjs.
    simplify_evals.
    eexists.
    split; econstructor; mauto 3.

  - intros ? ? [].
    specialize (IHHxinΓ _ _ _ equiv_Γ_Γ'0 H0 d{{{ ρ0 ↯ }}} d{{{ ρ'0 ↯ }}} equiv_ρ_drop_ρ'_drop).
    destruct_conjs.
    (on_all_hyp: destruct_rel_by_assumption tail_rel); destruct_conjs;
    eexists.

    assert (rel_typ_unsorted pred_P Δ B d{{{ ρ0 ↯ }}} B0 d{{{ ρ'0 ↯ }}} (head_rel d{{{ ρ0 ↯ }}} d{{{ ρ'0 ↯ }}} equiv_ρ_drop_ρ'_drop)) by mauto.
    destruct_by_head (@rel_typ_unsorted P).
    destruct_by_head (@rel_exp P).
    dir_inversion_by_head (@eval_exp P); subst.
    simplify_evals.
    split; econstructor; mauto.
Qed.

Lemma valid_exp_var {P} {pred_P : PredicativeSig P} : forall {Δ Γ x A},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ }} ->
    {{ # x : A ∈ Γ }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u #x : A }}.
Proof.
  intros * [? equiv_Γ] Hx.
  eexists; split; [eassumption|].
  unshelve epose proof (valid_lookup equiv_Γ _); shelve_unifiable; [eassumption |].
  eassumption.
Qed.

#[export]
Hint Resolve valid_exp_var : mcpts.

Lemma rel_exp_var {P} {pred_P : PredicativeSig P} : forall {Δ Γ x A},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ }} ->
    {{ # x : A ∈ Γ }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u #x ≈ #x : A}}.
Proof.
  intros.
  eapply valid_exp_var; mauto.
Qed.

Lemma rel_exp_var_0_sub {P} {pred_P : PredicativeSig P} : forall {Δ Γ M σ Γ' A},
  {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s σ : Γ' }} ->
  {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M : A[σ] }} ->
  {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u #0[σ ,, M] ≈ M : A[σ] }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΓ']]] HM.
  invert_rel_exp_unsorted HM.
  destruct_conjs.
  eexists; split; [eassumption|].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  dir_inversion_by_head (@eval_exp P); subst.
  functional_eval_rewrite_clear.
  eexists.
  split; mauto.
Qed.

#[export]
Hint Resolve rel_exp_var_0_sub : mcpts.

Lemma rel_exp_var_S_sub {P} {pred_P : PredicativeSig P} : forall {Δ Γ M σ Γ' A x B},
  {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨s σ : Γ' }} ->
  {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u M : A[σ] }} ->
  {{ #x : B ∈ Γ' }} ->
  {{ ⟪ pred_P ⟫ Δ ▶ Γ ⊨u #(S x)[σ ,, M] ≈ #x[σ] : B[σ] }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΓ']]] HM HxinΓ.
  invert_rel_exp_unsorted HM.
  destruct_conjs.
  pose proof (valid_lookup ltac:(eassumption) HxinΓ).
  destruct_conjs.
  eexists; split; [eassumption|].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  dir_inversion_by_head (@eval_exp P); subst.
  functional_eval_rewrite_clear.
  eexists.
  split; mauto;
    repeat (econstructor; mauto).
Qed.

#[export]
Hint Resolve rel_exp_var_S_sub : mcpts.

Lemma rel_exp_var_weaken {P} {pred_P : PredicativeSig P} : forall {Δ Γ B x A},
    {{ ⟪ pred_P ⟫ Δ ▶ Γ, B }} ->
    {{ #x : A ∈ Γ }} ->
    {{ ⟪ pred_P ⟫ Δ ▶ Γ, B ⊨u #x[Wk] ≈ #(S x) : A[Wk] }}.
Proof with mautosolve.
  intros * [env_relΓB] HxinΓ.
  invert_per_ctx_envs_unsorted.
  pose proof (valid_lookup ltac:(eassumption) HxinΓ).
  destruct_conjs.
  eexists; split; [eassumption |].
  apply_relation_equivalence.
  intros.
  destruct_by_head (@cons_per_ctx_env P).
  rename tail_rel into env_relΓ.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  dir_inversion_by_head (@eval_exp P); subst.
  eexists.
  split; mauto.
    inversion H2; subst;
    repeat (econstructor; mauto).
Qed.

#[export]
Hint Resolve rel_exp_var_weaken : mcpts.
