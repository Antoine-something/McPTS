From Coq Require Import Morphisms_Relations.

From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import LogicalRelation.
From McPTS.Core.Syntactic Require Import SystemOpt.
Import Domain_Notations.

Lemma valid_lookup {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ x A K env_relΓ}
                        (equiv_Γ_Γ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }}),
    {{ #x : A :: K ∈ Γ }} ->
    exists s, 
    forall ρ ρ' (equiv_p_p' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
    exists elem_rel,
      rel_typ pred_P s A ρ A ρ' elem_rel /\ rel_exp {{{ #x }}} ρ {{{ #x }}} ρ' elem_rel.
Proof with solve [split; mauto].
  intros * ? HxinΓ.      
  assert {{ #x : A :: K ∈ Γ }} as HxinΓ' by mauto.
  remember Γ as Δ eqn:HΔΓ in HxinΓ', equiv_Γ_Γ at 2. clear HΔΓ. rename equiv_Γ_Γ into equiv_Γ_Δ.
  remember A as A' eqn:HAA' in HxinΓ' |- * at 2. clear HAA'.
  gen Δ A' env_relΓ.
  induction HxinΓ; intros * equiv_Γ_Δ HxinΓ0; inversion HxinΓ0; subst; clear HxinΓ0; inversion_clear equiv_Γ_Δ; subst;
    [| specialize (IHHxinΓ _ _ _ equiv_Γ_Γ' H0) as [j ?]; destruct_conjs];
    apply_relation_equivalence;
    eexists; intros ? ? [];
    (on_all_hyp: destruct_rel_by_assumption tail_rel); destruct_conjs;
    eexists.
  - idtac...
  - destruct_by_head (@rel_typ P).
    destruct_by_head (@rel_exp P).
    dir_inversion_by_head (@eval_exp P); subst.
    split.
    + econstructor; mauto.
    + econstructor; mauto.
      * inversion H2; subst.
        econstructor; mauto.
        econstructor; mauto.
      * inversion H4; subst.
        econstructor; mauto.
        econstructor; mauto.
Qed.

Lemma valid_exp_var : forall {Γ x A},
    {{ ⊨ Γ }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Γ ⊨ #x : A }}.
Proof.
  intros * [? equiv_Γ_Γ] ?.
  unshelve epose proof (valid_lookup equiv_Γ_Γ _) as []; shelve_unifiable; [eassumption |].
  eexists_rel_exp; eassumption.
Qed.

#[export]
Hint Resolve valid_exp_var : mcpts.

Lemma rel_exp_var_0_sub : forall {Γ M σ Δ A},
  {{ Γ ⊨s σ : Δ }} ->
  {{ Γ ⊨ M : A[σ] }} ->
  {{ Γ ⊨ #0[σ ,, M] ≈ M : A[σ] }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΔ]]] HM.
  invert_rel_exp HM.
  destruct_conjs.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  dir_inversion_by_head eval_exp; subst.
  functional_eval_rewrite_clear.
  eexists.
  split...
Qed.

#[export]
Hint Resolve rel_exp_var_0_sub : mcpts.

Lemma rel_exp_var_S_sub : forall {Γ M σ Δ A x B},
  {{ Γ ⊨s σ : Δ }} ->
  {{ Γ ⊨ M : A[σ] }} ->
  {{ #x : B ∈ Δ }} ->
  {{ Γ ⊨ #(S x)[σ ,, M] ≈ #x[σ] : B[σ] }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΔ]]] HM HxinΓ.
  invert_rel_exp HM.
  destruct_conjs.
  pose proof (valid_lookup ltac:(eassumption) HxinΓ).
  destruct_conjs.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  dir_inversion_by_head eval_exp; subst.
  functional_eval_rewrite_clear.
  eexists.
  split...
Qed.

#[export]
Hint Resolve rel_exp_var_S_sub : mcpts.

Lemma rel_exp_var_weaken : forall {Γ B x A},
    {{ ⊨ Γ, B }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Γ, B ⊨ #x[Wk] ≈ #(S x) : A[Wk] }}.
Proof with mautosolve.
  intros * [env_relΓB] HxinΓ.
  invert_per_ctx_envs.
  pose proof (valid_lookup ltac:(eassumption) HxinΓ).
  destruct_conjs.
  eexists_rel_exp.
  apply_relation_equivalence.
  intros.
  destruct_by_head cons_per_ctx_env.
  rename tail_rel into env_relΓ.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head rel_typ.
  destruct_by_head rel_exp.
  dir_inversion_by_head eval_exp; subst.
  eexists.
  split...
Qed.

#[export]
Hint Resolve rel_exp_var_weaken : mcpts.
