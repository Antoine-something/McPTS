From Coq Require Import Morphisms_Relations.

From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import LogicalRelation.
From McPTS.Core.Syntactic Require Import SystemOpt.
Import Domain_Notations.

Lemma valid_lookup {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ x A env_relΓ s}
                        (equiv_Γ_Γ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }}),
    {{ #x : A@s ∈ Γ }} -> 
    forall ρ ρ' (equiv_p_p' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
    exists elem_rel,
      rel_typ_unsorted pred_P A ρ A ρ' elem_rel /\ rel_exp {{{ #x }}} ρ {{{ #x }}} ρ' elem_rel.
Proof with solve [split; mauto].
  intros * ? HxinΓ.      
  assert {{ #x : A@s ∈ Γ }} as HxinΓ' by mauto.
  remember Γ as Δ eqn:HΔΓ in HxinΓ', equiv_Γ_Γ at 2. clear HΔΓ. rename equiv_Γ_Γ into equiv_Γ_Δ.
  remember A as A' eqn:HAA' in HxinΓ' |- * at 2. clear HAA'.
  gen Δ A' env_relΓ.

  induction HxinΓ; intros * equiv_Γ_Δ HxinΓ0; inversion HxinΓ0; subst; clear HxinΓ0; inversion_clear equiv_Γ_Δ; subst; apply_relation_equivalence.
  - intros ? ? [];
      (on_all_hyp: destruct_rel_by_assumption tail_rel); destruct_conjs.
    simplify_evals.    
    eexists.
    split; econstructor; mauto 3.

  - intros ? ? [].
    specialize (IHHxinΓ _ _ _ equiv_Γ_Γ' H0 d{{{ ρ0 ↯ }}} d{{{ ρ'0 ↯ }}} equiv_ρ_drop_ρ'_drop).
    destruct_conjs.
    (on_all_hyp: destruct_rel_by_assumption tail_rel); destruct_conjs;
    eexists.
    
    assert (rel_typ_unsorted pred_P B d{{{ ρ0 ↯ }}} B0 d{{{ ρ'0 ↯ }}} (head_rel d{{{ ρ0 ↯ }}} d{{{ ρ'0 ↯ }}} equiv_ρ_drop_ρ'_drop)) by mauto.
    destruct_by_head (@rel_typ_unsorted P).
    destruct_by_head (@rel_exp P).
    dir_inversion_by_head (@eval_exp P); subst.
    simplify_evals.
    split; econstructor; mauto.
Qed.

(* Lemma valid_exp_var {P} {pred_P : PredicativeSig P} : forall {Γ x A}, *)
(*     {{ ⟪ pred_P ⟫ ⊨ Γ }} -> *)
(*     {{ #x : A ∈ Γ }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ ⊨ #x : A }}. *)
(* Proof. *)
(*   intros * [? equiv_Γ_Γ] ?. *)
(*   unshelve epose proof (valid_lookup equiv_Γ_Γ _); shelve_unifiable; [eassumption |]. *)
(*   eexists_rel_exp_unsorted. *)
  
(*   eexists_rel_exp; eassumption. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve valid_exp_var : mcpts. *)

Lemma valid_exp_var {P} {pred_P : PredicativeSig P} : forall {Γ x A s},
    {{ ⟪ pred_P ⟫ ⊨ Γ }} ->
    {{ # x : A@s ∈ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u #x : A }}.
Proof.
  intros * [? equiv_Γ] Hx.
  eexists; split; [eassumption|].
  unshelve epose proof (valid_lookup equiv_Γ _); shelve_unifiable; [eassumption |].
  eassumption.
Qed.

#[export]
Hint Resolve valid_exp_var : mcpts.

Lemma rel_exp_var {P} {pred_P : PredicativeSig P} : forall {Γ x A s},
    {{ ⟪ pred_P ⟫ ⊨ Γ }} ->
    {{ # x : A@s ∈ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u #x ≈ #x : A}}.
Proof.
  intros.
  eapply valid_exp_var; mauto.
Qed.

(* Lemma valid_exp_var_unsorted {P} {pred_P : PredicativeSig P} : forall {Γ x A}, *)
(*     {{ ⟪ pred_P ⟫⊨ Γ }} -> *)
(*     {{ #x : A ∈ Γ }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ ⊨u #x : A }}. *)
(* Proof. *)
(*   intros. *)
(*   assert ({{ ⟪ pred_P ⟫ Γ ⊨u #x : A }}) by mauto. *)
(*   inversion_clear H1. *)
(*   destruct_conjs. *)
(*   econstructor; split; mauto. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve valid_exp_var_unsorted : mcpts. *)



(* Lemma rel_exp_var_0_sub {P} {pred_P : PredicativeSig P} : forall {Γ M σ Δ A}, *)
(*   {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} -> *)
(*   {{ ⟪ pred_P ⟫ Γ ⊨ M : A[σ] }} -> *)
(*   {{ ⟪ pred_P ⟫ Γ ⊨ #0[σ ,, M] ≈ M : A[σ] }}. *)
(* Proof with mautosolve. *)
(*   intros * [env_relΓ [? [env_relΔ]]] HM. *)
(*   invert_rel_exp HM. *)
(*   destruct_conjs. *)
(*   eexists_rel_exp. *)
(*   intros. *)
(*   (on_all_hyp: destruct_rel_by_assumption env_relΓ). *)
(*   destruct_by_head (@rel_typ P). *)
(*   destruct_by_head (@rel_exp P). *)
(*   dir_inversion_by_head (@eval_exp P); subst. *)
(*   functional_eval_rewrite_clear. *)
(*   eexists. *)
(*   split; mauto. *)
(*   repeat (econstructor; mauto). *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve rel_exp_var_0_sub : mcpts. *)



Lemma rel_exp_var_0_sub {P} {pred_P : PredicativeSig P} : forall {Γ M σ Δ A},
  {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
  {{ ⟪ pred_P ⟫ Γ ⊨u M : A[σ] }} ->
  {{ ⟪ pred_P ⟫ Γ ⊨u #0[σ ,, M] ≈ M : A[σ] }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΔ]]] HM.
  invert_rel_exp_unsorted HM.
  destruct_conjs.

  (* eexists_rel_exp. *)
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



(* Lemma rel_exp_var_S_sub {P} {pred_P : PredicativeSig P} : forall {Γ M σ Δ A x B K}, *)
(*   {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} -> *)
(*   {{ ⟪ pred_P ⟫ Γ ⊨ M : A[σ] }} -> *)
(*   {{ #x : B ∈ Δ }} -> *)
(*   {{ ⟪ pred_P ⟫ Γ ⊨ #(S x)[σ ,, M] ≈ #x[σ] : B[σ] }}. *)
(* Proof with mautosolve. *)
(*   intros * [env_relΓ [? [env_relΔ]]] HM HxinΓ. *)
(*   invert_rel_exp HM. *)
(*   destruct_conjs. *)
(*   pose proof (valid_lookup ltac:(eassumption) HxinΓ). *)
(*   destruct_conjs. *)
(*   eexists_rel_exp. *)
(*   intros. *)
(*   (on_all_hyp: destruct_rel_by_assumption env_relΓ). *)
(*   (on_all_hyp: destruct_rel_by_assumption env_relΔ). *)
(*   destruct_by_head (@rel_typ P). *)
(*   destruct_by_head (@rel_exp P). *)
(*   dir_inversion_by_head (@eval_exp P); subst. *)
(*   functional_eval_rewrite_clear. *)
(*   eexists. *)
(*   split; mauto. *)
(*   repeat (econstructor; mauto). *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve rel_exp_var_S_sub : mcpts. *)



Lemma rel_exp_var_S_sub {P} {pred_P : PredicativeSig P} : forall {Γ M σ Δ A x B s},
  {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
  {{ ⟪ pred_P ⟫ Γ ⊨u M : A[σ] }} ->
  {{ #x : B@s ∈ Δ }} ->
  {{ ⟪ pred_P ⟫ Γ ⊨u #(S x)[σ ,, M] ≈ #x[σ] : B[σ] }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΔ]]] HM HxinΓ.
  invert_rel_exp_unsorted HM.
  destruct_conjs.
  pose proof (valid_lookup ltac:(eassumption) HxinΓ).
  destruct_conjs.

  (* eexists_rel_exp. *)
  eexists; split; [eassumption|].
  
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp P).
  dir_inversion_by_head (@eval_exp P); subst.
  functional_eval_rewrite_clear.
  eexists.
  split; mauto;
    repeat (econstructor; mauto).
Qed.

#[export]
Hint Resolve rel_exp_var_S_sub : mcpts.



(* Lemma rel_exp_var_weaken {P} {pred_P : PredicativeSig P} : forall {Γ B x A KA KB}, *)
(*     {{ ⟪ pred_P ⟫ ⊨ Γ, B }} -> *)
(*     {{ #x : A ∈ Γ }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ, B ⊨ #x[Wk] ≈ #(S x) : A[Wk] }}. *)
(* Proof with mautosolve. *)
(*   intros * [env_relΓB] HxinΓ. *)
(*   invert_per_ctx_envs. *)
(*   pose proof (valid_lookup ltac:(eassumption) HxinΓ). *)
(*   destruct_conjs. *)
(*   eexists_rel_exp. *)
(*   apply_relation_equivalence. *)
(*   intros. *)
(*   destruct_by_head (@cons_per_ctx_env P). *)
(*   rename tail_rel into env_relΓ. *)
(*   (on_all_hyp: destruct_rel_by_assumption env_relΓ). *)
(*   destruct_by_head (@rel_typ P). *)
(*   destruct_by_head (@rel_exp P). *)
(*   dir_inversion_by_head (@eval_exp P); subst. *)
(*   eexists. *)
(*   split; mauto. *)
(*   inversion H3; subst. *)
(*   repeat (econstructor; mauto).   *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve rel_exp_var_weaken : mcpts. *)



Lemma rel_exp_var_weaken {P} {pred_P : PredicativeSig P} : forall {Γ B x A s s'},
    {{ ⟪ pred_P ⟫ ⊨ Γ, B@s }} ->
    {{ #x : A@s' ∈ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ, B@s ⊨u #x[Wk] ≈ #(S x) : A[Wk] }}.
Proof with mautosolve.
  intros * [env_relΓB] HxinΓ.
  invert_per_ctx_envs_unsorted.
  pose proof (valid_lookup ltac:(eassumption) HxinΓ).
  destruct_conjs.

  (* eexists_rel_exp. *)
  eexists; split; [eassumption |].
    
  apply_relation_equivalence.
  intros.
  destruct_by_head (@cons_per_ctx_env P).
  rename tail_rel into env_relΓ.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ P).
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
