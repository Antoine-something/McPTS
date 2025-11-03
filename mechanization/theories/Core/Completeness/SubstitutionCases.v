From Coq Require Import Morphisms_Relations RelationClasses.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import ContextCases LogicalRelation SortCases.
Import Domain_Notations.

Lemma rel_sub_id {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ},
    {{ ⟪ pred_P ⟫ ⊨ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨s Id ≈ Id : Γ }}.
Proof with mautosolve.
  intros * [].
  eexists_rel_sub...
Qed.

#[export]
Hint Resolve rel_sub_id : mcpts.

Lemma rel_sub_weaken {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ A},
    {{ ⟪ pred_P ⟫ ⊨ Γ, A }} ->
    {{ ⟪ pred_P ⟫ Γ, A ⊨s Wk ≈ Wk : Γ }}.
Proof with mautosolve.
  intros * [env_relΓA].
  invert_per_ctx_envs.
  eexists_rel_sub.
  intros.
  apply_relation_equivalence.
  destruct_by_head (@cons_per_ctx_env P)...
Qed.

#[export]
Hint Resolve rel_sub_weaken : mcpts.

Lemma rel_sub_compose_cong {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ τ τ' Γ' σ σ' Γ''},
    {{ ⟪ pred_P ⟫ Γ ⊨s τ ≈ τ' : Γ' }} ->
    {{ ⟪ pred_P ⟫ Γ' ⊨s σ ≈ σ' : Γ'' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨s σ ∘ τ ≈ σ' ∘ τ' : Γ'' }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΓ']]] [].
  destruct_conjs.
  pose env_relΓ'.
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ')...
Qed.

#[export]
Hint Resolve rel_sub_compose_cong : mcpts.

Lemma rel_sub_extend_cong {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' σ σ' Δ A},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨ A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A[σ] }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨s σ ,, M ≈ σ' ,, M' : Δ, A }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΔ]]] HA [].
  destruct_conjs.
  pose env_relΓ.
  pose env_relΔ.
  assert {{ ⟪ pred_P ⟫ ⊨ Δ, A }} as [] by (eapply rel_ctx_extend; eauto; eexists; mauto).
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  invert_per_ctx_envs.
  handle_per_ctx_env_irrel.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head (@rel_typ_unsorted P).
  invert_rel_typ_body.
  destruct_by_head (@rel_exp P).
  econstructor; mauto.
  econstructor; mauto; [econstructor; mauto | econstructor; mauto|].
  assert (rel_typ_unsorted pred_P A ρ'0 A ρ'σ' (head_rel ρ'0 ρ'σ' H10)) by mauto.
  destruct_by_head (@rel_typ_unsorted P).
  simplify_evals.
  assert (per_typ_elem pred_P elem_rel m m0) by mauto.
  handle_per_typ_elem_irrel.
  simpl.
  eassumption.
Qed.

#[export]
Hint Resolve rel_sub_extend_cong : mcpts.


(* Lemma rel_sub_extend_cong_unsorted {P : PtsSig} {pred_P : PredicativeSig P} : forall {s Γ M M' σ σ' Δ A}, *)
(*     {{ ⟪ pred_P ⟫ Γ ⊨s σ ≈ σ' : Δ }} -> *)
(*     {{ ⟪ pred_P ⟫ Δ ⊨ A }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A[σ] }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ ⊨s σ ,, M ≈ σ' ,, M' : Δ, A::Sort@s }}. *)
(* Proof with mautosolve. *)
(*   intros * [env_relΓ [? [env_relΔ]]] HA []. *)
(*   destruct_conjs. *)
(*   pose env_relΓ. *)
(*   pose env_relΔ. *)
(*   assert {{ ⟪ pred_P ⟫ ⊨ Δ, A::Sort@s }} as [] by (eapply rel_ctx_extend_unsorted; eauto; eexists; mauto). *)
(*   handle_per_ctx_env_irrel. *)
(*   eexists_rel_sub. *)
(*   invert_per_ctx_envs_unsorted. *)
(*   handle_per_ctx_env_irrel. *)
(*   intros. *)
(*   (on_all_hyp: destruct_rel_by_assumption env_relΓ). *)
(*   (on_all_hyp: destruct_rel_by_assumption env_relΔ). *)
(*   destruct_by_head (@rel_typ_unsorted P). *)

(*   simplify_evals. *)
(*   match_by_head (@per_typ_elem P) ltac:(fun H => directed inversion_clear H); subst. *)
(*   clear_dups. *)
(*   clear_refl_eqs. *)
(*   handle_per_typ_elem_irrel. *)
(*   clear_dups. *)
  
(*   destruct_by_head (@rel_exp P). *)
(*   econstructor; mauto. *)
(*   econstructor; mauto; *)
(*     econstructor; mauto; *)
(*     econstructor; mauto. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve rel_sub_extend_cong_unsorted : mcpts. *)


Lemma rel_sub_id_compose_right {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ σ Δ},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨s Id ∘ σ ≈ σ : Δ }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ)...
Qed.

#[export]
Hint Resolve rel_sub_id_compose_right : mcpts.

Lemma rel_sub_id_compose_left {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ σ Δ},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨s σ ∘ Id ≈ σ : Δ }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ)...
Qed.

#[export]
Hint Resolve rel_sub_id_compose_left : mcpts.

Lemma rel_sub_compose_assoc {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ σ Γ' σ' Γ'' σ'' Γ'''},
    {{ ⟪ pred_P ⟫ Γ' ⊨s σ : Γ }} ->
    {{ ⟪ pred_P ⟫ Γ'' ⊨s σ' : Γ' }} ->
    {{ ⟪ pred_P ⟫ Γ''' ⊨s σ'' : Γ'' }} ->
    {{ ⟪ pred_P ⟫ Γ''' ⊨s (σ ∘ σ') ∘ σ'' ≈ σ ∘ (σ' ∘ σ'') : Γ }}.
Proof with mautosolve.
  intros * [env_relΓ'] [env_relΓ'' [? []]] [env_relΓ'''].
  destruct_conjs.
  pose env_relΓ'.
  pose env_relΓ''.
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ''').
  (on_all_hyp: destruct_rel_by_assumption env_relΓ'').
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  econstructor...
Qed.

#[export]
Hint Resolve rel_sub_compose_assoc : mcpts.

Lemma rel_sub_extend_compose {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ τ Γ' M σ Γ'' A},
    {{ ⟪ pred_P ⟫ Γ' ⊨s σ : Γ'' }} ->
    {{ ⟪ pred_P ⟫ Γ'' ⊨ A }} ->
    {{ ⟪ pred_P ⟫ Γ' ⊨u M : A[σ] }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨s τ : Γ' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨s (σ ,, M) ∘ τ ≈ (σ ∘ τ) ,, M[τ] : Γ'', A }}.
Proof with mautosolve.
  intros * [env_relΓ' [? [env_relΓ'']]] HA [] [env_relΓ].
  destruct_conjs.
  pose env_relΓ'.
  pose env_relΓ''.
  handle_per_ctx_env_irrel.
  assert {{ ⟪ pred_P ⟫ ⊨ Γ'', A }} as [] by (eapply rel_ctx_extend; mauto; econstructor; mauto).
  destruct_conjs.
  eexists_rel_sub.
  invert_per_ctx_envs_unsorted.
  handle_per_ctx_env_irrel.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  (on_all_hyp: destruct_rel_by_assumption env_relΓ'').
  assert (rel_typ_unsorted pred_P {{{ A[σ] }}} ρσ {{{ A[σ] }}} ρ'σ' elem_rel) by mauto.
  destruct_by_head (@rel_typ_unsorted P).
  
  simplify_evals.
  match_by_head (@per_typ_elem P) ltac:(fun H => directed inversion_clear H); subst.
  clear_dups.
  clear_refl_eqs.
  handle_per_typ_elem_irrel.
  clear_dups.
  
  destruct_by_head (@rel_exp P).
  econstructor; mauto.

  econstructor; mauto;
    econstructor; mauto;
    econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_sub_extend_compose : mcpts.



(* Lemma rel_sub_extend_compose_unsorted {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ τ Γ' M σ Γ'' A s}, *)
(*     {{ ⟪ pred_P ⟫ Γ' ⊨s σ : Γ'' }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ'' ⊨u A : Sort@s }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ' ⊨u M : A[σ] }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ ⊨s τ : Γ' }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ ⊨s (σ ,, M) ∘ τ ≈ (σ ∘ τ) ,, M[τ] : Γ'', A::Sort@s }}. *)
(* Proof with mautosolve. *)
(*   intros * [env_relΓ' [? [env_relΓ'']]] HA [] [env_relΓ]. *)
(*   destruct_conjs. *)
(*   pose env_relΓ'. *)
(*   pose env_relΓ''. *)
(*   handle_per_ctx_env_irrel. *)
(*   assert {{ ⟪ pred_P ⟫ ⊨ Γ'', A::Sort@s }} as [] by (eapply rel_ctx_extend_unsorted; eauto; eexists; eassumption). *)
(*   destruct_conjs. *)
(*   eexists_rel_sub. *)
(*   invert_per_ctx_envs_unsorted. *)
(*   handle_per_ctx_env_irrel. *)
(*   intros. *)
(*   (on_all_hyp: destruct_rel_by_assumption env_relΓ). *)
(*   (on_all_hyp: destruct_rel_by_assumption env_relΓ'). *)
(*   (on_all_hyp: destruct_rel_by_assumption env_relΓ''). *)
(*   assert (rel_typ_unsorted pred_P A ρσ0 A ρ'σ'0 (head_rel ρσ0 ρ'σ'0 H13)) by mauto. *)
(*   destruct_by_head (@rel_typ_unsorted P). *)

(*   simplify_evals. *)
(*   match_by_head (@per_typ_elem P) ltac:(fun H => directed inversion_clear H); subst. *)
(*   clear_dups. *)
(*   clear_refl_eqs. *)
(*   handle_per_typ_elem_irrel. *)
(*   clear_dups. *)
  
(*   destruct_by_head (@rel_exp P). *)
(*   econstructor; mauto. *)

(*   econstructor; mauto; *)
(*     econstructor; mauto; *)
(*     econstructor; mauto. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve rel_sub_extend_compose_unsorted : mcpts. *)



(* Lemma rel_sub_p_extend {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ' M σ Γ A}, *)
(*     {{ ⟪ pred_P ⟫ Γ' ⊨s σ : Γ }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ' ⊨ M : A[σ] }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ' ⊨s Wk ∘ (σ ,, M) ≈ σ : Γ }}. *)
(* Proof with mautosolve. *)
(*   intros * [env_relΓ'] []. *)
(*   destruct_conjs. *)
(*   pose env_relΓ'. *)
(*   handle_per_ctx_env_irrel. *)
(*   eexists_rel_sub. *)
(*   intros. *)
(*   (on_all_hyp: destruct_rel_by_assumption env_relΓ'). *)
(*   destruct_by_head (@rel_typ P). *)
(*   invert_rel_typ_body. *)
(*   destruct_by_head (@rel_exp P). *)
(*   econstructor... *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve rel_sub_p_extend : mcpts. *)




Lemma rel_sub_p_extend {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ' M σ Γ A},
    {{ ⟪ pred_P ⟫ Γ' ⊨s σ : Γ }} ->
    {{ ⟪ pred_P ⟫ Γ' ⊨u M : A[σ] }} ->
    {{ ⟪ pred_P ⟫ Γ' ⊨s Wk ∘ (σ ,, M) ≈ σ : Γ }}.
Proof with mautosolve.
  intros * [env_relΓ'] [].
  destruct_conjs.
  pose env_relΓ'.
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  destruct_by_head (@rel_typ_unsorted P).

  simplify_evals.
  match_by_head (@per_typ_elem P) ltac:(fun H => directed inversion_clear H); subst.
  clear_dups.
  clear_refl_eqs.
  handle_per_typ_elem_irrel.
  clear_dups.  
  
  destruct_by_head (@rel_exp P).
  econstructor...
Qed.

#[export]
Hint Resolve rel_sub_p_extend : mcpts.



Lemma rel_sub_extend {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ' σ Γ A},
    {{ ⟪ pred_P ⟫ Γ' ⊨s σ : Γ, A }} ->
    {{ ⟪ pred_P ⟫ Γ' ⊨s σ ≈ (Wk ∘ σ) ,, #0[σ] : Γ, A }}.
Proof with mautosolve.
  intros * [env_relΓ' [? [env_relΓA]]].
  destruct_conjs.
  pose env_relΓ'.
  invert_per_ctx_envs_of pred_P env_relΓA.
  rename tail_rel into env_relΓ.
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  inversion_by_head (@cons_per_ctx_env P); subst.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  do 3 (econstructor; mauto).
Qed.

#[export]
Hint Resolve rel_sub_extend : mcpts.

Lemma rel_sub_sym {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ σ σ' Δ},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨s σ' ≈ σ : Δ }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_sub.
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor; mauto; symmetry...
Qed.

#[export]
Hint Resolve rel_sub_sym : mcpts.

Lemma rel_sub_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ σ σ' σ'' Δ},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨s σ' ≈ σ'' : Δ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨s σ ≈ σ'' : Δ }}.
Proof with mautosolve.
  intros * [env_relΓ] [].
  destruct_conjs.
  pose env_relΓ.
  handle_per_ctx_env_irrel.
  eexists_rel_sub.
  intros.
  assert (env_relΓ ρ' ρ') by (etransitivity; [symmetry |]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  functional_eval_rewrite_clear.
  econstructor; mauto; etransitivity...
Qed.

#[export]
Hint Resolve rel_sub_trans : mcpts.

#[export]
Instance rel_sub_PER {P : PtsSig} {pred_P : PredicativeSig P} {Γ A} : PER (rel_sub_under_ctx pred_P Γ A).
Proof.
  split; mauto.
Qed.

Lemma rel_sub_conv {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ σ σ' Δ Δ'},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ ⟪ pred_P ⟫ ⊨ Δ ≈ Δ' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨s σ ≈ σ' : Δ' }}.
Proof with mautosolve.
  intros * [? [? [env_relΔ]]] [].
  destruct_conjs.
  pose env_relΔ.
  handle_per_ctx_env_irrel.
  assert {{ EF Δ' ≈ Δ' ∈ per_ctx_env pred_P ↘ env_relΔ }} by (etransitivity; [symmetry |]; eassumption).
  eexists_rel_sub...
Qed.

#[export]
Hint Resolve rel_sub_conv : mcpts.

Lemma presup_rel_sub {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ σ σ' Δ},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ ⟪ pred_P ⟫ ⊨ Γ }} /\ {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} /\ {{ ⟪ pred_P ⟫ Γ ⊨s σ' : Δ }} /\ {{ ⟪ pred_P ⟫ ⊨ Δ }}.
Proof with mautosolve.
  intros * [].
  destruct_conjs.
  repeat split; try solve [eexists; eauto];
    unfold valid_sub_under_ctx;
    etransitivity; only 2,3: symmetry;
    econstructor...
Qed.
