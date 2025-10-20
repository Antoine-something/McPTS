From Coq Require Import Morphisms_Relations RelationClasses.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import LogicalRelation SortCases.
Import Domain_Notations.

Lemma rel_exp_sub_cong {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ M M' A σ σ' Γ},
    {{ ⟪ pred_P ⟫ Δ ⊨ M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M[σ] ≈ M'[σ'] : A[σ] }}.
Proof with mautosolve.
  intros * [env_relΔ] [env_relΓ].
  destruct_conjs.
  pose env_relΔ.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eassumption).
  assert (env_relΓ ρ ρ) by (etransitivity; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  handle_per_sort_elem_irrel.
  match goal with
  | _: {{ ⟦ σ ⟧s ρ ↘ ^?ρ0 }},
      _: {{ ⟦ σ ⟧s ρ' ↘ ^?ρ'0 }} |- _ =>
      rename ρ0 into ρσ;
      rename ρ'0 into ρ'σ
  end.
  assert (env_relΔ ρσ ρ'σ) by (etransitivity; [|symmetry; eassumption]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp P).
  handle_per_sort_elem_irrel.
  eexists.
  split...
Qed.

#[export]
Hint Resolve rel_exp_sub_cong : mcpts.


Lemma rel_exp_sub_cong_unsorted {P : PtsSig} {pred_P : PredicativeSig P} : forall {Δ M M' A σ σ' Γ},
    {{ ⟪ pred_P ⟫ Δ ⊨u M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨s σ ≈ σ' : Δ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M[σ] ≈ M'[σ'] : A[σ] }}.
Proof with mautosolve.
  intros * [env_relΔ] [env_relΓ].
  destruct_conjs.
  pose env_relΔ.
  handle_per_ctx_env_irrel.
  eexists; split; [eassumption |].
  (* eexists_rel_exp. *)
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eassumption).
  assert (env_relΓ ρ ρ) by (etransitivity; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  handle_per_typ_elem_irrel.
  match goal with
  | _: {{ ⟦ σ ⟧s ρ ↘ ^?ρ0 }},
      _: {{ ⟦ σ ⟧s ρ' ↘ ^?ρ'0 }} |- _ =>
      rename ρ0 into ρσ;
      rename ρ'0 into ρ'σ
  end.
  assert (env_relΔ ρσ ρ'σ) by (etransitivity; [|symmetry; eassumption]; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  handle_per_typ_elem_irrel.
  
  eexists.
  split; mauto.  
Qed.

#[export]
Hint Resolve rel_exp_sub_cong_unsorted : mcpts.


Lemma rel_exp_sub_id {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M A},
    {{ ⟪ pred_P ⟫ Γ ⊨ M : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M[Id] ≈ M : A }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp P).
  eexists.
  split...
Qed.

#[export]
Hint Resolve rel_exp_sub_id : mcpts.



Lemma rel_exp_sub_id_unsorted {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M A},
    {{ ⟪ pred_P ⟫ Γ ⊨u M : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M[Id] ≈ M : A }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  (* eexists_rel_exp. *)
  eexists; split; [eassumption|].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  eexists.
  split...
Qed.

#[export]
Hint Resolve rel_exp_sub_id_unsorted : mcpts.


Lemma rel_exp_sub_compose {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ τ Γ' σ Γ'' M A},
    {{ ⟪ pred_P ⟫ Γ ⊨s τ : Γ' }} ->
    {{ ⟪ pred_P ⟫ Γ' ⊨s σ : Γ'' }} ->
    {{ ⟪ pred_P ⟫ Γ'' ⊨ M : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M[σ ∘ τ] ≈ M[σ][τ] : A[σ ∘ τ] }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΓ']]] [? [? [env_relΓ'']]] HM.
  destruct_conjs.
  invert_rel_exp HM.
  pose env_relΓ'.
  handle_per_ctx_env_irrel.
  eexists_rel_exp.
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eassumption).
  assert (env_relΓ ρ ρ) by (etransitivity; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  handle_per_sort_elem_irrel.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  handle_per_sort_elem_irrel.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ'').
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp P).
  handle_per_sort_elem_irrel.
  eexists.
  split; econstructor...
Qed.

#[export]
Hint Resolve rel_exp_sub_compose : mcpts.



Lemma rel_exp_sub_compose_unsorted {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ τ Γ' σ Γ'' M A},
    {{ ⟪ pred_P ⟫ Γ ⊨s τ : Γ' }} ->
    {{ ⟪ pred_P ⟫ Γ' ⊨s σ : Γ'' }} ->
    {{ ⟪ pred_P ⟫ Γ'' ⊨u M : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M[σ ∘ τ] ≈ M[σ][τ] : A[σ ∘ τ] }}.
Proof with mautosolve.
  intros * [env_relΓ [? [env_relΓ']]] [? [? [env_relΓ'']]] HM.
  destruct_conjs.
  invert_rel_exp_unsorted HM.
  pose env_relΓ'.
  handle_per_ctx_env_irrel.
  (* eexists_rel_exp. *)
  eexists; split; [eassumption |].
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eassumption).
  assert (env_relΓ ρ ρ) by (etransitivity; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  handle_per_typ_elem_irrel.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ').
  handle_per_typ_elem_irrel.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ'').
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  handle_per_typ_elem_irrel.
  eexists.  
  split; econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_exp_sub_compose_unsorted : mcpts.



Lemma rel_exp_conv {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' A A'},
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ A ≈ A' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A' }}.
Proof with mautosolve. 
  intros.
  invert_rel_exp_unsorted H;
    inversion_clear H0;
    destruct_conjs.
  rename x into env_relΓ.
  rename x0 into env_relΓ0.
  eexists.
  split; [eassumption|].
  assert (env_relΓ <~> env_relΓ0) by (eapply per_ctx_env_right_irrel; mauto).
  apply_relation_equivalence.

  intros.
  assert (equiv_ρ_ρ : env_relΓ ρ ρ) by (etransitivity; [|symmetry]; eassumption).
  assert (equiv_ρ'_ρ : env_relΓ ρ' ρ) by (symmetry; mauto).
  assert (equiv_ρ'_ρ' : env_relΓ ρ' ρ') by (etransitivity; [|symmetry]; eassumption).
    
  assert (exists elem_rel : relation (domain P), rel_typ_unsorted pred_P A ρ A ρ' elem_rel /\ rel_exp M ρ M' ρ' elem_rel) by mauto.
  assert (exists elem_rel : relation (domain P), rel_typ_unsorted pred_P A ρ' A' ρ' elem_rel) by mauto.
  assert (exists elem_rel : relation (domain P), rel_typ_unsorted pred_P A ρ A' ρ elem_rel) by mauto.
  destruct_conjs.

  destruct_by_head (@rel_typ_unsorted P).
  handle_per_typ_elem_irrel.
  exists H4; split; mauto.
  eexists; mauto.  
  symmetry in H11.
  transitivity a1; mauto.
  transitivity a'1; mauto.  
Qed.

#[export]
Hint Resolve rel_exp_conv : mcpts.

Lemma rel_exp_sym {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' A},
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M' ≈ M : A }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp.
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ); destruct_conjs.
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp P).
  handle_per_sort_elem_irrel.
  eexists.
  split; econstructor; mauto.
  symmetry...
Qed.

#[export]
Hint Resolve rel_exp_sym : mcpts.


Lemma rel_exp_sym_unsorted {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' A},
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M' ≈ M : A }}.
Proof with mautosolve.
  intros * [env_relΓ].
  destruct_conjs.
  
  (* eexists_rel_exp. *)
  eexists; split; [eassumption|].
  
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ); destruct_conjs.
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  handle_per_typ_elem_irrel.
  eexists.
  split; econstructor; mauto.

  eapply per_typ_elem_sym; mauto.
Qed.

#[export]
Hint Resolve rel_exp_sym_unsorted : mcpts.



Lemma rel_exp_trans {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M1 M2 M3 A},
    {{ ⟪ pred_P ⟫ Γ ⊨ M1 ≈ M2 : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M2 ≈ M3 : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M1 ≈ M3 : A }}.
Proof with mautosolve.
  intros * [env_relΓ] HM2M3.
  destruct_conjs.
  invert_rel_exp HM2M3.
  eexists_rel_exp.
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eauto).
  assert (env_relΓ ρ' ρ') by (etransitivity; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ); destruct_conjs.
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp P).
  handle_per_sort_elem_irrel.
  eexists.
  split; econstructor; mauto.
  etransitivity...
Qed.

#[export]
Hint Resolve rel_exp_trans : mcpts.


Lemma rel_exp_trans_unsorted {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M1 M2 M3 A},
    {{ ⟪ pred_P ⟫ Γ ⊨u M1 ≈ M2 : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M2 ≈ M3 : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M1 ≈ M3 : A }}.
Proof with mautosolve.
  intros * [env_relΓ] HM2M3.
  destruct_conjs.
  invert_rel_exp_unsorted HM2M3.

  (* eexists_rel_exp. *)
  eexists; split; [eassumption |].
  
  intros.
  assert (env_relΓ ρ' ρ) by (symmetry; eauto).
  assert (env_relΓ ρ' ρ') by (etransitivity; eauto).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ); destruct_conjs.
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  handle_per_typ_elem_irrel.
  eexists.
  split; econstructor; mauto.
  eapply per_typ_elem_trans; mauto.
Qed.

#[export]
Hint Resolve rel_exp_trans_unsorted : mcpts.



#[export]
Instance rel_exp_PER {P : PtsSig} {pred_P : PredicativeSig P} {Γ A} : PER (rel_exp_under_ctx pred_P Γ A).
Proof.
  split; mauto.
Qed.

#[export]
Instance rel_exp_unsorted_PER {P : PtsSig} {pred_P : PredicativeSig P} {Γ A} : PER (rel_exp_under_ctx_unsorted pred_P Γ A).
Proof.
  split; mauto.
Qed.


Lemma presup_rel_exp {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' A},
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ ⊨ Γ }} /\ {{ ⟪ pred_P ⟫ Γ ⊨ M : A }} /\ {{ ⟪ pred_P ⟫ Γ ⊨ M' : A }} /\ {{ ⟪ pred_P ⟫ Γ ⊨ A }}.
Proof.
  intros *.
  assert (Hpart : {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : A }} -> {{ ⟪ pred_P ⟫ Γ ⊨ M : A }} /\ {{ ⟪ pred_P ⟫ Γ ⊨ M' : A }})
    by (split; unfold valid_exp_under_ctx; etransitivity; [|symmetry|symmetry|]; eassumption).
  intros Hrel; repeat split;
    try solve [intuition]; clear Hpart;
    destruct Hrel as [env_relΓ];
    destruct_conjs.
  - eexists; eassumption.
  - destruct_by_head (@valid_exp_under_ctx P).
    destruct_conjs.
    eexists_rel_exp_of_typ.    
    intros.
    (on_all_hyp: destruct_rel_by_assumption env_relΓ).
    eapply rel_typ_unsorted_implies_rel_exp; eauto.
    eapply rel_typ_implies_rel_typ_unsorted; mauto.
Qed.


Lemma presup_rel_exp_unsorted {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' A},
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A }} ->
    {{ ⟪ pred_P ⟫ ⊨ Γ }} /\ {{ ⟪ pred_P ⟫ Γ ⊨u M : A }} /\ {{ ⟪ pred_P ⟫ Γ ⊨u M' : A }} /\ {{ ⟪ pred_P ⟫ Γ ⊨ A }}.
Proof.
  intros *.
  assert (Hpart : {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A }} -> {{ ⟪ pred_P ⟫ Γ ⊨u M : A }} /\ {{ ⟪ pred_P ⟫ Γ ⊨u M' : A }}) by (split; unfold valid_exp_under_ctx_unsorted; etransitivity; [|symmetry|symmetry|]; eassumption).
  intros Hrel; repeat split;
    try solve [intuition]; clear Hpart;
    destruct Hrel as [env_relΓ];
    destruct_conjs.
  - eexists; eassumption.
  - destruct_by_head (@valid_exp_under_ctx_unsorted P).
    destruct_conjs.
    eexists_rel_exp_of_typ.
    intros.
    (on_all_hyp: destruct_rel_by_assumption env_relΓ).
    eapply rel_typ_unsorted_implies_rel_exp; eauto.
Qed.

#[export]
Hint Resolve presup_rel_exp_unsorted : mcpts.
(* Lemma rel_exp_eq_subtyp : forall Γ M M' A A', *)
(*     {{ Γ ⊨ M ≈ M' : A }} -> *)
(*     {{ Γ ⊨ A ⊆ A' }} -> *)
(*     {{ Γ ⊨ M ≈ M' : A' }}. *)
(* Proof. *)
(*   intros * [env_relΓ [? [i]]] [? [? [j]]]. *)
(*   pose env_relΓ. *)
(*   handle_per_ctx_env_irrel. *)
(*   eexists_rel_exp_with (max i j). *)
(*   intros. *)
(*   (on_all_hyp: destruct_rel_by_assumption env_relΓ). *)
(*   destruct_by_head rel_typ. *)
(*   destruct_by_head rel_exp. *)
(*   simplify_evals. *)
(*   eexists. *)
(*   split; econstructor; eauto using per_sort_elem_cumu_max_right. *)
(*   handle_per_sort_elem_irrel. *)
(*   eapply per_elem_subtyping_gen with (i := max i j); try eassumption. *)
(*   - eauto using per_subtyp_cumu_right. *)
(*   - eauto using per_sort_elem_cumu_max_right. *)
(*   - symmetry. eauto using per_sort_elem_cumu_max_right. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve rel_exp_eq_subtyp : mcpts. *)
