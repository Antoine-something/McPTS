From Coq Require Import Morphisms_Relations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import LogicalRelation SubstitutionCases TermStructureCases SortCases.
From McPTS.Core.Semantic Require Import Realizability.
Import Domain_Notations.

Lemma rel_exp_of_nat_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M'},
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : ℕ }} ->
    exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}),
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      rel_exp M ρ M' ρ' per_nat.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists.
  eexists; [eassumption |].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ P).
  invert_rel_typ_body.
  apply H3.
Qed.

Lemma rel_exp_unsorted_of_nat_inversion {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M'},
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : ℕ }} ->
    exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}),
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      rel_exp M ρ M' ρ' per_nat.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists.
  eexists; [eassumption |].
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  invert_rel_typ_unsorted_body.
  invert_per_sort_elem H1.
  apply_relation_equivalence.
  apply H2.
Qed.

Lemma rel_exp_of_nat {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' s} {r : Ru_nat P s},
    (exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}),
      forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
        rel_exp M ρ M' ρ' per_nat) ->
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : ℕ }}.
Proof.
  intros * Hru [env_relΓ].
  destruct_conjs.
  eexists. 
  split.
  eassumption.
  intros.
  eexists.
  intros.
  eexists; split; mauto.
  econstructor; mauto.
  per_sort_elem_econstructor; mauto.
  reflexivity.
Qed.

Lemma rel_exp_unsorted_of_nat {P : PtsSig} {pred_P : PredicativeSig P} : forall {Γ M M' s} {r : Ru_nat P s},
    (exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}),
      forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
        rel_exp M ρ M' ρ' per_nat) ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : ℕ }}.
Proof.
  intros * Hru [env_relΓ].
  destruct_conjs.
  eexists. 
  split.
  eassumption.
  intros.
  eexists; split; mauto.
  econstructor; mauto.
  econstructor; mauto.
  per_sort_elem_econstructor; mauto.
  reflexivity.
Qed.


#[export]
Hint Resolve rel_exp_unsorted_of_nat : mcpts.

Ltac eexists_rel_exp_unsorted_of_nat :=
  unshelve eapply (rel_exp_unsorted_of_nat _);
  shelve_unifiable;
  [eassumption| eexists; eexists ];
  [eassumption|];
intros.


Lemma valid_exp_unsorted_nat {P} {pred_P : PredicativeSig P} : forall {Γ s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ ⊨ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u ℕ : Sort@s }}.
Proof.
  intros * Hru [env_relΓ].
  eexists_rel_exp_untyped.
  intros.
  eexists; split; econstructor; mauto.
  econstructor; mauto. eexists; mauto.
  eexists; per_sort_elem_econstructor; mauto.
  reflexivity.
Qed.

#[export]
Hint Resolve valid_exp_unsorted_nat : mcpts.

Lemma rel_exp_unsorted_nat_sub {P} {pred_P : PredicativeSig P}: forall {Γ σ Δ s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u ℕ[σ] ≈ ℕ : Sort@s }}.
Proof.
  intros * Hru Hσ.
  invert_rel_sub Hσ env_relΓ.  
  eexists_rel_exp_of_sort.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor; mauto.
  eexists.
  per_sort_elem_econstructor; mauto.
  reflexivity.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_nat_sub : mcpts.

Lemma valid_exp_unsorted_zero {P} {pred_P : PredicativeSig P} : forall {Γ s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ ⊨ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u zero : ℕ }}.
Proof.
  intros * Hru [env_relΓ].
  apply (@rel_exp_unsorted_of_nat) with (s := s); mauto.
Qed.

#[export]
Hint Resolve valid_exp_unsorted_zero : mcpts.

Lemma rel_exp_unsorted_zero_sub {P} {pred_P : PredicativeSig P} : forall {Γ σ Δ s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u zero[σ] ≈ zero : ℕ }}.
Proof.
  intros * Hru Hσ.
  invert_rel_sub Hσ env_relΓ.    
  eexists_rel_exp_unsorted_of_nat.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_zero_sub : mcpts.

Lemma rel_exp_unsorted_succ_sub {P} {pred_P : PredicativeSig P} : forall {Γ σ Δ M s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ Γ ⊨s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨u M : ℕ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u (succ M)[σ] ≈ succ (M[σ]) : ℕ }}.
Proof.
  intros * Hru Hσ [env_relΔ]%rel_exp_unsorted_of_nat_inversion.
  destruct_all.
  invert_rel_sub Hσ.
  eexists_rel_exp_unsorted_of_nat.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  econstructor; mauto.
Qed.

#[export]
Hint Resolve rel_exp_unsorted_succ_sub : mcpts.

Lemma rel_exp_unsorted_succ_cong {P} {pred_P : PredicativeSig P} : forall {Γ M M' s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : ℕ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u succ M ≈ succ M' : ℕ }}.
Proof.
  intros * Hru [env_relΓ]%rel_exp_unsorted_of_nat_inversion.
  destruct_all.
  eexists_rel_exp_unsorted_of_nat.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  econstructor; mauto.
Qed.

#[export]
  Hint Resolve rel_exp_unsorted_succ_cong : mcpts.


Ltac invert_rel_exp_2 H l :=
  (unshelve (epose proof (rel_exp_clean_inversion _ H); deex); shelve_unifiable; [eassumption |]; clear H)
    + (destruct H as [l [? H]]; deex_in H).



Lemma rel_exp_of_sub_id_zero_inversion  {P} {pred_P : PredicativeSig P} : forall {Γ M M' A} ,
    {{ ⟪ pred_P ⟫ Γ ⊨ M ≈ M' : A[Id,,zero] }} ->
    exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}) s,
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
    exists elem_rel, rel_typ pred_P s A d{{{ ρ ↦ zero }}} A d{{{ ρ' ↦ zero }}} elem_rel /\ rel_exp M ρ M' ρ' elem_rel.
Proof.
  intros * HM.
  invert_rel_exp_2 HM env_relΓ.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ P).
  simplify_evals.
  mauto.
Qed.


Lemma rel_exp_unsorted_of_sub_id_zero_inversion  {P} {pred_P : PredicativeSig P} : forall {Γ M M' A} ,
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A[Id,,zero] }} ->
    exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}),
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
    exists elem_rel, rel_typ_unsorted pred_P A d{{{ ρ ↦ zero }}} A d{{{ ρ' ↦ zero }}} elem_rel /\ rel_exp M ρ M' ρ' elem_rel.
Proof.
  intros * HM.
  invert_rel_exp_unsorted HM env_relΓ.
  eexists_rel_exp_untyped.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  simplify_evals.
  mauto.
Qed.

Lemma rel_exp_unsorted_of_sub_id_zero {P} {pred_P : PredicativeSig P} : forall {Γ M M' A},
    (exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}),
      forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      exists elem_rel, rel_typ_unsorted pred_P A d{{{ ρ ↦ zero }}} A d{{{ ρ' ↦ zero }}} elem_rel /\ rel_exp M ρ M' ρ' elem_rel) ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A[Id,,zero] }}.
Proof.
  intros * [env_relΓ].
  destruct_conjs.
  eexists_rel_exp_untyped.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  eexists.
  split; econstructor; mauto.
Qed.

Ltac eexists_rel_exp_unsorted_of_sub_id_zero :=
  apply rel_exp_unsorted_of_sub_id_zero;
  eexists_rel_exp_untyped.


Lemma rel_exp_of_sub_wkwk_succ_var1_inversion {P} {pred_P : PredicativeSig P} : forall {Γ M M' A},
    {{ ⟪ pred_P ⟫ Γ, ℕ, A ⊨ M ≈ M' : A[Wk∘Wk,,succ(#1)] }} ->
    exists env_rel (_ : {{ EF Γ, ℕ, A ≈ Γ, ℕ, A ∈ per_ctx_env pred_P ↘ env_rel }}) s,
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}) d d',
      env_lookup ρ 1 d -> env_lookup ρ' 1 d' ->
    exists elem_rel, rel_typ pred_P s A d{{{ ρ ↯ ↯ ↦ succ d }}} A d{{{ ρ' ↯ ↯ ↦ succ d' }}} elem_rel /\ rel_exp M ρ M' ρ' elem_rel.
Proof.
  intros * HM.
  invert_rel_exp_2 HM env_relΓℕA.
  eexists_rel_exp.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓℕA).
  destruct_by_head (@rel_typ P).
  invert_rel_typ_body.
  mauto.
Qed.  

Lemma rel_exp_unsorted_of_sub_wkwk_succ_var1_inversion {P} {pred_P : PredicativeSig P} : forall {Γ M M' A},
    {{ ⟪ pred_P ⟫ Γ, ℕ, A ⊨u M ≈ M' : A[Wk∘Wk,,succ(#1)] }} ->
    exists env_rel (_ : {{ EF Γ, ℕ, A ≈ Γ, ℕ, A ∈ per_ctx_env pred_P ↘ env_rel }}),
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}) d d',
      env_lookup ρ 1 d -> env_lookup ρ' 1 d' ->
    exists elem_rel, rel_typ_unsorted pred_P A d{{{ ρ ↯ ↯ ↦ succ d }}} A d{{{ ρ' ↯ ↯ ↦ succ d' }}} elem_rel /\ rel_exp M ρ M' ρ' elem_rel.
Proof.
  intros * HM.
  invert_rel_exp_unsorted HM env_relΓ.
  eexists_rel_exp_untyped.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  invert_rel_typ_unsorted_body_nouip; mauto.
Qed.



Lemma rel_exp_unsorted_of_sub_id_N {P} {pred_P : PredicativeSig P} : forall {Γ M M' N A s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ Γ ⊨u N : ℕ }} ->
    (exists env_rel (_ : {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}),
      forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_rel }}),
      exists n n',
        {{ ⟦ N ⟧ ρ ↘ n }} /\
          {{ ⟦ N ⟧ ρ' ↘ n' }} /\
          exists elem_rel, rel_typ_unsorted pred_P A d{{{ ρ ↦ n }}} A d{{{ ρ' ↦ n' }}} elem_rel /\ rel_exp M ρ M' ρ' elem_rel) ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : A[Id,,N] }}.
Proof.
  intros * Hru []%rel_exp_unsorted_of_nat_inversion [env_relΓ].
  destruct_conjs.
  pose env_relΓ.
  handle_per_ctx_env_irrel.
  eexists_rel_exp_untyped.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp P).
  eexists; split; mauto.
  econstructor; mauto.
Qed.

Ltac eexists_rel_exp_unsorted_of_sub_id_N :=
  apply rel_exp_unsorted_of_sub_id_N; [eassumption |];
  eexists_rel_exp_untyped.


Ltac invert_rel_exp_of_typ_2 H l :=
  (unshelve epose proof (rel_exp_of_typ_inversion2 _ _ H); shelve_unifiable; [eassumption |]; clear H)
  + (pose proof (rel_exp_of_typ_inversion1 _ H) as [l []]; clear H)
  + invert_rel_exp_2 H l.

Ltac invert_rel_exp_of_typ_unsorted_2 H l :=
  (unshelve epose proof (rel_exp_of_typ_unsorted_inversion2 _ _ H); shelve_unifiable; [eassumption |]; clear H)
  + (pose proof (rel_exp_of_typ_unsorted_inversion1 _ H) as [l []]; clear H)
  + invert_rel_exp_2 H l.

  
Lemma eval_natrec_sub_neut {P} {pred_P : PredicativeSig P} : forall {Γ env_relΓ σ Δ env_relΔ MZ MZ' MS MS' A A' s m m' },
    {{ DF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }} ->
    {{ DF Δ ≈ Δ ∈ per_ctx_env pred_P ↘ env_relΔ }} ->
    {{ ⟪ pred_P ⟫ Δ, ℕ ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Δ ⊨u MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Δ, ℕ, A ⊨u MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Dom m ≈ m' ∈ per_bot }} ->
    (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) ρσ ρ'σ' mz mz',
        {{ ⟦ σ ⟧s ρ ↘ ρσ }} ->
        {{ ⟦ σ ⟧s ρ' ↘ ρ'σ' }} ->
        {{ Dom ρσ ≈ ρ'σ' ∈ env_relΔ }} ->
        {{ ⟦ MZ ⟧ ρσ ↘ mz }} ->
        {{ ⟦ MZ' ⟧ ρ'σ' ↘ mz' }} ->
        {{ Dom rec m under ρσ return A | zero -> mz | succ -> MS end ≈ rec m' under ρ' return A'[q σ] | zero -> mz' | succ -> MS'[q (q σ)] end ∈ per_bot }}).
Proof.
  intros * equiv_Γ_Γ equiv_Δ_Δ
             HA
             []%rel_exp_unsorted_of_sub_id_zero_inversion
             [env_relΔℕA]%rel_exp_unsorted_of_sub_wkwk_succ_var1_inversion
             equiv_m_m'.
  invert_rel_exp_of_typ_unsorted_2 HA env_relΔℕ.
  destruct_conjs.
  pose env_relΔℕA.
  pose env_relΔℕ.
  handle_per_ctx_env_irrel.
  invert_per_ctx_envs_of pred_P env_relΔℕA.
  handle_per_ctx_env_irrel.
  invert_per_ctx_envs_of pred_P env_relΔℕ.
  handle_per_ctx_env_irrel.
  intros.
  (on_all_hyp: destruct_rel_by_assumption env_relΔ).
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_typ P).
  invert_rel_typ_unsorted_body.
  destruct_by_head (@rel_exp P).
  destruct_by_head (@per_sort P).
  functional_eval_rewrite_clear.
  match goal with
  | _: {{ ⟦ σ ⟧s ρ ↘ ^?ρ1 }},
      _: {{ ⟦ σ ⟧s ρ' ↘ ^?ρ2 }} |- _ =>
      rename ρ1 into ρσ;
      rename ρ2 into ρ'σ
  end.
  intro t.
  assert {{ Dom ⇑! ℕ t ≈ ⇑! ℕ t ∈ (@per_nat P) }} by mauto.
  
  invert_per_sort_elem H12.   (* This line gets you the assumption that head_rel0 <~> per_nat *)
  
  assert {{ Dom ρσ ↦ ⇑! ℕ t ≈ ρ'σ ↦ ⇑! ℕ t ∈ env_relΔℕ }} as HinΔℕs.
  {
    (* This block seems to solve all the problematic admits *)
    apply_relation_equivalence; econstructor; mauto 2.
    eapply H11; mauto.  (* Not sure why the relation equivalence is not applied directly by mauto *)
  }
  (on_all_hyp: fun H => destruct (H _ _ HinΔℕs)).
  assert {{ Dom succ (⇑! ℕ t) ≈ succ (⇑! ℕ t) ∈ per_nat }} by mauto.
  assert {{ Dom ρσ ↦ succ (⇑! ℕ t) ≈ ρ'σ ↦ succ (⇑! ℕ t) ∈ env_relΔℕ }} as HinΔℕsuccs.
  {
    apply_relation_equivalence; econstructor; mauto 2.
    eapply H11; mauto.
  }
  (on_all_hyp: fun H => destruct (H _ _ HinΔℕsuccs)).
  assert {{ Dom ρσ ↦ ⇑! ℕ t ≈ ρ'σ ↦ ⇑! ℕ t ∈ env_relΔℕ }} as HinΔℕs'.
  {
    apply_relation_equivalence; econstructor; mauto 2.
    eapply H11; mauto.
  }
  assert {{ Dom ρσ ↦ succ (⇑! ℕ t) ≈ ρ'σ ↦ succ (⇑! ℕ t) ∈ env_relΔℕ }} as HinΔℕsuccs'.
  {
    apply_relation_equivalence; econstructor; mauto 2.
    eapply H11; mauto.
  }
  assert {{ Dom zero ≈ zero ∈ (@per_nat P) }}  by econstructor.
  assert {{ Dom ρσ ↦ zero ≈ ρ'σ ↦ zero ∈ env_relΔℕ }} as HinΔℕz.
  {
    apply_relation_equivalence; econstructor; mauto 2.
    eapply H11; mauto.
  }
  apply_relation_equivalence.
  (on_all_hyp: fun H => destruct (H _ _ HinΔℕs')).
  (on_all_hyp: fun H => destruct (H _ _ HinΔℕsuccs')).
  (on_all_hyp: fun H => destruct (H _ _ HinΔℕz)).
  destruct_by_head (@per_sort P).
  handle_per_sort_elem_irrel.
  (* rename a' into a''. *)
  (* rename m'0 into a'. *)
  (* rename a1 into asucc. *)
  (* rename m'1 into asucc'. *)
  (* assert {{ Dom ρσ ↦ ⇑! ℕ s ↦ ⇑! a (S s) ≈ ρ'σ ↦ ⇑! ℕ s ↦ ⇑! a' (S s) ∈ env_relΔℕA }} as HinΔℕA. *)
  (* { *)
  (*   apply_relation_equivalence; eexists; eauto. *)
  (*   unfold drop_env. *)
  (*   repeat change (fun n => d{{{ ^?ρσ ↦ ^?x ↦ ^?y }}} (S n)) with (fun n => d{{{ ρ ↦ x }}} n). *)
  (*   repeat change (d{{{ ^?ρσ ↦ ^?x ↦ ^?y }}} 0) with y. *)
  (*   eapply per_bot_then_per_elem; mauto. *)
  (* } *)
  (* apply_relation_equivalence. *)
  (* (on_all_hyp: fun H => destruct (H _ _ HinΔℕA)). *)
  (* destruct_conjs. *)
  (* destruct_by_head rel_typ. *)
  (* handle_per_univ_elem_irrel. *)
  (* destruct_by_head rel_exp. *)
  (* (on_all_hyp: fun H => edestruct (per_univ_then_per_top_typ H (S s)) as [? []]). *)
  (* functional_read_rewrite_clear. *)
  (* (on_all_hyp: fun H => unshelve epose proof (per_elem_then_per_top H _ s) as [? []]; shelve_unifiable; [eassumption |]). *)
  (* (on_all_hyp: fun H => unshelve epose proof (per_elem_then_per_top H _ (S (S s))) as [? []]; shelve_unifiable; [eassumption |]). *)
  (* functional_read_rewrite_clear. *)
  (* destruct (equiv_m_m' s) as [? []]. *)
  (* do 3 econstructor; mauto. *)
  (* repeat econstructor; mauto. *)
Admitted.

Corollary eval_natrec_neut {P} {pred_P : PredicativeSig P}: forall {Γ env_relΓ MZ MZ' MS MS' A A' m m' s},
    {{ DF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A ⊨u MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Dom m ≈ m' ∈ per_bot }} ->
    (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) mz mz',
        {{ ⟦ MZ ⟧ ρ ↘ mz }} ->
        {{ ⟦ MZ' ⟧ ρ' ↘ mz' }} ->
        {{ Dom rec m under ρ return A | zero -> mz | succ -> MS end ≈ rec m' under ρ' return A' | zero -> mz' | succ -> MS' end ∈ per_bot }}).
Proof.
  intros.
  assert {{ Dom rec m under ρ return A | zero -> mz | succ -> MS end ≈ rec m' under ρ' return A'[q Id] | zero -> mz' | succ -> MS'[q (q Id)] end ∈ per_bot }} by (admit).
  etransitivity; [eassumption |].
  intros t.
  match_by_head (@per_bot P) ltac:(fun H => specialize (H t) as [? []]).
  eexists; split; [eassumption |].
  dir_inversion_by_head (@read_ne P); subst.
  simplify_evals.
  mauto.
Admitted.

Lemma eval_natrec_rel {P} {pred_P : PredicativeSig P}: forall {Γ env_relΓ MZ MZ' MS MS' A A' s m m'},
    {{ DF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A ⊨u MS ≈ MS' : A[Wk∘Wk,,succ(#1)] }} ->
    {{ Dom m ≈ m' ∈ per_nat }} ->
    (forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}),
      forall elem_rel,
        rel_typ_unsorted pred_P A d{{{ ρ ↦ m }}} A d{{{ ρ' ↦ m' }}} elem_rel ->
        exists r r',
          {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
            {{ rec m' ⟦return A' | zero -> MZ' | succ -> MS' end⟧ ρ' ↘ r' }} /\
            {{ Dom r ≈ r' ∈ elem_rel }}).
Proof.
  intros * equiv_Γ_Γ HA HMZ HMS equiv_m_m'.
  induction equiv_m_m'; intros;
    invert_rel_exp_of_typ_unsorted_2 HA env_relΓℕ;
    apply rel_exp_unsorted_of_sub_id_zero_inversion in HMZ as [];
    destruct_conjs;
    pose env_relΓℕ.
  - handle_per_ctx_env_irrel.
    invert_per_ctx_envs_unsorted.
    handle_per_ctx_env_irrel.
    (on_all_hyp: destruct_rel_by_assumption env_relΓ).
    destruct_by_head (@rel_typ_unsorted P).
    handle_per_sort_elem_irrel.
    destruct_by_head (@rel_exp P).
    do 3 eexists; repeat split; mauto. mauto.
    admit.
  (* - assert {{ ⟪ pred_P ⟫ Γ, ℕ ⊨u A ≈ A : Sort@s }} as HA' by (etransitivity; mauto). *)
  (*   invert_rel_exp_of_typ HA. *)
  (*   apply rel_exp_of_sub_wkwk_succ_var1_inversion in HMS as [env_relΓℕA]. *)
  (*   destruct_conjs. *)
  (*   pose env_relΓℕA. *)
  (*   invert_per_ctx_envs_of env_relΓℕA. *)
  (*   handle_per_ctx_env_irrel. *)
  (*   invert_per_ctx_envs_of env_relΓℕ. *)
  (*   handle_per_ctx_env_irrel. *)
  (*   (on_all_hyp_rev: destruct_rel_by_assumption env_relΓ). *)
  (*   destruct_by_head rel_typ. *)
  (*   invert_rel_typ_body_nouip. *)
  (*   match goal with *)
  (*   | _: env_relΓ ρ ?ρ0 |- _ => *)
  (*       rename ρ0 into ρ' *)
  (*   end. *)
  (*   assert {{ Dom ρ ↦ m ≈ ρ' ↦ m' ∈ env_relΓℕ }} by (apply_relation_equivalence; mauto). *)
  (*   (on_all_hyp: destruct_rel_by_assumption env_relΓℕ). *)
  (*   assert {{ Dom ρ ↦ m ≈ ρ' ↦ m' ∈ env_relΓℕ }} as HinΓℕ by (apply_relation_equivalence; mauto). *)
  (*   apply_relation_equivalence. *)
  (*   (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕ)). *)
  (*   destruct_by_head per_univ. *)
  (*   unshelve epose proof (IHequiv_m_m' _ _ equiv_ρ_ρ' _ _) as [? [? [? []]]]; shelve_unifiable; [solve [mauto] |]. *)
  (*   handle_per_univ_elem_irrel. *)
  (*   match goal with *)
  (*   | _: {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ ^?r0 }}, *)
  (*       _: {{ rec m' ⟦return A' | zero -> MZ' | succ -> MS' end⟧ ρ' ↘ ^?r0' }} |- _ => *)
  (*       rename r0 into rm; *)
  (*       rename r0' into rm' *)
  (*   end. *)
  (*   assert {{ Dom ρ ↦ m ↦ rm ≈ ρ' ↦ m' ↦ rm' ∈ env_relΓℕA }} as HinΓℕA by (apply_relation_equivalence; mauto). *)
  (*   apply_relation_equivalence. *)
  (*   (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕA)). *)
  (*   destruct_conjs. *)
  (*   destruct_by_head rel_typ. *)
  (*   handle_per_univ_elem_irrel. *)
  (*   destruct_by_head rel_exp. *)
  (*   do 2 eexists; mauto. *)
  (* - match goal with *)
  (*   | _: per_bot m ?n |- _ => *)
  (*       rename n into m' *)
  (*   end. *)
  (*   handle_per_ctx_env_irrel. *)
  (*   invert_per_ctx_envs_of env_relΓℕ. *)
  (*   handle_per_ctx_env_irrel. *)
  (*   (on_all_hyp: destruct_rel_by_assumption env_relΓ). *)
  (*   (on_all_hyp_rev: destruct_rel_by_assumption env_relΓ). *)
  (*   invert_rel_typ_body_nouip. *)
  (*   match goal with *)
(*     | _: env_relΓ ρ ?ρ0 |- _ => *)
(*         rename ρ0 into ρ' *)
(*     end. *)
(*     assert {{ Dom ⇑ a m ≈ ⇑ a' m' ∈ per_nat }} by (econstructor; eassumption). *)
(*     assert {{ Dom ρ ↦ ⇑ a m ≈ ρ' ↦ ⇑ a' m' ∈ env_relΓℕ }} as HinΓℕ by (apply_relation_equivalence; mauto). *)
(*     apply_relation_equivalence. *)
(*     (on_all_hyp: fun H => directed destruct (H _ _ HinΓℕ)). *)
(*     destruct_by_head per_univ. *)
(*     destruct_by_head rel_typ. *)
(*     handle_per_univ_elem_irrel. *)
(*     destruct_by_head rel_exp. *)
(*     do 2 eexists. *)
(*     repeat split; only 1-2: mauto. *)
(*     eapply per_bot_then_per_elem; [eassumption |]. *)
(*     eapply eval_natrec_neut; eauto. *)
(*     + assert {{ EF Γ, ℕ ≈ Γ, ℕ ∈ per_ctx_env ↘ env_relΓℕ }} by (per_ctx_env_econstructor; eauto). *)
(*       eexists_rel_exp_of_typ. *)
(*       apply_relation_equivalence. *)
(*       eauto. *)
(*     + eexists_rel_exp_of_sub_id_zero. *)
(*       eauto. *)
      (* Qed. *)
Admitted.

Lemma rel_exp_unsorted_natrec_cong_rel_typ {P} {pred_P : PredicativeSig P} : forall {Γ A A' s M M' env_relΓ s'} {r : Ru_nat P s'},
    {{ DF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ ⊨u A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : ℕ }} ->
    forall ρ ρ' (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) n n',
      {{ ⟦ M ⟧ ρ ↘ n }} ->
      {{ ⟦ M' ⟧ ρ' ↘ n' }} ->
      exists elem_rel,
        rel_typ_unsorted pred_P A d{{{ ρ ↦ n }}} A d{{{ ρ' ↦ n' }}} elem_rel.
Proof.
  intros.
  assert {{ ⟪ pred_P ⟫ ⊨ Γ }} by (eexists; eauto).
  assert {{ ⟪ pred_P ⟫ Γ ⊨u ℕ : Sort@s' }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u M ≈ M' : ℕ[Id] }} by mauto 5.
  assert {{ ⟪ pred_P ⟫ Γ ⊨s Id,,M ≈ Id,,M' : Γ, ℕ }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ ⊨s Id,,M : Γ, ℕ }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u A[Id,,M] ≈ A[Id,,M'] : Sort@s[Id,,M] }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u A[Id,,M] ≈ A[Id,,M'] : Sort@s }} as HAId by mauto.
  invert_rel_exp_of_typ_unsorted HAId.
  destruct_conjs.
  (on_all_hyp_rev: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@per_sort P).
  invert_rel_typ_unsorted_body_nouip.
  apply rel_exp_implies_rel_typ_unsorted.
  econstructor; mauto.
Admitted.
