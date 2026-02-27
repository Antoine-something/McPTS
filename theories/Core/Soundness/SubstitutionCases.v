From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness Require Import LogicalRelation TermStructureCases SortCases.
Import Domain_Notations.

Lemma presup_glu_rel_sub {P} (pred_P : PredicativeSig P) : forall {Γ σ Δ},
    {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ }} /\ {{ ⟪ pred_P ⟫ ⊩ Δ }}.
Proof.
  intros * [].
  destruct_conjs.
  split; eexists; eassumption.
Qed.

Lemma presup_left_glu_rel_sub {P} (pred_P : PredicativeSig P) : forall {Γ σ Δ},
    {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ }}.
Proof.
  intros * []%presup_glu_rel_sub.
  eassumption.
Qed.

#[export]
Hint Resolve presup_left_glu_rel_sub : mcpts.

Lemma presup_right_glu_rel_sub {P} (pred_P : PredicativeSig P) : forall {Γ σ Δ},
    {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ ⊩ Δ }}.
Proof.
  intros * []%presup_glu_rel_sub.
  eassumption.
Qed.

#[export]
Hint Resolve presup_right_glu_rel_sub : mcpts.

Lemma glu_rel_sub_id {P} (pred_P : PredicativeSig P) : forall {Γ},
    {{ ⟪ pred_P ⟫ ⊩ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩s Id : Γ }}.
Proof.
  intros * [Sb].
  do 2 eexists; repeat split; mauto.
  intros.
  econstructor; mauto.
  enough {{ Δ ⊢s σ ≈ Id∘σ : Γ }} as <-; mauto.
Qed.

#[export]
Hint Resolve glu_rel_sub_id : mcpts.

Lemma glu_rel_sub_weaken {P} (pred_P : PredicativeSig P) : forall {Γ A s},
    {{ ⟪ pred_P ⟫ ⊩ Γ, A@s }} ->
    {{ ⟪ pred_P ⟫ Γ, A@s ⊩s Wk : Γ }}.
Proof.
  intros * [SbΓA].
  inversion_clear H.
  handle_functional_glu_ctx_env P.
  do 2 eexists; repeat split; [econstructor | |]; try reflexivity; mauto.
  intros.
  destruct_by_head (@cons_glu_sub_pred P).
  econstructor; mauto.
Qed.

#[export]
Hint Resolve glu_rel_sub_weaken : mcpts.

Lemma glu_rel_sub_compose {P} (pred_P : PredicativeSig P) : forall {Γ1 σ2 Γ2 σ1 Γ3},
    {{ ⟪ pred_P ⟫ Γ1 ⊩s σ2 : Γ2 }} ->
    {{ ⟪ pred_P ⟫ Γ2 ⊩s σ1 : Γ3 }} ->
    {{ ⟪ pred_P ⟫ Γ1 ⊩s σ1 ∘ σ2 : Γ3 }}.
Proof.
  intros * Hσ2 Hσ1.
  assert {{ Γ2 ⊢s σ1 : Γ3 }} by mauto.
  assert {{ Γ1 ⊢s σ2 : Γ2 }} by mauto.
  destruct Hσ2 as [SbΓ1 [SbΓ2]].
  destruct_conjs.
  invert_glu_rel_sub Hσ1.
  destruct_conjs.
  do 2 eexists; repeat split; mauto.
  intros.
  handle_functional_glu_ctx_env P.
  destruct_glu_rel_sub_with_sub.
  rewrite <- H10 in H9.
  destruct_glu_rel_sub_with_sub.
  econstructor; mauto.
  enough {{ Δ ⊢s (σ1 ∘ σ2) ∘ σ ≈ σ1 ∘ (σ2 ∘ σ) : Γ3 }} as -> by eassumption.
  mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_sub_compose : mcpts.

Lemma glu_rel_sub_extend {P} (pred_P : PredicativeSig P) : forall {Γ σ Δ M A s s'},
    {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ⊩ A : Sort@s @ s' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ M : A[σ] @ s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩s (σ ,, M) : Δ , A@s }}.
Proof.
  intros * Hσ HA HM.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ A : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ M : A[σ] }} by mauto 3.
  assert {{ Δ ⊢ Sort@s : Sort@s' }} by (eapply glu_rel_exp_typ_well_sorted; mauto 2).
  assert (Ax P s s') by (eapply glu_rel_exp_sort_implies_ax; mauto 2).
  destruct Hσ as [SbΓ [SbΔ]].
  destruct_conjs.
  destruct HA as [Sb []].
  destruct HM as [Sb' []].
  handle_functional_glu_ctx_env P.
  do 2 eexists; repeat split; mauto.
  - econstructor; mauto 3; try reflexivity.
    intros.
    rewrite <- H13 in H4.
    assert (glu_rel_exp_with_sub pred_P s' Δ0 A {{{ Sort@s }}} σ0 ρ) by mauto 2.
    mauto 2.
    
  - intros.
    handle_functional_glu_ctx_env P.
    destruct_glu_rel_sub_with_sub.
    rewrite <- H14 in H4.
    rewrite <- H13 in H11.
    destruct_glu_rel_exp_with_sub.
    simplify_evals.
    match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
    apply_predicate_equivalence.
    unfold sort_glu_exp_pred' in *.
    unfold glu_sort_typ_rec in *.
    destruct_conjs.
    handle_functional_glu_sort_elem P.
    rename m into a.
    assert {{ Δ0 ⊢s σ0 : Γ }} by mauto 4.
    econstructor; mauto 3.
    assert {{ Δ0 ⊢s (σ,,M)∘σ0 : Δ, A@s }} by mauto 3.
    assert {{ Δ0 ⊢s (σ,,M)∘σ0 ≈ (σ∘σ0),,M[σ0] : Δ, A@s }} by mauto 3.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) : Δ }} by mauto 4.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ Wk∘((σ∘σ0),,M[σ0]) : Δ }} by mauto 4.
    assert {{ Δ0 ⊢ M[σ0] : A[σ][σ0] }} by mauto 3.
    assert {{ Δ0 ⊢ M[σ0] : A[σ∘σ0] }} by mauto 4.
    assert {{ Δ0 ⊢s Wk∘((σ∘σ0),,M[σ0]) ≈ σ∘σ0 : Δ }} by mauto 3.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ σ∘σ0 : Δ }} by mauto 3.
    econstructor; mauto 4.
    + assert {{ Δ, A@s ⊢s Wk : Δ }} by mauto 4.
      assert {{ Δ0 ⊢ A[Wk][(σ,,M)∘σ0] ≈ A[Wk∘((σ,,M)∘σ0)] : Sort@s }} as -> by (symmetry; mauto 3).
      assert {{ Δ0 ⊢ A[Wk∘((σ,,M)∘σ0)] ≈ A[σ∘σ0] : Sort@s }} as -> by mauto 3.
      assert {{ Δ0 ⊢ A[σ∘σ0] ≈ A[σ][σ0] : Sort@s }} by mauto 3.
      rewrite -> H30.
      assert {{ Δ, A@s ⊢ #0 : A[Wk] }} by mauto 3.
      assert {{ Δ0 ⊢ #0[(σ,,M)∘σ0] ≈ #0[(σ∘σ0),,M[σ0]] : A[Wk][(σ,,M)∘σ0] }} by mauto 4.
      assert {{ Δ0 ⊢ #0[(σ,,M)∘σ0] ≈ #0[(σ∘σ0),,M[σ0]] : A[σ][σ0] }} as -> by mauto 4.
      assert {{ Δ0 ⊢ #0[(σ∘σ0),,M[σ0]] ≈ M[σ0] : A[σ∘σ0] }} by mauto.
      assert {{ Δ0 ⊢ #0[(σ∘σ0),,M[σ0]] ≈ M[σ0] : A[σ][σ0] }} as -> by (eapply wf_exp_eq_conv; mauto 4).
      eapply glu_sort_elem_exp_conv with (exp_rel := exp_rel); mauto 3.
      eapply glu_sort_elem_trm_typ; mauto 2.
      
    + simpl.
      eapply glu_ctx_env_sub_resp_sub_eq with (Sb := SbΔ) (σ := {{{ σ∘σ0 }}}); mauto 3.      
Qed.

#[export]
Hint Resolve glu_rel_sub_extend : mcpts.


Lemma glu_rel_sub_extend_unsorted {P} (pred_P : PredicativeSig P) : forall {Γ σ Δ M A s so},
    {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ⊩u A : Sort@s @ so }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u M : A[σ] @ ^(Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩s (σ ,, M) : Δ , A@s }}.
Proof.
  intros * Hσ HA HM'.
  assert {{ ⟪ pred_P ⟫ Γ ⊩ M : A[σ] @ s }} as HM by mauto 2.
  destruct so.
  - assert {{ Γ ⊢s σ : Δ }} by mauto 3.
    assert {{ Δ ⊢ A : Sort@s }} by mauto 3.
    assert {{ Γ ⊢ M : A[σ] }} by mauto 3.
    destruct Hσ as [SbΓ [SbΔ]].
    destruct_conjs.
    destruct HA as [Sb []].
    destruct HM as [Sb' []].
    handle_functional_glu_ctx_env P.
    do 2 eexists; repeat split; mauto.    
    + 
      econstructor; mauto 3; try reflexivity.
      intros.
      rewrite <- H11 in H2.
      assert (glu_rel_exp_with_sub_unsorted pred_P None Δ0 A {{{ Sort@s }}} σ0 ρ) by mauto 2.
      dependent destruction H3.
      inversion H13; subst.
      simpl_glu_rel.
      assert (glu_rel_typ_with_sub_unsorted pred_P (Some s) Δ0 M0 σ0 ρ) by (econstructor; mauto 3).
      dependent destruction H17.
      econstructor; mauto 3.

    + intros.
      
      admit.
  - assert {{ ⟪ pred_P ⟫ Δ ⊩ A : Sort@s @ s0 }} by mauto 2.  
    mauto 2.
  
  (*   intros. *)
  (*   handle_functional_glu_ctx_env P. *)
  (*   destruct_glu_rel_sub_with_sub. *)
  (*   rewrite <- H14 in H4. *)
  (*   rewrite <- H13 in H11. *)
  (*   destruct_glu_rel_exp_with_sub. *)
  (*   simplify_evals. *)
  (*   match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H). *)
  (*   apply_predicate_equivalence. *)
  (*   unfold sort_glu_exp_pred' in *. *)
  (*   unfold glu_sort_typ_rec in *. *)
  (*   destruct_conjs. *)
  (*   handle_functional_glu_sort_elem P. *)
  (*   rename m into a. *)
  (*   assert {{ Δ0 ⊢s σ0 : Γ }} by mauto 4. *)
  (*   econstructor; mauto 3. *)
  (*   assert {{ Δ0 ⊢s (σ,,M)∘σ0 : Δ, A@s }} by mauto 3. *)
  (*   assert {{ Δ0 ⊢s (σ,,M)∘σ0 ≈ (σ∘σ0),,M[σ0] : Δ, A@s }} by mauto 3. *)
  (*   assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) : Δ }} by mauto 4. *)
  (*   assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ Wk∘((σ∘σ0),,M[σ0]) : Δ }} by mauto 4. *)
  (*   assert {{ Δ0 ⊢ M[σ0] : A[σ][σ0] }} by mauto 3. *)
  (*   assert {{ Δ0 ⊢ M[σ0] : A[σ∘σ0] }} by mauto 4. *)
  (*   assert {{ Δ0 ⊢s Wk∘((σ∘σ0),,M[σ0]) ≈ σ∘σ0 : Δ }} by mauto 3. *)
  (*   assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ σ∘σ0 : Δ }} by mauto 3. *)
  (*   econstructor; mauto 4. *)
  (*   + assert {{ Δ, A@s ⊢s Wk : Δ }} by mauto 4. *)
  (*     assert {{ Δ0 ⊢ A[Wk][(σ,,M)∘σ0] ≈ A[Wk∘((σ,,M)∘σ0)] : Sort@s }} as -> by (symmetry; mauto 3). *)
  (*     assert {{ Δ0 ⊢ A[Wk∘((σ,,M)∘σ0)] ≈ A[σ∘σ0] : Sort@s }} as -> by mauto 3. *)
  (*     assert {{ Δ0 ⊢ A[σ∘σ0] ≈ A[σ][σ0] : Sort@s }} by mauto 3. *)
  (*     rewrite -> H30. *)
  (*     assert {{ Δ, A@s ⊢ #0 : A[Wk] }} by mauto 3. *)
  (*     assert {{ Δ0 ⊢ #0[(σ,,M)∘σ0] ≈ #0[(σ∘σ0),,M[σ0]] : A[Wk][(σ,,M)∘σ0] }} by mauto 4. *)
  (*     assert {{ Δ0 ⊢ #0[(σ,,M)∘σ0] ≈ #0[(σ∘σ0),,M[σ0]] : A[σ][σ0] }} as -> by mauto 4. *)
  (*     assert {{ Δ0 ⊢ #0[(σ∘σ0),,M[σ0]] ≈ M[σ0] : A[σ∘σ0] }} by mauto. *)
  (*     assert {{ Δ0 ⊢ #0[(σ∘σ0),,M[σ0]] ≈ M[σ0] : A[σ][σ0] }} as -> by (eapply wf_exp_eq_conv; mauto 4). *)
  (*     eapply glu_sort_elem_exp_conv with (exp_rel := exp_rel); mauto 3. *)
  (*     eapply glu_sort_elem_trm_typ; mauto 2. *)
      
  (*   + simpl. *)
  (*     eapply glu_ctx_env_sub_resp_sub_eq with (Sb := SbΔ) (σ := {{{ σ∘σ0 }}}); mauto 3.         *)
Admitted.

#[export]
Hint Resolve glu_rel_sub_extend_unsorted : mcpts.  

Lemma glu_rel_sub_conv {P} (pred_P : PredicativeSig P) : forall {Γ σ Δ Δ'},
    {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ ⊩ Δ' }} ->
    {{ ⊢ Δ ≈ Δ' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ' }}.
Proof.
  intros * [SbΓ [SbΔ [? []]]] [SbΔ'] HΔΔ'.
  assert (SbΔ <∙> SbΔ').
  {
    split; eapply glu_ctx_env_resp_per_ctx_helper; mauto 3.
  }
  do 2 eexists; repeat split; mauto 3.
  intros.
  destruct_glu_rel_sub_with_sub.
  eapply H3 in H6.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_sub_conv : mcpts.
 
