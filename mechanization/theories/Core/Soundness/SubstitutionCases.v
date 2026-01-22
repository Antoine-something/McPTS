From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness Require Import LogicalRelation TermStructureCases SortCases.
Import Domain_Notations.

Lemma presup_glu_rel_sub {P} (pred_P : PredicativeSig P) : forall {sts sts' Γ σ Δ},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩s σ : Δ : sts' }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ : sts }} /\ {{ ⟪ pred_P ⟫ ⊩ Δ : sts' }}.
Proof.
  intros * [].
  destruct_conjs.
  split; eexists; eassumption.
Qed.

Lemma presup_left_glu_rel_sub {P} (pred_P : PredicativeSig P) : forall {sts sts' Γ σ Δ},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩s σ : Δ : sts' }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ : sts }}.
Proof.
  intros * []%presup_glu_rel_sub.
  eassumption.
Qed.

#[export]
Hint Resolve presup_left_glu_rel_sub : mcpts.

Lemma presup_right_glu_rel_sub {P} (pred_P : PredicativeSig P) : forall {sts sts' Γ σ Δ},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩s σ : Δ : sts' }} ->
    {{ ⟪ pred_P ⟫ ⊩ Δ : sts' }}.
Proof.
  intros * []%presup_glu_rel_sub.
  eassumption.
Qed.

#[export]
Hint Resolve presup_right_glu_rel_sub : mcpts.

Lemma glu_rel_sub_id {P} (pred_P : PredicativeSig P) : forall {sts Γ},
    {{ ⟪ pred_P ⟫ ⊩ Γ : sts }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩s Id : Γ : sts }}.
Proof.
  intros * [Sb].
  do 2 eexists; repeat split; mauto.
  intros.
  econstructor; mauto.
  enough {{ Δ ⊢s σ ≈ Id∘σ : Γ }} as <-; mauto.
Qed.

#[export]
Hint Resolve glu_rel_sub_id : mcpts.

Lemma glu_rel_sub_weaken {P} (pred_P : PredicativeSig P) : forall {Γ sts A s},
    {{ ⟪ pred_P ⟫ ⊩ Γ, A : (s :: sts) }} ->
    {{ ⟪ pred_P ⟫ Γ, A : (s :: sts) ⊩s Wk : Γ : sts }}.
Proof.
  intros * [SbΓA].
  inversion_clear H.
  (* match_by_head1 (@glu_ctx_env P) invert_glu_ctx_env. *)
  handle_functional_glu_ctx_env P.
  do 2 eexists; repeat split; [econstructor | |]; try reflexivity; mauto.
  intros.
  destruct_by_head (@cons_glu_sub_pred P).
  econstructor; mauto.
Qed.

#[export]
Hint Resolve glu_rel_sub_weaken : mcpts.

Lemma glu_rel_sub_compose {P} (pred_P : PredicativeSig P) : forall {sts1 sts2 sts3 Γ1 σ2 Γ2 σ1 Γ3},
    {{ ⟪ pred_P ⟫ Γ1 : sts1 ⊩s σ2 : Γ2 : sts2 }} ->
    {{ ⟪ pred_P ⟫ Γ2 : sts2 ⊩s σ1 : Γ3 : sts3 }} ->
    {{ ⟪ pred_P ⟫ Γ1 : sts1 ⊩s σ1 ∘ σ2 : Γ3 : sts3 }}.
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

Lemma glu_rel_sub_extend {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts sts' Γ σ Δ M A s s'},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩s σ : Δ : sts' }} ->
    {{ ⟪ pred_P ⟫ Δ : sts' ⊩ A : Sort@s : s' }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A[σ] : s }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩s (σ ,, M) : Δ , A : (s :: sts') }}.
Proof.
  intros * Hσ HA HM.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ A : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ M : A[σ] }} by mauto 3.
  assert {{ Δ ⊢ Sort@s : Sort@s' }} by (eapply glu_rel_exp_typ_well_sorted; mauto 2).
  assert (exists s'', {{ Δ ⊢ Sort@s'' ≈ Sort@s' }} /\ Ax P s s'') as [s'' []] by (eapply wf_exp_sort_sort; mauto 2).  
  (* assert (exists s''', Ax P s'' s''') as [s'''] by (eapply full_P; mauto 2). *)
  (* assert {{ ⟪ pred_P ⟫ Γ : sts ⊩ Sort@s : Sort@s'' : s''' }} by mauto 3. *)
  (* assert {{ Γ ⊢ Sort@s[σ] ≈ Sort@s }} by mauto 3. *)
  (* assert {{ ⟪ pred_P ⟫ Γ : sts ⊩ A[σ] : Sort@s : s' }} by mauto 3. *)
  destruct Hσ as [SbΓ [SbΔ]].
  destruct_conjs.

  destruct HA as [Sb []].
  destruct HM as [Sb' []].
  handle_functional_glu_ctx_env P.
  
  (* invert_glu_rel_exp HA. *)
  (* invert_glu_rel_exp HM. *)
  do 2 eexists; repeat split; mauto.
  - econstructor; mauto 3; try reflexivity.
    intros.
    rewrite <- H14 in H5.
    assert (glu_rel_exp_with_sub pred_P s' Δ0 A {{{ Sort@s }}} σ0 ρ) by mauto 2.
    mauto 2.
    
  - intros.
    handle_functional_glu_ctx_env P.
    destruct_glu_rel_sub_with_sub.
    rewrite <- H14 in H8.
    destruct_glu_rel_sub_with_sub.
    rewrite <- H15 in H5.
    (* rewrite <- H14 in H12. *)
    (* rewrite <- H14 in H16. *)
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
    assert {{ Δ0 ⊢s (σ,,M)∘σ0 : Δ, A }} by mauto 3.
    assert {{ Δ0 ⊢s (σ,,M)∘σ0 ≈ (σ∘σ0),,M[σ0] : Δ, A }} by mauto 3.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) : Δ }} by mauto 4.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ Wk∘((σ∘σ0),,M[σ0]) : Δ }} by mauto 4.
    assert {{ Δ0 ⊢ M[σ0] : A[σ][σ0] }} by mauto 3.
    assert {{ Δ0 ⊢ M[σ0] : A[σ∘σ0] }} by mauto 4.
    assert {{ Δ0 ⊢s Wk∘((σ∘σ0),,M[σ0]) ≈ σ∘σ0 : Δ }} by mauto 3.
    assert {{ Δ0 ⊢s Wk∘((σ,,M)∘σ0) ≈ σ∘σ0 : Δ }} by mauto 3.
    econstructor; mauto 4.
    + assert {{ Δ, A ⊢s Wk : Δ }} by mauto 4.
      assert {{ Δ0 ⊢ A[Wk][(σ,,M)∘σ0] ≈ A[Wk∘((σ,,M)∘σ0)] : Sort@s }} as -> by (symmetry; mauto 3).
      assert {{ Δ0 ⊢ A[Wk∘((σ,,M)∘σ0)] ≈ A[σ∘σ0] : Sort@s }} as -> by mauto 3.
      assert {{ Δ0 ⊢ A[σ∘σ0] ≈ A[σ][σ0] : Sort@s }} by mauto 3.
      rewrite -> H29.
      assert {{ Δ, A ⊢ #0 : A[Wk] }} by mauto 3.
      assert {{ Δ0 ⊢ #0[(σ,,M)∘σ0] ≈ #0[(σ∘σ0),,M[σ0]] : A[Wk][(σ,,M)∘σ0] }} by mauto 3.
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

