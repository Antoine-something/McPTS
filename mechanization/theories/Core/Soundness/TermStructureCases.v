From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations.

Lemma presup_glu_rel_exp {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts Γ M A},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ : sts }} /\ (exists s, {{ ⟪ pred_P ⟫ Γ : sts ⊩ A : Sort@s }}).
Proof.
  intros * [? [? []]].
  split; [eexists; eassumption |].
  do 2 eexists; intuition.
  assert (exists s', Ax P x0 s') by (eapply full_P; mauto).
  destruct_conjs.  
  eexists; mauto 4.
Qed.

Lemma presup_ctx_glu_rel_exp {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts Γ M A},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ : sts }}.
Proof.
  intros * []%presup_glu_rel_exp;
    eassumption.
Qed.

#[export]
Hint Resolve presup_ctx_glu_rel_exp : mcpts.

Lemma presup_typ_glu_rel_exp {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts Γ M A},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A }} ->
    exists s, {{ ⟪ pred_P ⟫ Γ : sts ⊩ A : Sort@s }}.
Proof.
  intros * []%presup_glu_rel_exp;
    eassumption.
Qed.

#[export]
Hint Resolve presup_typ_glu_rel_exp : mcpts.

Lemma glu_rel_exp_vlookup {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts Γ x A},
    {{ #x : A ∈ Γ }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ : sts }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ #x : A }}.
Proof.
  intros * Hx.
  gen sts.
  induction Hx; intros * [Sb];
    match_by_head1 (@glu_ctx_env P) ltac:(fun H => invert_glu_ctx_env H).

  
  (* intros * [Sb] Hx. gen Sb. *)
  (* induction Hx; intros; *)
  (*   match_by_head1 (@glu_ctx_env P) ltac:(fun H => invert_glu_ctx_env H). *)
  - eexists.
    split; [econstructor |]; try reflexivity; mauto.
    eexists.
    intros.
    destruct_by_head (@cons_glu_sub_pred P).
    econstructor; mauto.
  - assert (glu_ctx_env pred_P {{{ sts, s }}} Sb {{{ Γ, B }}}) by (econstructor; mauto).
    assert {{ ⟪ pred_P ⟫ Γ : sts ⊩ #n : A }} as Hn.
    {
      eapply IHHx.
      econstructor; eauto.
    }
    
    assert (exists s, {{ Γ ⊢ A : Sort@s }}) as [s'] by (gen_presups; mauto 3).
    invert_glu_rel_exp Hn.
    rename x into k.
    eexists.
    split.
    + econstructor; try reflexivity; mauto.
      intros.
      dependent destruction H3.
      handle_functional_glu_ctx_env P.
      eapply H5.
      eassumption.
    + eexists.
      intros.
      destruct_by_head (@cons_glu_sub_pred P).
      destruct_glu_rel_exp_with_sub.
      simplify_evals.
      rename a into b.
      rename a0 into a.
      assert {{ Dom a ≈ a ∈ per_sort pred_P x0 }} as [] by mauto.
      eapply mk_glu_rel_exp_with_sub''; intuition mauto.
      handle_functional_glu_sort_elem P.
      
      
      assert {{ ⊢ Γ, B }} by mauto 3.
      assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] : Sort@s' }} by mauto.
      assert {{ Γ ⊢ A : Sort@x0 }} by mauto.
      assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] : Sort@x0 }} as -> by mauto.
      assert {{ Γ ⊢ #n : A }} by mauto 4.
      assert {{ Γ, B ⊢ #n[Wk] : A[Wk] }} by mauto 3.
      assert {{ Γ, B ⊢ #n[Wk] ≈ #(S n) : A[Wk] }} by mauto 3.
      assert {{ Δ ⊢ #n[Wk][σ] ≈ #(S n)[σ] : A[Wk∘σ] }} as <- by (eapply wf_exp_eq_conv; mauto).
      assert {{ Δ ⊢ #n[Wk∘σ] ≈ #n[Wk][σ] : A[Wk∘σ] }} as <- by mauto 3.
      eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_vlookup : mcpts.

Lemma glu_rel_exp_sub {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts Γ σ Δ sts' M A},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩s σ : Δ : sts' }} ->
    {{ ⟪ pred_P ⟫ Δ : sts' ⊩ M : A }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M[σ] : A[σ] }}.
Proof.
  intros * Hσ HM.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ M : A }} by mauto 3.
  assert (exists s, {{ ⟪ pred_P ⟫ Δ : sts' ⊩ A : Sort@s }}) as [s] by mauto 3.
  destruct Hσ as [SbΓ [SbΔ]].
  destruct_conjs.
  invert_glu_rel_exp HM.
  assert {{ Δ ⊢ A : Sort@s }} by mauto 3.
  eexists; split; mauto.
  eexists.
  intros Δ' τ ρ ?.
  destruct_glu_rel_sub_with_sub.
  handle_functional_glu_ctx_env P.
  rewrite <- H12 in H10.
  destruct_glu_rel_exp_with_sub.
  assert {{ Dom a ≈ a ∈ per_sort pred_P x0 }} as [] by mauto.
  econstructor; mauto.
  assert {{ Δ' ⊢s τ : Γ }} by mauto 3.
  assert {{ Δ' ⊢ A[σ∘τ] : Sort@x0 }} by (eapply glu_sort_elem_trm_sort_lvl; mauto).
  assert (exists Δ'' K, {{ Δ' ⊢s σ∘τ : Δ'' }} /\ {{ Δ'' ⊢ A : K }} /\ {{ Δ' ⊢ K[σ∘τ] ≈ Sort@x0 }}) by mauto.
  destruct H18 as [Δ'' [? []]].
  assert (exists Δ''', {{ Δ' ⊢s τ : Δ''' }} /\ {{ Δ''' ⊢s σ : Δ'' }}) by mauto.
  destruct_conjs.
  assert {{ Δ' ⊢ A[σ][τ] ≈ A[σ∘τ] : Sort@x0 }} as -> by (symmetry; mauto).
  assert {{ Δ' ⊢ M[σ][τ] ≈ M[σ∘τ] : A[σ∘τ] }} as ->; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_sub : mcpts.
