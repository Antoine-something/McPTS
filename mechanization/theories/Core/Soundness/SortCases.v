From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness Require Import LogicalRelation TermStructureCases.
Import Domain_Notations.

Lemma glu_rel_exp_of_typ {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ Sb A s s'},
    Ax P s s' ->
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    (forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        {{ Δ ⊢ A[σ] : Sort@s }} /\
          exists a,
            {{ ⟦ A ⟧ ρ ↘ a }} /\
              {{ Dom a ≈ a ∈ per_sort pred_P s }} /\
              forall typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} -> {{ Δ ⊢ A[σ] ® typ_rel }}) ->
      {{ ⟪ pred_P ⟫ Γ ⊩ A : Sort@s > s' }}.
Proof.
  intros * Hax ? Hbody.
  (* assert (exists s', Ax P s s') as [s'] by (eapply full_P). *)
  eexists; split; mauto.
  intros.
  edestruct Hbody as [? [? [? []]]]; mauto.
Qed.

Lemma glu_rel_exp_typ {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ s s' s''},
    Ax P s s' -> Ax P s' s'' ->
    {{ ⟪ pred_P ⟫ ⊩ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ Sort@s : Sort@s' > s'' }}.
Proof.
  intros * Hax Hax' [].
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  split; mauto 4.
  eexists; repeat split; mauto.
  intros.
  match_by_head1 (@glu_sort_elem P) invert_glu_sort_elem.
  apply_predicate_equivalence.
  cbn.
  mauto 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_typ : mcpts.

Lemma glu_rel_exp_clean_inversion2' {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {s s' Γ Sb M},
    Ax P s s' ->
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ M : Sort@s > s' }} ->
    glu_rel_exp_resp_sub_env pred_P s' Sb M {{{ Sort@s }}}.
Proof.
  intros * Hax ? HM.
  assert (exists s'', {{ ⟪ pred_P ⟫ Γ ⊩ Sort@s : Sort@s' > s'' }}) as [s''] by mauto 3.
  eapply glu_rel_exp_clean_inversion2 in HM; mauto 3.
Qed.

#[local]
  Ltac invert_glu_rel_exp_old H :=
  invert_glu_rel_exp H.

#[global]
  Ltac invert_glu_rel_exp H :=
  (unshelve eapply (glu_rel_exp_clean_inversion2' _ _ _ _ _ _) in H; shelve_unifiable; [eassumption |];
   simpl in H)
  + invert_glu_rel_exp_old H.



Lemma glu_rel_exp_sub_typ {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {s' Γ σ Δ s A},
    {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ⊩ A : Sort@s > s' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ A[σ] : Sort@s > s' }}.
Proof.
  intros.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  (* assert (exists s'', Ax P s s'') as [s''] by (eapply full_P). *)
  (* assert {{ Γ ⊢ Sort@s[σ] ≈ Sort@s : Sort@s'' }} by mauto 3. *)
  assert {{ ⟪ pred_P ⟫ Γ ⊩ A[σ] : Sort@s[σ] > s' }} by mauto 4.
  
  simpl in H2.
  destruct_conjs.
  eexists.
  split; mauto.
  (* eexists. *)
  intros.
  assert (glu_rel_exp_with_sub pred_P s' Δ0 {{{ A[σ] }}} {{{ Sort@s[σ] }}} σ0 ρ) by mauto.
  dependent destruction H6.
  simplify_evals.
  econstructor; mauto.

  assert {{ Δ0 ⊢ Sort@s[σ][σ0] : Sort@s' }} by (eapply glu_sort_elem_trm_sort_lvl; mauto 2).

  assert {{ ⊢ Γ }} by mauto 2.
  assert (Ax P s s') by (eapply glu_rel_exp_sort_implies_ax; mauto 2).
  assert {{ Γ ⊢ Sort@s[σ] ≈ Sort@s : Sort@s' }} by mauto 4.  
  assert {{ Δ0 ⊢ Sort@s[σ][σ0] ≈ Sort@s[σ0] : Sort@s' }} as <- by mauto 4.
  eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_sub_typ : mcpts.
