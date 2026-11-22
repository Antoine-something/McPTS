From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Import Corollaries SystemAnnotated.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations.

(* All these presupposition results should probably go in LogicalRelation/Lemmas.v *)
Lemma presup_glu_rel_exp_typ_of_sort {P} (pred_P : PredicativeSig P) : forall {s anns Γ M A},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : A @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} /\ {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A : Sort@s @ ^so_None }}.
Proof.
  intros * [SbΓ []].
  split; [eexists; eassumption |].
  eexists; intuition.
  assert (glu_rel_exp_with_sub pred_P (so_Some s) Γ' M A σ ρ) as [] by mauto 2.
  econstructor; try reflexivity; mauto 2.
  - econstructor; try reflexivity.
  - split; [mauto 3|].
    match_by_head (@glu_typ_elem) ltac:(fun H => inversion H; subst).
    do 2 eexists; split; mauto 2.
    eapply glu_typ_elem_trm_typ; mauto 2.
Qed.

Lemma presup_glu_rel_exp_of_sort {P} (pred_P : PredicativeSig P) : forall {anns Γ M A},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : A @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} /\ {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A @ ^so_None }} /\ (exists s, {{ Γ ⊢ A ≈ Sort@s }} ).
Proof.
  intros * [SbΓ []].
  split; [eexists; eassumption |].
  split.
  - eexists; split; [ eassumption |].
    intros.
    assert (glu_rel_exp_with_sub pred_P so_None Γ' M A σ ρ) as [] by mauto 2.
    econstructor; mauto 3.
    eapply glu_typ_elem_trm_typ; mauto 2.
  - assert (exists env_relΓ, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }}) as [env_relΓ] by mauto 2.
    assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ [ρ' []]] by (eauto using per_ctx_then_per_env_initial_env).
    assert {{ Γ ⊢s Id ® ρ ∈ SbΓ }} by (eapply initial_env_glu_rel_exp; mauto 2).
    assert (glu_rel_exp_with_sub pred_P so_None Γ M A {{{ Id }}} ρ) by mauto 2.
    match_by_head @glu_rel_exp_with_sub ltac:(fun H => inversion H; subst).
    match_by_head @glu_typ_elem ltac:(fun H => inversion H; subst).
    simpl_glu_rel.
    assert {{ Γ ⊢ A }} by mauto 3.
    assert {{ Γ ⊢ A[Id] ≈ A }} by mauto 3.
    assert {{ Γ ⊢ A ≈ Sort@s }} by mauto 3.
    eauto.
Qed.

Lemma presup_ctx_glu_rel_exp {P} (pred_P : PredicativeSig P) : forall {so anns Γ M A},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : A @ so }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }}.
Proof.
  intros *.
  destruct so;
    [ intros []%presup_glu_rel_exp_of_sort
    | intros []%presup_glu_rel_exp_typ_of_sort];
    eassumption.
Qed.

#[export]
Hint Resolve presup_ctx_glu_rel_exp : mcpts.


Lemma presup_typ_glu_rel_exp_typ_of_sort {P} (pred_P : PredicativeSig P) : forall {s anns Γ M A},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : A @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A : Sort@s @ ^so_None }}.
Proof.
  intros * []%presup_glu_rel_exp_typ_of_sort;
    eassumption.
Qed.

#[export]
Hint Resolve presup_typ_glu_rel_exp_typ_of_sort : mcpts.

Lemma presup_typ_glu_rel_exp {P} (pred_P : PredicativeSig P) : forall {so anns Γ M A},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : A @ so }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A  @ so }}.
Proof.
  intros *.
  destruct so.
  - intros []%presup_glu_rel_exp_of_sort.
    destruct_conjs.
    eassumption.
  - intros []%presup_glu_rel_exp_typ_of_sort.
    destruct H0 as [SbΓ []].
    eexists; split; [eassumption |].
    intros.
    assert (glu_rel_exp_with_sub pred_P so_None Γ' A {{{ Sort@s }}} σ ρ) as [] by mauto 2.
    simplify_evals.
    match_by_head (@glu_typ_elem) ltac:(fun H => inversion H; subst).
    simpl_glu_rel.
    econstructor; mauto 3.
    econstructor; mauto 2.
Qed.

#[export]
Hint Resolve presup_typ_glu_rel_exp : mcpts.

Lemma presup_typ_glu_rel_exp_of_sort {P} (pred_P : PredicativeSig P) : forall {anns Γ M A},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : A @ ^so_None }} ->
    exists s, {{ Γ ⊢ A ≈ Sort@s }}.
Proof.
  intros * []%presup_glu_rel_exp_of_sort;
    destruct_conjs;
    eauto.
Qed.

#[export]
Hint Resolve presup_typ_glu_rel_exp_of_sort : mcpts.



Lemma presup_glu_rel_typ_of_sort {P} (pred_P : PredicativeSig P) : forall {s anns Γ A},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} /\ {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A : Sort@s @ ^so_None }}.
Proof.
  intros * [SbΓ []].
  split; [eexists; eassumption |].
  eexists; intuition.
  assert (glu_rel_typ_with_sub pred_P (so_Some s) Γ' A σ ρ) as [] by mauto 2.
  econstructor; try reflexivity; mauto 2.
  - econstructor; try reflexivity.
  - split; [mauto 3|].
    match_by_head @glu_typ_elem ltac:(fun H => inversion H; subst).
    do 2 eexists; split; mauto 2.
Qed.

Lemma presup_glu_rel_typ_sort {P} (pred_P : PredicativeSig P) : forall {anns Γ A},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} /\ (exists s, {{ Γ ⊢ A ≈ Sort@s }}).
Proof.
  intros * [SbΓ []].
  split; [eexists; eassumption |].
  assert (exists env_relΓ, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }}) as [env_relΓ] by mauto 2.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ [ρ' []]] by (eauto using per_ctx_then_per_env_initial_env).
  assert {{ Γ ⊢s Id ® ρ ∈ SbΓ }} by (eapply initial_env_glu_rel_exp; mauto 2).
  assert (glu_rel_typ_with_sub pred_P so_None Γ A {{{ Id }}} ρ) by mauto 2.
  match_by_head @glu_rel_typ_with_sub ltac:(fun H => inversion H; subst).
  match_by_head @glu_typ_elem ltac:(fun H => inversion H; subst).
  simpl_glu_rel.
  assert {{ Γ ⊢ A }} by mauto 3.
  assert {{ Γ ⊢ A[Id] ≈ A }} by mauto 3.
  assert {{ Γ ⊢ A ≈ Sort@s }} by mauto 3.
  eauto.
Qed.  


Lemma presup_typ_glu_rel_typ_of_sort {P} (pred_P : PredicativeSig P) : forall {s anns Γ A},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A : Sort@s @ ^so_None }}.
Proof.
  intros * []%presup_glu_rel_typ_of_sort;
    eassumption.
Qed.

#[export]
Hint Resolve presup_typ_glu_rel_typ_of_sort : mcpts.


Lemma presup_typ_glu_rel_typ_sort {P} (pred_P : PredicativeSig P) : forall {anns Γ A},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A @ ^so_None }} ->
    exists s, {{ Γ ⊢ A ≈ Sort@s }}.
Proof.
  intros * []%presup_glu_rel_typ_sort;
    eassumption.
Qed.

#[export]
Hint Resolve presup_typ_glu_rel_typ_sort : mcpts.

Lemma glu_rel_ctx_ann_lookup {P} (pred_P : PredicativeSig P) : forall {anns Γ x A},
    {{ #x : A ∈ Γ }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} ->
    exists so, {{ #x : A @ so ∈ Γ @ anns }}.
Proof.
  intros * H.
  gen anns.
  induction H.
  - intros * [Sb];
      inversion_clear H;
      repeat econstructor.
  - intros * [Sb];
      inversion_clear H0;
      apply_predicate_equivalence;
      assert {{ ⟪ pred_P ⟫ ⊩ Γ @ anns0 }} by (exists TSb; mauto);
      assert (exists so' : SortOption P, {{ # n : A @ so' ∈ Γ @ anns0 }}) as [so'] by mauto 2;
      repeat econstructor; mauto.
Qed.

#[export]
Hint Resolve glu_rel_ctx_ann_lookup : mcpts.

Lemma glu_rel_exp_vlookup {P} (pred_P : PredicativeSig P) : forall {anns so Γ x A},
    {{ #x : A ∈ Γ }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} ->
    {{ #x : A @ so ∈ Γ @ anns }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ #x : A @ so}}.
Proof.
  intros * Hx.
  gen anns so.
  dependent induction Hx; intros * [Sb];
    match_by_head1 (@glu_ctx_env P) ltac:(fun H => invert_glu_ctx_env H).

  - intros Hlookup.
    inversion Hlookup; subst.
    eexists.
    split; [econstructor |]; try reflexivity; mauto.
    intros.
    destruct_by_head (@cons_glu_sub_pred P).
    assert (glu_rel_typ_with_sub pred_P so0 Γ' A {{{ Wk∘σ }}} d{{{ ρ ↯ }}}) as [] by mauto 3.
    handle_functional_glu_typ_elem P.
    econstructor; mauto.
    
  - intros Hlookup.
    inversion Hlookup; subst.
    assert {{ ⟪ pred_P ⟫ ⊩ Γ @ anns0 }} by (eexists; mauto 2).
    assert {{ ⟪ pred_P ⟫ Γ @ anns0 ⊩ #n : A @ so }} as Hxn by mauto 2.
    pose proof Hxn as [SbΓ' []].
    handle_functional_glu_ctx_env P.
    econstructor; split; [econstructor|]; mauto; try reflexivity.
    intros.
    match_by_head @cons_glu_sub_pred ltac:(fun H => inversion_clear H).
    assert (SbΓ' Γ' {{{ Wk∘σ }}} d{{{ ρ ↯ }}}) by (apply_predicate_equivalence; eassumption).
    assert (glu_rel_exp_with_sub pred_P so Γ' {{{ #n }}} A {{{ Wk∘σ }}} d{{{ ρ ↯ }}}) as [] by mauto 2.
    simplify_evals.
    econstructor; mauto 3.

    assert {{ Γ ⊢ A }} by mauto 3.
    assert {{ Γ, B ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, B ⊢ A[Wk] }} by mauto 3.
    assert {{ Γ, B ⊢ #(S n) ≈ #n[Wk] : A[Wk] }} by mauto 4.
    assert {{ Γ' ⊢s σ ≈ σ : Γ, B }} by mauto 2.
    assert {{ Γ' ⊢ #(S n)[σ] ≈ #n[Wk][σ] : A[Wk][σ] }} by mauto 4.
    assert {{ Γ' ⊢ #n[Wk][σ] ≈ #n[Wk∘σ] : A[Wk∘σ] }} by mauto 4.
    assert {{ Γ' ⊢ #(S n)[σ] ≈ #n[Wk∘σ] : A[Wk][σ] }} as -> by (etransitivity; mauto 3).
    destruct so.
    + assert {{ Γ' ⊢ A[Wk∘σ] ≈ A[Wk][σ] }} as <- by mauto 3.
      eassumption.
    + match_by_head @glu_typ_elem ltac:(fun H => directed inversion H; subst).
      assert {{ Γ' ⊢ A[Wk∘σ] : Sort@s }} by (eapply glu_sort_elem_trm_sort_lvl; mauto 2).
      assert {{ Γ' ⊢ A[Wk∘σ] ≈ A[Wk][σ] : Sort@s }} as <- by mauto 3.
      eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_vlookup : mcpts.

Lemma glu_rel_exp_sub {P} (pred_P : PredicativeSig P) : forall {anns Γ σ anns' Γ' M A so},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩s σ : Γ' @ anns' }} ->
    {{ ⟪ pred_P ⟫ Γ' @ anns' ⊩ M : A @ so }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M[σ] : A[σ] @ so }}.
Proof.
  intros * Hσ HM.
  assert {{ Γ ⊢s σ : Γ' }} by mauto 3.
  assert {{ Γ' ⊢ M : A }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ' @ anns' ⊩ A @ so }} by mauto 2.
  destruct Hσ as [SbΓ [SbΓ' [? []]]].
  destruct HM as [? []].
  handle_functional_glu_ctx_env P.
  assert {{ Γ' ⊢ A }} by (gen_presups; eassumption).
  eexists; split; [eassumption |].
  intros Γ'' σ' ρ ?.
  destruct_glu_rel_sub_with_sub.
  rewrite <- H8 in H10.
  destruct_glu_rel_exp_with_sub.
  econstructor; mauto.

  assert {{ Γ'' ⊢ M[σ∘σ'] : A[σ∘σ'] }} by (eapply glu_typ_elem_trm_escape; mauto 2).
  gen_presup H15.
  assert {{ Γ'' ⊢ A[σ∘σ'] ≈ A[σ][σ'] }} as HAeq by mauto 3.
  assert {{ Γ'' ⊢s σ' : Γ }} by mauto 3.
  assert {{ Γ'' ⊢ M[σ∘σ'] ≈ M[σ][σ'] : A[σ][σ'] }} as <- by mauto 3.
  destruct so.
  - rewrite <- HAeq.
    eassumption.
  - match_by_head @glu_typ_elem ltac:(fun H => directed inversion H; subst).
    assert {{ Γ'' ⊢ A[σ∘σ'] : Sort@s }} by (eapply glu_sort_elem_trm_sort_lvl; mauto 3).
    assert {{ Γ'' ⊢ A[σ∘σ'] ≈ A[σ][σ'] : Sort@s }} as <- by mauto 3.
    eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_sub : mcpts.
 
Lemma glu_rel_typ_sub {P} (pred_P : PredicativeSig P) : forall {anns Γ σ anns' Γ' A so},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩s σ : Γ' @ anns' }} ->
    {{ ⟪ pred_P ⟫ Γ' @ anns' ⊩ A @ so }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A[σ] @ so }}.
Proof.
  intros * Hσ HA.
  assert {{ Γ ⊢s σ : Γ' }} by mauto 3.
  assert {{ Γ' ⊢ A }} by mauto 3.
  destruct Hσ as [SbΓ [SbΓ' [? []]]].
  destruct HA as [? []].
  handle_functional_glu_ctx_env P.
  eexists; split; [eassumption |].
  intros Γ'' σ' ρ ?.
  destruct_glu_rel_sub_with_sub.
  rewrite <- H7 in H8. (* Rewrite SbΓ' to x *)
  destruct_glu_rel_typ_with_sub.
  econstructor; mauto 3.
  eapply glu_typ_elem_typ_rel_sub_compose_decompose; mauto 2.    
Qed.

#[export]
Hint Resolve glu_rel_typ_sub : mcpts.

Ltac rewrite_Sb Sb Γ' σ ρ :=
  match goal with
  | H : Sb <∙> ?Sb', H2 : ?Sb' Γ' σ ρ |- _ =>
      assert (Sb Γ' σ ρ) by (rewrite <- H in H2; mauto 2)
  end.


Lemma glu_rel_exp_conv {P} (pred_P : PredicativeSig P) : forall {anns Γ M A A' so so'},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : A @ so }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A' @ so' }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : A' @ so' }}.
Proof. 
  intros * [SbΓ [? HA]] [SbΓ' [? HA']] ?.
  handle_functional_glu_ctx_env P.
  eexists; split; [eassumption|].
  intros.
  assert (SbΓ' Γ' σ ρ) by (apply_predicate_equivalence; mauto 2).
  destruct_glu_rel_exp_with_sub.
  destruct_glu_rel_typ_with_sub.
  econstructor; mauto 3.

  enough {{ SubT a <: a0 ∈ per_subtyp pred_P }} by (eapply glu_typ_elem_per_subtyp_trm_if'; mauto 3).
  
  assert {{ ⟪ pred_P ⟫ Γ ⊨ A ⊆ A' }} as [env_relΓ [? rel_subtyp]] by (eapply completeness_fundamental; mauto 2).
  assert (exists ρinit ρinit', initial_env Γ ρinit /\ initial_env Γ ρinit' /\ {{ Dom ρinit ≈ ρinit' ∈ env_relΓ }}) as [ρinit [ρinit']] by (eauto using per_ctx_then_per_env_initial_env).
  destruct_conjs.
  assert {{ Γ ⊢s Id ® ρinit ∈ SbΓ }} by (eapply initial_env_glu_rel_exp; mauto 2).
  destruct_glu_rel_exp_with_sub.
  destruct_rel_by_assumption env_relΓ rel_subtyp.
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp).
  simplify_evals.
  
  unshelve (epose proof HA Γ' σ ρ _ as glu_relA); mauto 2.
  inversion glu_relA; subst.
         
  assert (env_relΓ ρ ρ) by (eapply glu_ctx_env_per_env; mauto 2).
  assert (exists R0 R0' : relation (domain P),
             rel_typ pred_P A ρ A ρ R0 /\ rel_typ pred_P A' ρ A' ρ R0' /\ rel_exp A ρ A' ρ (per_subtyp pred_P)
           ) as [R0 [R0']] by mauto.
  destruct_conjs.
  destruct_by_head (@rel_typ P).
  destruct_by_head (@rel_exp).
  simplify_evals.
  eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_conv : mcpts.

Lemma glu_rel_exp_conv_ann {P} (pred_P : PredicativeSig P) : forall {anns Γ M A so so'},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : A @ so }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A @ so' }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : A @ so' }}.
Proof.
  intros * [SbΓ []] [SbΓ' []].
  handle_functional_glu_ctx_env P.
  eexists; split; mauto 2.
  intros.
  assert (SbΓ' Γ' σ ρ) by (eapply H4; eassumption).
  destruct_glu_rel_exp_with_sub.
  destruct_glu_rel_typ_with_sub.
  simplify_evals.
  econstructor; mauto 3.

  assert (per_typ pred_P a a) by (eapply glu_typ_elem_per_typ; mauto 2).
  eapply (glu_typ_elem_exp_conv pred_P H9 H7 H10); mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_exp_conv_ann : mcpts.
