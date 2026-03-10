From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations.

Lemma presup_glu_rel_exp {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {s Γ M A},
    {{ ⟪ pred_P ⟫ Γ ⊩ M : A @ s }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ }} /\ (exists s', {{ ⟪ pred_P ⟫ Γ ⊩ A : Sort@s @ s' }}).
Proof.
  intros * [? []].
  split; [eexists; eassumption |].
  assert (exists s', Ax P s s') as [s'] by (eapply full_P; mauto).
  do 2 eexists; intuition.
  destruct_conjs.
  destruct_glu_rel_exp_with_sub.
  eexists; mauto 4.
  assert {{ Δ ⊢ Sort@s[σ] ≈ Sort@s }} by mauto 3.
  assert {{ Δ ⊢ A[σ] : Sort@s }} by (eapply glu_sort_elem_trm_sort_lvl; mauto 2).
  assert {{ Δ ⊢ A[σ] : Sort@s[σ] }} by mauto 3.
  repeat split; mauto 3.
  repeat eexists; mauto 2.
  eapply glu_sort_elem_trm_typ; mauto 2.
Qed.

Lemma presup_ctx_glu_rel_exp {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {s Γ M A},
    {{ ⟪ pred_P ⟫ Γ ⊩ M : A @ s }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ }}.
Proof.
  intros * []%presup_glu_rel_exp;
    eassumption.
Qed.

#[export]
Hint Resolve presup_ctx_glu_rel_exp : mcpts.

Lemma presup_typ_glu_rel_exp {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {s Γ M A},
    {{ ⟪ pred_P ⟫ Γ ⊩ M : A @ s }} ->
    exists s', {{ ⟪ pred_P ⟫ Γ ⊩ A : Sort@s @ s' }}.
Proof.
  intros * []%presup_glu_rel_exp;
    eassumption.
Qed.

#[export]
Hint Resolve presup_typ_glu_rel_exp : mcpts.


Lemma presup_glu_rel_exp_unsorted_typ {P} (pred_P : PredicativeSig P) : forall {s Γ M A},
    {{ ⟪ pred_P ⟫ Γ ⊩u M : A @ ^(Some s) }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ }} /\ {{ ⟪ pred_P ⟫ Γ ⊩u A : Sort@s @ ^None }}.
Proof.
  intros * [SbΓ []].  
  split; [eexists; eassumption |].
  eexists; intuition.
  specialize (H0 Δ σ ρ H1).
  inversion_clear H0.
  econstructor; try reflexivity; mauto 2.
  - econstructor; try reflexivity.
  - split; [reflexivity| ].
    do 2 eexists; split; mauto 2.
    eapply glu_sort_elem_trm_typ; mauto 2.
Qed.

Lemma presup_glu_rel_exp_unsorted_sort {P} (pred_P : PredicativeSig P) : forall {Γ M A},
    {{ ⟪ pred_P ⟫ Γ ⊩u M : A @ ^None }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ }} /\ (exists s, A = {{{ Sort@s }}}).
Proof.
  intros * [SbΓ []].
  split; [eexists; eassumption |].

  assert (exists env_relΓ, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }}) as [env_relΓ] by mauto 2.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ [ρ' []]] by (eauto using per_ctx_then_per_env_initial_env).
  assert {{ Γ ⊢s Id ® ρ ∈ SbΓ }} by (eapply initial_env_glu_rel_exp; mauto 2).
  assert (glu_rel_exp_with_sub_unsorted pred_P None Γ M A {{{ Id }}} ρ) by mauto 2.
  inversion_clear H5.
  eauto.
Qed.


Lemma presup_ctx_glu_rel_exp_unsorted {P} (pred_P : PredicativeSig P) : forall {so Γ M A},
    {{ ⟪ pred_P ⟫ Γ ⊩u M : A @ so }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ }}.
Proof.
  intros *.
  dependent destruction so.
  - intros * []%presup_glu_rel_exp_unsorted_sort;
    eassumption.
  - intros * []%presup_glu_rel_exp_unsorted_typ;
    eassumption.
Qed.

#[export]
Hint Resolve presup_ctx_glu_rel_exp_unsorted : mcpts.

Lemma presup_typ_glu_rel_exp_unsorted_typ {P} (pred_P : PredicativeSig P) : forall {s Γ M A},
    {{ ⟪ pred_P ⟫ Γ ⊩u M : A @ ^(Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u A : Sort@s @ ^None }}.
Proof.
  intros * []%presup_glu_rel_exp_unsorted_typ;
    eassumption.
Qed.

#[export]
  Hint Resolve presup_typ_glu_rel_exp_unsorted_typ : mcpts.

Lemma presup_typ_glu_rel_exp_unsorted_sort {P} (pred_P : PredicativeSig P) : forall {Γ M A},
    {{ ⟪ pred_P ⟫ Γ ⊩u M : A @ ^None }} ->
    exists s, A = {{{ Sort@s }}}.
Proof.
  intros * []%presup_glu_rel_exp_unsorted_sort;
    eassumption.
Qed.

#[export]
Hint Resolve presup_typ_glu_rel_exp_unsorted_sort : mcpts.



Lemma glu_rel_exp_vlookup {P} (pred_P : PredicativeSig P) : forall {Γ x A s},
    {{ #x : A@s ∈ Γ }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ #x : A @ s}}.
Proof.
  intros * Hx.
  dependent induction Hx; intros * [Sb];
    match_by_head1 (@glu_ctx_env P) ltac:(fun H => invert_glu_ctx_env H).

  - eexists.
    split; [econstructor |]; try reflexivity; mauto.
    intros.
    destruct_by_head (@cons_glu_sub_pred P).
    econstructor; mauto.
  - assert (glu_ctx_env pred_P Sb {{{ Γ, B@s' }}}) by (econstructor; mauto).
    specialize (IHHx ltac:(econstructor; mauto 2)).
    assert {{ Γ ⊢ A : Sort@s }} by mauto 3.
    inversion_clear IHHx.
    destruct_conjs.
    handle_functional_glu_ctx_env P.
    do 2 eexists.
    + econstructor; try reflexivity; mauto.
    + intros.
      destruct_by_head (@cons_glu_sub_pred P).
      rewrite <- H8 in H11.
      destruct_glu_rel_exp_with_sub.      
      simplify_evals.
      rename a into b.
      rename a0 into a.
      assert {{ Dom a ≈ a ∈ per_sort pred_P s }} as [] by mauto.      
      eapply mk_glu_rel_exp_with_sub''; intuition mauto.      
      handle_functional_glu_sort_elem P.
      
      assert {{ ⊢ Γ, B@s' }} by mauto 3.
      assert {{ Δ ⊢ A[Wk∘σ] : Sort@s }} by (eapply glu_sort_elem_trm_sort_lvl; mauto 3).
      assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] : Sort@s }} as -> by mauto 4.
      assert {{ Γ ⊢ #n : A }} by mauto 4.
      assert {{ Γ, B@s' ⊢ #n[Wk] : A[Wk] }} by mauto 3.
      assert {{ Γ, B@s' ⊢ #n[Wk] ≈ #(S n) : A[Wk] }} by mauto 3.
      assert {{ Δ ⊢ #n[Wk][σ] ≈ #(S n)[σ] : A[Wk∘σ] }} as <-.
      {
        eapply wf_exp_eq_conv' with (A := {{{ A[Wk][σ] }}}); mauto 3.
        eapply wf_exp_eq_sub_cong_typ; mauto 3.
      }
      assert {{ Δ ⊢ #n[Wk∘σ] ≈ #n[Wk][σ] : A[Wk∘σ] }} as <- by mauto 3.
      eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_vlookup : mcpts.


Lemma glu_rel_exp_vlookup_unsorted {P} (pred_P : PredicativeSig P) : forall {Γ x A s},
    {{ #x : A@s ∈ Γ }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u #x : A @ ^(Some s)}}.
Proof.
  intros.
  assert {{ ⟪ pred_P ⟫ Γ ⊩ #x : A @ s}} by mauto 2.
  mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_exp_vlookup_unsorted : mcpts.

Lemma glu_rel_exp_sub {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ σ Δ M A s},
    {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ⊩ M : A @ s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ M[σ] : A[σ] @ s }}.
Proof .
  intros * Hσ HM.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ M : A }} by mauto 3.
  assert (exists s', {{ ⟪ pred_P ⟫ Δ ⊩ A : Sort@s @ s' }}) as [s'] by mauto 3.
  destruct Hσ as [SbΓ [SbΔ]].
  destruct_conjs.
  inversion_clear HM as [? []].
  assert {{ Δ ⊢ A : Sort@s }} by mauto 3.
  eexists; split; mauto.
  intros Δ' τ ρ ?.
  destruct_glu_rel_sub_with_sub.
  handle_functional_glu_ctx_env P.
  rewrite <- H12 in H10.
  destruct_glu_rel_exp_with_sub.
  assert {{ Dom a ≈ a ∈ per_sort pred_P s }} as [] by mauto.
  econstructor; mauto.

  assert {{ Δ' ⊢ A[σ][τ] ≈ A[σ∘τ] : Sort@s }} as -> by (symmetry; mauto 4).
  assert {{ Δ' ⊢ M[σ][τ] ≈ M[σ∘τ] : A[σ∘τ] }} as ->; mauto 3.
  symmetry; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_sub : mcpts.


Lemma glu_rel_exp_sub_typ_unsorted {P} (pred_P : PredicativeSig P) : forall {Γ σ Δ M A s},
    {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ⊩u M : A @ ^(Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u M[σ] : A[σ] @ ^(Some s) }}.
Proof.
  intros * Hσ HM.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ M : A }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Δ ⊩u A : Sort@s @ ^None }} by mauto 3.
  destruct Hσ as [SbΓ [SbΔ]].
  destruct_conjs.  
  inversion_clear HM as [? []].
  assert {{ Δ ⊢ A : Sort@s }} by mauto 3.
  eexists; split; mauto.
  intros Δ' τ ρ ?.
  destruct_glu_rel_sub_with_sub.
  handle_functional_glu_ctx_env P.
  rewrite <- H12 in H10.
  assert (glu_rel_exp_with_sub_unsorted pred_P (Some s) Δ' M A {{{ σ∘τ }}} ρ') by mauto 3.
  inversion_clear H3.
  assert {{ Dom a ≈ a ∈ per_sort pred_P s }} as [] by mauto.
  econstructor; mauto.

  assert {{ Δ' ⊢ A[σ][τ] ≈ A[σ∘τ] : Sort@s }} as -> by (symmetry; mauto 4).
  assert {{ Δ' ⊢ M[σ][τ] ≈ M[σ∘τ] : A[σ∘τ] }} as ->; mauto 3.
  symmetry; mauto 3.  
Qed.

#[export]
Hint Resolve glu_rel_exp_sub_typ_unsorted : mcpts.

Lemma glu_rel_exp_sub_sort_unsorted {P} (pred_P : PredicativeSig P) : forall {Γ σ Δ M A},
    {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }} ->
    {{ ⟪ pred_P ⟫ Δ ⊩u M : A @ ^None }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u M[σ] : A @ ^None }}.
Proof.
  intros * Hσ HM.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ M : A }} by mauto 3.
  (* assert {{ ⟪ pred_P ⟫ Δ ⊩u A : Sort@s @ ^None }} by mauto 3. *)
  destruct Hσ as [SbΓ [SbΔ]].
  destruct_conjs.  
  inversion_clear HM as [? []].
  (* assert {{ Δ ⊢ A : Sort@s }} by mauto 3. *)
  eexists; split; mauto.
  intros Δ' τ ρ ?.
  destruct_glu_rel_sub_with_sub.
  handle_functional_glu_ctx_env P.
  rewrite <- H10 in H8.
  assert (glu_rel_exp_with_sub_unsorted pred_P None Δ' M A {{{ σ∘τ }}} ρ') by mauto 3.
  inversion_clear H2.
  inversion H13; subst.
  simpl_glu_rel.
  inversion H19; subst.
  econstructor; mauto 3.
  eapply H15.
  split; [reflexivity |].
  do 2 eexists; split; mauto 3.

  assert {{ Δ' ⊢ M[σ∘τ] ≈ M[σ][τ] : Sort@s }} as <- by mauto 3.
  eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_sub_sort_unsorted : mcpts.


Lemma glu_rel_exp_conv {P} (pred_P : PredicativeSig P) : forall {Γ M A A' s},
    {{ ⟪ pred_P ⟫ Γ ⊩ M : A @ s }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ M : A' @ s }}.
Proof.
  intros * [Sb [?]] HAA'.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u A ≈ A' : Sort@s }} as [env_relΓ [? ?]] by (eapply completeness_fundamental_exp_eq; mauto 2).
  
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ [ρ']] by (eauto using per_ctx_then_per_env_initial_env).
  destruct_conjs.
  assert (exists elem_rel : relation (domain P),
             rel_typ_unsorted pred_P {{{ Sort@s }}} ρ {{{ Sort@s }}} ρ' elem_rel /\
               rel_exp A ρ A' ρ' elem_rel) as [elem_rel []] by mauto.

  
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp).
  simplify_evals.
  
  assert {{ Γ ⊢s Id ® ρ ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto 2).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  rename m into a.
  rename m' into a'.
  
  eexists; split; [eauto |].
  intros.
  assert (glu_rel_exp_with_sub pred_P s Δ M A σ ρ0) by mauto 2.
  destruct H15.
  simplify_evals.
  handle_functional_glu_sort_elem P.

  assert (env_relΓ ρ0 ρ0) by (eapply glu_ctx_env_per_env; mauto 2).
  assert (exists elem_rel0, rel_typ_unsorted pred_P {{{ Sort@s }}} ρ0 {{{ Sort@s }}} ρ0 elem_rel0 /\ rel_exp A ρ0 A' ρ0 elem_rel0) as [elem_rel0 []] by mauto 2.
  destruct_by_head (@rel_typ_unsorted P).
  destruct_by_head (@rel_exp).
  simplify_evals.
  rename m' into a0'.
  assert (per_typ_elem pred_P (per_sort pred_P s) d{{{ Sort@s }}} d{{{ Sort@s }}}) by (eapply per_typ_sort; reflexivity).
  handle_per_typ_elem_irrel.
  assert (per_sort pred_P s a0' a0') by (transitivity a0; [symmetry |]; mauto 2).
  
  eapply mk_glu_rel_exp_with_sub''; mauto 3.
  intros.
  assert {{ Δ ⊢ A[σ] ≈ A'[σ] : Sort@s }} as <- by mauto 3.

  assert (glu_sort_elem pred_P s typ_rel1 exp_rel1 a0).
  {
    symmetry in H25.
    eapply glu_sort_elem_resp_per_sort; mauto 2.
  }
  eapply glu_sort_elem_exp_conv with (a := a0) (a' := a0) (exp_rel := exp_rel0); mauto.

  assert (typ_rel0 Δ {{{ A [σ] }}}) by (eapply glu_sort_elem_trm_typ; mauto 2).
  handle_functional_glu_sort_elem P.
  eassumption.  
Qed.

#[export]
Hint Resolve glu_rel_exp_conv : mcpts.

Lemma glu_rel_exp_conv_unsorted {P} (pred_P : PredicativeSig P) : forall {Γ M A A' s},
    {{ ⟪ pred_P ⟫ Γ ⊩u M : A @ ^(Some s) }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u M : A' @ ^(Some s) }}.
Proof.
  intros * HMA HAA'.
  assert {{ ⟪ pred_P ⟫ Γ ⊩ M : A @ s }} by mauto 2.
  assert {{ ⟪ pred_P ⟫ Γ ⊩ M : A' @ s }} by mauto 2.
  mauto 2.
Qed.  

#[export]
Hint Resolve glu_rel_exp_conv_unsorted : mcpts.
  
Lemma glu_rel_exp_conv_sort {P} (pred_P : PredicativeSig P) : forall {Γ M A s s'},
    {{ ⟪ pred_P ⟫ Γ ⊩ M : A @ s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ A @ s' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ M : A @ s' }}.
Proof.
  intros * [SbΓ []] [SbΓ' []].
  handle_functional_glu_ctx_env P.
  eexists; split; mauto 2.
  intros.
  assert (SbΓ' Δ σ ρ) by (eapply H4; eassumption).
  destruct_glu_rel_exp_with_sub.
  destruct_glu_rel_typ_with_sub.
  simplify_evals.
  econstructor; mauto 3.

  assert (per_sort pred_P s a a) by mauto 3.
  eapply (glu_sort_elem_exp_conv pred_P H9 H7 H10); mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_exp_conv_sort : mcpts.

Lemma glu_rel_exp_conv_sort_unsorted {P} (pred_P : PredicativeSig P) : forall {Γ M A so so'},
    {{ ⟪ pred_P ⟫ Γ ⊩u M : A @ so }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u A @ so' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩u M : A @ so' }}.
Proof.
  intros * [SbΓ []] [SbΓ' []].
  handle_functional_glu_ctx_env P.
  eexists; split; mauto 2.
  intros.
  assert (SbΓ' Δ σ ρ) by (eapply H4; eassumption).
  (* destruct_glu_rel_exp_with_sub. *)
  assert (glu_rel_exp_with_sub_unsorted pred_P so Δ M A σ ρ) by mauto 2.
  dependent destruction H5.
  - inversion_clear H8.
    (* destruct_glu_rel_typ_with_sub. *)  
    assert (glu_rel_typ_with_sub_unsorted pred_P so' Δ A σ ρ) by mauto 2.
    dependent destruction H8. 
    + inversion_clear H13.
      simpl_glu_rel.
      assert (s = s1).
      {
        assert ({{{ Sort@s }}} = {{{ Sort@s1 }}}).
        {
          transitivity A; [symmetry |]; eassumption.          
        }
        inversion H.
        reflexivity.
      }
      subst.
      econstructor; mauto 3.
      * econstructor; reflexivity.
      * split; [reflexivity |].
        do 2 eexists; split; mauto 3.
    + simpl_glu_rel.
      inversion H9.
      subst.
      econstructor; mauto 3.
      simplify_evals.
      invert_glu_sort_elem H12.
      simpl_glu_rel.
      assert {{ Δ ⊢ M[σ] : Sort@s0 }} by (eapply glu_sort_elem_sort_lvl; mauto 2).
      assert {{ Δ ⊢ M[σ] : Sort@s0[σ] }} by mauto 3.
      repeat split; mauto 2.
      do 2 eexists; split; mauto 2.

  - assert (glu_rel_typ_with_sub_unsorted pred_P so' Δ A σ ρ) by mauto 2.
    dependent destruction H9. 
    + inversion_clear H11.
      subst.
      simplify_evals.
      invert_glu_sort_elem H7.
      simpl_glu_rel.
      econstructor; mauto 3.
      * econstructor; reflexivity.
      * split; [reflexivity |].
        unfold glu_sort_typ_rec in H10.
        destruct H10 as [typ_rel1 [exp_rel1 []]].
        do 2 eexists; split; mauto 3.
    + 
      simplify_evals.
      econstructor; mauto 3.
      assert (per_sort pred_P s a a) by mauto 3.
      eapply (glu_sort_elem_exp_conv pred_P H9 H7 H10); mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_exp_conv_sort_unsorted : mcpts.
