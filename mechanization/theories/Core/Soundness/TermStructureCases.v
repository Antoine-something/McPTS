From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations.

Lemma presup_glu_rel_exp {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts s Γ M A},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A : s }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ : sts }} /\ (exists s', {{ ⟪ pred_P ⟫ Γ : sts ⊩ A : Sort@s : s' }}).
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

Lemma presup_ctx_glu_rel_exp {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts s Γ M A},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A : s }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ : sts }}.
Proof.
  intros * []%presup_glu_rel_exp;
    eassumption.
Qed.

#[export]
Hint Resolve presup_ctx_glu_rel_exp : mcpts.

Lemma presup_typ_glu_rel_exp {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts s Γ M A},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A : s }} ->
    exists s', {{ ⟪ pred_P ⟫ Γ : sts ⊩ A : Sort@s : s' }}.
Proof.
  intros * []%presup_glu_rel_exp;
    eassumption.
Qed.

#[export]
Hint Resolve presup_typ_glu_rel_exp : mcpts.

Lemma glu_rel_exp_vlookup {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts Γ x A},
    {{ #x : A ∈ Γ }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ : sts }} ->
    exists s,
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ #x : A : s}}.
Proof.
  intros * Hx.
  gen sts.
  induction Hx; intros * [Sb];
    match_by_head1 (@glu_ctx_env P) ltac:(fun H => invert_glu_ctx_env H).
  
  (* intros * [Sb] Hx. gen Sb. *)
  (* induction Hx; intros; *)
  (*   match_by_head1 (@glu_ctx_env P) ltac:(fun H => invert_glu_ctx_env H). *)
  - exists s.
    eexists.
    split; [econstructor |]; try reflexivity; mauto.
    intros.
    destruct_by_head (@cons_glu_sub_pred P).
    econstructor; mauto.
  - assert (glu_ctx_env pred_P {{{ sts, s }}} Sb {{{ Γ, B }}}) by (econstructor; mauto).
    assert (exists s, {{ ⟪ pred_P ⟫ Γ : sts ⊩ #n : A : s}}) as [s' Hn].
    {
      eapply IHHx.
      econstructor; eauto.
    }
    assert (exists s, {{ Γ ⊢ A : Sort@s }}) as [s''] by (gen_presups; mauto 3).
    inversion_clear Hn.
    (* invert_glu_rel_exp Hn. *)
    destruct_conjs.
    handle_functional_glu_ctx_env P.
    do 2 eexists.
    split.
    + econstructor; try reflexivity; mauto.
   
      (* intros. *)
      (* dependent destruction H3. *)
      (* handle_functional_glu_ctx_env P. *)
      (* eapply H5. *)
      (* eassumption. *)
    + (* eexists. *)
      intros.
      destruct_by_head (@cons_glu_sub_pred P).
      rewrite <- H8 in H11.
      destruct_glu_rel_exp_with_sub.      
      simplify_evals.
      rename a into b.
      rename a0 into a.
      assert {{ Dom a ≈ a ∈ per_sort pred_P s' }} as [] by mauto.      
      eapply mk_glu_rel_exp_with_sub''; intuition mauto.      
      handle_functional_glu_sort_elem P.
      
      assert {{ ⊢ Γ, B }} by mauto 3.
      assert {{ Δ ⊢ A[Wk∘σ] : Sort@s' }} by (eapply glu_sort_elem_trm_sort_lvl; mauto 3).
      assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk∘σ] : Sort@s' }} as ->.
      {
        assert (exists Δ0 K0, {{ Δ ⊢s Wk∘σ : Δ0 }} /\ {{ Δ0 ⊢ A : K0 }} /\ {{ Δ ⊢ K0[Wk∘σ] ≈ Sort@s' }}) as [Δ0 [K0 [? []]]] by mauto 2.
        assert (exists Δ1, {{ Δ ⊢s σ : Δ1 }} /\ {{ Δ1 ⊢s Wk : Δ0 }}) as [Δ1 []] by mauto 2.
        eapply wf_exp_eq_conv'; mauto 3.
      }                                                                 
      assert {{ Γ ⊢ #n : A }} by mauto 4.
      assert {{ Γ, B ⊢ #n[Wk] : A[Wk] }} by mauto 3.
      assert {{ Γ, B ⊢ #n[Wk] ≈ #(S n) : A[Wk] }} by mauto 3.
      assert {{ Δ ⊢ #n[Wk][σ] ≈ #(S n)[σ] : A[Wk∘σ] }} as <- by (eapply wf_exp_eq_conv; mauto).
      assert {{ Δ ⊢ #n[Wk∘σ] ≈ #n[Wk][σ] : A[Wk∘σ] }} as <- by mauto 3.
      eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_vlookup : mcpts.

Lemma glu_rel_exp_sub {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts Γ σ Δ sts' M A s},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩s σ : Δ : sts' }} ->
    {{ ⟪ pred_P ⟫ Δ : sts' ⊩ M : A : s }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M[σ] : A[σ] : s }}.
Proof .
  intros * Hσ HM.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Δ ⊢ M : A }} by mauto 3.
  assert (exists s', {{ ⟪ pred_P ⟫ Δ : sts' ⊩ A : Sort@s : s' }}) as [s'] by mauto 3.
  destruct Hσ as [SbΓ [SbΔ]].
  destruct_conjs.
  inversion_clear HM as [? []].
  (* invert_glu_rel_exp HM. *)
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


Lemma glu_rel_exp_conv' {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts Γ M A A' s},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A : s }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A' : s }}.
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



(* Lemma glu_rel_exp_conv {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts Γ M A A' s}, *)
(*     {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A : s }} -> *)
(*     {{ Γ ⊢ A ≈ A' }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A' : s }}. *)
(* Proof. *)
(*   intros * [Sb [?]] HAA'. *)
(*   assert {{ ⟪ pred_P ⟫ Γ ⊨ A ≈ A' }} as [env_relΓ [? ?]] by (eapply completeness_fundamental_typ_eq; mauto 2). *)
  
(*   assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ [ρ']] by (eauto using per_ctx_then_per_env_initial_env). *)
(*   destruct_conjs. *)
(*   assert (exists elem_rel : relation (domain P), *)
(*              rel_typ_unsorted pred_P A ρ A' ρ' elem_rel) as [elem_rel] by mauto. *)
  
  
(*   destruct_by_head (@rel_typ_unsorted P). *)
(*   simplify_evals. *)
  
(*   assert {{ Γ ⊢s Id ® ρ ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto 2). *)
(*   destruct_glu_rel_exp_with_sub. *)
(*   simplify_evals. *)
  
(*   eexists; split; [eauto |]. *)
(*   intros. *)
(*   assert (glu_rel_exp_with_sub pred_P s Δ M A σ ρ0) by mauto 2. *)
(*   destruct H14. *)
(*   simplify_evals. *)
(*   handle_functional_glu_sort_elem P. *)

(*   assert (env_relΓ ρ0 ρ0) by (eapply glu_ctx_env_per_env; mauto 2). *)
(*   assert (exists elem_rel0, rel_typ_unsorted pred_P A ρ0 A' ρ0 elem_rel0) as [elem_rel0] by mauto 2. *)
(*   destruct_by_head (@rel_typ_unsorted P). *)
(*   simplify_evals. *)
(*   assert (per_typ_elem pred_P (per_sort pred_P s) d{{{ Sort@s }}} d{{{ Sort@s }}}) by (eapply per_typ_sort; reflexivity). *)
(*   handle_per_typ_elem_irrel. *)
(*   assert (per_sort pred_P s a0 a0) as [R] by mauto 3. *)
(*   assert (per_sort_elem pred_P s elem_rel0 a0 a'0) by mauto 3. *)
(*   assert (per_sort_elem pred_P s elem_rel0 a'0 a'0) by (transitivity a0; [symmetry |]; mauto 2). *)
  
(*   eapply mk_glu_rel_exp_with_sub''; mauto 3. *)
(*   intros. *)
(*   assert {{ Δ ⊢ A[σ] ≈ A'[σ] : Sort@s }} as <- by admit. *)

(*   assert (glu_sort_elem pred_P s typ_rel1 exp_rel1 a0). *)
(*   { *)
(*     symmetry in H23. *)
(*     eapply glu_sort_elem_resp_per_sort; mauto 3. *)
(*   } *)
(*   eapply glu_sort_elem_exp_conv with (a := a0) (a' := a0) (exp_rel := exp_rel0); mauto. *)

(*   assert (typ_rel0 Δ {{{ A [σ] }}}) by (eapply glu_sort_elem_trm_typ; mauto 2). *)
(*   handle_functional_glu_sort_elem P. *)
(*   eassumption.   *)
(* Qed. *)


  
(* Lemma glu_rel_exp_conv {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts s Γ M A A' }, *)
(*     {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A : s }} -> *)
(*     {{ Γ ⊢ A ≈ A' }} -> *)
(*     {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : A' : s }}. *)
(* Proof. *)
(*   intros. *)
(*   enough {{ Γ ⊢ A ≈ A' : Sort@s }} by (eapply glu_rel_exp_conv'; mauto). *)
(*   destruct H as [Sb [?]]. *)
  
(*   assert {{ ⟪ pred_P ⟫ Γ ⊨ A ≈ A' }} as [env_relΓ [? ?]] by (eapply completeness_fundamental_typ_eq; mauto 2).   *)
(*   assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ [ρ']] by (eauto using per_ctx_then_per_env_initial_env). *)
(*   destruct_conjs. *)
(*   assert (exists elem_rel : relation (domain P), rel_typ_unsorted pred_P A ρ A' ρ' elem_rel) by mauto 2. *)
(*   destruct_conjs. *)
(*   destruct_rel_typ_unsorted. *)
  
(*   assert {{ Γ ⊢s Id ® ρ ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto 2). *)
(*   destruct_glu_rel_exp_with_sub. *)
(*   simplify_evals. *)
(*   assert (per_sort pred_P s a a) as [R] by mauto 2. *)
(*   assert (per_sort_elem pred_P s H7 a a') by mauto 3. *)
(*   assert (glu_sort_elem pred_P s typ_rel exp_rel a') by (eapply glu_sort_elem_resp_per_sort_elem with (typ_rel := typ_rel) (exp_rel := exp_rel); mauto 3). *)

(*   assert {{ Γ ⊢ A[Id] ≈ A : Sort@s }} by mauto 4. *)
(*   assert {{ Γ ⊢ A : Sort@s }} by mauto 3. *)
  
  
