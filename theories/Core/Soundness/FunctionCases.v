From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Completeness Require Import FundamentalTheorem SortCases.
From McPTS.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  SubstitutionCases
  TermStructureCases
  SortCases.
Import Domain_Notations.

Lemma cons_glu_sub_pred_pi_helper {P} (pred_P : PredicativeSig P) : forall {anns Γ Sb Γ' σ ρ A a typ_rel exp_rel Γ'' τ M c s},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ Γ' ⊢s σ ® ρ ∈ Sb }} ->
    {{ Γ ⊢ A : Sort@s }} ->
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ'' ⊢w τ : Γ' }} ->
    {{ Γ'' ⊢ M : A[σ][τ] ® c ∈ exp_rel }} ->
    {{ Γ'' ⊢s σ∘τ,,M ® ρ ↦ c ∈ cons_glu_sub_pred pred_P (so_Some s) Γ A Sb }}.
Proof.
  intros.
  assert {{ Γ'' ⊢s σ∘τ ® ρ ∈ Sb }} by (eapply glu_ctx_env_sub_monotone; mauto 3).
  eapply cons_glu_sub_pred_helper_sorted; only 5: econstructor; mauto 2.
  assert {{ Γ' ⊢s σ : Γ }} by mauto 2.
  assert {{ Γ'' ⊢s τ : Γ' }} by mauto 2.
  enough {{ Γ'' ⊢ A[σ∘τ] ≈ A[σ][τ] : Sort@s }} as ->; mauto 3.
Qed.

Hint Resolve cons_glu_sub_pred_pi_helper : mcpts.

(* This lemma should move to LogicalRelation/Lemmas *)
Lemma glu_typ_elem_exp_rel_glu_sort_elem_typ_rel {P} (pred_P : PredicativeSig P) : forall {so s typ_rel exp_rel IP IEL Γ K A a},
    glu_typ_elem pred_P so typ_rel exp_rel d{{{ Sort @ s }}} ->
    glu_sort_elem pred_P s IP IEL a ->
    exp_rel Γ K A a ->
    IP Γ A.
Proof.
  intros.
  dependent destruction H.
  - simpl_glu_rel.
    handle_functional_glu_sort_elem P.
    eassumption.
  - invert_glu_sort_elem H.
    simpl_glu_rel.
    unfold glu_sort_typ_rec in *.
    deex.
    destruct_conjs.
    handle_functional_glu_sort_elem P.
    eassumption.
Qed.

Lemma glu_rel_exp_pi {P} (pred_P : PredicativeSig P) : forall {anns Γ A B s1 s2 s3 so1 so2} {r : Ru_pi P s1 s2 s3},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A : Sort@s1 @ so1 }} ->
    {{ ⟪ pred_P ⟫ Γ, A @ anns, ^(so_Some s1) ⊩ B : Sort@s2 @ so2 }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ Π r A B : Sort@s3 @ ^so_None }}.
Proof.
  intros * HA HB.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} as [SbΓ'] by mauto.
  assert {{ Γ ⊢ A : Sort@s1 }} by mauto 2.
  inversion_clear HA as [SbΓ []].  
  handle_functional_glu_ctx_env P.
  assert {{ EG Γ, A ∈ glu_ctx_env pred_P ((so_Some s1)::anns) ↘ cons_glu_sub_pred pred_P (so_Some s1) Γ A SbΓ }} by (econstructor; mauto 3; reflexivity).
  assert {{ Γ, A ⊢ B : Sort@s2 }} by mauto 2.
  inversion_clear HB as [SbΓA []].  
  eapply glu_rel_exp_of_typ; [eassumption |].
  intros Γ'; intros.
  assert {{ Γ' ⊢s σ : Γ }} by mauto 3.
  split; mauto 3.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  eexists; split; [mauto 3| ].
  rename m into a.
  assert {{ ⟪ pred_P ⟫ Γ ⊨ Π r A B : Sort@s3 }} as [env_relΓ []]%rel_exp_of_sort_inversion1 by mauto 3 using completeness_fundamental_exp.
  assert {{ ⟪ pred_P ⟫ Γ, A ⊨ B : Sort@s2 }} as [env_relΓA []]%rel_exp_of_sort_inversion1 by mauto 3 using completeness_fundamental_exp.
  match_by_head1 (per_ctx_env pred_P env_relΓA) invert_per_ctx_env.
  pose env_relΓA.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} as equiv_ρ_ρ by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  simplify_evals.
  split; [mauto |].

  intros.  
  unshelve (match_by_head1 (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H)); mauto 2.
  clear_pi_sort_eq_and_pred_rel.
  handle_functional_glu_sort_elem P.
  econstructor; mauto 3.
  - intros Γ'' σ' ?.
    eapply glu_sort_elem_typ_monotone; mauto 3.
    eapply glu_typ_elem_exp_rel_glu_sort_elem_typ_rel; mauto 3.
  - intros Γ'' σ'; intros.
    saturate_weakening_escape.
    handle_per_typ_elem_per_sort_elem_irrel.
    assert {{ Dom ρ ↦ m ≈ ρ ↦ m ∈ env_relΓA }} as HrelΓA by (apply_relation_equivalence; mautosolve 2).
    apply_relation_equivalence.
    assert (rel_exp B d{{{ ρ ↦ m }}} B d{{{ ρ ↦ m }}} (per_sort pred_P s2)) as HrelB by mauto 2.
    destruct HrelB as [? ? ? ? [out_rel]].
    functional_eval_rewrite_clear.
    match goal with
    | _: {{ ⟦ B ⟧ ρ ↦ m ↘ ^?a }} |- _ =>
        rename a into b
    end.    
    assert ((s2 = s3 -> glu_sort_elem pred_P s3 (OP m equiv_m) (OEL m equiv_m) b) /\
              (pred_rel pred_P s2 s3 -> glu_sort_elem pred_P s2 (OP m equiv_m) (OEL m equiv_m) b))
      as [] by mauto 2.
    clear_pi_sort_eq_and_pred_rel.    
    assert {{ Γ'' ⊢ M : A[σ][σ'] }} by mauto 3 using glu_sort_elem_trm_escape.
    assert {{ DG b ∈ glu_sort_elem pred_P s2 ↘ OP m equiv_m ↘ OEL m equiv_m }} by mauto 2.    
    assert {{ Γ'' ⊢ B[σ∘σ',,M] ≈ B[q σ][σ',,M] : Sort@s2 }} as <-.
    {
      gen_presups.
      assert {{ Γ'' ⊢s (q σ)∘(σ' ,, M) ≈ σ∘σ' ,, M : Γ, A }} by (eapply sub_decompose_q; mauto 2).
      transitivity {{{ B[(q σ)∘(σ',,M)] }}}; mauto 3.
      eapply wf_exp_eq_sub_compose_sorted1; mauto 3.
      econstructor; mauto 3.
    }
    assert {{ Γ'' ⊢s (σ∘σ'),,M ® ρ ↦ m ∈ cons_glu_sub_pred pred_P (so_Some s1) Γ A SbΓ }} as Hconspred by mauto 2.
    handle_functional_glu_ctx_env P.
    assert (SbΓA Γ'' {{{ σ∘σ',,M }}} d{{{ ρ ↦ m }}}) as Hconspred' by (apply_predicate_equivalence; eassumption).
    destruct_glu_rel_exp_with_sub.
    simplify_evals.

    eapply (glu_typ_elem_exp_rel_glu_sort_elem_typ_rel pred_P H32); mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_exp_pi : mcpts.

Lemma glu_rel_exp_of_pi {P} (pred_P : PredicativeSig P) : forall {anns Γ M A B Sb s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨ Π r A B : Sort@s3 }} ->
    (forall Γ' σ ρ,
        {{ Γ' ⊢s σ ® ρ ∈ Sb }} ->
        exists a m,
          {{ ⟦ A ⟧ ρ ↘ a }} /\
            {{ ⟦ M ⟧ ρ ↘ m }} /\
            forall (typ_rel : glu_typ_pred P) (exp_rel : glu_exp_pred P), {{ DG Π r a ρ B ∈ glu_sort_elem pred_P s3 ↘ typ_rel ↘ exp_rel }} -> {{ Γ' ⊢ M[σ] : (Π r A B)[σ] ® m ∈ exp_rel }}) ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : Π r A B @ ^(so_Some s3) }}.
Proof.
  intros * ? [env_relΓ] Hbody.
  destruct_conjs.
  eexists; split; mauto 3.
  intros.
  edestruct Hbody as [? [? [? []]]]; mauto 3.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ P).
  simplify_evals.
  inversion_clear H10;
    clear_dups;
    clear_refl_eqs;
    handle_per_sort_elem_irrel;
    clear_dups;
    try rewrite <- per_sort_elem_equation_1 in *.
  - destruct_by_head (@rel_exp P).
    simplify_evals.
    mauto 3.
  - destruct_by_head (@rel_exp P).
    simplify_evals.
    invert_per_sort_elem H7.
    rewrite H8 in H10.
    unfold per_sort_rec in *.
    destruct_conjs.
    assert (exists typ_rel exp_rel, {{ DG Π r x ρ B ∈ glu_sort_elem pred_P s3 ↘ typ_rel ↘ exp_rel }}) as [typ_rel [exp_rel]] by mauto 2.
    econstructor; mauto 2.
    + econstructor; mauto 2.
    + eapply H5; mauto 2.
Qed.

Lemma glu_rel_exp_fn {P} (pred_P : PredicativeSig P) : forall {anns Γ M A B s1 s2 s3 so1 so2 } {r : Ru_pi P s1 s2 s3},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A : Sort@s1 @ so1 }} ->
    {{ ⟪ pred_P ⟫ Γ, A @ anns, ^(so_Some s1) ⊩ B : Sort@s2 @ so2 }} ->
    {{ ⟪ pred_P ⟫ Γ, A @ anns, ^(so_Some s1) ⊩ M : B @ ^(so_Some s2) }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ λ r A B M : Π r A B @ ^(so_Some s3) }}.
Proof.
  intros * HA HB HM.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} as [SbΓ'] by mauto 3.
  assert {{ Γ ⊢ A : Sort@s1 }} by mauto 3.
  inversion_clear HA as [SbΓ []].
  handle_functional_glu_ctx_env P.

  pose (SbΓA := cons_glu_sub_pred pred_P (so_Some s1) Γ A SbΓ).
  assert {{ EG Γ, A ∈ glu_ctx_env pred_P ((so_Some s1)::anns) ↘ SbΓA }} by (econstructor; only 4: econstructor; mauto 4; try reflexivity).
  assert {{ Γ, A ⊢ M : B }} by mauto 3.
  inversion_clear HM as [SbΓA' []].
  handle_functional_glu_ctx_env P.
  rename SbΓA' into SbΓA.
  assert {{ Γ, A ⊢ B : Sort@s2 }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ, A  ⊨ M : B }} as [env_relΓA] by mauto using completeness_fundamental_exp.
  destruct_conjs.
  pose env_relΓA.
  match_by_head (per_ctx_env pred_P env_relΓA) invert_per_ctx_env.
  rename tail_rel into env_relΓ.
  apply_relation_equivalence.
  assert {{ ⟪ pred_P ⟫ Γ ⊨ Π r A B : Sort@s3 }} by mauto using completeness_fundamental_exp.
  eapply glu_rel_exp_of_pi; mauto.
  intros.
  assert {{ Γ' ⊢s σ : Γ }} by mauto 4.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} as equiv_ρ_ρ by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  destruct_rel_typ.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  do 2 eexists; split; [eassumption |].
  split; [mauto 3|].
  
  intros.
  match_by_head @glu_sort_elem ltac:(fun H => directed invert_glu_sort_elem H).
  match_by_head @per_sort_elem ltac:(fun H => directed invert_per_sort_elem H).
  clear_pi_sort_eq_and_pred_rel.
  handle_per_typ_elem_per_sort_elem_irrel.
  apply_relation_equivalence.

  assert {{ Γ', A[σ] ⊢ B[q σ] : Sort@s2 }} by mauto 3.
  assert {{ Γ ⊢ λ r A B M : Π r A B }} by mauto 3.
  assert {{ Γ' ⊢ (λ r A B M)[σ] : (Π r A B)[σ] }} by (eapply wf_exp_sub; mauto 3).
  
  
  apply_predicate_equivalence.
  econstructor; mauto 2; intros.  
  - assert {{ Dom ρ ↦ n ≈ ρ ↦ n' ∈ env_relΓA }}as HrelΓA by (apply_relation_equivalence; mauto 2).
    apply_relation_equivalence.
    assert (exists elem_rel : relation (domain P),
               rel_typ pred_P B d{{{ ρ ↦ n }}} B d{{{ ρ ↦ n' }}} elem_rel /\ rel_exp M d{{{ ρ ↦ n }}} M d{{{ ρ ↦ n' }}} elem_rel) as [elem_rel [[] []]] by mauto 3.
    destruct_rel_mod_eval.
    clear_pi_sort_eq_and_pred_rel.
    simplify_evals.    
    rename a0 into b, a' into b'.
    handle_per_typ_elem_per_sort_elem_irrel.
    econstructor; mauto 3.
    
  - eapply glu_sort_elem_typ_monotone; mauto 2.
    eapply glu_typ_elem_exp_rel_glu_sort_elem_typ_rel; mauto 2.

  - assert {{ Dom ρ ↦ n ≈ ρ ↦ n ∈ env_relΓA }} as HrelΓA by (apply_relation_equivalence; mautosolve 2).
    destruct_rel_mod_eval.
    apply_relation_equivalence.
    assert (exists elem_rel : relation (domain P),
               rel_typ pred_P B d{{{ ρ ↦ n }}} B d{{{ ρ ↦ n }}} elem_rel /\ rel_exp M d{{{ ρ ↦ n }}} M d{{{ ρ ↦ n }}} elem_rel) as [elem_rel [[] []]] by mauto 3.
    simplify_evals.
    rename a0 into b.
    handle_per_typ_elem_per_sort_elem_irrel.
    eexists; split; mauto 3.
    assert ((s2 = s3 -> glu_sort_elem pred_P s3 (OP n equiv_n) (OEL n equiv_n) b) /\ (pred_rel pred_P s2 s3 -> glu_sort_elem pred_P s2 (OP n equiv_n) (OEL n equiv_n) b)) as [] by mauto 2.
    clear_pi_sort_eq_and_pred_rel.
    assert {{ Γ'0 ⊢s σ0 : Γ' }} by mauto 3.
    assert {{ Γ'0 ⊢ N : A[σ][σ0] }} by mauto 2 using glu_sort_elem_trm_escape.
    assert {{ Γ'0 ⊢s σ0,,N : Γ', A[σ] }} by mauto 4.
    assert {{ Γ'0 ⊢s (q σ)∘(σ0,,N) ≈ σ∘σ0,,N : Γ, A }} by (eapply sub_decompose_q; mauto 2).
    assert {{ Γ'0 ⊢ B[(q σ)∘(σ0,,N)] ≈ B[q σ][σ0,,N] : Sort@s2 }} as <- by mauto 3.
    assert {{ Γ'0 ⊢ B[σ∘σ0,,N] ≈ B[(q σ)∘(σ0,,N)] : Sort@s2 }} as <- by mauto 3.

    assert {{ Γ ⊢ Π r A B : Sort@s3 }} by mauto 3.
    assert {{ Γ'0 ⊢s σ∘σ0 : Γ }} by mauto 3.
    assert  {{ Γ'0, A[σ∘σ0] ⊢s q (σ∘σ0) : Γ, A }} by mauto 3. 
    assert {{ Γ'0, A[σ∘σ0] ⊢ M[q (σ∘σ0)] : B[q (σ∘σ0)] }} by mauto 3.
    assert {{ Γ'0 ⊢ (λ r A B M)[σ][σ0] ≈ (λ r A B M)[σ∘σ0] : (Π r A B)[σ∘σ0] }} by (symmetry; mauto 3).
    assert {{ Γ'0 ⊢ (λ r A B M)[σ][σ0] ≈ (λ r A[σ∘σ0] B[q (σ∘σ0)] M[q (σ∘σ0)]) : (Π r A B)[σ∘σ0] }} by mauto 3.
    assert {{ Γ'0 ⊢ (λ r A B M)[σ][σ0] ≈ (λ r A[σ∘σ0] B[q (σ∘σ0)] M[q (σ∘σ0)]) : Π r A[σ∘σ0] B[q (σ∘σ0)] }} by mauto 3.
    assert {{ Γ'0 ⊢ N : A[σ∘σ0] }} by mauto 3.
    assert {{ Γ'0 ⊢ (λ r A B M)[σ][σ0] N ≈ (λ r A[σ∘σ0] B[q (σ∘σ0)] M[q (σ∘σ0)]) N : B[q (σ∘σ0)][Id,,N] }} by mauto 3.

    assert {{ Γ'0 ⊢ (λ r A B M)[σ][σ0] N ≈ (λ r A[σ∘σ0] B[q (σ∘σ0)] M[q (σ∘σ0)]) N : B[q (σ∘σ0)][Id,,N] }} by mauto 2.
    assert {{ Γ'0 ⊢ (λ r A[σ∘σ0] B[q (σ∘σ0)] M[q (σ∘σ0)]) N ≈ M[q (σ∘σ0)][Id,,N] : B[q (σ∘σ0)][Id,,N] }} by (eapply wf_exp_eq_pi_beta'; mauto 3).
    assert {{ Γ'0 ⊢ (λ r A B M)[σ][σ0] N ≈ M[q (σ∘σ0)][Id,,N] : B[q (σ∘σ0)][Id,,N] }} by (etransitivity; eassumption).
    assert {{ Γ'0 ⊢s Id,,N : Γ'0, A[σ∘σ0] }} by mauto 4.
    assert {{ Γ'0, A[σ∘σ0] ⊢s q (σ∘σ0) : Γ, A }} by mauto 2.
    assert {{ Γ'0 ⊢s q (σ∘σ0)∘(Id,,N) ≈ σ∘σ0,,N : Γ, A }} by mauto 3.
    assert {{ Γ'0 ⊢ B[q (σ∘σ0)∘(Id,,N)] ≈ B[q (σ∘σ0)][Id,,N] : Sort@s2 }} by mauto 3.
    assert {{ Γ'0 ⊢ (λ r A B M)[σ][σ0] N ≈ M[q (σ∘σ0)][Id,,N] : B[q (σ∘σ0)∘(Id,,N)] }} by mauto 3.
    assert {{ Γ'0 ⊢ M[q (σ∘σ0)][Id,,N] ≈ M[q (σ∘σ0)∘(Id,,N)] : B[q (σ∘σ0)∘(Id,,N)] }} by (symmetry; mauto 3).
    assert {{ Γ'0 ⊢ (λ r A B M)[σ][σ0] N ≈ M[q (σ∘σ0)∘(Id,,N)] : B[q (σ∘σ0)∘(Id,,N)] }} by (etransitivity; eassumption).
    assert {{ Γ'0 ⊢ M[q (σ∘σ0)∘(Id,,N)] ≈ M[(σ∘σ0),,N] : B[q (σ∘σ0)∘(Id,,N)] }} by mauto 4.
    assert {{ Γ'0 ⊢ (λ r A B M)[σ][σ0] N ≈ M[(σ∘σ0),,N] : B[q (σ∘σ0)∘(Id,,N)] }} by (etransitivity; eassumption).    
    assert {{ Γ'0 ⊢ B[q (σ∘σ0)∘(Id,,N)] ≈ B[σ∘σ0,,N] : Sort@s2 }} by mauto 4.
    assert {{ Γ'0 ⊢ (λ r A B M)[σ][σ0] N ≈ M[(σ∘σ0),,N] : B[σ∘σ0,,N] }} as -> by mauto 2.
    
    assert {{ Γ'0 ⊢ N : A[σ][σ0] ® n ∈ IEL }} by mauto 3.
    assert (SbΓA <∙> cons_glu_sub_pred pred_P (so_Some s1) Γ A SbΓ) by (eapply glu_ctx_env_cons_clean_inversion; mauto 3).
    assert {{ Γ'0 ⊢s (σ∘σ0),,N ® ρ ↦ n ∈ SbΓA }} as HSbΓA by (apply_predicate_equivalence; mauto 3).
    assert (glu_rel_exp_with_sub pred_P (so_Some s2) Γ'0 M B {{{ (σ∘σ0),,N }}} d{{{ ρ ↦ n }}}) as [] by mauto 2.
    simplify_evals.
    match_by_head @glu_typ_elem ltac:(fun H => directed inversion H; subst).
    handle_functional_glu_sort_elem P.
    eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_fn : mcpts.

Lemma glu_rel_exp_app {P} (pred_P : PredicativeSig P) : forall {anns Γ M N A B s1 s2 s3 so1 so2} {r : Ru_pi P s1 s2 s3},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A : Sort@s1 @ so1 }} ->
    {{ ⟪ pred_P ⟫ Γ, A @ anns, ^(so_Some s1) ⊩ B : Sort@s2 @ ^so2 }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : Π r A B @ ^(so_Some s3) }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ N : A @ ^(so_Some s1) }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M N : B[Id,,N] @ ^(so_Some s2) }}.
Proof.
  intros * HA HB HM HN.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} as [SbΓ'] by mauto 3.
  assert {{ Γ ⊢ N : A }} by mauto 2.
  inversion_clear HN as [SbΓ []].
  handle_functional_glu_ctx_env P.
  assert {{ Γ ⊢ A : Sort@s1 }} by mauto 3.
  inversion_clear HA as [SbΓ' []].
  handle_functional_glu_ctx_env P.
  pose (SbΓA := cons_glu_sub_pred pred_P (so_Some s1) Γ A SbΓ).
  
  assert {{ EG Γ, A ∈ glu_ctx_env pred_P ((so_Some s1)::anns) ↘ SbΓA }}. (* This should be proved in a lemma *)
  {
    econstructor; mauto 3; try reflexivity.
    intros.
    rewrite <- H6 in H1.
    mauto 4.
  }
  assert {{ Γ, A ⊢ B : Sort@s2 }} by mauto 2.
  inversion_clear HB as [SbΓA' []].
  handle_functional_glu_ctx_env P.
  rename SbΓA' into SbΓA.
  assert {{ Γ ⊢ M : Π r A B }} by mauto 2.
  inversion_clear HM as [SbΓ'' []].
  handle_functional_glu_ctx_env P.
  eexists; split; [eassumption |].
  intros.
  assert (SbΓ Γ' σ ρ) by intuition. 
  assert (SbΓ' Γ' σ ρ) by intuition.
  destruct_glu_rel_exp_with_sub.  
  simplify_evals.

  match_by_head @glu_typ_elem ltac:(fun H => directed inversion H; subst).
  match_by_head (@glu_sort_elem) ltac:(fun H => directed invert_glu_sort_elem H).
  clear_pi_sort_eq_and_pred_rel.
  handle_functional_glu_sort_elem P.
  rename typ_rel1 into IP, exp_rel1 into IEL, m1 into n.

  match_by_head (@per_sort_elem P) ltac:(fun H => directed invert_per_sort_elem H).
  clear_pi_sort_eq_and_pred_rel.
  handle_per_sort_elem_irrel.

  assert {{ Dom n ≈ n ∈ in_rel0 }} as equiv0_n by (eapply glu_sort_elem_per_elem; revgoals; eassumption).
  assert {{ Dom n ≈ n ∈ in_rel }} as equiv_n by intuition.
  destruct_rel_mod_eval.
  clear_pi_sort_eq_and_pred_rel.
  simplify_evals.
  rename a0 into b.
  assert ((s2 = s3 -> glu_sort_elem pred_P s3 (OP n equiv_n) (OEL n equiv_n) b) /\
    (pred_rel pred_P s2 s3 -> glu_sort_elem pred_P s2 (OP n equiv_n) (OEL n equiv_n) b)) as [] by mauto 2.
  clear_pi_sort_eq_and_pred_rel.

  simpl_glu_rel.
  destruct_rel_mod_app.
  simplify_evals.

  econstructor; mauto 3;
    [econstructor; mauto 2 |].
  
  assert {{ Γ' ⊢s σ : Γ }} by mauto 2.
  assert {{ Γ' ⊢ N[σ] : A[σ] }} by mauto 3.
  assert {{ Γ' ⊢ B[Id,,N][σ] ≈ B[(Id,,N)∘σ] : Sort@s2 }} as -> by (eapply wf_exp_eq_sub_compose_sorted2; mauto 3).
  assert {{ Γ' ⊢s (Id,,N)∘σ ≈ σ,,N[σ] : Γ, A }} by mauto 3.
  assert {{ Γ' ⊢ B[(Id,,N)∘σ] ≈ B[σ,,N[σ]] : Sort@s2 }} as -> by mauto 3.
  
  assert {{ Γ' ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }} as -> by mauto 2.
  assert {{ Γ' ⊢ M[σ][Id] N[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }} as <-.
  {
    assert {{ Γ' ⊢ M[σ][Id] ≈ M[σ] : (Π r A B)[σ] }} by mauto 2.
    assert {{ Γ' ⊢ M[σ][Id] ≈ M[σ] : Π r A[σ] B[q σ] }} by mauto 4.
    assert {{ Γ' ⊢ M[σ][Id] N[σ] ≈ M[σ] N[σ] : B[q σ][Id,,N[σ]] }} as HGoal' by mauto 3.
    assert {{ Γ' ⊢ B[q σ][Id,,N[σ]] ≈ B[σ,,N[σ]] }} by mauto 3.
    eapply wf_exp_eq_conv'; mauto 2.
  }
  assert {{ Γ' ⊢ B[σ,,N[σ]] ≈ B[(σ∘Id),,N[σ]] : Sort@s2 }} as -> by (eapply wf_exp_eq_sub_cong_sorted2; try eassumption; econstructor; mauto 3).

  assert {{ Γ' ⊢s σ∘Id,,N[σ] ® ρ ↦ n ∈ SbΓA }} as Hcons. (* May want to get this from a lemma *)
  {
    match_by_head @glu_ctx_env ltac:(fun H => directed invert_glu_ctx_env H).
    apply_predicate_equivalence.
    eapply cons_glu_sub_pred_helper_sorted; mauto 3.
    - (* TSb Γ' {{{ σ∘Id }}} ρ *)
      assert {{ Γ' ⊢s σ∘Id ≈ σ : Γ }} as -> by mauto 3.
      handle_functional_glu_ctx_env P.
      intuition.
    - (* IEL Γ' {{{ A[σ∘Id] }}} {{{ N[σ] }}} n *) 
      assert {{ Γ' ⊢ A[σ∘Id] ≈ A[σ] : Sort@s1 }} as -> by mauto 3.
      eassumption.
  }
  
  assert (IP Γ' {{{ A[σ] }}}) by (eapply glu_typ_elem_exp_rel_glu_sort_elem_typ_rel; mauto 2).
  assert (IP Γ' {{{ IT[Id] }}}) by mauto 3.
  assert {{ Γ' ⊢ IT[Id] ≈ A[σ] : Sort@s1 }} as HAeq by mauto 2.
  match goal with
  | H : IEL Γ' {{{ A[σ] }}} ?N ?n |- _ => rewrite <- HAeq in H
  end.
  
  assert (exists mn, {{ $| m & n |↘ mn }} /\ {{ Γ' ⊢ M[σ][Id] N[σ] : OT[Id,,N[σ]] ® mn ∈ OEL n equiv_n }}) as [mn' []] by mauto 3.
  simplify_evals.
  
  assert {{ Γ' ⊢ OT[Id,,N[σ]] ® OP n equiv_n }} by (eapply glu_sort_elem_trm_typ; eassumption).  
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  assert (OP n equiv_n Γ' {{{ B[σ∘Id,,N[σ]] }}}) by (eapply @glu_typ_elem_exp_rel_glu_sort_elem_typ_rel with (s := s2); mauto 3).  
  enough {{ Γ' ⊢ B[(σ∘Id),,N[σ]] ≈ OT[Id,,N[σ]] : Sort@s2 }} as -> by eassumption.
  eapply glu_sort_elem_typ_unique_upto_exp_eq; revgoals; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_app : mcpts.
