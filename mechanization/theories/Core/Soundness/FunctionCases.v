From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import  Base.
From McPTS.Core.Completeness Require Import FundamentalTheorem SortCases.
From McPTS.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  SubstitutionCases
  TermStructureCases
  SortCases.
Import Domain_Notations.

Lemma cons_glu_sub_pred_pi_helper {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ Sb Γ' σ ρ A a typ_rel exp_rel Γ'' τ M c s},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ Γ' ⊢s σ ® ρ ∈ Sb }} ->
    {{ Γ ⊢ A : Sort@s }} ->
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ'' ⊢w τ : Γ' }} ->
    {{ Γ'' ⊢ M : A[σ][τ] ® c ∈ exp_rel }} ->
    {{ Γ'' ⊢s σ∘τ,,M ® ρ ↦ c ∈ cons_glu_sub_pred pred_P s Γ A Sb }}.
Proof.
  intros.
  assert {{ Γ'' ⊢s σ∘τ ® ρ ∈ Sb }} by (eapply glu_ctx_env_sub_monotone; mauto 3).
  eapply cons_glu_sub_pred_helper; try eassumption.
  assert {{ Γ' ⊢s σ : Γ }} by mauto 2.
  assert {{ Γ'' ⊢s τ : Γ' }} by mauto 2.
  enough {{ Γ'' ⊢ A[σ∘τ] ≈ A[σ][τ] : Sort@s }} as ->; mauto 3.
Qed.

(* #[local] *)
Hint Resolve cons_glu_sub_pred_pi_helper : mcpts.

Lemma glu_rel_exp_pi {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ A B s1 s2 s3 s1' s2' s3'} {r : Ru P s1 s2 s3},
    Ax P s3 s3' ->
    {{ ⟪ pred_P ⟫ Γ ⊩ A : Sort@s1 > s1'}} ->
    {{ ⟪ pred_P ⟫ Γ, A@s1 ⊩ B : Sort@s2 > s2' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ Π r A B : Sort@s3 > s3' }}.
Proof.
  intros * Hax HA HB.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ }} as [SbΓ] by mauto.
  assert {{ Γ ⊢ A : Sort@s1 }} by mauto.
  inversion_clear HA as [SbΓ' []].
  handle_functional_glu_ctx_env P.
  rename SbΓ' into SbΓ.
  assert {{ EG Γ, A@s1 ∈ glu_ctx_env pred_P ↘ cons_glu_sub_pred pred_P s1 Γ A SbΓ }} by (econstructor; mauto; reflexivity).
  assert {{ Γ, A@s1 ⊢ B : Sort@s2 }} by mauto.
  inversion_clear HB as [SbΓA []].
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  split; mauto 3.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.  
  match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
  assert (typ_rel Δ {{{ Sort@s1[σ] }}}) by (eapply glu_sort_elem_trm_typ; mauto 3).  
  handle_functional_glu_sort_elem P.
  unfold sort_glu_typ_pred in *.
  unfold sort_glu_exp_pred' in *.
  unfold glu_sort_typ_rec in *.
  destruct_conjs.
  rename m into a.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u Π r A B : Sort@s3 }} as [env_relΓ]%rel_exp_unsorted_of_typ_inversion1 by mauto 3 using completeness_fundamental_exp.
  assert {{ ⟪ pred_P ⟫ Γ, A@s1 ⊨u B : Sort@s2 }} as [env_relΓA]%rel_exp_unsorted_of_typ_inversion1 by mauto 3 using completeness_fundamental_exp.
  destruct_conjs.
  match_by_head1 (per_ctx_env pred_P env_relΓA) invert_per_ctx_env.
  pose env_relΓA.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  simplify_evals.
  eexists; repeat split; mauto.
  intros.
  match_by_head1 (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
  rename x into OP, x0 into OEL.
  rename H11 into IP, H13 into IEL.
  (* assert (glu_sort_elem pred_P s1 IP IEL a). *)
  (* { *)
  (*   assert ((pred_rel pred_P s1 s3 \/ s1 = s3) /\ (pred_rel pred_P s2 s3 \/ s2 = s3)) as [pr1 pr2] by (eapply ord_ru; mauto 2). *)
  (*   destruct glu_a as [glu_a_eq glu_a_rel]. *)
  (*   destruct pr1; *)
  (*     [eapply glu_a_rel | subst; eapply glu_a_eq]; mauto 2.     *)
  (* } *)
  (* assert (forall c (equiv_c : in_rel c c) b, *)
  (*            {{ ⟦ B ⟧ ρ ↦ c ↘ b }} -> *)
  (*            glu_sort_elem pred_P s2 (OP c equiv_c) (OEL c equiv_c) b). *)
  (* { *)
  (*   assert ((pred_rel pred_P s1 s3 \/ s1 = s3) /\ (pred_rel pred_P s2 s3 \/ s2 = s3)) as [pr1 pr2] by (eapply ord_ru; mauto 2). *)
  (*   intros. *)
  (*   assert ((s2 = s3 -> glu_sort_elem pred_P s3 (OP c equiv_c) (OEL c equiv_c) b) /\ *)
  (*             (pred_rel pred_P s2 s3 -> glu_sort_elem pred_P s2 (OP c equiv_c) (OEL c equiv_c) b)) as [glu_b_eq glu_b_rel] by mauto 2. *)
  (*   destruct pr2; *)
  (*     [eapply glu_b_rel | subst; eapply glu_b_eq]; mauto 2. *)
  (* } *)
  
  assert (per_sort_elem pred_P s1 (head_rel ρ ρ H21) a a) by mauto 2.
  handle_per_sort_elem_irrel.
  handle_functional_glu_sort_elem P.
    
  econstructor; mauto 3.  
  - intros.
    eapply glu_sort_elem_typ_monotone; mauto 3.
  - intros Δ' τ **.
    assert {{ Δ' ⊢s τ : Δ }} by mauto 2.
    assert {{ Dom ρ ↦ m ≈ ρ ↦ m ∈ env_relΓA }} as HrelΓA by (apply_relation_equivalence; mautosolve 2).
    apply_relation_equivalence.
    (on_all_hyp: fun H => destruct (H _ _ HrelΓA)).
    destruct_by_head (@per_sort P).
    functional_eval_rewrite_clear.
    match goal with
    | _: {{ ⟦ B ⟧ ρ ↦ m ↘ ^?a }} |- _ =>
        rename a into b
    end.
    assert {{ Δ' ⊢ M : A[σ][τ] }} by mauto 3 using glu_sort_elem_trm_escape.
    assert {{ DG b ∈ glu_sort_elem pred_P s2 ↘ OP m equiv_m ↘ OEL m equiv_m }} by mauto 2.
    assert {{ Δ' ⊢ B[σ∘τ,,M] ≈ B[q σ][τ,,M] : Sort@s2 }} as <-.
    {
      gen_presups.
      assert {{ Δ' ⊢s q σ ∘ (τ ,, M) ≈ σ ∘ τ ,, M : Γ, A@s1 }} by (eapply sub_decompose_q; mauto 2).
      transitivity {{{ B[(q σ)∘(τ,,M)] }}}.
      - eapply wf_exp_eq_sub_cong_sort; mauto 3.
      - eapply exp_eq_sub_compose_typ_sort; mauto 3.
        + eapply sub_q; mauto 2.
        + econstructor; mauto 2.
    }
    assert {{ Δ' ⊢s (σ∘τ),,M ® ρ ↦ m ∈ cons_glu_sub_pred pred_P s1 Γ A SbΓ }} as Hconspred by mauto 2.
    handle_functional_glu_ctx_env P.
    assert (SbΓA Δ' {{{ σ∘τ,,M }}} d{{{ ρ ↦ m }}}) as Hconspred' by (eapply H30; eassumption).
    (on_all_hyp: fun H => destruct (H _ _ _ Hconspred')).
    simplify_evals.
    match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
    apply_predicate_equivalence.
    unfold sort_glu_exp_pred' in *.
    unfold glu_sort_typ_rec in *.
    destruct_conjs.
    handle_functional_glu_sort_elem P.
    eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_pi : mcpts.

Lemma glu_rel_exp_of_pi {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ M A B Sb s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} ->
    {{ ⟪ pred_P ⟫ Γ ⊨u Π r A B : Sort@s3 }} ->
    (forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        exists a m,
          {{ ⟦ A ⟧ ρ ↘ a }} /\
            {{ ⟦ M ⟧ ρ ↘ m }} /\
            forall (typ_rel : glu_typ_pred P) (exp_rel : glu_exp_pred P), {{ DG Π r a ρ B ∈ glu_sort_elem pred_P s3 ↘ typ_rel ↘ exp_rel }} -> {{ Δ ⊢ M[σ] : (Π r A B)[σ] ® m ∈ exp_rel }}) ->
    {{ ⟪ pred_P ⟫ Γ ⊩ M : Π r A B > s3 }}.
Proof.
  intros * ? [env_relΓ] Hbody.
  destruct_conjs.
  eexists; split; mauto 3.
  intros.
  edestruct Hbody as [? [? [? []]]]; mauto 3.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
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
    eapply H5; mauto 2.
Qed.

Lemma glu_rel_exp_fn_helper {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ M A B s1 s2 s3 s1' s2' } {r : Ru P s1 s2 s3},
    {{ ⟪ pred_P ⟫ Γ ⊩ A : Sort@s1 > s1' }} ->
    {{ ⟪ pred_P ⟫ Γ, A@s1 ⊩ B : Sort@s2 > s2' }} ->
    {{ ⟪ pred_P ⟫ Γ, A@s1 ⊩ M : B > s2 }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ λ r A M : Π r A B > s3 }}.
Proof.
  intros * HA HB HM.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ }} as [SbΓ] by mauto 3.
  assert {{ Γ ⊢ A : Sort@s1 }} by mauto 3.
  inversion_clear HA as [SbΓ' []].  
  handle_functional_glu_ctx_env P.
  rename SbΓ' into SbΓ.
  pose (SbΓA := cons_glu_sub_pred pred_P s1 Γ A SbΓ).
  assert {{ EG Γ, A@s1 ∈ glu_ctx_env pred_P ↘ SbΓA }} by (econstructor; mauto 3; reflexivity).
  assert {{ Γ, A@s1 ⊢ M : B }} by mauto 3.
  inversion_clear HM as [SbΓA' []].
  handle_functional_glu_ctx_env P.
  rename SbΓA' into SbΓA.
  assert {{ Γ, A@s1 ⊢ B : Sort@s2 }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ, A@s1 ⊨u M : B }} as [env_relΓA] by mauto using completeness_fundamental_exp.
  destruct_conjs.
  pose env_relΓA.
  match_by_head (per_ctx_env pred_P env_relΓA) invert_per_ctx_env.
  rename tail_rel into env_relΓ.
  apply_relation_equivalence.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u Π r A B : Sort@s3 }} by mauto using completeness_fundamental_exp.
  eapply glu_rel_exp_of_pi; mauto.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 4.
  assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
  destruct_rel_typ_unsorted.
  destruct_rel_typ.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
  apply_predicate_equivalence.
  unfold sort_glu_exp_pred' in *.
  unfold glu_sort_typ_rec in *.
  destruct_conjs.
  handle_functional_glu_sort_elem P.
  do 2 eexists; repeat split; mauto.
  intros.
  match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
  rename H19 into IP, H20 into IEL, x into OP, x0 into OEL.
  (* assert (glu_sort_elem pred_P s1 IP IEL a). *)
  (* { *)
  (*   assert ((pred_rel pred_P s1 s3 \/ s1 = s3) /\ (pred_rel pred_P s2 s3 \/ s2 = s3)) as [pr1 pr2] by (eapply ord_ru; mauto 2). *)
  (*   destruct glu_a as [glu_a_eq glu_a_rel]. *)
  (*   destruct pr1; *)
  (*     [eapply glu_a_rel | subst; eapply glu_a_eq]; mauto 2.     *)
  (* } *)
  (* assert (forall c (equiv_c : in_rel c c) b, *)
  (*            {{ ⟦ B ⟧ ρ ↦ c ↘ b }} -> *)
  (*            glu_sort_elem pred_P s2 (OP c equiv_c) (OEL c equiv_c) b). *)
  (* { *)
  (*   assert ((pred_rel pred_P s1 s3 \/ s1 = s3) /\ (pred_rel pred_P s2 s3 \/ s2 = s3)) as [pr1 pr2] by (eapply ord_ru; mauto 2). *)
  (*   intros. *)
  (*   assert ((s2 = s3 -> glu_sort_elem pred_P s3 (OP c equiv_c) (OEL c equiv_c) b) /\ *)
  (*             (pred_rel pred_P s2 s3 -> glu_sort_elem pred_P s2 (OP c equiv_c) (OEL c equiv_c) b)) as [glu_b_eq glu_b_rel] by mauto 2. *)
  (*   destruct pr2; *)
  (*     [eapply glu_b_rel | subst; eapply glu_b_eq]; mauto 2. *)
  (* } *)
  assert (per_typ_elem pred_P (head_rel ρ ρ H11) a a) by mauto 2.
  handle_per_typ_elem_irrel.
  handle_functional_glu_sort_elem P.
  match goal with
  | H : {{ DG a ∈ glu_sort_elem ?pred_P ?i ↘ ?P ↘ ?El }} |- _ =>
      rename P into typ_rel_a;
      rename El into exp_rel_a
  end.
  match_by_head (@per_sort_elem P) ltac:(fun H => directed invert_per_sort_elem H).
  apply_relation_equivalence.
  assert {{ Δ, A[σ]@s1 ⊢ B[q σ] : Sort@s2 }} by mauto 3.
  econstructor; mauto 4; intros.
  - assert {{ Dom ρ ↦ n ≈ ρ ↦ n' ∈ env_relΓA }} as HrelΓA by (apply_relation_equivalence; mautosolve 3).
    destruct_rel_mod_eval.
    apply_relation_equivalence.
    assert (exists elem_rel : relation (domain P),
               rel_typ_unsorted pred_P B d{{{ ρ ↦ n }}} B d{{{ ρ ↦ n' }}} elem_rel /\ rel_exp M d{{{ ρ ↦ n }}} M d{{{ ρ ↦ n' }}} elem_rel) as [? [[] []]] by mauto 3.
    simplify_evals.
    assert (per_typ_elem pred_P (x n n' equiv_n_n') a0 a') by mauto 2.
    handle_per_typ_elem_irrel.
    econstructor; mauto 3.
  - eapply glu_sort_elem_typ_monotone; mauto 2.
  - assert {{ Dom ρ ↦ n ≈ ρ ↦ n ∈ env_relΓA }} as HrelΓA by (apply_relation_equivalence; mautosolve 2).
    destruct_rel_mod_eval.
    apply_relation_equivalence.
    (on_all_hyp: fun H => destruct (H _ _ HrelΓA) as [? [[] []]]).
    handle_per_sort_elem_irrel.
    eexists; split; mauto 3.
    match goal with
    | _: {{ ⟦ B ⟧ ρ ↦ n ↘ ^?a }} |- _ =>
        rename a into b
    end.
    assert {{ DG b ∈ glu_sort_elem pred_P s2 ↘ OP n equiv_n ↘ OEL n equiv_n }} by mauto 3.
    assert {{ Δ0 ⊢s σ0 : Δ }} by mauto 3.
    assert {{ Δ0 ⊢ N : A[σ][σ0] }} by mauto 2 using glu_sort_elem_trm_escape.
    assert {{ Δ0 ⊢ B[σ∘σ0,,N] ≈ B[q σ][σ0,,N] : Sort@s2 }} as <-.
    {
      gen_presups.
      assert {{ Δ0 ⊢s q σ ∘ (σ0 ,, N) ≈ σ ∘ σ0 ,, N : Γ, A@s1 }} by (eapply sub_decompose_q; mauto 2).
      transitivity {{{ B[(q σ)∘(σ0,,N)] }}}; mauto 3.
      eapply wf_exp_eq_sub_compose_sort; mauto 3.
    }    

    assert {{ Δ0 ⊢ (λ r A M)[σ][σ0] N ≈ M[(σ∘σ0),,N] : B[σ∘σ0,,N] }} as ->.
    {
      assert {{ Δ0 ⊢s σ∘σ0 : Γ }} by mauto 3.
      assert {{ Δ0, A[σ∘σ0]@s1 ⊢ M[q (σ∘σ0)] : B[q (σ∘σ0)] }} by mauto 3.
      assert {{ Δ0 ⊢ (λ r A M)[σ][σ0] ≈ (λ r A M)[σ∘σ0] : (Π r A B)[σ∘σ0] }} by (symmetry; mauto 4).
      assert {{ Δ0 ⊢ (λ r A M)[σ][σ0] ≈ (λ r A[σ∘σ0] M[q (σ∘σ0)]) : (Π r A B)[σ∘σ0] }} by mauto 3.
      assert {{ Δ0 ⊢ (λ r A M)[σ][σ0] ≈ (λ r A[σ∘σ0] M[q (σ∘σ0)]) : Π r A[σ∘σ0] B[q (σ∘σ0)] }} by mauto 4.
      assert {{ Δ0 ⊢ N : A[σ∘σ0] }} by mauto 4.
      assert {{ Δ0 ⊢ (λ r A M)[σ][σ0] N ≈ (λ r A[σ∘σ0] M[q (σ∘σ0)]) N : B[q (σ∘σ0)][Id,,N] }} by mauto 3.
      assert {{ Δ0 ⊢ (λ r A M)[σ][σ0] N ≈ M[q (σ∘σ0)][Id,,N] : B[q (σ∘σ0)][Id,,N] }}.
      {
        transitivity {{{ (λ r A[σ∘σ0] M[q (σ∘σ0)]) N }}}; mauto 2.
        eapply wf_exp_eq_pi_beta'; mauto 3.
      }
      transitivity {{{ M[q (σ∘σ0)][Id,,N] }}}; [mauto 4 |].
      assert {{ Δ0 ⊢s Id,,N : Δ0, A[σ∘σ0]@s1 }} by mauto 3.
      assert {{ Δ0, A[σ∘σ0]@s1 ⊢s q (σ∘σ0) : Γ, A@s1 }} by mauto 2.
      assert {{ Δ0 ⊢s q (σ∘σ0)∘(Id,,N) ≈ σ∘σ0,,N : Γ, A@s1 }} by mauto 2.
      assert {{ Δ0 ⊢ B[q (σ∘σ0)∘(Id,,N)] ≈ B[σ∘σ0,,N] : Sort@s2 }} as <- by mauto 4.
      transitivity {{{ M[q (σ∘σ0)∘(Id,,N)] }}}; mauto 3.
    }
    assert {{ Δ0 ⊢ N : A[σ][σ0] ® n ∈ exp_rel_a }} by mauto 3.
    assert {{ Δ0 ⊢s (σ∘σ0),,N ® ρ ↦ n ∈ SbΓA }} as HSbΓA.
    {
      assert (SbΓA <∙> cons_glu_sub_pred pred_P s1 Γ A SbΓ) by (eapply glu_ctx_env_cons_clean_inversion; mauto 3).
      eapply H36.
      mauto 3.
    }
    (on_all_hyp: fun H => destruct (H _ _ _ HSbΓA)).
    simplify_evals.
    match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
    handle_functional_glu_sort_elem P.
    mauto 3.
Qed.

Lemma glu_rel_exp_fn {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ M A B s1 s2 s3 s1'} {r : Ru P s1 s2 s3},
    {{ ⟪ pred_P ⟫ Γ ⊩ A : Sort@s1 > s1' }} ->
    {{ ⟪ pred_P ⟫ Γ, A@s1 ⊩ M : B > s2 }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ λ r A M : Π r A B > s3 }}.
Proof.
  intros * HA HM.
  assert (exists s2', {{ ⟪ pred_P ⟫ Γ, A@s1 ⊩ B : Sort@s2 > s2' }}) as [s2'] by mauto 3.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ, A@s1 }} by mauto 3.
  mauto 3 using glu_rel_exp_fn_helper.
Qed.

#[export]
Hint Resolve glu_rel_exp_fn : mcpts.

Lemma glu_rel_exp_app_helper {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ M N A B s1 s2 s3 s1' s2'} {r : Ru P s1 s2 s3},
    {{ ⟪ pred_P ⟫ Γ ⊩ A : Sort@s1 > s1' }} ->
    {{ ⟪ pred_P ⟫ Γ, A@s1 ⊩ B : Sort@s2 > s2' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ M : Π r A B > s3 }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ N : A > s1 }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ M N : B[Id,,N] > s2 }}.
Proof.
  intros * HA HB HM HN.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ }} as [SbΓ] by mauto 3.
  assert (exists s3', {{ ⟪ pred_P ⟫ Γ ⊩ Π r A B : Sort@s3 > s3' }}) as [s3'] by mauto 4.
  assert {{ Γ ⊢ N : A }} by mauto 2.
  inversion_clear HN as [SbΓ' []].
  handle_functional_glu_ctx_env P.
  rename SbΓ' into SbΓ.
  assert {{ Γ ⊢ A : Sort@s1 }} by mauto 3.
  inversion_clear HA as [SbΓ' []].
  handle_functional_glu_ctx_env P.
  pose (SbΓA := cons_glu_sub_pred pred_P s1 Γ A SbΓ).
  assert {{ EG Γ, A@s1 ∈ glu_ctx_env pred_P ↘ SbΓA }}.
  {
    econstructor; mauto 3; try reflexivity.
    intros.
    eapply glu_rel_exp_typ_implies_glu_rel_typ.
    eapply H5.
    eapply H7.
    eassumption.
  }
  assert {{ Γ, A@s1 ⊢ B : Sort@s2 }} by mauto 2.
  inversion_clear HB as [SbΓA' []].
  handle_functional_glu_ctx_env P.
  rename SbΓA' into SbΓA.
  assert {{ Γ ⊢ M : Π r A B }} by mauto 2.
  inversion_clear HM as [SbΓ'' []].
  handle_functional_glu_ctx_env P.
  eexists; split; [eassumption |].
  intros.
  assert (SbΓ Δ σ ρ) by (eapply H7; mauto 2).
  assert (SbΓ' Δ σ ρ) by (eapply H13; mauto 2).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head (@glu_sort_elem) ltac:(fun H => directed invert_glu_sort_elem H).

  assert (glu_sort_elem pred_P s1 IP IEL a).
  {
    assert ((pred_rel pred_P s1 s3 \/ s1 = s3) /\ (pred_rel pred_P s2 s3 \/ s2 = s3)) as [pr1 pr2] by (eapply ord_ru; mauto 2).
    destruct glu_a as [glu_a_eq glu_a_rel].
    destruct pr1;
      [eapply glu_a_rel | subst; eapply glu_a_eq]; mauto 2.    
  }
  assert (forall c (equiv_c : in_rel c c) b,
             {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
             glu_sort_elem pred_P s2 (OP c equiv_c) (OEL c equiv_c) b).
  {
    assert ((pred_rel pred_P s1 s3 \/ s1 = s3) /\ (pred_rel pred_P s2 s3 \/ s2 = s3)) as [pr1 pr2] by (eapply ord_ru; mauto 2).
    intros.
    assert ((s2 = s3 -> glu_sort_elem pred_P s3 (OP c equiv_c) (OEL c equiv_c) b) /\
              (pred_rel pred_P s2 s3 -> glu_sort_elem pred_P s2 (OP c equiv_c) (OEL c equiv_c) b)) as [glu_b_eq glu_b_rel] by mauto 2.
    destruct pr2;
      [eapply glu_b_rel | subst; eapply glu_b_eq]; mauto 2.
  }
  
  apply_predicate_equivalence.
  unfold sort_glu_exp_pred' in *.
  unfold glu_sort_typ_rec in *.
  destruct_conjs.
  handle_functional_glu_sort_elem P.
  match_by_head (@per_sort_elem P) ltac:(fun H => directed invert_per_sort_elem H).
  inversion_clear H22.
  match goal with
  | _: glu_sort_elem pred_P s1 ?P' ?El' a,
      _: {{ ⟦ A ⟧ ρ ↘ ^?a' }},
      _: {{ ⟦ N ⟧ ρ ↘ ^?n' }} |- _ =>
      rename a' into a;
      rename n' into n;
      rename P' into Pa;
      rename El' into Ela
  end.
  assert {{ Dom a ≈ a ∈ per_sort pred_P s1 }} as [] by mauto 3.
  handle_per_sort_elem_irrel.
  assert {{ Dom n ≈ n ∈ in_rel }} by (eapply glu_sort_elem_per_elem; revgoals; eassumption).
  (on_all_hyp: destruct_rel_by_assumption in_rel).
  simplify_evals.
  match goal with
  | _: {{ ⟦ B ⟧ ρ ↦ n ↘ ^?b' }},
      _: {{ $| m & n |↘ ^?mn' }} |- _ =>
      rename b' into b;
      rename mn' into mn
  end.
  eapply mk_glu_rel_exp_with_sub''; mauto 3.
  intros.
  match_by_head1 (in_rel n n) ltac:(fun H => rename H into equiv_n).
  assert {{ DG b ∈ glu_sort_elem pred_P s2 ↘ OP n equiv_n ↘ OEL n equiv_n }} by mauto 3.
  handle_functional_glu_sort_elem P.
  assert {{ Δ ⊢w Id : Δ }} by mauto 3.
  assert {{ Δ ⊢ IT[Id] ≈ A[σ] : Sort@s1 }} as HAeq.
  {
    autorewrite with mcpts; eapply glu_sort_elem_typ_unique_upto_exp_eq; revgoals; try eassumption.
    enough (Pa Δ {{{ IT[Id] }}}) by (eapply glu_sort_elem_typ_resp_exp_eq; mauto 3).
    eapply H36; mauto 3.    
  }

  assert {{ Δ ⊢ N[σ] : IT[Id] ® n ∈ Ela }} by (rewrite HAeq; eassumption).
  assert (exists mn, {{ $| m & n |↘ mn }} /\ {{ Δ ⊢ M[σ][Id] N[σ] : OT[Id,,N[σ]] ® mn ∈ OEL n equiv_n }}) as [] by mauto 2.
  destruct_conjs.
  functional_eval_rewrite_clear.
  assert {{ Δ ⊢ N[σ] : A[σ][Id] ® n ∈ Ela }} by (autorewrite with mcpts; eassumption).
  assert (SbΓA <∙> cons_glu_sub_pred pred_P s1 Γ A SbΓ).
  {
    eapply glu_ctx_env_cons_clean_inversion; mauto 3.
    rewrite H7.
    eassumption.
  }
  assert {{ Δ ⊢s σ∘Id,,N[σ] ® ρ ↦ n ∈ SbΓA }} as Hcons.
  {
    eapply H43.
    eapply cons_glu_sub_pred_helper; only 1-2: rewrite H7; mauto 3.
    enough (SbΓ'' Δ σ ρ) by (eapply glu_ctx_env_sub_resp_sub_eq; mauto 4); eassumption.
    assert {{ Δ ⊢ A[σ∘Id] ≈ A[σ][Id] : Sort@s1 }} by (eapply exp_eq_sub_compose_typ_sort; mauto 3).
    enough (Ela Δ {{{ A[σ][Id] }}} {{{ N[σ] }}} n) by (eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 3); eassumption.    
  }
  
  (on_all_hyp: destruct_glu_rel_by_assumption SbΓA).
  simplify_evals.
  match_by_head1 (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
  apply_predicate_equivalence.
  unfold sort_glu_exp_pred' in *.
  unfold glu_sort_typ_rec in *.
  destruct_conjs.
  handle_functional_glu_sort_elem P.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ Δ ⊢ N[σ] : A[σ] }} by mauto 2.
  assert {{ Δ ⊢ B[Id,,N][σ] ≈ B[(Id,,N)∘σ] : Sort@s2 }} by (symmetry; mauto 4).
  assert {{ Δ ⊢s (Id,,N)∘σ ≈ σ,,N[σ] : Γ, A@s1 }} by mauto 3.
  assert {{ Δ ⊢ B[(Id,,N)∘σ] ≈ B[σ,,N[σ]] : Sort@s2 }} by mauto 3. 
  assert {{ Δ ⊢ B[Id,,N][σ] ≈ B[σ,,N[σ]] : Sort@s2 }} as -> by mauto 3.
  assert {{ Δ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }} as -> by mauto 2.
  assert {{ Δ ⊢ M[σ][Id] N[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }} as <-.
  {
    assert {{ Δ ⊢ M[σ][Id] ≈ M[σ] : (Π r A B)[σ] }} by mauto 2.
    assert {{ Δ ⊢ M[σ][Id] ≈ M[σ] : Π r A[σ] B[q σ] }} by mauto 4.
    assert {{ Δ ⊢ M[σ][Id] N[σ] ≈ M[σ] N[σ] : B[q σ][Id,,N[σ]] }} as HGoal' by mauto 3.
    assert {{ Δ ⊢ B[q σ][Id,,N[σ]] ≈ B[σ,,N[σ]] }} by mauto 3.
    eapply wf_exp_eq_conv'; mauto 2.
  }
  assert {{ Δ ⊢ B[σ,,N[σ]] ≈ B[(σ∘Id),,N[σ]] : Sort@s2 }} as -> by (eapply exp_eq_sub_cong_typ2_sorted; try eassumption; econstructor; mauto 3).
  enough {{ Δ ⊢ B[(σ∘Id),,N[σ]] ≈ OT[Id,,N[σ]] : Sort@s2 }} as -> by eassumption.
  assert {{ Δ ⊢ OT[Id,,N[σ]] ® OP n equiv_n }} by (eapply glu_sort_elem_trm_typ; eassumption).
  eapply glu_sort_elem_typ_unique_upto_exp_eq; revgoals; eassumption.
Qed.

Lemma glu_rel_exp_app {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {Γ M N A B s1 s2 s3 s2'} {r : Ru P s1 s2 s3},
    {{ ⟪ pred_P ⟫ Γ, A@s1 ⊩ B : Sort@s2 > s2' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ M : Π r A B > s3 }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ N : A > s1 }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ M N : B[Id,,N] > s2 }}.
Proof.
  intros * HB HM HN.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ, A@s1 }} as [SbΓA] by mauto 3.
  match_by_head (glu_ctx_env pred_P SbΓA) invert_glu_ctx_env.
  apply_predicate_equivalence.
  rename TSb into SbΓ.
  assert (exists s1', Ax P s1 s1') as [s1'] by (eapply full_P).
  assert {{ ⟪ pred_P ⟫ Γ ⊩ A : Sort@s1 > s1' }}.
  {
    eexists.
    intuition.
    destruct_glu_rel_typ_with_sub.
    econstructor; mauto 4.
    econstructor; [| split]; mauto 3.
    eapply wf_exp_sub_typ; mauto 3.
    do 2 eexists; mauto 2.
  }
  assert {{ ⟪ pred_P ⟫ ⊩ Γ }} by mauto 2.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ, A@s1 }} by mauto 3.
  mauto 2 using glu_rel_exp_app_helper.
Qed.

#[export]
Hint Resolve glu_rel_exp_app : mcpts.
