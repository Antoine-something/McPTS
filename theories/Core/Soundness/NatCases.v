From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import SystemAnnotated.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  SubstitutionCases
  TermStructureCases
  SortCases.
Import Domain_Notations.

Lemma glu_rel_exp_nat {P} (pred_P : PredicativeSig P) : forall {anns Γ s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u ℕ : Sort@s @ ^so_None }}.
Proof.
  intros * ? [Sb].
  assert {{ ⊢ Γ }} by mauto 2.
  eapply glu_rel_exp_of_typ_unsorted; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  split; mauto 3.
  eexists; repeat split; mauto 3.
  - eexists; per_sort_elem_econstructor;
      [eassumption | mauto 2 | reflexivity].
  - intros.
    match_by_head1 (@glu_sort_elem P) invert_glu_sort_elem.
    apply_predicate_equivalence.
    unfold nat_glu_typ_pred.
    econstructor; mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_exp_nat : mcpts.

Lemma glu_rel_exp_sub_nat {P} (pred_P : PredicativeSig P) : forall {anns Γ σ anns' Δ M s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }} ->
    {{ ⟪ pred_P ⟫ Δ with anns' ⊩u M : ℕ @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M[σ] : ℕ @ ^(so_Some s) }}.
Proof.
  intros.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Γ ⊢ ℕ[σ] ≈ ℕ : Sort@s }} by (econstructor; mauto 2).
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩u M[σ] : ℕ[σ] @ ^(so_Some s) }} as [Sb [HgluΓ]]%glu_rel_exp_unsorted_implies_glu_rel_exp by (eapply TermStructureCases.glu_rel_exp_sub_typ_unsorted; mauto 3).
  exists Sb.
  split; [eassumption |].
  intros.
  (on_all_hyp: fun H => destruct_glu_rel_by_assumption Sb H).
  simplify_evals.
  econstructor; mauto 3.
  match_by_head (@glu_sort_elem P) invert_glu_sort_elem.
  apply_predicate_equivalence.
  invert_glu_rel1.
  simpl; split; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_sub_nat : mcpts.

Lemma glu_rel_exp_of_nat {P} (pred_P : PredicativeSig P) : forall {s} {r : Ru_nat P s} {anns Γ Sb M},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ Sb }} -> exists m, {{ ⟦ M ⟧ ρ ↘ m }} /\ glu_nat r Δ {{{ M[σ] }}} m) ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : ℕ @ ^(so_Some s) }}.
Proof.
  intros * ? Hbody.
  eexists; split; mauto 3.
  intros.
  assert (st_subtyp s s) by mauto 2.
  edestruct Hbody as [? []]; mauto 3.
  econstructor; mauto 3.
  - unshelve (glu_sort_elem_econstructor; mauto 3; reflexivity);
      mauto 2.    
  - simpl; split; mauto 3.    
Qed.

Lemma glu_rel_exp_zero {P} (pred_P : PredicativeSig P) : forall {s} {r : Ru_nat P s} {anns Γ},
    {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u zero : ℕ @ ^(so_Some s) }}.
Proof.
  intros * ? * [Sb].
  eapply glu_rel_exp_of_nat with (r := r); mauto 3.
  intros.
  eexists; split; mauto 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_zero : mcpts.

Lemma glu_rel_exp_succ {P} (pred_P : PredicativeSig P) : forall {s} {r : Ru_nat P s} {anns Γ M},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : ℕ @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u succ M : ℕ @ ^(so_Some s) }}.
Proof.
  intros * ? * HM.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} as [SbΓ] by mauto 3.
  assert {{ Γ ⊢ M : ℕ }} by mauto 3.
  invert_glu_rel_exp_unsorted HM.
  destruct_conjs.
  eapply glu_rel_exp_of_nat with (r := r); mauto.
  intros.
  destruct_glu_rel_exp_with_sub_unsorted.
  simplify_evals.
  match_by_head1 (@glu_sort_elem P) invert_glu_sort_elem.
  apply_predicate_equivalence.
  inversion_clear_by_head (@nat_glu_exp_pred P).
  eexists; split; mauto 3.
  econstructor; mauto.
  eapply glu_nat_rule_irrelevance; mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_exp_succ : mcpts.

Lemma glu_rel_sub_extend_nat {P} (pred_P : PredicativeSig P) : forall {s} {r : Ru_nat P s} {anns Γ σ anns' Δ M},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns' }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : ℕ @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ,,M : Δ, ℕ with (so_Some s)::anns' }}.
Proof.
  intros.
  assert {{ ⟪ pred_P ⟫ ⊩ Δ with anns' }} by mauto 2.
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩u ℕ[σ] : Sort@s @ ^so_None }} by mauto 3.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Γ ⊢ ℕ ≈ ℕ[σ] : Sort@s }} by (symmetry; econstructor; mauto 2).
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : ℕ[σ] @ ^(so_Some s) }} by (eapply glu_rel_exp_conv_unsorted; mauto 3).
  assert {{ ⟪ pred_P ⟫ Δ with anns' ⊩u ℕ : Sort@s @ ^so_None }} by mauto 3.
  eapply glu_rel_sub_extend; mauto 3.
Qed.

#[export]
  Hint Resolve glu_rel_sub_extend_nat : mcpts.


Lemma glu_rel_exp_natrec_zero_helper_sorted {P} (pred_P : PredicativeSig P) : forall {sn s anns Γ SbΓ A MZ MS Δ M σ ρ am typ_rel exp_rel} {r : Ru_nat P sn},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ Γ, ℕ ⊢ A : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A[Id,,zero] @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u MZ : A[Id,,zero] @ ^(so_Some s) }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ⊢ M ≈ zero : ℕ }} ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟦ A ⟧ ρ ↦ zero ↘ am }} ->
    {{ DG am ∈ glu_typ_elem pred_P (so_Some s) ↘ typ_rel ↘ exp_rel }} ->
    exists r,
      {{ rec zero ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
        {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ exp_rel }}.
Proof.
  intros * ? ? ? HMZ **.
  inversion_clear H6.
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩ MZ : A[Id,,zero] @ s }} by mauto 2.
  assert {{ Γ ⊢ MZ : A[Id,,zero] }} by mauto 3.
  inversion HMZ as [SbΓ' []].
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩u ℕ : Sort@sn @ ^so_None }} as [SbΓ'' []] by mauto 3.
  handle_functional_glu_ctx_env P.
  pose (SbΓℕ := cons_glu_sub_pred pred_P (so_Some sn) Γ {{{ ℕ }}} SbΓ'').
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P ((so_Some sn)::anns) ↘ SbΓℕ }} by (econstructor; mauto 4; try reflexivity).
  handle_functional_glu_ctx_env P.
  invert_glu_rel_exp_unsorted H1.
  assert (forall (Δ : list (exp P)%type) (σ : sub P) (ρ : list (domain P)), SbΓ'' Δ σ ρ -> glu_rel_typ_with_sub pred_P sn Δ {{{ ℕ }}} σ ρ) by mauto 3.
  directed destruct_glu_rel_exp_unsorted_by_assumption SbΓ'' H1.

  simplify_evals.
  rename m into mz.
  eexists mz; split; mauto 3.

  handle_functional_glu_sort_elem P.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ ⊢ Δ, ℕ }} by mauto 3.
  assert {{ Δ, ℕ ⊢s q σ : Γ, ℕ }} by mauto 3.
  assert {{ ⊢ Δ, ℕ, A[q σ] }} by mauto 3.
  assert {{ Δ ⊢s Id : Δ }} by mauto 2.
  assert {{ Δ ⊢s σ,,M ≈ σ,,zero : Γ, ℕ }} as -> by mauto 3.
  assert {{ Δ, ℕ ⊢s Wk : Δ }} by mauto 2.
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk : Δ, ℕ }} by mauto 2.
  assert {{ Γ ⊢ ℕ : Sort@sn }} by mauto 3.
  assert {{ Δ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ zero[σ] ≈ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,zero] : Sort@s }} by mauto 3.
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[(q σ)∘(Id,,zero)] : Sort@s }} by (symmetry; mauto 4).
  assert {{ Δ ⊢s (q σ)∘(Id,,zero) ≈ σ,,zero : Γ, ℕ }} by mauto 4.
  assert {{ Γ, ℕ ⊢ A ≈ A : Sort@s }} by mauto 2.
  assert {{ Δ ⊢ A[(q σ)∘(Id,,zero)] ≈ A[σ,,zero] : Sort@s }} by (mauto 3).
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] : Sort@s }} by (etransitivity; eassumption).
  assert {{ Δ ⊢ zero ≈ zero[σ] : ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ,,zero ≈ σ,,zero[σ] : Γ, ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,zero] ≈ A[σ,,zero[σ]] : Sort@s }} by (symmetry; mauto 4).
  assert {{ Γ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ,,zero[σ] ≈ (Id,,zero)∘σ : Γ, ℕ }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[(Id,,zero)∘σ] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ A[(Id,,zero)∘σ] ≈ A[Id,,zero][σ] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[Id,,zero][σ] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] : Sort@s }} as <- by mauto 2.
  assert {{ Γ ⊢ A[Id,,zero] }} by (gen_presup H8; eassumption).
  assert {{ Δ ⊢ MZ[σ] : A[Id,,zero][σ] }} by (eapply wf_exp_sub_typ; mauto 2).
  assert {{ Δ ⊢ MZ[σ] : A[q σ][Id,,zero] }} by (eapply wf_conv' with (A := {{{ A[Id,,zero][σ] }}}); mauto 4).
  assert {{ Δ, ℕ ⊢ A[q σ] : Sort@s }} by mauto 3.
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by (eapply (@sub_weak_compose_weak_extend_succ_var_1 _ _ _ _ r); mauto 2).
  assert {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by (eapply (@sub_weak_compose_weak_extend_succ_var_1 _ _ _ _ r); mauto 2).
  assert {{ Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1] : Sort@s }} by mauto 3.
  assert {{ Δ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q σ)] }} by (eapply (@exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1 _ _ _ _ _ _ r); mauto 2).
  assert {{ Δ, ℕ, A[q σ] ⊢s q (q σ) : Γ, ℕ, A }} by mauto 3.
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[Wk∘Wk,,succ #1][q (q σ)] }} by (econstructor; mauto 3).
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by mauto 3.
  pose (R := {{{ rec zero return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}}).
  assert
    {{ Δ ⊢ R ≈ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[q σ][Id,,zero] }} as <-
      by (econstructor; try eapply exp_eq_refl; mauto 3).
  assert
    {{ Δ ⊢ R ≈ MZ[σ] : A[q σ][Id,,zero] }} as ->
      by (econstructor; mauto 3).
  bulky_rewrite.
Qed.


Lemma glu_rel_exp_natrec_zero_helper_unsorted {P} (pred_P : PredicativeSig P) : forall {sn anns Γ SbΓ A MZ MS Δ M σ ρ am typ_rel exp_rel} {r : Ru_nat P sn},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ Γ, ℕ ⊢ A }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A[Id,,zero] @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u MZ : A[Id,,zero] @ ^so_None }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ⊢ M ≈ zero : ℕ }} ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟦ A ⟧ ρ ↦ zero ↘ am }} ->
    {{ DG am ∈ glu_typ_elem pred_P so_None ↘ typ_rel ↘ exp_rel }} ->
    exists r,
      {{ rec zero ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
        {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ exp_rel }}.
Proof.
  intros * ? ? ? HMZ **.
  assert {{ Γ ⊢ MZ : A[Id,,zero] }} by mauto 3.
  inversion HMZ as [SbΓ' []].
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩u ℕ : Sort@sn @ ^so_None }} as [SbΓ'' []] by mauto 3.
  handle_functional_glu_ctx_env P.
  pose (SbΓℕ := cons_glu_sub_pred pred_P (so_Some sn) Γ {{{ ℕ }}} SbΓ'').
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P ((so_Some sn)::anns) ↘ SbΓℕ }} by (econstructor; mauto 4; try reflexivity).
  handle_functional_glu_ctx_env P.
  invert_glu_rel_exp_unsorted H1.
  assert (forall (Δ : list (exp P)%type) (σ : sub P) (ρ : list (domain P)), SbΓ'' Δ σ ρ -> glu_rel_typ_with_sub pred_P sn Δ {{{ ℕ }}} σ ρ) by mauto 3.
  directed destruct_glu_rel_exp_unsorted_by_assumption SbΓ'' H1.
  simplify_evals.
  handle_functional_glu_typ_elem P.
  inversion_clear H6.
  apply_predicate_equivalence.
  unfold top_sort_glu_exp_pred in *.
  destruct_conjs.
  rename m into mz.
  eexists mz; split; mauto 3.

  handle_functional_glu_sort_elem P.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ ⊢ Δ, ℕ }} by mauto 3.
  assert {{ Δ, ℕ ⊢s q σ : Γ, ℕ }} by mauto 3.
  assert {{ ⊢ Δ, ℕ, A[q σ] }} by mauto 3.
  assert {{ Δ ⊢s Id : Δ }} by mauto 2.
  assert {{ Δ ⊢s σ,,M ≈ σ,,zero : Γ, ℕ }} by mauto 3.
  assert {{ Δ, ℕ ⊢s Wk : Δ }} by mauto 2.
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk : Δ, ℕ }} by mauto 2.
  assert {{ Γ ⊢ ℕ : Sort@sn }} by mauto 3.
  assert {{ Δ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ zero[σ] ≈ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,zero] }} by mauto 3.
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[(q σ)∘(Id,,zero)] }} by (symmetry; mauto 4).
  assert {{ Δ ⊢s (q σ)∘(Id,,zero) ≈ σ,,zero : Γ, ℕ }} by mauto 4.
  assert {{ Γ, ℕ ⊢ A ≈ A }} by mauto 2.
  assert {{ Δ ⊢ A[(q σ)∘(Id,,zero)] ≈ A[σ,,zero] }} by (mauto 3).
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] }} by (etransitivity; eassumption).
  assert {{ Δ ⊢ zero ≈ zero[σ] : ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ,,zero ≈ σ,,zero[σ] : Γ, ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,zero] ≈ A[σ,,zero[σ]] }} by (symmetry; mauto 4).
  assert {{ Γ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ,,zero[σ] ≈ (Id,,zero)∘σ : Γ, ℕ }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[(Id,,zero)∘σ]  }} by mauto 4.
  assert {{ Δ ⊢ A[(Id,,zero)∘σ] ≈ A[Id,,zero][σ]  }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[Id,,zero][σ] }} by mauto 4.
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero]  }}  by mauto 2.
  assert {{ Γ ⊢ A[Id,,zero] }} by (gen_presup H7; eassumption).
  assert {{ Δ ⊢ MZ[σ] : A[Id,,zero][σ] }} by (eapply wf_exp_sub_typ; mauto 2).
  assert {{ Δ ⊢ MZ[σ] : A[q σ][Id,,zero] }} by (eapply wf_conv_typ with (A := {{{ A[Id,,zero][σ] }}}); mauto 4).
  assert {{ Δ, ℕ ⊢ A[q σ] }} by mauto 3.
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by (eapply (@sub_weak_compose_weak_extend_succ_var_1 _ _ _ _ r); mauto 2).
  assert {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by (eapply (@sub_weak_compose_weak_extend_succ_var_1 _ _ _ _ r); mauto 2).
  assert {{ Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1] }} by mauto 3.
  assert {{ Δ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q σ)] }} by (eapply (@exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1 _ _ _ _ _ _ r); mauto 2).
  assert {{ Δ, ℕ, A[q σ] ⊢s q (q σ) : Γ, ℕ, A }} by mauto 3.
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[Wk∘Wk,,succ #1][q (q σ)] }} by (econstructor; mauto 3).
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by mauto 3.
  pose (R := {{{ rec zero return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}}).
  assert
    {{ Δ ⊢ R ≈ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[q σ][Id,,zero] }}
      by (econstructor; mauto 3).
  assert
    {{ Δ ⊢ R ≈ MZ[σ] : A[q σ][Id,,zero] }}
    by (econstructor; mauto 3).
  split.
  assert {{ Δ ⊢ A[σ,,M] ≈ A[Id,,zero][σ] }} by mauto 4.
  etransitivity; mauto 2.
  repeat eexists; mauto 4.
  assert {{ Δ ⊢ A[Id,,zero][σ] ≈ A[q σ][Id,,zero] }} by mauto 4.
  assert {{ Δ ⊢ MZ[σ] ≈ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[q σ][Id,,zero] }} by mauto 3.
  eapply glu_sort_elem_typ_resp_exp_eq; mauto 4.
Qed.

Lemma cons_glu_sub_pred_nat_helper {P} (pred_P : PredicativeSig P) : forall {anns Γ SbΓ Δ σ ρ s M m} {r : Ru_nat P s},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    glu_nat r Δ M m ->
    {{ Δ ⊢s σ,,M ® ρ ↦ m ∈ cons_glu_sub_pred pred_P (so_Some s) Γ {{{ ℕ }}} SbΓ }}.
Proof.
  intros * ? HM ?.
  assert (st_subtyp s s) as Hst by mauto 2.  
  assert {{ DG ℕ ∈ glu_sort_elem pred_P s ↘ nat_glu_typ_pred r Hst ↘ nat_glu_exp_pred r Hst }} by (glu_sort_elem_econstructor; reflexivity).
  eapply cons_glu_sub_pred_helper_sorted; mauto 3.
  econstructor; mauto 2.
  econstructor; [unfold nat_glu_typ_pred |]; mauto 3.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_nat_helper : mcpts.

Lemma glu_rel_exp_natrec_succ_helper_sorted {P} (pred_P : PredicativeSig P) : forall {s anns Γ SbΓ A MZ MS Δ M M' m' σ ρ am typ_rel exp_rel sn} {r : Ru_nat P sn},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ with (so_Some sn)::anns ⊩u A @ ^(so_Some s) }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A with (so_Some s)::(so_Some sn)::anns ⊩u A[Wk∘Wk,,succ #1] @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A with (so_Some s)::(so_Some sn)::anns ⊩u MS : A[Wk∘Wk,,succ #1] @ ^(so_Some s) }} ->
    {{ Δ ⊢ M ≈ succ M' : ℕ }} ->
    glu_nat r Δ M' m' ->
    (forall σ ρ am typ_rel exp_rel,
        {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
        {{ ⟦ A ⟧ ρ ↦ m' ↘ am }} ->
        {{ DG am ∈ glu_typ_elem pred_P (so_Some s) ↘ typ_rel ↘ exp_rel }} ->
        exists e,
          {{ rec m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\
            {{ Δ ⊢ rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M'] ® e ∈ exp_rel }}) ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟦ A ⟧ ρ ↦ succ m' ↘ am }} ->
    {{ DG am ∈ glu_typ_elem pred_P (so_Some s) ↘ typ_rel ↘ exp_rel }} ->
    exists e,
      {{ rec succ m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\
        {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® e ∈ exp_rel }}.
Proof.
  intros * ? HA ? ? HMS **.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} by (eexists; eassumption).
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩u ℕ : Sort@sn @ ^so_None }} as Hℕ by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred pred_P (so_Some sn) Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ  ∈ glu_ctx_env pred_P ((so_Some sn)::anns) ↘ SbΓℕ }} by (invert_glu_rel_exp_unsorted Hℕ; econstructor; mauto 4; try reflexivity).


  assert {{ Γ, ℕ ⊢ A : Sort@s }} by mauto 3.
  invert_glu_rel_typ_unsorted HA.
  pose (SbΓℕA := cons_glu_sub_pred pred_P (so_Some s) {{{ Γ, ℕ }}} A SbΓℕ).
  assert {{ EG Γ, ℕ, A ∈ glu_ctx_env pred_P ((so_Some s)::(so_Some sn)::anns) ↘ SbΓℕA }} by (econstructor; mauto 3; reflexivity).

  assert {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} by mauto 2.
  invert_glu_rel_exp_unsorted HMS.
  handle_functional_glu_ctx_env P.
  assert {{ Δ ⊢s σ,,M' ® ρ ↦ m' ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 3).
  assert (glu_rel_typ_with_sub_unsorted pred_P (so_Some s) Δ A {{{ σ,,M' }}} d{{{ ρ ↦ m' }}}) by mauto 3; subst.
  inversion H14; subst.
  match goal with
  | _: {{ ⟦ A ⟧ ^d{{{ ρ ↦ m' }}} ↘ ^?m }}, _: {{ DG ^?m ∈ glu_sort_elem pred_P ?s ↘ ?P ↘ ?El }} |- _ =>
      rename m into am';
      rename P into typ_rel';
      rename El into exp_rel'
  end.
  
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ ⊢ Δ, ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  assert {{ Δ, ℕ ⊢ A[q σ] : Sort@s }} by mauto 3.
  assert {{ ⊢ Δ, ℕ, A[q σ] }} by mauto 3.
  assert {{ Δ ⊢ M' : ℕ }} by mauto 3.
  assert {{ Δ ⊢ ℕ : Sort@sn }} by mauto 3.
  assert {{ Δ ⊢ ℕ[σ] ≈ ℕ : Sort@sn }} by (econstructor; mauto 2).
  assert {{ Δ ⊢ M' : ℕ[σ] }} by mauto 3.
  assert {{ Δ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ zero : ℕ[σ] }} by mauto 3.
  assert {{ Δ ⊢ zero[σ] ≈ zero : ℕ }} by mauto 3.
  assert {{ Γ, ℕ ⊢ A ≈ A : Sort@s }} by mauto 2.
  assert {{ Δ, ℕ ⊢s q σ : Γ, ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[(q σ)∘(Id,,zero)] : Sort@s }} by (symmetry; mauto 4).
  assert {{ Δ ⊢ A[(q σ)∘(Id,,zero)] ≈ A[σ,,zero] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] : Sort@s }} by (etransitivity; mauto 3).

  assert {{ Δ ⊢ zero ≈ zero[σ] : ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ,,zero ≈ σ,,zero[σ] : Γ, ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,zero] ≈ A[σ,,zero[σ]] : Sort@s }} by mauto 4.
  assert {{ Γ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Γ ⊢s Id,,zero : Γ, ℕ }} by mauto 4.
  assert {{ Δ ⊢s σ,,zero[σ] ≈ (Id,,zero)∘σ : Γ, ℕ }} by (eapply wf_sub_eq_sym; mauto 4).
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[(Id,,zero)∘σ] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ A[(Id,,zero)∘σ] ≈ A[Id,,zero][σ] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[Id,,zero][σ] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ MZ[σ] : A[q σ][Id,,zero] }} by (eapply wf_conv' with (A := {{{ A[Id,,zero][σ] }}}); mauto 4).
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by (eapply (@sub_weak_compose_weak_extend_succ_var_1 _ _ _ _ r); mauto 2).

  assert {{ Δ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q σ)] }} by (eapply (@exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1 _ _ _ _ _ _ r); mauto 2).
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[Wk∘Wk,,succ #1][q (q σ)] }} by (econstructor; mauto 3).
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by mauto 3.
  pose (R := {{{ rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}}).
  assert (exists e, {{ rec m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\ {{ Δ ⊢ R : A[σ,,M'] ® e ∈ exp_rel' }}) as [e' []] by (eapply H4; [| | econstructor]; mauto 3).

  assert {{ Δ ⊢ R : A[σ,,M'] }}.
  {
    assert {{ Δ ⊢ A[q σ][Id,,M'] ≈ A[σ,,M'] : Sort@s }} by mauto 4.
    mauto 4.
  }

  assert {{ Δ ⊢s σ,,M',,R ® (ρ ↦ m') ↦ e' ∈ SbΓℕA }}.
  {
    unfold SbΓℕA.
    econstructor; mauto 4.
    econstructor; mauto 2.
    - assert {{ Δ ⊢ A[Wk][σ,,M',,R] ≈ A[Wk∘(σ,,M',,R)] : Sort@s }}.
      {
        symmetry.
        eapply exp_eq_sub_compose_typ_sort; mauto 3; econstructor; mauto 3.
      }
      assert {{ Δ ⊢s Wk∘(σ,,M',,R) ≈ σ,,M' : Γ, ℕ }} as HWk by mauto 4.
      assert {{ Δ ⊢ A[Wk∘(σ,,M',,R)] ≈ A[σ,,M'] : Sort@s }} by mauto 3.
      assert {{ Δ ⊢ A[Wk][σ,,M',,R] ≈ A[σ,,M'] : Sort@s }} as -> by mauto 4.

      assert {{ Δ ⊢ R ≈ #0[σ,,M',,R] : A[σ,,M'] }} by (symmetry; mauto 4).
      eapply glu_sort_elem_trm_resp_exp_eq; mauto 3.
    - simpl.
      assert {{ Δ ⊢s Wk∘(σ,,M',,R) ≈ σ,,M' : Γ, ℕ }} as -> by mauto 4.
      eassumption.
  }
  destruct_glu_rel_exp_unsorted_by_assumption SbΓℕA HMS.
  match goal with
  | _: {{ ⟦ MS ⟧ ^d{{{ (ρ ↦ m') ↦ e' }}} ↘ ^?m }} |- _ =>
      rename m into ms
  end.
  exists ms; split; mauto 3.
  assert {{ Δ ⊢s σ,,M ≈ σ,,succ M' : Γ, ℕ }} as -> by mauto 3.
  assert {{ Δ ⊢ succ M' : ℕ }} by mauto 3.
  assert {{ Δ ⊢ succ M' : ℕ[σ] }} by mauto 3.
  assert {{ Δ ⊢s (q σ)∘(Id,,succ M') ≈ σ,,succ M' : Γ, ℕ }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,succ M'] ≈ A[(q σ)∘(Id,,succ M')] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ A[(q σ)∘(Id,,succ M')] ≈ A[q σ][Id,,succ M'] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,succ M'] ≈ A[q σ][Id,,succ M'] : Sort@s }} as -> by mauto 4.
  assert {{ Δ ⊢ rec succ M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[q σ][Id,,succ M'] }} as <- by (econstructor; mauto 3).
  assert {{ Δ ⊢ rec succ M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ MS[q (q σ)][Id,,M',,R] : A[q σ][Id,,succ M'] }} as -> by mauto 3.
  assert {{ Δ ⊢ A[σ,,M'] ≈ A[q σ][Id,,M'] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ R : A[q σ][Id,,M'] }} by mauto 2.
  assert {{ Δ ⊢s Id,,M',,R : Δ, ℕ, A[q σ] }} by (eapply wf_sub_extend; mauto 3).
  assert {{ Δ ⊢ A[σ,,succ M'] ≈ A[q σ][Id,,succ M'] : Sort@s }} as <- by mauto 3.
  assert {{ Δ ⊢ A[Wk∘Wk,,succ #1][σ,,M',,R] ≈ A[σ,,succ M'] : Sort@s }} as <-.
  {
    transitivity {{{ A[(Wk∘Wk,,succ #1)∘(σ,,M',,R)] }}}.
    - symmetry; mauto 3.
      eapply exp_eq_sub_compose_typ_sort; mauto 3.
      eapply (@sub_weak_compose_weak_extend_succ_var_1 _ _ _ _ r); mauto 3.
    - enough {{ Δ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M',,R) ≈ σ,,succ M' : Γ, ℕ }} by mauto 4.
      assert {{ Δ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M',,R) ≈ ((Wk∘Wk)∘(σ,,M',,R)),,(succ #1)[σ,,M',,R] : Γ, ℕ }}.
      {
        eapply wf_sub_eq_extend_compose; mauto 3.
        - econstructor; mauto 3.
        - assert {{ Γ, ℕ, A ⊢ ℕ[Wk∘Wk] ≈ ℕ : Sort@sn }}.
          {
            eapply wf_exp_eq_nat_sub; mauto 3.
            econstructor; mauto 3.
          }
          gen_presup H65.
          assert  {{ Γ, ℕ ⊢ A }} by mauto 3.
          assert {{ Γ, ℕ, A ⊢ succ #1 : ℕ }} by mauto 3.
          econstructor; mauto 4.
      }
      transitivity {{{ ((Wk∘Wk)∘(σ,,M',,R)),,(succ #1)[σ,,M',,R] }}}; mauto 2.
      assert {{ Δ ⊢s σ,,M',,R : Γ, ℕ, A }} by mauto 3.
      assert {{ Γ, ℕ, A ⊢ #1 : ℕ }} by mauto 3.
      assert {{ Δ ⊢ (succ #1)[σ,,M',,R] ≈ succ M' : ℕ }}.
      {
        assert {{ Δ ⊢ (succ #1)[σ,,M',,R] ≈ succ #1[σ,,M',,R] : ℕ }} by mauto 3.
        transitivity {{{ succ (#1[σ,,M',,R]) }}}; [mautosolve 4 |].
        assert {{ Δ ⊢ #1[σ,,M',,R] ≈ M' : ℕ }} by (transitivity {{{ #0[σ,,M'] }}}; mauto 4).
        mauto 3.
      }
      eapply wf_sub_eq_extend_cong; mauto 4.
      + assert {{ Δ ⊢s (Wk∘Wk)∘(σ,,M',,R) ≈ Wk∘(Wk∘(σ,,M',,R)) : Γ }} by (eapply wf_sub_eq_compose_assoc; mauto 3).
        transitivity {{{ Wk∘(Wk∘(σ,,M',,R)) }}}; mauto 2.
        assert {{ Δ ⊢s (Wk∘(σ,,M',,R)) ≈ (σ,,M') : Γ, ℕ }} by mauto 4.
        assert {{ Δ ⊢s Wk∘(Wk∘(σ,,M',,R)) ≈ Wk∘(σ,,M') : Γ }} by (eapply wf_sub_eq_compose_cong; mauto 3).
        transitivity {{{ Wk∘(σ,,M') }}}; mauto 2.
      + eapply wf_exp_eq_conv'; mauto 2.
        symmetry.
        enough {{ Δ ⊢ ℕ[(Wk∘Wk)∘(σ,,M',,R)] ≈ ℕ : Sort@sn }} by mauto 2.
        econstructor; mauto 2.
        econstructor; mauto 3.
        do 2 econstructor; mauto 2.
  }
  assert {{ Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1] : Sort@s }} by mauto 3.
  assert {{ Δ ⊢ MS[q (q σ)][Id,,M',,R] ≈ MS[σ,,M',,R] : A[Wk∘Wk,,succ #1][σ,,M',,R] }} as -> by mauto 4.
  simplify_evals.
  inversion H7; subst.
  handle_functional_glu_sort_elem P.
  eassumption.
Qed.


Lemma glu_rel_exp_natrec_succ_helper_unsorted {P} (pred_P : PredicativeSig P) : forall {anns Γ SbΓ A MZ MS Δ M M' m' σ ρ am typ_rel exp_rel sn} {r : Ru_nat P sn},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ with (so_Some sn)::anns ⊩u A @ ^so_None }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A with so_None::(so_Some sn)::anns ⊩u A[Wk∘Wk,,succ #1] @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A with so_None::(so_Some sn)::anns ⊩u MS : A[Wk∘Wk,,succ #1] @ ^so_None }} ->
    {{ Δ ⊢ M ≈ succ M' : ℕ }} ->
    glu_nat r Δ M' m' ->
    (forall σ ρ am typ_rel exp_rel,
        {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
        {{ ⟦ A ⟧ ρ ↦ m' ↘ am }} ->
        {{ DG am ∈ glu_typ_elem pred_P so_None ↘ typ_rel ↘ exp_rel }} ->
        exists e,
          {{ rec m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\
            {{ Δ ⊢ rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M'] ® e ∈ exp_rel }}) ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟦ A ⟧ ρ ↦ succ m' ↘ am }} ->
    {{ DG am ∈ glu_typ_elem pred_P so_None ↘ typ_rel ↘ exp_rel }} ->
    exists e,
      {{ rec succ m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\
        {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® e ∈ exp_rel }}.
Proof.
  intros * ? HA ? ? HMS **.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} by (eexists; eassumption).
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩u ℕ : Sort@sn @ ^so_None }} as Hℕ by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred pred_P (so_Some sn) Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ  ∈ glu_ctx_env pred_P ((so_Some sn)::anns) ↘ SbΓℕ }} by (invert_glu_rel_exp_unsorted Hℕ; econstructor; mauto 4; try reflexivity).


  assert {{ Γ, ℕ ⊢ A }} by mauto 2.
  invert_glu_rel_typ_unsorted HA.
  pose (SbΓℕA := cons_glu_sub_pred pred_P so_None {{{ Γ, ℕ }}} A SbΓℕ).
  assert {{ EG Γ, ℕ, A ∈ glu_ctx_env pred_P (so_None::(so_Some sn)::anns) ↘ SbΓℕA }} by (econstructor; mauto 3; reflexivity).

  assert {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} by mauto 2.
  invert_glu_rel_exp_unsorted HMS.
  handle_functional_glu_ctx_env P.
  assert {{ Δ ⊢s σ,,M' ® ρ ↦ m' ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 3).
  assert (glu_rel_typ_with_sub_unsorted pred_P so_None Δ A {{{ σ,,M' }}} d{{{ ρ ↦ m' }}}) by mauto 3; subst.
  inversion H14; subst.
  functional_eval_rewrite_clear.
  match goal with
  | _: {{ ⟦ A ⟧ ^d{{{ ρ ↦ m' }}} ↘ ^?m }}, _: {{ DG ^?m ∈ glu_typ_elem pred_P ?so ↘ ?P ↘ ?El }} |- _ =>
      rename P into typ_rel';
      rename El into exp_rel'
  end.

  inversion H17; subst.
  apply_predicate_equivalence.
  unfold top_sort_glu_typ_pred in *.

  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ ⊢ Δ, ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  assert {{ Δ, ℕ ⊢ A[q σ] }} by mauto 3.
  assert {{ ⊢ Δ, ℕ, A[q σ] }} by mauto 3.
  assert {{ Δ ⊢ M' : ℕ }} by mauto 3.
  assert {{ Δ ⊢ ℕ : Sort@sn }} by mauto 3.
  assert {{ Δ ⊢ ℕ[σ] ≈ ℕ : Sort@sn }} by (econstructor; mauto 2).
  assert {{ Δ ⊢ M' : ℕ[σ] }} by mauto 3.
  assert {{ Δ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ zero : ℕ[σ] }} by mauto 3.
  assert {{ Δ ⊢ zero[σ] ≈ zero : ℕ }} by mauto 3.
  assert {{ Γ, ℕ ⊢ A ≈ A }} by mauto 2.
  assert {{ Δ, ℕ ⊢s q σ : Γ, ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[(q σ)∘(Id,,zero)] }} by (symmetry; mauto 4).
  assert {{ Δ ⊢ A[(q σ)∘(Id,,zero)] ≈ A[σ,,zero] }} by mauto 4.
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] }} by (etransitivity; mauto 3).

  assert {{ Δ ⊢ zero ≈ zero[σ] : ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ,,zero ≈ σ,,zero[σ] : Γ, ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,zero] ≈ A[σ,,zero[σ]] }} by mauto 4.
  assert {{ Γ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Γ ⊢s Id,,zero : Γ, ℕ }} by mauto 4.
  assert {{ Δ ⊢s σ,,zero[σ] ≈ (Id,,zero)∘σ : Γ, ℕ }} by (eapply wf_sub_eq_sym; mauto 4).
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[(Id,,zero)∘σ] }} by mauto 4.
  assert {{ Δ ⊢ A[(Id,,zero)∘σ] ≈ A[Id,,zero][σ] }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[Id,,zero][σ] }} by mauto 4.
  assert {{ Δ ⊢ MZ[σ] : A[q σ][Id,,zero] }} by (eapply wf_conv_typ with (A := {{{ A[Id,,zero][σ] }}}); mauto 4).
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by (eapply (@sub_weak_compose_weak_extend_succ_var_1 _ _ _ _ r); mauto 2).

  assert {{ Δ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q σ)] }} by (eapply (@exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1 _ _ _ _ _ _ r); mauto 2).
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[Wk∘Wk,,succ #1][q (q σ)] }} by (econstructor; mauto 3).
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by mauto 3.
  pose (R := {{{ rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}}).
  assert (exists e, {{ rec m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\ {{ Δ ⊢ R : A[σ,,M'] ® e ∈ exp_rel' }}) as [e' []] by mauto 3.

  assert {{ Δ ⊢ R : A[σ,,M'] }}.
  {
    assert {{ Δ ⊢ A[q σ][Id,,M'] ≈ A[σ,,M'] }} by mauto 4.
    mauto 4.
  }

  assert {{ Δ ⊢s σ,,M',,R ® (ρ ↦ m') ↦ e' ∈ SbΓℕA }}.
  {
    unfold SbΓℕA.
    econstructor; mauto 4.
    - assert {{ Δ ⊢ A[Wk][σ,,M',,R] ≈ A[Wk∘(σ,,M',,R)] }}.
      {
        eapply typ_eq_sub_compose_typ; mauto 3; econstructor; mauto 3.
      }
      assert {{ Δ ⊢s Wk∘(σ,,M',,R) ≈ σ,,M' : Γ, ℕ }} as HWk by mauto 4.
      assert {{ Δ ⊢ A[Wk∘(σ,,M',,R)] ≈ A[σ,,M'] }} by mauto 3.
      assert {{ Δ ⊢ A[Wk][σ,,M',,R] ≈ A[σ,,M'] }} as -> by mauto 4.

      assert {{ Δ ⊢ R ≈ #0[σ,,M',,R] : A[σ,,M'] }} by (symmetry; mauto 4).
      assert {{ Δ ⊢ R ≈ #0[σ,,M',,R] : Sort@s }} by (symmetry; mauto 4).
      eapply glu_typ_elem_trm_resp_exp_eq; mauto 3.
    - simpl.
      assert {{ Δ ⊢s Wk∘(σ,,M',,R) ≈ σ,,M' : Γ, ℕ }} as -> by mauto 3.
      eassumption.
  }
  destruct_glu_rel_exp_unsorted_by_assumption SbΓℕA HMS.
  handle_functional_glu_typ_elem P.
  unfold top_sort_glu_exp_pred in *.
  destruct_conjs.
  eexists.
  split; mauto 4.
  assert {{ Δ ⊢s σ,,M ≈ σ,,succ M' : Γ, ℕ }} by mauto 3.
  assert {{ Δ ⊢ succ M' : ℕ }} by mauto 3.
  assert {{ Δ ⊢ succ M' : ℕ[σ] }} by mauto 3.
  assert {{ Δ ⊢s (q σ)∘(Id,,succ M') ≈ σ,,succ M' : Γ, ℕ }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,succ M'] ≈ A[(q σ)∘(Id,,succ M')] }} by mauto 4.
  assert {{ Δ ⊢ A[(q σ)∘(Id,,succ M')] ≈ A[q σ][Id,,succ M'] }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,succ M'] ≈ A[q σ][Id,,succ M'] }} by mauto 4.
  assert {{ Δ ⊢ rec succ M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[q σ][Id,,succ M'] }} by (econstructor; mauto 3).
  assert {{ Δ ⊢ rec succ M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ MS[q (q σ)][Id,,M',,R] : A[q σ][Id,,succ M'] }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,M'] ≈ A[q σ][Id,,M'] }} by mauto 4.
  assert {{ Δ ⊢ R : A[q σ][Id,,M'] }} by mauto 2.
  assert {{ Δ ⊢s Id,,M',,R : Δ, ℕ, A[q σ] }} by (eapply wf_sub_extend; mauto 3).
  assert {{ Δ ⊢ A[σ,,succ M'] ≈ A[q σ][Id,,succ M'] }} by mauto 3.
  assert {{ Δ ⊢ A[Wk∘Wk,,succ #1][σ,,M',,R] ≈ A[σ,,succ M'] }}.
  {
    transitivity {{{ A[(Wk∘Wk,,succ #1)∘(σ,,M',,R)] }}}.
    - eapply typ_eq_sub_compose_typ; mauto 3.
      eapply (@sub_weak_compose_weak_extend_succ_var_1 _ _ _ _ r); mauto 3.
    - enough {{ Δ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M',,R) ≈ σ,,succ M' : Γ, ℕ }} by mauto 4.
      assert {{ Δ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M',,R) ≈ ((Wk∘Wk)∘(σ,,M',,R)),,(succ #1)[σ,,M',,R] : Γ, ℕ }}.
      {
        eapply wf_sub_eq_extend_compose; mauto 3.
        - econstructor; mauto 3.
        - assert {{ Γ, ℕ, A ⊢ ℕ[Wk∘Wk] ≈ ℕ : Sort@sn }}.
          {
            eapply wf_exp_eq_nat_sub; mauto 3.
            econstructor; mauto 3.
          }
          gen_presup H76.
          assert  {{ Γ, ℕ ⊢ A }} by mauto 3.
          assert {{ Γ, ℕ, A ⊢ succ #1 : ℕ }} by mauto 3.
          econstructor; mauto 4.
      }
      transitivity {{{ ((Wk∘Wk)∘(σ,,M',,R)),,(succ #1)[σ,,M',,R] }}}; mauto 2.
      assert {{ Δ ⊢s σ,,M',,R : Γ, ℕ, A }} by mauto 3.
      assert {{ Γ, ℕ, A ⊢ #1 : ℕ }} by mauto 3.
      assert {{ Δ ⊢ (succ #1)[σ,,M',,R] ≈ succ M' : ℕ }}.
      {
        assert {{ Δ ⊢ (succ #1)[σ,,M',,R] ≈ succ #1[σ,,M',,R] : ℕ }} by mauto 3.
        transitivity {{{ succ (#1[σ,,M',,R]) }}}; [mautosolve 4 |].
        assert {{ Δ ⊢ #1[σ,,M',,R] ≈ M' : ℕ }} by (transitivity {{{ #0[σ,,M'] }}}; mauto 4).
        mauto 3.
      }
      eapply wf_sub_eq_extend_cong; mauto 4.
      + assert {{ Δ ⊢s (Wk∘Wk)∘(σ,,M',,R) ≈ Wk∘(Wk∘(σ,,M',,R)) : Γ }} by (eapply wf_sub_eq_compose_assoc; mauto 3).
        transitivity {{{ Wk∘(Wk∘(σ,,M',,R)) }}}; mauto 2.
        assert {{ Δ ⊢s (Wk∘(σ,,M',,R)) ≈ (σ,,M') : Γ, ℕ }} by mauto 4.
        assert {{ Δ ⊢s Wk∘(Wk∘(σ,,M',,R)) ≈ Wk∘(σ,,M') : Γ }} by (eapply wf_sub_eq_compose_cong; mauto 3).
        transitivity {{{ Wk∘(σ,,M') }}}; mauto 2.
      + eapply wf_exp_eq_conv'; mauto 2.
        symmetry.
        enough {{ Δ ⊢ ℕ[(Wk∘Wk)∘(σ,,M',,R)] ≈ ℕ : Sort@sn }} by mauto 2.
        econstructor; mauto 2.
        econstructor; mauto 3.
        do 2 econstructor; mauto 2.
  }

  assert {{ Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1] }} by mauto 3.
  assert {{ Δ ⊢ MS[q (q σ)][Id,,M',,R] ≈ MS[σ,,M',,R] : A[Wk∘Wk,,succ #1][σ,,M',,R] }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,M]≈ A[Wk∘Wk,,succ #1][σ,,M',,R] }} as -> by mauto 4.
  assert {{ Δ ⊢ MS[q (q σ)][Id,,M',,R] ≈ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[q σ][Id,,succ M'] }} by mauto 3.
  assert {{ Δ ⊢ MS[q (q σ)][Id,,M',,R] ≈ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,succ M'] }} by mauto 3.
  assert {{ Δ ⊢ MS[q (q σ)][Id,,M',,R] ≈ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[Wk∘Wk,,succ #1][σ,,M',,R] }} by mauto 3.
  assert {{ Δ ⊢ MS[σ,,M',,R] ≈ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[Wk∘Wk,,succ #1][σ,,M',,R] }} as <- by mauto 3.
  simplify_evals.
  handle_functional_glu_typ_elem P.
  eassumption.
Qed.

Lemma cons_glu_sub_pred_q_helper {P} (pred_P : PredicativeSig P) : forall {so anns Γ SbΓ Δ σ ρ A a},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A @ so }} ->
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ Δ, A[σ] ⊢s q σ ® ρ ↦ ⇑! a (length Δ) ∈ cons_glu_sub_pred pred_P so Γ A SbΓ }}.
Proof.
  intros * ? ? HA ?.
  destruct so;
    [ assert {{ Γ ⊢ A }} by mauto 2 | assert {{ Γ ⊢ A : Sort@s }} by mauto 3];
    invert_glu_rel_typ_unsorted HA;
    handle_functional_glu_ctx_env P;

    assert {{ Δ ⊢s σ : Γ }} by mauto 2;
    assert {{ ⊢ Δ, A[σ] }} by mauto 4;
    assert {{ Δ, A[σ] ⊢w Wk : Δ }} by mauto 2;
    [assert (glu_rel_typ_with_sub_unsorted pred_P so_None Δ A σ ρ) by mauto 2 |
      assert (glu_rel_typ_with_sub_unsorted pred_P (so_Some s) Δ A σ ρ) by mauto 2];
    inversion H6;
    simplify_evals.
  - eapply cons_glu_sub_pred_helper_unsorted; mauto 2.
    + eapply glu_ctx_env_sub_monotone; eassumption.
    + assert {{ Δ, A[σ] ⊢s Wk : Δ }} by mauto 2.
      assert {{ Δ, A[σ] ⊢ A[σ∘Wk] ≈ A[σ][Wk] }} as -> by mauto 3.
      eapply var0_glu_elem_unsorted; eassumption.
  - eapply cons_glu_sub_pred_helper_sorted; mauto 2.
  + eapply glu_ctx_env_sub_monotone; eassumption.
  + econstructor; mauto 2.
  + assert {{ Δ, A[σ] ⊢s Wk : Δ }} by mauto 2.
    assert {{ Δ, A[σ] ⊢ A[σ∘Wk] ≈ A[σ][Wk] : Sort@s }} as -> by mauto 3.
    eapply var0_glu_elem; eassumption.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_q_helper : mcpts.

Lemma cons_glu_sub_pred_q_nat_helper {P} (pred_P : PredicativeSig P) : forall {anns Γ SbΓ Δ σ ρ s} {r : Ru_nat P s},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ Δ, ℕ ⊢s q σ ® ρ ↦ ⇑! ℕ (length Δ) ∈ cons_glu_sub_pred pred_P (so_Some s) Γ {{{ ℕ }}} SbΓ }}.
Proof.
  intros.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} by (eexists; eassumption).
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩u ℕ : Sort@s @ ^so_None }} as Hℕ by mauto 3.
  assert {{ ⟦ ℕ ⟧ ρ ↘ ℕ }} by mauto 3.
  assert {{ Δ, ℕ[σ] ⊢s q σ ® ρ ↦ ⇑! ℕ (length Δ) ∈ cons_glu_sub_pred pred_P (so_Some s) Γ {{{ ℕ }}} SbΓ }} by mauto 3.
  assert {{ Δ ⊢ ℕ[σ] ≈ ℕ : Sort@s }} by (econstructor; mauto 4).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P ((so_Some s)::anns) ↘ cons_glu_sub_pred pred_P (so_Some s) Γ {{{ ℕ }}} SbΓ }}.
  {
    invert_glu_rel_exp_unsorted Hℕ; destruct_conjs; econstructor; mauto 3.
    assert (forall (Δ : list (exp P)%type) (σ : sub P) (ρ : list (domain P)), SbΓ Δ σ ρ -> glu_rel_typ_with_sub pred_P s Δ {{{ ℕ }}} σ ρ) by mauto 3.
    - intros; mauto 3.
    - split; intros * Hglu; invert_glu_ctx_env Hglu; econstructor; mauto 2.
  }
  assert {{ ⊢ Δ }} by mauto 2.
  cbn.
  assert {{ ⊢ Δ, ℕ[σ] ≈ Δ, ℕ }} as <- by mauto 4.
  eassumption.
Qed.

#[local]
  Hint Resolve cons_glu_sub_pred_q_nat_helper : mcpts.

Lemma glu_rel_exp_natrec_neut_helper_sorted {P} (pred_P : PredicativeSig P) : forall {s anns Γ SbΓ A MZ MS Δ M a m σ ρ am typ_rel exp_rel sn} {r : Ru_nat P sn},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ with (so_Some sn)::anns ⊩u A @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A[Id,,zero] @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u MZ : A[Id,,zero] @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A with (so_Some s)::(so_Some sn)::anns ⊩u A[Wk∘Wk,,succ #1] @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A with (so_Some s)::(so_Some sn)::anns ⊩u MS : A[Wk∘Wk,,succ #1] @ ^(so_Some s) }} ->
    {{ Dom m ≈ m ∈ per_bot }} ->
    (forall Δ' τ V, {{ Δ' ⊢w τ : Δ }} -> {{ Rne m in length Δ' ↘ V }} -> {{ Δ' ⊢ M[τ] ≈ V : ℕ }}) ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟦ A ⟧ ρ ↦ ⇑ a m ↘ am }} ->
    {{ DG am ∈ glu_typ_elem pred_P (so_Some s) ↘ typ_rel ↘ exp_rel }} ->
    exists e,
      {{ rec ⇑ a m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\
        {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® e ∈ exp_rel }}.
Proof.
  intros * ? ? HA ? HMZ ? HMS **.
  assert {{ Γ ⊢ MZ : A[Id,,zero] }} by mauto 2.
  invert_glu_rel_exp_unsorted HMZ.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} by (eexists; eassumption).
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩u ℕ : Sort@sn @ ^so_None }} as Hℕ by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred pred_P (so_Some sn) Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P ((so_Some sn)::anns) ↘ SbΓℕ }} by (invert_glu_rel_exp_unsorted Hℕ; econstructor; mauto 4; try reflexivity).
  assert {{ Γ, ℕ ⊢ A : Sort@s }} by mauto 3.
  pose proof HA.
  invert_glu_rel_typ_unsorted HA.
  assert (forall Δ σ ρ, SbΓℕ Δ σ ρ -> glu_rel_typ_with_sub_unsorted pred_P (so_Some s) Δ A σ ρ) by mauto 3.
  pose (SbΓℕA := cons_glu_sub_pred pred_P (so_Some s) {{{ Γ, ℕ }}} A SbΓℕ).
  assert {{ EG Γ, ℕ, A ∈ glu_ctx_env pred_P ((so_Some s)::(so_Some sn)::anns) ↘ SbΓℕA }} by (econstructor; mauto 3; reflexivity).

  assert {{ Δ ⊢s σ,,M ® ρ ↦ ⇑ a m ∈ SbΓℕ }}.
  {
    unfold SbΓℕ.
    eapply (@cons_glu_sub_pred_nat_helper _ _ _ _ _ _ _ _ _ _ _ r); mauto 2.
  }

  assert {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} by mauto 2.
  invert_glu_rel_exp_unsorted HMS.
  destruct_conjs.
  apply_functional_glu_ctx_env.
  assert (glu_rel_typ_with_sub_unsorted pred_P (so_Some s) Δ A {{{ σ,,M }}} d{{{ ρ ↦ ⇑ a m }}}) by mauto 2.
  assert (glu_rel_exp_with_sub_unsorted pred_P (so_Some s) Δ MZ {{{ A[Id,,zero] }}} σ ρ) by mauto 2.
 
  
  destruct_glu_rel_typ_with_sub_unsorted.
  destruct_glu_rel_exp_with_sub_unsorted.
  simplify_evals.
  handle_functional_glu_sort_elem P.
  rename M0 into MZ.
  match goal with
  | _: {{ ⟦ MZ ⟧ ^?ρ0 ↘ ^?m }}, _: {{ ⟦ A ⟧ ^?ρ0 ↦ zero ↘ ^?a }} |- _ =>
      rename ρ0 into ρ;
      rename m into mz;
      rename a into az
  end.
  eexists; split; mauto 3.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ ⊢ Δ, ℕ }} by mauto 3.
  assert {{ Δ, ℕ ⊢ A[q σ] : Sort@s }} by mauto 3.
  assert {{ ⊢ Δ, ℕ, A[q σ] }} by mauto 3.
  assert {{ Δ ⊢ M : ℕ }} by (unshelve mauto 3; mauto 2).

  assert {{ Δ ⊢ ℕ : Sort@sn }} by mauto 3.
  assert {{ Δ ⊢ ℕ[σ] ≈ ℕ : Sort@sn }} by (econstructor; mauto 2).
  assert {{ Δ ⊢ M : ℕ[σ] }} by mauto 3.
  assert {{ Δ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ zero[σ] ≈ zero : ℕ }} by mauto 3.
  assert {{ Δ, ℕ ⊢s q σ : Γ, ℕ }} by mauto 3.

  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[(q σ)∘(Id,,zero)] : Sort@s }} by (symmetry; eapply wf_exp_eq_sym; mauto 4).
  assert {{ Δ ⊢s (q σ)∘(Id,,zero) ≈ σ,,zero : Γ, ℕ }} by (eapply sub_eq_q_sigma_id_extend; mauto 3).
  assert {{ Δ ⊢ A[(q σ)∘(Id,,zero)] ≈ A[σ,,zero] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢s σ,,zero ≈ σ,,zero[σ] : Γ, ℕ }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,zero] ≈ A[σ,,zero[σ]] : Sort@s }} by mauto 4.
  assert {{ Γ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ,,zero[σ] ≈ (Id,,zero)∘σ : Γ, ℕ }} by mauto 5.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[(Id,,zero)∘σ] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ A[(Id,,zero)∘σ] ≈ A[Id,,zero][σ] : Sort@s }} by (eapply exp_eq_sub_compose_typ_sort; mauto 4).
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[Id,,zero][σ] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ MZ[σ] : A[q σ][Id,,zero] }} by (eapply wf_conv' with (A := {{{ A[Id,,zero][σ] }}}); mauto 4).
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by (eapply (@sub_weak_compose_weak_extend_succ_var_1 _ _ _ _ r); mauto 3).
  assert {{ Δ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,, succ #1][q (q σ)]  }} by (eapply (@exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1 _ _ _ _ _ _ r); mauto 3).
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[Wk∘Wk,,succ #1][q (q σ)] }} by (eapply wf_exp_sub_typ; mauto 4).
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by mauto 3.
  pose (R := {{{ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}}).
  enough {{ Δ ⊢ R : A[σ,,M] ® rec m under ρ return A | zero -> mz | succ -> MS end ∈ glu_elem_bot_unsorted pred_P (so_Some s) am }} by (eapply realize_glu_elem_bot_unsorted; mauto 3).
  econstructor; mauto 3.
  - assert {{ Δ ⊢ A[q σ][Id,,M] ≈ A[σ,,M] : Sort@s }} by mauto 2.
    eapply wf_conv'; mauto 3.
  - assert {{ Δ ⊢ MZ[σ] : A[Id,,zero][σ] ® mz ∈ glu_elem_top pred_P s az }} as [] by (eapply realize_glu_elem_top; eassumption).
    handle_functional_glu_sort_elem P.
    assert {{ ⟪ pred_P ⟫ ⊨ Γ }} as [env_relΓ] by mauto 3 using completeness_fundamental_ctx.
    assert {{ ⟪ pred_P ⟫ Γ, ℕ ⊨u A : Sort@s }} as [env_relΓℕ] by mauto 3 using completeness_fundamental_exp.
    assert {{ ⟪ pred_P ⟫ Γ, ℕ, A ⊨u MS : A[Wk∘Wk,,succ #1] }} as [env_relΓℕA] by mauto 3 using completeness_fundamental_exp.
    destruct_conjs.
    pose env_relΓℕA.
    match_by_head (per_ctx_env pred_P env_relΓℕA) ltac:(fun H => invert_per_ctx_env H).
    match_by_head (per_ctx_env pred_P env_relΓℕ) ltac:(fun H => invert_per_ctx_env H).
    intros k.
    enough (exists e, {{ Rne rec m under ρ return A | zero -> mz | succ -> MS end in k ↘ e }}) as [] by (eexists; split; eassumption).
    assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
    destruct_rel_typ_unsorted.

    assert {{ Dom ! k ≈ ! k ∈ (@per_bot P) }} by mauto 3.
    assert {{ Dom ρ ↦ ⇑! ℕ k ≈ ρ ↦ ⇑! ℕ k ∈ env_relΓℕ }}.
    {
      apply_relation_equivalence.
      econstructor; mauto 3.
      simplify_evals.
      eapply (@per_bot_then_per_typ_elem _ pred_P); mauto 2.
    }

    assert {{ Dom ρ ↦ succ ⇑! ℕ k ≈ ρ ↦ succ ⇑! ℕ k ∈ env_relΓℕ }}.
    {
      apply_relation_equivalence.
      econstructor; mauto 4.
      simplify_evals.
      inversion H64; subst.
      invert_per_sort_elems.
      intuition.
    }

    destruct_rel_typ_unsorted.
    invert_rel_typ_unsorted_body.
    
    match goal with
    | _: {{ ⟦ A ⟧ ρ ↦ ⇑! ℕ k ↘ ^?a }}, _: {{ ⟦ A ⟧ ρ ↦ (succ ⇑! ℕ k) ↘ ^?a' }} |- _ =>
        rename a into as'; (** We cannot use [as] as a name *)
        rename a' into asucc
    end.

    
    assert {{ Dom (ρ ↦ ⇑! ℕ k) ↦ ⇑! as' (S k) ≈ (ρ ↦ ⇑! ℕ k) ↦ ⇑! as' (S k) ∈ env_relΓℕA }} as HΓℕA.
    {
      apply_relation_equivalence.
      econstructor; mauto 3.
      eapply (@per_bot_then_per_typ_elem P pred_P); mauto 3.
    }
    apply_relation_equivalence.
    (on_all_hyp_rev: fun H => destruct (H _ _ HΓℕA)).
    destruct_conjs.
    inversion_clear_by_head (@rel_typ_unsorted P).
    inversion_clear_by_head (@rel_exp P).
    simplify_evals.
    
    handle_per_sort_elem_irrel.
    match goal with
    | _: {{ ⟦ MS ⟧ (ρ ↦ ⇑! ℕ k) ↦ ⇑! as' (S k) ↘ ^?m }} |- _ =>
        rename m into ms
    end.

    assert {{ Dom as' ≈ as' ∈ per_top_typ }} as [? []]%(fun {a} (f : per_top_typ a a) => f (S k)) by mauto 3.
    assert {{ Dom ⇓ asucc ms ≈ ⇓ asucc ms ∈ per_top }} as [? []]%(fun {a} (f : per_top a a) => f (S (S k))) by mauto 3.
    match_by_head1 (per_top d{{{ ⇓ az mz }}} d{{{ ⇓ az mz }}}) ltac:(fun H => destruct (H k) as [? []]).
    match_by_head1 (per_bot m m) ltac:(fun H => destruct (H k) as [? []]).
    eexists.
    mauto.
  - intros Δ' τ w **.
    assert {{ ⊢ Δ' }} by mauto 3.
    assert {{ ⊢ Δ', ℕ }} by mauto 3.
    assert {{ Δ' ⊢s τ : Δ }} by mauto 3.
    assert {{ Δ' ⊢s σ∘τ : Γ }} by mauto 3.
    assert {{ Δ' ⊢s σ∘τ ® ρ ∈ SbΓ }} by (eapply glu_ctx_env_sub_monotone; mauto 4).
    assert {{ Δ', ℕ ⊢s q (σ∘τ) ® ρ ↦ ⇑! ℕ (length Δ') ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 3).
    assert (forall (Δ : list (exp P)%type) (σ : sub P) (ρ : list (domain P)), SbΓℕ Δ σ ρ -> glu_rel_typ_with_sub_unsorted pred_P (so_Some s) Δ A σ ρ) by mauto 3.
    destruct_glu_rel_typ_with_sub_unsorted.
    simplify_evals.
    dir_inversion_clear_by_head (@read_ne P).
    handle_functional_glu_sort_elem P.
    match goal with
    | _: {{ ⟦ A ⟧ ^?ρ' ↦ ⇑! ℕ (length Δ') ↘ ^?a }} |- _ =>
        rename ρ' into ρ;
        rename a into aΔ'
    end.
    assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q (σ∘τ)) ® (ρ ↦ ⇑! ℕ (length Δ')) ↦ ⇑! aΔ' (length {{{ Δ', ℕ }}}) ∈ SbΓℕA }} by (unfold SbΓℕA; mauto 3).
    assert (glu_rel_typ_with_sub_unsorted pred_P (so_Some s) {{{ Δ', ℕ }}} A {{{ q (σ∘τ) }}}
              d{{{ ρ ↦ ⇑! ℕ (length Δ') }}}) as Hglu_typ_unsorted by mauto 2.
    inversion Hglu_typ_unsorted; subst.
    destruct_glu_rel_exp_with_sub_unsorted.
    simplify_evals.
    handle_functional_glu_sort_elem P.

    match goal with
    | _: {{ ⟦ A ⟧ ^?ρ' ↦ succ (⇑! ℕ (length Δ')) ↘ ^?a }},
        _: {{ Rtyp aΔ' in S (length Δ') ↘ ^?A }},
        _: {{ Rnf ⇓ az mz in length Δ' ↘ ^?MZ }},
            _: {{ Rne m in length Δ' ↘ ^?M }} |- _ =>
        rename A into A';
        rename ρ' into ρ;
        rename a into asucc;
        rename MZ into MZ';
        rename M into M'
    end.
    assert {{ Δ', ℕ ⊢ A[q (σ∘τ)] ® glu_typ_top_unsorted pred_P (so_Some s) aΔ' }} as Hglu_typ_top by (eapply realize_glu_typ_top_unsorted; mauto 3; econstructor; mauto 2).
    inversion Hglu_typ_top; subst.
    assert {{ Δ ⊢ MZ[σ] : A[Id,,zero][σ] ® mz ∈ glu_elem_top pred_P s az }} as [] by (eapply realize_glu_elem_top; eassumption).
    assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q (σ∘τ))] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] ® ms ∈ glu_elem_top pred_P s asucc }} as []
        by (eapply realize_glu_elem_top; eassumption).
    assert {{ Δ ⊢s σ,,M : Γ, ℕ }} by mauto 4.
    assert {{ Δ' ⊢s σ∘τ,,M[τ] : Γ, ℕ }} by mauto 4.
    assert {{ Δ' ⊢ A[σ,,M][τ] ≈ A[(σ,,M)∘τ] : Sort@s }} as -> by mauto 3.
    assert {{ Δ' ⊢ A[(σ,,M)∘τ] ≈ A[σ∘τ,,M[τ]] : Sort@s }} as -> by mauto 3.
    assert {{ Δ' ⊢ A[σ∘τ,,M[τ]] ≈ A[q σ][τ,,M[τ]] : Sort@s }} as -> by (eapply sub_decompose_q_typ_sorted; mauto 4).
    assert {{ Δ' ⊢ R[τ] ≈ rec M[τ] return A[q σ][q τ] | zero -> MZ[σ][τ] | succ -> MS[q (q σ)][q (q τ)] end : A[q σ][τ,,M[τ]] }} as -> by mauto 3.
    assert {{ Δ' ⊢ A[q σ][q τ][Id,,M[τ]] ≈ A[q σ][τ,,M[τ]] : Sort@s }} as <- by mauto 4.
    assert {{ Δ', ℕ ⊢w Id : Δ', ℕ }} by mauto 3.
    assert {{ Δ', ℕ ⊢ A[q (σ∘τ)][Id] ≈ A' : Sort@s }} as HA' by mauto 4.
    gen_presup HA'.
    eapply (@wf_exp_eq_natrec_cong' _ _ _ _ _ _ _ _ _ _ _ r); fold (@ne_to_exp P) (@nf_to_exp P); only 1, 2: mauto 4.
    + assert {{ Δ', ℕ ⊢s q σ∘q τ : Γ, ℕ }} by mauto 3.
      assert {{ Δ', ℕ ⊢ A[q σ∘q τ] : Sort@s }} by mauto 3.
      assert {{ Δ', ℕ ⊢ A[q σ][q τ] ≈ A' : Sort@s }}. {
        rewrite <- HA'.
        transitivity {{{ A[q σ∘q τ] }}}; mauto 3.
        transitivity {{{ A[q σ∘q τ][Id] }}}; mauto 3.
        eapply exp_eq_sub_cong_typ1_sorted; mauto 3.
        }
        mauto 2.
    + assert {{ Δ, ℕ ⊢ A[q σ] : Sort@s }} by mauto 3.
      assert {{ Δ', ℕ ⊢s q τ : Δ, ℕ }} by mauto 3.
      assert {{ Δ' ⊢ zero : ℕ }} by mauto 3.
      assert {{ Δ' ⊢ A[q σ][q τ][Id,,zero] ≈ A[q σ][τ,,zero] : Sort@s }} as -> by mauto 3.
      assert {{ Δ' ⊢ zero ≈ zero[τ] : ℕ }} by mauto 3.
      assert {{ Δ' ⊢ zero ≈ zero[τ] : ℕ[τ] }} by mauto 4.
      assert {{ Δ' ⊢s τ,,zero ≈ τ,,zero[τ] : Δ, ℕ }} by mauto 3.
      assert {{ Δ' ⊢ A[q σ][τ,,zero] ≈ A[q σ][τ,,zero[τ]] : Sort@s }} by (symmetry; mauto 4).
      assert {{ Δ' ⊢ A[q σ][τ,,zero] ≈ A[q σ][Id,,zero][τ] : Sort@s }} as -> by mauto 4.
      assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[Id,,zero][σ] : Sort@s }} by mauto 3.
      assert {{ Δ' ⊢ A[q σ][Id,,zero][τ] ≈ A[Id,,zero][σ][τ] : Sort@s }} as -> by mauto 3.
      mauto 3.
    + assert {{ Δ, ℕ ⊢ A[q σ] : Sort@s }} by mauto 3.
      assert {{ Δ', ℕ ⊢s q τ : Δ, ℕ }} by mauto 2.
      assert {{ Δ, ℕ, A[q σ] ⊢s q (q σ) : Γ, ℕ, A }} by mauto 3.
      assert {{ Δ', ℕ, A[q σ][q τ] ⊢s q (q τ) : Δ, ℕ, A[q σ] }} by mauto 3.
      assert {{ Δ', ℕ ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, ℕ }} by mauto 4.
      assert {{ ⊢ Δ', ℕ, A[q (σ∘τ)] }} by mauto 2.
      assert {{ Δ', ℕ ⊢ A[q σ][q τ] ≈ A[q σ∘q τ] : Sort@s }} by mauto 2.
      assert {{ Δ', ℕ ⊢ A[q σ∘q τ] ≈ A[q (σ∘τ)] : Sort@s }} by mauto 2.
      assert {{ ⊢ Δ', ℕ, A[q σ∘q τ] ≈ Δ', ℕ, A[q (σ∘τ)] }} by mauto 4.
      assert {{ ⊢ Δ', ℕ, A[q σ][q τ] ≈ Δ', ℕ, A[q (σ∘τ)] }} by mauto 5.
      assert {{ ⊢ Δ', ℕ, A[q σ][q τ] ≈ Δ', ℕ, A[q (σ∘τ)] }} as -> by eassumption.
      assert {{ Δ', ℕ ⊢s Wk : Δ' }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s Wk : Δ', ℕ }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ #1 : ℕ }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ succ #1 : ℕ }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s Wk∘Wk,,succ #1 : Δ', ℕ }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[q σ][q τ][Wk∘Wk,,succ #1] ≈ A[q (σ∘τ)][Wk∘Wk,,succ #1] : Sort@s }} as -> by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[q (σ∘τ)][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q (σ∘τ))]  }} as -> by mauto 3 using exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1.
      assert {{ Δ', ℕ ⊢s q (σ∘τ) : Γ, ℕ }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q (σ∘τ)) : Γ, ℕ, A }} by mauto 2.
      assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
      assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 3.
      assert {{ Γ, ℕ, A ⊢ #1 : ℕ }} by mauto 3.
      assert {{ Γ, ℕ, A ⊢ succ #1 : ℕ }} by mauto 3.
      assert {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q τ) : Δ, ℕ, A[q σ] }} by mauto 2.
      assert {{ Δ', ℕ, A[q σ][q τ] ⊢ MS[q (q σ)∘q (q τ)] ≈ MS[q (q σ)][q (q τ)] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by (eapply wf_exp_eq_sub_compose_typ; mauto 3).
      assert {{ Δ', ℕ, A[q σ][q τ] ⊢ MS[q (q σ)][q (q τ)] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 3.
      assert {{ Δ', ℕ, A[q σ∘q τ] ⊢s q (q σ)∘q (q τ) ≈ q (q σ∘q τ) : Γ, ℕ, A }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q σ)∘q (q τ) ≈ q (q σ∘q τ) : Γ, ℕ, A }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q σ∘q τ) ≈ q (q (σ∘τ)) : Γ, ℕ, A }} by mauto 4.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q σ)∘q (q τ) ≈ q (q (σ∘τ)) : Γ, ℕ, A }} by mauto 2.
      assert {{ Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1] : Sort@s }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] ≈ A[Wk∘Wk,,succ #1][q (q (σ∘τ))] : Sort@s }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q σ)][q (q τ)] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q σ)][q (q τ)] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as -> by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q σ)∘q (q τ)] ≈ MS[q (q (σ∘τ))] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 4.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q (σ∘τ))] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as <- by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q (σ∘τ))][Id] ≈ MS[q (q (σ∘τ))] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as <- by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[Wk∘Wk,,succ #1][q (q (σ∘τ))][Id] ≈ A[Wk∘Wk,,succ #1][q (q (σ∘τ))] : Sort@s }} as <- by mauto 3.
      mauto 3.
    + intuition.
Qed.

Lemma glu_rel_exp_natrec_neut_helper_unsorted {P} (pred_P : PredicativeSig P) : forall {anns Γ SbΓ A MZ MS Δ M a m σ ρ am typ_rel exp_rel sn} {r : Ru_nat P sn},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ with (so_Some sn)::anns ⊩u A @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A[Id,,zero] @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u MZ : A[Id,,zero] @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A with so_None::(so_Some sn)::anns ⊩u A[Wk∘Wk,,succ #1] @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A with so_None::(so_Some sn)::anns ⊩u MS : A[Wk∘Wk,,succ #1] @ ^so_None }} ->
    {{ Dom m ≈ m ∈ per_bot }} ->
    (forall Δ' τ V, {{ Δ' ⊢w τ : Δ }} -> {{ Rne m in length Δ' ↘ V }} -> {{ Δ' ⊢ M[τ] ≈ V : ℕ }}) ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟦ A ⟧ ρ ↦ ⇑ a m ↘ am }} ->
    {{ DG am ∈ glu_typ_elem pred_P (so_None) ↘ typ_rel ↘ exp_rel }} ->
    exists e,
      {{ rec ⇑ a m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\
        {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® e ∈ exp_rel }}.
Proof.
  intros * ? ? HA ? HMZ ? HMS **.
  assert {{ Γ ⊢ MZ : A[Id,,zero] }} by mauto 2.
  invert_glu_rel_exp_unsorted HMZ.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} by (eexists; eassumption).
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩u ℕ : Sort@sn @ ^so_None }} as Hℕ by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred pred_P (so_Some sn) Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P ((so_Some sn)::anns) ↘ SbΓℕ }} by (invert_glu_rel_exp_unsorted Hℕ; econstructor; mauto 4; try reflexivity).
  assert {{ Γ, ℕ ⊢ A }} by mauto 3.
  pose proof HA.
  invert_glu_rel_typ_unsorted HA.
  assert (forall Δ σ ρ, SbΓℕ Δ σ ρ -> glu_rel_typ_with_sub_unsorted pred_P so_None Δ A σ ρ) by mauto 3.
  pose (SbΓℕA := cons_glu_sub_pred pred_P so_None {{{ Γ, ℕ }}} A SbΓℕ).
  assert {{ EG Γ, ℕ, A ∈ glu_ctx_env pred_P (so_None::(so_Some sn)::anns) ↘ SbΓℕA }} by (econstructor; mauto 3; reflexivity).

  assert {{ Δ ⊢s σ,,M ® ρ ↦ ⇑ a m ∈ SbΓℕ }}.
  {
    unfold SbΓℕ.
    eapply (@cons_glu_sub_pred_nat_helper _ _ _ _ _ _ _ _ _ _ _ r); mauto 2.
  }

  assert {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} by mauto 2.
  invert_glu_rel_exp_unsorted HMS.
  destruct_conjs.
  apply_functional_glu_ctx_env.
  assert (glu_rel_typ_with_sub_unsorted pred_P so_None Δ A {{{ σ,,M }}} d{{{ ρ ↦ ⇑ a m }}}) by mauto 2.
  assert (glu_rel_exp_with_sub_unsorted pred_P so_None Δ MZ {{{ A[Id,,zero] }}} σ ρ) by mauto 2.
 
  
  destruct_glu_rel_typ_with_sub_unsorted.
  destruct_glu_rel_exp_with_sub_unsorted.
  simplify_evals.
  handle_functional_glu_typ_elem P.
  rename M0 into MZ.
  match goal with
  | _: {{ ⟦ MZ ⟧ ^?ρ0 ↘ ^?m }}, _: {{ ⟦ A ⟧ ^?ρ0 ↦ zero ↘ ^?a }} |- _ =>
      rename ρ0 into ρ;
      rename m into mz
  end.
  eexists; split; mauto 3.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ ⊢ Δ, ℕ }} by mauto 3.
  assert {{ Δ, ℕ ⊢ A[q σ] }} by mauto 3.
  assert {{ ⊢ Δ, ℕ, A[q σ] }} by mauto 3.
  assert (glu_nat r Δ M d{{{ ⇑ Sort@s0 m }}}) as Hgn by mauto 2.
  assert {{ Δ ⊢ M : ℕ }} by mauto 3.
  assert {{ Δ ⊢ ℕ : Sort@sn }} by mauto 3.
  assert {{ Δ ⊢ ℕ[σ] ≈ ℕ : Sort@sn }} by (econstructor; mauto 2).
  assert {{ Δ ⊢ M : ℕ[σ] }} by mauto 3.
  assert {{ Δ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ zero[σ] ≈ zero : ℕ }} by mauto 3.
  assert {{ Δ, ℕ ⊢s q σ : Γ, ℕ }} by mauto 3.

  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[(q σ)∘(Id,,zero)] }} by (symmetry; eapply wf_typ_eq_sym; mauto 4).
  assert {{ Δ ⊢s (q σ)∘(Id,,zero) ≈ σ,,zero : Γ, ℕ }} by (eapply sub_eq_q_sigma_id_extend; mauto 3).
  assert {{ Δ ⊢ A[(q σ)∘(Id,,zero)] ≈ A[σ,,zero]  }} by mauto 4.
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero]  }} by mauto 4.
  assert {{ Δ ⊢s σ,,zero ≈ σ,,zero[σ] : Γ, ℕ }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,zero] ≈ A[σ,,zero[σ]] }} by mauto 4.
  assert {{ Γ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ,,zero[σ] ≈ (Id,,zero)∘σ : Γ, ℕ }} by mauto 5.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[(Id,,zero)∘σ] }} by mauto 4.
  assert {{ Δ ⊢ A[(Id,,zero)∘σ] ≈ A[Id,,zero][σ] }} by (symmetry; eapply typ_eq_sub_compose_typ; mauto 4).
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[Id,,zero][σ] }} by mauto 4.
  assert {{ Δ ⊢ MZ[σ] : A[q σ][Id,,zero] }} by (eapply wf_conv_typ with (A := {{{ A[Id,,zero][σ] }}}); mauto 4).
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by (eapply (@sub_weak_compose_weak_extend_succ_var_1 _ _ _ _ r); mauto 3).
  assert {{ Δ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,, succ #1][q (q σ)]  }} by (eapply (@exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1 _ _ _ _ _ _ r); mauto 3).
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[Wk∘Wk,,succ #1][q (q σ)] }} by (eapply wf_exp_sub_typ; mauto 4).
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by mauto 3.
  pose (R := {{{ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}}).
  enough {{ Δ ⊢ R : A[σ,,M] ® rec m under ρ return A | zero -> mz | succ -> MS end ∈ glu_elem_bot_unsorted pred_P so_None d{{{ Sort@s }}} }} by (eapply realize_glu_elem_bot_unsorted; mauto 3).

  econstructor; mauto 3.
  - assert {{ Δ ⊢ A[q σ][Id,,M] ≈ A[σ,,M] }} by mauto 2.
    eapply wf_conv_typ; mauto 4.
  - assert {{ Δ ⊢ MZ[σ] : A[Id,,zero][σ] ® mz ∈ glu_elem_top_unsorted pred_P so_None d{{{ Sort@s0 }}} }} as Hglu_top_unsorted by (eapply realize_glu_elem_top_unsorted; eassumption).
    inversion Hglu_top_unsorted; subst.
    
    assert {{ ⟪ pred_P ⟫ ⊨ Γ }} as [env_relΓ] by mauto 3 using completeness_fundamental_ctx.
    assert {{ ⟪ pred_P ⟫ Γ, ℕ ⊨ A }} as [env_relΓℕ] by mauto 3 using completeness_fundamental_typ.
    assert {{ ⟪ pred_P ⟫ Γ, ℕ, A ⊨u MS : A[Wk∘Wk,,succ #1] }} as [env_relΓℕA] by mauto 3 using completeness_fundamental_exp.
    destruct_conjs.
    pose env_relΓℕA.
    match_by_head (per_ctx_env pred_P env_relΓℕA) ltac:(fun H => invert_per_ctx_env H).
    match_by_head (per_ctx_env pred_P env_relΓℕ) ltac:(fun H => invert_per_ctx_env H).
    intros k.
    enough (exists e, {{ Rne rec m under ρ return A | zero -> mz | succ -> MS end in k ↘ e }}) as [] by (eexists; split; eassumption).
    assert {{ Dom ρ ≈ ρ ∈ env_relΓ }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
    destruct_rel_typ_unsorted.

    assert {{ Dom ! k ≈ ! k ∈ (@per_bot P) }} by mauto 3.
    assert {{ Dom ρ ↦ ⇑! ℕ k ≈ ρ ↦ ⇑! ℕ k ∈ env_relΓℕ }}.
    {
      apply_relation_equivalence.
      econstructor; mauto 3.
      simplify_evals.
      eapply (@per_bot_then_per_typ_elem _ pred_P); mauto 2.
    }

    assert {{ Dom ρ ↦ succ ⇑! ℕ k ≈ ρ ↦ succ ⇑! ℕ k ∈ env_relΓℕ }}.
    {
      apply_relation_equivalence.
      econstructor; mauto 4.
      simplify_evals.
      inversion H67; subst.
      invert_per_sort_elems.
      intuition.
    }

    destruct_rel_typ_unsorted.
    invert_rel_typ_unsorted_body.
    
    match goal with
    | _: {{ ⟦ A ⟧ ρ ↦ ⇑! ℕ k ↘ ^?a }}, _: {{ ⟦ A ⟧ ρ ↦ (succ ⇑! ℕ k) ↘ ^?a' }} |- _ =>
        rename a into as'; (** We cannot use [as] as a name *)
        rename a' into asucc
    end.

    
    assert {{ Dom (ρ ↦ ⇑! ℕ k) ↦ ⇑! as' (S k) ≈ (ρ ↦ ⇑! ℕ k) ↦ ⇑! as' (S k) ∈ env_relΓℕA }} as HΓℕA.
    {
      apply_relation_equivalence.
      econstructor; mauto 3.
      eapply (@per_bot_then_per_typ_elem P pred_P); mauto 3.
    }
    apply_relation_equivalence.
    (on_all_hyp_rev: fun H => destruct (H _ _ HΓℕA)).
    destruct_conjs.
    inversion_clear_by_head (@rel_typ_unsorted P).
    inversion_clear_by_head (@rel_exp P).
    simplify_evals.
    
    handle_per_sort_elem_irrel.
    match goal with
    | _: {{ ⟦ MS ⟧ (ρ ↦ ⇑! ℕ k) ↦ ⇑! as' (S k) ↘ ^?m }} |- _ =>
        rename m into ms
    end.

    assert {{ Dom as' ≈ as' ∈ per_top_typ }} as [? []]%(fun {a} (f : per_top_typ a a) => f (S k)) by mauto 3.
    assert {{ Dom ⇓ asucc ms ≈ ⇓ asucc ms ∈ per_top }} as [? []]%(fun {a} (f : per_top a a) => f (S (S k))) by mauto 3.
    match_by_head1 (per_top d{{{ ⇓ Sort@s0 mz }}} d{{{ ⇓ Sort@s0  mz }}}) ltac:(fun H => destruct (H k) as [? []]).
    match_by_head1 (per_bot m m) ltac:(fun H => destruct (H k) as [? []]).
    eexists.
    mauto.
  - intros Δ' τ w **.
    assert {{ ⊢ Δ' }} by mauto 3.
    assert {{ ⊢ Δ', ℕ }} by mauto 3.
    assert {{ Δ' ⊢s τ : Δ }} by mauto 3.
    assert {{ Δ' ⊢s σ∘τ : Γ }} by mauto 3.
    assert {{ Δ' ⊢s σ∘τ ® ρ ∈ SbΓ }} by (eapply glu_ctx_env_sub_monotone; mauto 4).
    assert {{ Δ', ℕ ⊢s q (σ∘τ) ® ρ ↦ ⇑! ℕ (length Δ') ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 3).
    assert (forall Δ σ ρ, SbΓℕ Δ σ ρ -> glu_rel_typ_with_sub_unsorted pred_P so_None Δ A σ ρ) by mauto 3.
    destruct_glu_rel_typ_with_sub_unsorted.
    simplify_evals.
    dir_inversion_clear_by_head (@read_ne P).
    handle_functional_glu_typ_elem P.
    match goal with
    | _: {{ ⟦ A ⟧ ^?ρ' ↦ ⇑! ℕ (length Δ') ↘ ^?a }} |- _ =>
        rename ρ' into ρ;
        rename a into aΔ'
    end.
    assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q (σ∘τ)) ® (ρ ↦ ⇑! ℕ (length Δ')) ↦ ⇑! aΔ' (length {{{ Δ', ℕ }}}) ∈ SbΓℕA }} by (unfold SbΓℕA; mauto 3).
    assert (glu_rel_typ_with_sub_unsorted pred_P so_None {{{ Δ', ℕ }}} A {{{ q (σ∘τ) }}}
              d{{{ ρ ↦ ⇑! ℕ (length Δ') }}}) as Hglu_typ_unsorted by mauto 2.
    assert (glu_rel_exp_with_sub_unsorted pred_P so_None Δ MZ {{{ A[Id,,zero] }}} σ ρ) by mauto 2.
    inversion Hglu_typ_unsorted; subst.
    destruct_glu_rel_exp_with_sub_unsorted.
    simplify_evals.
    handle_functional_glu_typ_elem P.
    clear H83 H79 H62 s4 s1 s0.
    rename s5 into s0.
    rename s2 into s1.
    rename s3 into s2.
     
    match goal with
    | _: {{ ⟦ A ⟧ ^?ρ' ↦ succ (⇑! ℕ (length Δ')) ↘ ^?a }},
        _: {{ Rtyp ^?aΔ' in S (length Δ') ↘ ^?A }},
        _: {{ Rnf ⇓ ^?az mz in length Δ' ↘ ^?MZ }},
            _: {{ Rne m in length Δ' ↘ ^?M }} |- _ =>
        rename A into A';
        rename ρ' into ρ;
        rename MZ into MZ';
        rename M into M'        
    end.
    inversion H61; subst.
    rename M1 into MZ.
    assert {{ Δ', ℕ ⊢ A[q (σ∘τ)] ® glu_typ_top_unsorted pred_P so_None d{{{ Sort@s1 }}} }} as Hglu_typ_top by (eapply realize_glu_typ_top_unsorted; mauto 3; econstructor; mauto 2).
    inversion Hglu_typ_top; subst.
    inversion H62; subst; clear H62.
    assert {{ Δ ⊢ MZ[σ] : A[Id,,zero][σ] ® mz ∈ glu_elem_top_unsorted pred_P so_None d{{{ Sort@s0 }}} }} as Hglu_typ_top' by (eapply realize_glu_elem_top_unsorted; eassumption).
    inversion Hglu_typ_top'; subst.
    
    assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q (σ∘τ))] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] ® ms ∈ glu_elem_top_unsorted pred_P so_None d{{{ Sort@s2 }}} }} as Hglu_elem_top by (eapply realize_glu_elem_top_unsorted; mauto 3).
    inversion Hglu_elem_top; subst.
    assert {{ Δ ⊢s σ,,M : Γ, ℕ }} by mauto 4.
    assert {{ Δ' ⊢s σ∘τ,,M[τ] : Γ, ℕ }} by mauto 4.
    assert {{ Δ' ⊢ A[σ,,M][τ] ≈ A[(σ,,M)∘τ] }} as -> by mauto 3.
    assert {{ Δ' ⊢ A[(σ,,M)∘τ] ≈ A[σ∘τ,,M[τ]] }} as -> by mauto 3.
    assert {{ Δ' ⊢ A[σ∘τ,,M[τ]] ≈ A[q σ][τ,,M[τ]] }} as -> by (eapply sub_decompose_q_typ; mauto 4).
    assert {{ Δ' ⊢ R[τ] ≈ rec M[τ] return A[q σ][q τ] | zero -> MZ[σ][τ] | succ -> MS[q (q σ)][q (q τ)] end : A[q σ][τ,,M[τ]] }} as -> by mauto 3.
    assert {{ Δ' ⊢ A[q σ][q τ][Id,,M[τ]] ≈ A[q σ][τ,,M[τ]] }} as <- by mauto 4.
    assert {{ Δ', ℕ ⊢w Id : Δ', ℕ }} by mauto 3.
    assert {{ Δ', ℕ ⊢ A[q (σ∘τ)][Id] ≈ Sort@s3[Id] }} by mauto 4.
    assert {{ Δ', ℕ ⊢ A[q (σ∘τ)][Id] ≈ Sort@s3 }} as HA' by mauto 4.
    gen_presup HA'.
    eapply (@wf_exp_eq_natrec_cong' _ _ _ _ _ _ _ _ _ _ _ r); fold (@ne_to_exp P) (@nf_to_exp P); only 1, 2: mauto 4.
    + assert {{ Δ', ℕ ⊢s q σ∘q τ : Γ, ℕ }} by mauto 3.
      assert {{ Δ', ℕ ⊢ A[q σ∘q τ] }} by mauto 3.
      assert {{ Δ', ℕ ⊢ A[q σ][q τ] ≈ Sort@s3 }}. {
        rewrite <- HA'.
        transitivity {{{ A[q σ∘q τ] }}}; mauto 3.
        transitivity {{{ A[q σ∘q τ][Id] }}}; mauto 3.
        eapply typ_eq_sub_cong_typ1; mauto 3.
        }
        mauto 2.
    + assert {{ Δ, ℕ ⊢ A[q σ] }} by mauto 3.
      assert {{ Δ', ℕ ⊢s q τ : Δ, ℕ }} by mauto 3.
      assert {{ Δ' ⊢ zero : ℕ }} by mauto 3.
      assert {{ Δ' ⊢ A[q σ][q τ][Id,,zero] ≈ A[q σ][τ,,zero] }} as -> by mauto 3.
      assert {{ Δ' ⊢ zero ≈ zero[τ] : ℕ }} by mauto 3.
      assert {{ Δ' ⊢ zero ≈ zero[τ] : ℕ[τ] }} by mauto 4.
      assert {{ Δ' ⊢s τ,,zero ≈ τ,,zero[τ] : Δ, ℕ }} by mauto 3.
      assert {{ Δ' ⊢ A[q σ][τ,,zero] ≈ A[q σ][τ,,zero[τ]] }} by (symmetry; mauto 4).
      assert {{ Δ' ⊢ A[q σ][τ,,zero] ≈ A[q σ][Id,,zero][τ] }} as -> by mauto 4.
      assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[Id,,zero][σ] }} by mauto 3.
      assert {{ Δ' ⊢ A[q σ][Id,,zero][τ] ≈ A[Id,,zero][σ][τ] }} as -> by mauto 3.
      mauto 3.
    + assert {{ Δ, ℕ ⊢ A[q σ] }} by mauto 3.
      assert {{ Δ', ℕ ⊢s q τ : Δ, ℕ }} by mauto 2.
      assert {{ Δ, ℕ, A[q σ] ⊢s q (q σ) : Γ, ℕ, A }} by mauto 3.
      assert {{ Δ', ℕ, A[q σ][q τ] ⊢s q (q τ) : Δ, ℕ, A[q σ] }} by mauto 3.
      assert {{ Δ', ℕ ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, ℕ }} by mauto 4.
      assert {{ ⊢ Δ', ℕ, A[q (σ∘τ)] }} by mauto 2.
      assert {{ Δ', ℕ ⊢ A[q σ][q τ] ≈ A[q σ∘q τ] }} by mauto 2.
      assert {{ Δ', ℕ ⊢ A[q σ∘q τ] ≈ A[q (σ∘τ)] }} by mauto 2.
      assert {{ ⊢ Δ', ℕ, A[q σ∘q τ] ≈ Δ', ℕ, A[q (σ∘τ)] }} by mauto 4.
      assert {{ ⊢ Δ', ℕ, A[q σ][q τ] ≈ Δ', ℕ, A[q (σ∘τ)] }} by mauto 5.
      assert {{ ⊢ Δ', ℕ, A[q σ][q τ] ≈ Δ', ℕ, A[q (σ∘τ)] }} as -> by eassumption.
      assert {{ Δ', ℕ ⊢s Wk : Δ' }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s Wk : Δ', ℕ }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ #1 : ℕ }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ succ #1 : ℕ }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s Wk∘Wk,,succ #1 : Δ', ℕ }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[q σ][q τ][Wk∘Wk,,succ #1] ≈ A[q (σ∘τ)][Wk∘Wk,,succ #1] }} as -> by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[q (σ∘τ)][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q (σ∘τ))]  }} as -> by mauto 3 using exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1.
      assert {{ Δ', ℕ ⊢s q (σ∘τ) : Γ, ℕ }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q (σ∘τ)) : Γ, ℕ, A }} by mauto 2.
      assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
      assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 3.
      assert {{ Γ, ℕ, A ⊢ #1 : ℕ }} by mauto 3.
      assert {{ Γ, ℕ, A ⊢ succ #1 : ℕ }} by mauto 3.
      assert {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q τ) : Δ, ℕ, A[q σ] }} by mauto 2.
      assert {{ Δ', ℕ, A[q σ][q τ] ⊢ MS[q (q σ)∘q (q τ)] ≈ MS[q (q σ)][q (q τ)] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by (eapply wf_exp_eq_sub_compose_typ; mauto 3).
      assert {{ Δ', ℕ, A[q σ][q τ] ⊢ MS[q (q σ)][q (q τ)] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 3.
      assert {{ Δ', ℕ, A[q σ∘q τ] ⊢s q (q σ)∘q (q τ) ≈ q (q σ∘q τ) : Γ, ℕ, A }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q σ)∘q (q τ) ≈ q (q σ∘q τ) : Γ, ℕ, A }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q σ∘q τ) ≈ q (q (σ∘τ)) : Γ, ℕ, A }} by mauto 4.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q σ)∘q (q τ) ≈ q (q (σ∘τ)) : Γ, ℕ, A }} by mauto 2.
      assert {{ Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1] }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] ≈ A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q σ)][q (q τ)] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q σ)][q (q τ)] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as -> by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q σ)∘q (q τ)] ≈ MS[q (q (σ∘τ))] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 4.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q (σ∘τ))] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as <- by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q (σ∘τ))][Id] ≈ MS[q (q (σ∘τ))] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as <- by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[Wk∘Wk,,succ #1][q (q (σ∘τ))][Id] ≈ A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as <- by mauto 3.
      mauto 3.
    + intuition.
Qed.


Lemma glu_rel_exp_natrec_helper {P} (pred_P : PredicativeSig P) : forall {sn so anns Γ SbΓ A MZ MS} {r : Ru_nat P sn},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ with (so_Some sn)::anns ⊩u A @ so }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u MZ : A[Id,,zero] @ so }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A with so::(so_Some sn)::anns ⊩u MS : A[Wk∘Wk,,succ #1] @ so }} ->
    forall {Δ M m},
      glu_nat r Δ M m ->
      forall {σ ρ am P El},
        {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
        {{ ⟦ A ⟧ ρ ↦ m ↘ am }} ->
        {{ DG am ∈ glu_typ_elem pred_P so ↘ P ↘ El }} ->
        exists r,
          {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
            {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ El }}.
Proof.
  intros * ? HA ? ?.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩u ℕ : Sort@sn @ ^so_None }} as Hℕ by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩u A[Id,,zero] @ so }}.
  {
    assert {{ Γ ⊢ ℕ : Sort@sn }} by mauto 2.
    assert {{ Γ ⊢ ℕ ≈ ℕ[Id] : Sort@sn }} by mauto 4.
    mauto.
  }
  pose (SbΓℕ := cons_glu_sub_pred pred_P (so_Some sn) Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P ((so_Some sn)::anns) ↘ SbΓℕ }} by (invert_glu_rel_exp_unsorted Hℕ; econstructor; mauto 4; try reflexivity).
  pose proof HA.
  invert_glu_rel_typ_unsorted HA.
  assert (forall Δ σ ρ, SbΓℕ Δ σ ρ -> glu_rel_typ_with_sub_unsorted pred_P so Δ A σ ρ) by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ, ℕ, A with so::(so_Some sn)::anns ⊩u A[Wk∘Wk,,succ #1] @ so }}.
  {
    assert {{ ⟪ pred_P ⟫ ⊩ Γ, ℕ, A with so::(so_Some sn)::anns }} by mauto 3.
    assert {{ ⟪ pred_P ⟫ Γ, ℕ with (so_Some sn)::anns ⊩s Wk : Γ with anns }} by mauto 4.
    assert {{ ⟪ pred_P ⟫ Γ, ℕ, A with so::(so_Some sn)::anns ⊩s Wk : Γ, ℕ with (so_Some sn)::anns }} by mauto 3.
    assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 3.
    assert {{ Γ, ℕ, A ⊢ ℕ[Wk][Wk] ≈ ℕ : Sort@sn }} by mauto 3.
    assert {{ Γ, ℕ, A ⊢ ℕ[Wk][Wk] ⊆ ℕ }} by mauto 3.
    assert {{ ⟪ pred_P ⟫ Γ, ℕ, A with so::(so_Some sn)::anns ⊩u  ℕ : Sort@sn @ ^so_None }} by mauto 3.
    assert {{ #1 : ℕ[Wk][Wk] @ (so_Some sn) ∈ Γ, ℕ, A with so::(so_Some sn)::anns }} by mauto 2.
    assert {{ ⟪ pred_P ⟫ Γ, ℕ, A with so::(so_Some sn)::anns ⊩ #1 : ℕ[Wk][Wk] @ ^ sn }} by mauto 4.
    assert {{ ⟪ pred_P ⟫ Γ, ℕ, A with so::(so_Some sn)::anns ⊩ #1 : ℕ @ sn }} by mauto 4.
    assert {{ ⟪ pred_P ⟫ Γ, ℕ, A with so::(so_Some sn)::anns  ⊩ succ #1 : ℕ @ sn }} by mauto 4.
    assert {{ ⟪ pred_P ⟫ Γ, ℕ, A with so::(so_Some sn)::anns ⊩u succ #1 : ℕ @ ^ (so_Some sn) }} by mauto 3.
    mauto 4.
  }
  destruct so; induction 1; intros; rename Γ0 into Δ.
  - (** [glu_nat_zero] *)
    eapply glu_rel_exp_natrec_zero_helper_unsorted; revgoals; mauto 3.
  - (** [glu_nat_succ] *)
    eapply glu_rel_exp_natrec_succ_helper_unsorted; revgoals; mauto 3.
  - (** [glu_nat_neut] *)
    eapply glu_rel_exp_natrec_neut_helper_unsorted; revgoals; mauto 3.
  - (** [glu_nat_zero] *)
    eapply glu_rel_exp_natrec_zero_helper_sorted; revgoals; mauto 3.
  - (** [glu_nat_succ] *)
    eapply glu_rel_exp_natrec_succ_helper_sorted; revgoals; mauto 3.
  - (** [glu_nat_neut] *)
    eapply glu_rel_exp_natrec_neut_helper_sorted; revgoals; mauto 3.
Qed.

Lemma glu_nat_resp_subtyp {P} {s} (r : Ru_nat P s) : forall (Γ : ctx P) M a,
    glu_nat r Γ M a ->
    forall s' (r' : Ru_nat P s'),
      st_subtyp s s' ->
      glu_nat r' Γ M a.
Proof.
  induction 1; intros; mauto 3.
Qed.

#[export]
  Hint Resolve glu_nat_resp_subtyp : mcpts.
  

Lemma glu_rel_exp_natrec_sorted {P} (pred_P : PredicativeSig P) : forall {sn s anns Γ A MZ MS M} {r : Ru_nat P sn},
    {{ ⟪ pred_P ⟫ Γ, ℕ with (so_Some sn)::anns ⊩u A @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u MZ : A[Id,,zero] @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A with (so_Some s)::(so_Some sn)::anns ⊩u MS : A[Wk∘Wk,,succ #1] @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ M : ℕ @ sn }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] @ ^(so_Some s) }}.
Proof.
  intros * r HA HMZ HMS HM.
  assert {{ Γ, ℕ ⊢ A : Sort@s }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} as [SbΓ] by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩u ℕ : Sort@sn @ ^so_None }} as Hℕ by mauto 4.
  pose (SbΓℕ := cons_glu_sub_pred pred_P (so_Some sn) Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P ((so_Some sn)::anns)↘ SbΓℕ }} by (invert_glu_rel_exp_unsorted Hℕ; econstructor; mauto 4; reflexivity).
  pose (SbΓℕA := cons_glu_sub_pred pred_P (so_Some s) {{{ Γ, ℕ }}} {{{ A }}} SbΓℕ).
  assert {{ EG Γ, ℕ, A ∈ glu_ctx_env pred_P ((so_Some s)::(so_Some sn)::anns) ↘ SbΓℕA }} by (invert_glu_rel_typ_unsorted HA; econstructor; mauto 4; try reflexivity).
  pose proof HM.
  invert_glu_rel_exp HM.
  pose proof HA.
  invert_glu_rel_typ_unsorted HA.
  assert (forall Δ σ ρ, SbΓℕ Δ σ ρ -> glu_rel_typ_with_sub_unsorted pred_P (so_Some s) Δ A σ ρ) by mauto 3.
  eexists; split; [eassumption |].
  intros.
  destruct_glu_rel_by_assumption SbΓ HM.
  simplify_evals.
  match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
  apply_predicate_equivalence.
  inversion_clear_by_head (@nat_glu_exp_pred P).
  assert (glu_nat r Δ {{{ M[σ] }}} m) by mauto 2.
  assert {{ Δ ⊢s σ,,M[σ] ® ρ ↦ m ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 3).
  assert (glu_rel_typ_with_sub_unsorted pred_P (so_Some s) Δ A {{{ σ,,M[σ] }}} d{{{ ρ ↦ m }}}) by mauto 2.
  inversion H12; subst.

  assert (exists r, {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\ exp_rel Δ {{{ A[σ,, M[σ]] }}} {{{ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}} r) as [? []] by (eapply glu_rel_exp_natrec_helper; revgoals; mauto 4; econstructor; mauto 2).
  econstructor; mauto 3.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ Γ ⊢ M : ℕ }} by mauto 2.
  assert {{ Γ, ℕ ⊢ A : Sort@s }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,M[σ]] ≈ A[Id,,M][σ] : Sort@s }} as <- by (symmetry; mauto 2).
  assert {{ Δ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }} as -> by (econstructor; mauto 4).
  eassumption.
Qed.

Lemma glu_rel_exp_natrec_unsorted {P} (pred_P : PredicativeSig P) : forall {sn anns Γ A MZ MS M} {r : Ru_nat P sn},
    {{ ⟪ pred_P ⟫ Γ, ℕ with (so_Some sn)::anns ⊩u A @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u MZ : A[Id,,zero] @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A with so_None::(so_Some sn)::anns ⊩u MS : A[Wk∘Wk,,succ #1] @ ^so_None }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ M : ℕ @ sn }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] @ ^so_None }}.
Proof.
  intros * r HA HMZ HMS HM.
  assert {{ Γ, ℕ ⊢ A }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ with anns }} as [SbΓ] by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ with anns ⊩u ℕ : Sort@sn @ ^so_None }} as Hℕ by mauto 4.
  pose (SbΓℕ := cons_glu_sub_pred pred_P (so_Some sn) Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P ((so_Some sn)::anns)↘ SbΓℕ }} by (invert_glu_rel_exp_unsorted Hℕ; econstructor; mauto 4; reflexivity).
  pose (SbΓℕA := cons_glu_sub_pred pred_P so_None {{{ Γ, ℕ }}} {{{ A }}} SbΓℕ).
  assert {{ EG Γ, ℕ, A ∈ glu_ctx_env pred_P (so_None::(so_Some sn)::anns) ↘ SbΓℕA }} by (invert_glu_rel_typ_unsorted HA; econstructor; mauto 4; try reflexivity).
  pose proof HM.
  invert_glu_rel_exp HM.
  pose proof HA.
  invert_glu_rel_typ_unsorted HA.
  assert (forall Δ σ ρ, SbΓℕ Δ σ ρ -> glu_rel_typ_with_sub_unsorted pred_P so_None Δ A σ ρ) by mauto 3.
  eexists; split; [eassumption |].
  intros.
  destruct_glu_rel_by_assumption SbΓ HM.
  simplify_evals.
  match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
  apply_predicate_equivalence.
  inversion_clear_by_head (@nat_glu_exp_pred P).
  assert (glu_nat r Δ {{{ M[σ] }}} m) by mauto 2.
  assert {{ Δ ⊢s σ,,M[σ] ® ρ ↦ m ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 3).
  assert (glu_rel_typ_with_sub_unsorted pred_P so_None Δ A {{{ σ,,M[σ] }}} d{{{ ρ ↦ m }}}) by mauto 2.
  inversion H12; subst.

  assert (exists r, {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\ exp_rel Δ {{{ A[σ,, M[σ]] }}} {{{ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}} r) as [? []] by (eapply glu_rel_exp_natrec_helper; revgoals; mauto 4; econstructor; mauto 2).
  econstructor; mauto 3.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ Γ ⊢ M : ℕ }} by mauto 2.
  assert {{ Γ, ℕ ⊢ A }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,M[σ]] ≈ A[Id,,M][σ] }} as <- by (symmetry; mauto 2).
  assert {{ Δ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }} as -> by (econstructor; mauto 4).
  eassumption.
Qed.

Lemma glu_rel_exp_natrec {P} (pred_P : PredicativeSig P) : forall {sn so anns Γ A MZ MS M} {r : Ru_nat P sn},
    {{ ⟪ pred_P ⟫ Γ, ℕ with (so_Some sn)::anns ⊩u A @ so }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u MZ : A[Id,,zero] @ so }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A with so::(so_Some sn)::anns ⊩u MS : A[Wk∘Wk,,succ #1] @ so }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ M : ℕ @ sn }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] @ so }}.
Proof.
  intros.
  destruct so; mauto using glu_rel_exp_natrec_sorted, glu_rel_exp_natrec_unsorted.
Qed.

#[export]
Hint Resolve glu_rel_exp_natrec : mcpts.
