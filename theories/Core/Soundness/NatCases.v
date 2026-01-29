From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness Require Import
  ContextCases
  LogicalRelation
  SubstitutionCases
  TermStructureCases
  SortCases.
Import Domain_Notations.

Lemma glu_rel_exp_nat {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts Γ s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ ⊩ Γ : sts }} ->
    exists s',
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ ℕ : Sort@s : s' }}.
Proof.
  intros * ? [Sb].
  assert {{ ⊢ Γ }} by mauto 2.
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  split; mauto 3.
  eexists; repeat split; mauto 3.
  - eexists; per_sort_elem_econstructor; [eassumption | reflexivity].
  - intros.
    match_by_head1 (@glu_sort_elem P) invert_glu_sort_elem.
    apply_predicate_equivalence.
    unfold nat_glu_typ_pred.
    econstructor; mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_exp_nat : mcpts.

Lemma glu_rel_exp_sub_nat {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts sts' Γ σ Δ M s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩s σ : Δ : sts' }} ->
    {{ ⟪ pred_P ⟫ Δ : sts' ⊩ M : ℕ : s }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M[σ] : ℕ : s }}.
Proof.
  intros.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Γ ⊢ ℕ[σ] ≈ ℕ : Sort@s }} by (econstructor; mauto 2).
  assert {{ ⟪ pred_P ⟫ Γ : sts ⊩ M[σ] : ℕ[σ] : s }} by (eapply glu_rel_exp_sub; mauto 3).
  destruct H3 as [Sb [HgluΓ]].
  exists Sb.
  split; [eassumption |].
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  econstructor; mauto 3.
  invert_glu_sort_elem H9.
  apply_predicate_equivalence.
  simpl in H10.
  destruct H10.
  simpl; split; mauto 3.
  econstructor; mauto 2.  
Qed.

#[export]
Hint Resolve glu_rel_exp_sub_nat : mcpts.

Lemma glu_rel_exp_clean_inversion2'' {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts Γ Sb M s} {r : Ru_nat P s},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : ℕ : s }} ->
    glu_rel_exp_resp_sub_env pred_P s Sb M {{{ ℕ }}}.
Proof.
  intros * ? ? HM.
  assert (exists s', {{ ⟪ pred_P ⟫ Γ : sts ⊩ ℕ : Sort@s : s' }}) as [s'] by mauto 3.
  eapply glu_rel_exp_clean_inversion2 in HM; mauto 3.
Qed.

Ltac invert_glu_rel_exp H ::=
  (unshelve eapply (glu_rel_exp_clean_inversion2'' _ _ _ _ _) in H; shelve_unifiable; [eassumption |];
   unfold glu_rel_exp_resp_sub_env in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion2' _ _ _ _ _ _) in H; shelve_unifiable; [eassumption |];
     unfold glu_rel_exp_resp_sub_env in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion2 _ _ _ _ _) in H; shelve_unifiable; [eassumption | eassumption |];
     unfold glu_rel_exp_resp_sub_env in H)
  + (unshelve eapply (glu_rel_exp_clean_inversion1 _ _ _ _) in H; shelve_unifiable; [eassumption |];
     destruct H as [])
  + (inversion H; subst).

Lemma glu_rel_exp_of_nat {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts s} {r : Ru_nat P s} {Γ Sb M},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ Sb }} ->
    (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ Sb }} -> exists m, {{ ⟦ M ⟧ ρ ↘ m }} /\ glu_nat r Δ {{{ M[σ] }}} m) ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : ℕ : s }}.
Proof.
  intros * ? Hbody.
  eexists; split; mauto 3.
  intros.
  edestruct Hbody as [? []]; mauto 3.
  econstructor; mauto 3.
  - glu_sort_elem_econstructor; mauto 3; reflexivity.
  - simpl; split; mauto 3.
    econstructor; mauto 2.
Qed.

Lemma glu_rel_exp_zero {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts s} {r : Ru_nat P s} {Γ},
    {{ ⟪ pred_P ⟫ ⊩ Γ : sts }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ zero : ℕ : s }}.
Proof.
  intros * ? * [Sb].
  eapply glu_rel_exp_of_nat with (r := r); mauto 3.
  intros.
  eexists; split; mauto 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_zero : mcpts.

Lemma glu_rel_exp_succ {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts s} {r : Ru_nat P s} {Γ M},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : ℕ : s }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ succ M : ℕ : s }}.
Proof.
  intros * ? * HM.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ : sts }} as [SbΓ] by mauto 3.
  assert {{ Γ ⊢ M : ℕ }} by mauto 3.
  invert_glu_rel_exp HM.
  destruct_conjs.
  eapply glu_rel_exp_of_nat with (r := r); mauto.
  intros.
  destruct_glu_rel_exp_with_sub.
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


Lemma glu_rel_sub_extend_nat {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts sts' s} {r : Ru_nat P s} {Γ σ Δ M},
    {{ ⟪ pred_P ⟫ Γ : sts ⊩s σ : Δ : sts' }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : ℕ : s }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩s σ,,M : Δ, ℕ : (s :: sts') }}.
Proof.
  intros.
  assert {{ ⟪ pred_P ⟫ ⊩ Δ : sts' }} by mauto 2.
  assert (exists s', {{ ⟪ pred_P ⟫ Γ : sts ⊩ ℕ[σ] : Sort@s : s' }}) as [s'] by mauto 4.
  assert {{ Γ ⊢s σ : Δ }} by mauto 3.
  assert {{ Γ ⊢ ℕ ≈ ℕ[σ] : Sort@s }} by (symmetry; econstructor; mauto 2).
  assert {{ ⟪ pred_P ⟫ Γ : sts ⊩ M : ℕ[σ] : s }} by (eapply glu_rel_exp_conv'; mauto 2).
  assert (exists s'', {{ ⟪ pred_P ⟫ Δ : sts' ⊩ ℕ : Sort@s : s'' }}) as [s'']  by (eapply glu_rel_exp_nat; mauto 3).
  eapply glu_rel_sub_extend; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_sub_extend_nat : mcpts.

Lemma glu_rel_exp_natrec_zero_helper {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts sn s s' Γ SbΓ A MZ MS Δ M σ ρ am typ_rel exp_rel} {r : Ru_nat P sn},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ SbΓ }} ->
    {{ Γ, ℕ ⊢ A : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ A[Id,,zero] : Sort@s : s' }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ MZ : A[Id,,zero] : s }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ⊢ M ≈ zero : ℕ }} ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟦ A ⟧ ρ ↦ zero ↘ am }} ->
    {{ DG am ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    exists r,
      {{ rec zero ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
        {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ exp_rel }}.
Proof.
  intros * ? ? ? HMZ **.
  assert {{ Γ ⊢ MZ : A[Id,,zero] }} by mauto 3.
  invert_glu_rel_exp HMZ.
  assert (exists sn', {{ ⟪ pred_P ⟫ Γ : sts ⊩ ℕ : Sort@sn : sn' }}) as [sn' Hℕ] by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred pred_P sn Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P (sn :: sts) ↘ SbΓℕ }}.
  {
    invert_glu_rel_exp Hℕ; econstructor; mauto 3; try reflexivity.
    destruct_conjs.
    handle_functional_glu_ctx_env P.
    intros.
    assert (glu_rel_exp_with_sub pred_P sn' Δ0 {{{ ℕ }}} {{{ Sort@sn }}} σ0 ρ0) by (eapply H10; eapply H14; mauto 3).
    destruct H8.
    simplify_evals.
    econstructor; mauto.
    - glu_sort_elem_econstructor; reflexivity.
    - instantiate (1 := r).
      simpl.
      econstructor; mauto 3.
      eapply glu_ctx_env_sub_escape; mauto 3.
      eapply H14; mauto 2.      
  }
  on_all_hyp: (fun H => match type of H with {{ ⟪ ?pred_P ⟫ ^?Γ : ?sts ⊩ ^?M : ^?A : ?s }} => simpl in H end).
  simpl in HMZ.
  simpl in H1.
  simpl in Hℕ.
  destruct_conjs.
  handle_functional_glu_ctx_env P.
  assert (x Δ σ ρ) by (eapply H24; mauto 3).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  rename m1 into mz.
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
  assert {{ Δ ⊢s (q σ)∘(Id,,zero) ≈ σ,,zero : Γ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ ⊢ A ≈ A : Sort@s }} by mauto 2.
  assert {{ Δ ⊢ A[(q σ)∘(Id,,zero)] ≈ A[σ,,zero] : Sort@s }} by (eapply eq_exp_eq_sub_typ; mauto 3).
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] : Sort@s }} by (etransitivity; eassumption).
  assert {{ Δ ⊢ zero ≈ zero[σ] : ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ,,zero ≈ σ,,zero[σ] : Γ, ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,zero] ≈ A[σ,,zero[σ]] : Sort@s }} by (symmetry; mauto 4).
  assert {{ Γ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ,,zero[σ] ≈ (Id,,zero)∘σ : Γ, ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[(Id,,zero)∘σ] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ A[(Id,,zero)∘σ] ≈ A[Id,,zero][σ] : Sort@s }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[Id,,zero][σ] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] : Sort@s }} as <- by mauto 2.
  assert {{ Δ ⊢ MZ[σ] : A[q σ][Id,,zero] }} by bulky_rewrite.
  assert {{ Δ, ℕ ⊢ A[q σ] : Sort@s }} by mauto 3.  
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by (eapply (@sub_weak_compose_weak_extend_succ_var_1 _ _ _ _ _ r); mauto 2).
  assert {{ Δ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q σ)] }} by (eapply (@exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1 _ _ _ _ _ _ _ r); mauto 2).
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[Wk∘Wk,,succ #1][q (q σ)] }} by mauto 3.
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

Lemma cons_glu_sub_pred_nat_helper {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts Γ SbΓ Δ σ ρ s M m} {r : Ru_nat P s},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ SbΓ }} ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    glu_nat r Δ M m ->
    {{ Δ ⊢s σ,,M ® ρ ↦ m ∈ cons_glu_sub_pred pred_P s Γ {{{ ℕ }}} SbΓ }}.
Proof.
  intros * ? HM ?.
  assert {{ DG ℕ ∈ glu_sort_elem pred_P s ↘ nat_glu_typ_pred r ↘ nat_glu_exp_pred r }} by (glu_sort_elem_econstructor; reflexivity).
  eapply cons_glu_sub_pred_helper; mauto 3.
  econstructor; [unfold nat_glu_typ_pred |]; mauto 3.
  econstructor; mauto 3.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_nat_helper : mcpts.

Lemma glu_rel_exp_natrec_succ_helper {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts s' s Γ SbΓ A MZ MS Δ M M' m' σ ρ am typ_rel exp_rel sn} {r : Ru_nat P sn},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ SbΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ : (sn :: sts) ⊩ A : Sort@s : s' }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A : (s :: (sn :: sts)) ⊩ A[Wk∘Wk,,succ #1] : Sort@s : s' }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A : (s :: (sn :: sts)) ⊩ MS : A[Wk∘Wk,,succ #1] : s }} ->
    {{ Δ ⊢ M ≈ succ M' : ℕ }} ->
    glu_nat r Δ M' m' ->
    (forall σ ρ am typ_rel exp_rel,
        {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
        {{ ⟦ A ⟧ ρ ↦ m' ↘ am }} ->
        {{ DG am ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
        exists e,
          {{ rec m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\
            {{ Δ ⊢ rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M'] ® e ∈ exp_rel }}) ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟦ A ⟧ ρ ↦ succ m' ↘ am }} ->
    {{ DG am ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    exists e,
      {{ rec succ m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\
        {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® e ∈ exp_rel }}.
Proof.
  intros * ? HA ? ? HMS **.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ : sts }} by (eexists; eassumption).
  assert (exists sn', {{ ⟪ pred_P ⟫ Γ : sts ⊩ ℕ : Sort@sn : sn' }}) as [sn' Hℕ] by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred pred_P sn Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P (sn :: sts) ↘ SbΓℕ }}.
  {
    invert_glu_rel_exp Hℕ; econstructor; mauto 3; try reflexivity.
    intros.
    eapply glu_rel_exp_typ_implies_glu_rel_typ; mauto 2.
    destruct_conjs.
    handle_functional_glu_ctx_env P.
    mauto 2.
  }

  assert {{ Γ, ℕ ⊢ A : Sort@s }} by mauto 2.
  invert_glu_rel_exp HA.
  pose (SbΓℕA := cons_glu_sub_pred pred_P s {{{ Γ, ℕ }}} A SbΓℕ).
  assert {{ EG Γ, ℕ, A ∈ glu_ctx_env pred_P (s :: (sn :: sts)) ↘ SbΓℕA }}.
  {
    econstructor; mauto 3; try reflexivity.
    intros.
    eapply glu_rel_exp_typ_implies_glu_rel_typ; mauto 2.
    destruct_conjs.
    handle_functional_glu_ctx_env P.
    mauto 2.
  }

  assert {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} by mauto 2.
  invert_glu_rel_exp HMS.
  assert {{ Δ ⊢s σ,,M' ® ρ ↦ m' ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 3).
  destruct_conjs.
  apply_functional_glu_ctx_env.
  (* handle_functional_glu_ctx_env P. *)
  simpl in H15.
  rewrite H20 in H15.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  destruct_conjs.
  match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
  (* apply_predicate_equivalence. *)
  unfold sort_glu_exp_pred' in *.
  unfold glu_sort_typ_rec in *.
  rewrite H24 in H25.
  destruct_conjs.
  match goal with
  | _: {{ ⟦ A ⟧ ^{{{ ρ,m' }}} ↘ ^?m }}, _: {{ DG ^?m ∈ glu_sort_elem pred_P ?s ↘ ?P ↘ ?El }} |- _ =>
      rename m into am';
      rename P into typ_rel';
      rename El into exp_rel'
  end.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ ⊢ Δ, ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ : Γ }} by mauto 3.
  assert {{ Δ, ℕ ⊢ A[q σ] : Sort@s }} by mauto 3.
  assert {{ ⊢ Δ, ℕ, A[q σ] }} by mauto 2.
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
  assert {{ Δ ⊢ A[(q σ)∘(Id,,zero)] ≈ A[σ,,zero] : Sort@s }} by (eapply eq_exp_eq_sub_typ; mauto 3).
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] : Sort@s }} by (etransitivity; mauto 3).
  
  assert {{ Δ ⊢ zero ≈ zero[σ] : ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ,,zero ≈ σ,,zero[σ] : Γ, ℕ }} by mauto 3.    
  assert {{ Δ ⊢ A[σ,,zero] ≈ A[σ,,zero[σ]] : Sort@s }} by mauto 4.
  assert {{ Γ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ,,zero[σ] ≈ (Id,,zero)∘σ : Γ, ℕ }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[(Id,,zero)∘σ] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ A[(Id,,zero)∘σ] ≈ A[Id,,zero][σ] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[Id,,zero][σ] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ MZ[σ] : A[q σ][Id,,zero] }} by bulky_rewrite.
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by (eapply (@sub_weak_compose_weak_extend_succ_var_1 _ _ _ _ _ r); mauto 2).

  assert {{ Δ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q σ)] }} by (eapply (@exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1 _ _ _ _ _ _ _ r); mauto 2).
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[Wk∘Wk,,succ #1][q (q σ)] }} by mauto 3.
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by mauto 3.
  pose (R := {{{ rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}}).
  assert (exists e, {{ rec m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\ {{ Δ ⊢ R : A[σ,,M'] ® e ∈ exp_rel' }}) as [e' []] by mauto 3.
  assert {{ Δ ⊢ R : A[σ,,M'] }}.
  {
    assert {{ Δ ⊢ A[q σ][Id,,M'] ≈ A[σ,,M'] }} by (eapply exp_eq_elim_sub_rhs_typ; mauto 3).
    mauto 3.
  }
  
  assert {{ Δ ⊢s σ,,M',,R ® (ρ ↦ m') ↦ e' ∈ SbΓℕA }}.
  {
    unfold SbΓℕA.
    econstructor; mauto 3.
    - assert {{ Δ ⊢ A[Wk][σ,,M',,R] ≈ A[Wk∘(σ,,M',,R)] : Sort@s }}.
      {
        symmetry.
        eapply exp_eq_sub_compose_typ_sort; mauto 3; econstructor; mauto 3.
      }
      assert {{ Δ ⊢s Wk∘(σ,,M',,R) ≈ σ,,M' : Γ, ℕ }} by mauto 3.
      gen_presup H63.
      assert {{ Δ ⊢ A[Wk∘(σ,,M',,R)] ≈ A[σ,,M'] : Sort@s }} by mauto 3.
      assert {{ Δ ⊢ A[Wk][σ,,M',,R] ≈ A[σ,,M'] : Sort@s }} as -> by mauto 4.

      assert {{ Δ ⊢ R ≈ #0[σ,,M',,R] : A[σ,,M'] }} by (symmetry; mauto 4).
      eapply glu_sort_elem_trm_resp_exp_eq; mauto 3.
    - simpl.
      rewrite <- H21.
      assert {{ Δ ⊢s Wk∘(σ,,M',,R) ≈ σ,,M' : Γ, ℕ }} as -> by mauto 3.
      eassumption.
  }
  simpl in H62.
  rewrite H18 in H62.  
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
  apply_predicate_equivalence.
  clear_dups.
  unfold sort_glu_exp_pred' in *.
  unfold glu_sort_typ_rec in *.
  destruct_conjs.
  handle_functional_glu_sort_elem P.
  match goal with
  | _: {{ ⟦ MS ⟧ ^{{{ ρ, m', e' }}} ↘ ^?m }} |- _ =>
      rename m into ms
  end.
  exists ms; split; mauto 3.
  assert {{ Δ ⊢s σ,,M ≈ σ,,succ M' : Γ, ℕ }} as -> by mauto 3.
  assert {{ Δ ⊢ succ M' : ℕ }} by mauto 3.
  assert {{ Δ ⊢ succ M' : ℕ[σ] }} by mauto 3.
  assert {{ Δ ⊢s (q σ)∘(Id,,succ M') ≈ σ,,succ M' : Γ, ℕ }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,succ M'] ≈ A[(q σ)∘(Id,,succ M')] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ A[(q σ)∘(Id,,succ M')] ≈ A[q σ][Id,,succ M'] : Sort@s }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,succ M'] ≈ A[q σ][Id,,succ M'] : Sort@s }} as -> by mauto 4.
  assert {{ Δ ⊢ rec succ M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[q σ][Id,,succ M'] }} as <- by (econstructor; mauto 3).
  assert {{ Δ ⊢ rec succ M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ MS[q (q σ)][Id,,M',,R] : A[q σ][Id,,succ M'] }} as -> by mauto 2.
  assert {{ Δ ⊢ R : A[q σ][Id,,M'] }}.
  {
    assert {{ Δ ⊢ A[σ,,M'] ≈ A[q σ][Id,,M'] }} by mauto 4.
    gen_presup H25.
    eapply wf_conv; mauto 2.
  }
  assert {{ Δ ⊢s Id,,M',,R : Δ, ℕ, A[q σ] }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,succ M'] ≈ A[q σ][Id,,succ M'] : Sort@s }} as <- by mauto 3.
  assert {{ Δ ⊢ A[Wk∘Wk,,succ #1][σ,,M',,R] ≈ A[σ,,succ M'] : Sort@s }} as <-.
  {
    transitivity {{{ A[(Wk∘Wk,,succ #1)∘(σ,,M',,R)] }}}.
    - symmetry; mauto 3.
      eapply exp_eq_sub_compose_typ_sort; mauto 3.
      eapply (@sub_weak_compose_weak_extend_succ_var_1 _ _ _ _ _ r); mauto 3.
    - enough {{ Δ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M',,R) ≈ σ,,succ M' : Γ, ℕ }}.
      {
        eapply eq_exp_eq_sub_typ; mauto 4.
        gen_presup H29.
        eassumption.
      }
      assert {{ Δ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M',,R) ≈ ((Wk∘Wk)∘(σ,,M',,R)),,(succ #1)[σ,,M',,R] : Γ, ℕ }}.
      {
        eapply wf_sub_eq_extend_compose; mauto 3.
        - econstructor; mauto 3.
        - assert {{ Γ, ℕ, A ⊢ ℕ[Wk∘Wk] ≈ ℕ : Sort@sn }}.
          {
            eapply wf_exp_eq_nat_sub; mauto 3.
            econstructor; mauto 3.
          }
          gen_presup H29.
          econstructor; mauto 3.
      }
      transitivity {{{ ((Wk∘Wk)∘(σ,,M',,R)),,(succ #1)[σ,,M',,R] }}}; mauto 2.
      assert {{ Δ ⊢ (succ #1)[σ,,M',,R] ≈ succ M' : ℕ }}.
      {
        transitivity {{{ succ (#1[σ,,M',,R]) }}}; mauto 4.
        assert {{ Δ ⊢ #1[σ,,M',,R] ≈ M' : ℕ }} by (transitivity {{{ #0[σ,,M'] }}}; mauto 3).
        mauto 3.
      }
      eapply wf_sub_eq_extend_cong; mauto 4.
      + assert {{ Δ ⊢s (Wk∘Wk)∘(σ,,M',,R) ≈ Wk∘(Wk∘(σ,,M',,R)) : Γ }} by (eapply wf_sub_eq_compose_assoc; mauto 3).
        transitivity {{{ Wk∘(Wk∘(σ,,M',,R)) }}}; mauto 2.
        assert {{ Δ ⊢s (Wk∘(σ,,M',,R)) ≈ (σ,,M') : Γ, ℕ }} by mauto 3.
        assert {{ Δ ⊢s Wk∘(Wk∘(σ,,M',,R)) ≈ Wk∘(σ,,M') : Γ }} by (eapply wf_sub_eq_compose_cong; mauto 3).
        transitivity {{{ Wk∘(σ,,M') }}}; mauto 2.
      + eapply wf_exp_eq_conv'; mauto 2.
        symmetry.
        enough {{ Δ ⊢ ℕ[(Wk∘Wk)∘(σ,,M',,R)] ≈ ℕ : Sort@sn }} by mauto 2.
        econstructor; mauto 2.
        econstructor; mauto 3.
        do 2 econstructor; mauto 2.
  }
  assert {{ Δ ⊢ MS[q (q σ)][Id,,M',,R] ≈ MS[σ,,M',,R] : A[Wk∘Wk,,succ #1][σ,,M',,R] }} as -> by mauto 4.
  eassumption.
Qed.

Lemma cons_glu_sub_pred_q_helper {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {s' sts Γ SbΓ Δ σ ρ s A a},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ SbΓ }} ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ A : Sort@s : s' }} ->
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ Δ, A[σ] ⊢s q σ ® ρ ↦ ⇑! a (length Δ) ∈ cons_glu_sub_pred pred_P s Γ A SbΓ }}.
Proof.
  intros * ? ? HA ?.
  assert {{ Γ ⊢ A : Sort@s }} by mauto 2.
  invert_glu_rel_exp HA.
  destruct_conjs.
  handle_functional_glu_ctx_env P.
  
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).  
  
  apply_predicate_equivalence.
  unfold sort_glu_exp_pred' in *.
  unfold glu_sort_typ_rec in *.
  destruct_conjs.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ ⊢ Δ, A[σ] }} by mauto 3.
  assert {{ Δ, A[σ] ⊢w Wk : Δ }} by mauto 2.
  eapply cons_glu_sub_pred_helper; mauto 2.
  - apply_predicate_equivalence; eassumption.
  - apply_predicate_equivalence.
    eapply glu_ctx_env_sub_monotone; eassumption.
  - assert {{ Δ, A[σ] ⊢s Wk : Δ }} by mauto 2.
    assert {{ Δ, A[σ] ⊢ A[σ∘Wk] ≈ A[σ][Wk] : Sort@s }} as -> by mauto 3.
    eapply var0_glu_elem; eassumption.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_q_helper : mcpts.

Lemma cons_glu_sub_pred_q_nat_helper {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts Γ SbΓ Δ σ ρ s} {r : Ru_nat P s},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ SbΓ }} ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ Δ, ℕ ⊢s q σ ® ρ ↦ ⇑! ℕ (length Δ) ∈ cons_glu_sub_pred pred_P s Γ {{{ ℕ }}} SbΓ }}.
Proof.
  intros.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ : sts }} by (eexists; eassumption).
  assert (exists s', {{ ⟪ pred_P ⟫ Γ : sts ⊩ ℕ : Sort@s : s' }}) as [s' Hℕ] by mauto 3.
  assert {{ ⟦ ℕ ⟧ ρ ↘ ℕ }} by mauto 3.
  assert {{ Δ, ℕ[σ] ⊢s q σ ® ρ ↦ ⇑! ℕ (length Δ) ∈ cons_glu_sub_pred pred_P s Γ {{{ ℕ }}} SbΓ }} by mauto 3.
  assert {{ Δ ⊢ ℕ[σ] ≈ ℕ : Sort@s }} by (econstructor; mauto 4).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P (s :: sts) ↘ cons_glu_sub_pred pred_P s Γ {{{ ℕ }}} SbΓ }}.
  {
    invert_glu_rel_exp Hℕ; destruct_conjs; econstructor; mauto 3.
    handle_functional_glu_ctx_env P.
    split; intros * Hglu; invert_glu_ctx_env Hglu;
      [rewrite -> H7 in H12 | rewrite <- H7 in H12];
      econstructor;
      mauto 2.
  }
  assert {{ ⊢ Δ }} by mauto 2.
  cbn.
  assert {{ ⊢ Δ, ℕ[σ] ≈ Δ, ℕ }} as <- by mauto 3.
  eassumption.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_q_nat_helper : mcpts.


Lemma full_per_typ_elem_implies_per_sort_elem {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {R a a'},
    {{ DF a ≈ a' ∈ per_typ_elem pred_P ↘ R }} ->
    exists s, {{ DF a ≈ a' ∈ per_sort_elem pred_P s ↘ R }}.
Proof.
  intros.
  inversion_clear H.
  - assert (exists s', Ax P s s') as [s'] by (eapply full_P; mauto 2).
    exists s'.
    eapply per_sort_elem_core_sort'; eassumption.    
  - eauto.
Qed.  
  
Lemma glu_rel_exp_natrec_neut_helper {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {sts s s' Γ SbΓ A MZ MS Δ M a m σ ρ am typ_rel exp_rel sn} {r : Ru_nat P sn},
    {{ EG Γ ∈ glu_ctx_env pred_P sts ↘ SbΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ : (sn :: sts) ⊩ A : Sort@s : s' }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ A[Id,,zero] : Sort@s : s' }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ MZ : A[Id,,zero] : s }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A : (s :: (sn :: sts)) ⊩ A[Wk∘Wk,,succ #1] : Sort@s : s' }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A : (s :: (sn :: sts)) ⊩ MS : A[Wk∘Wk,,succ #1] : s }} ->
    {{ Dom m ≈ m ∈ per_bot }} ->
    (forall Δ' τ V, {{ Δ' ⊢w τ : Δ }} -> {{ Rne m in length Δ' ↘ V }} -> {{ Δ' ⊢ M[τ] ≈ V : ℕ }}) ->
    {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟦ A ⟧ ρ ↦ ⇑ a m ↘ am }} ->
    {{ DG am ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    exists e,
      {{ rec ⇑ a m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\
        {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® e ∈ exp_rel }}.
Proof.
  intros * ? ? HA ? HMZ ? HMS **.
  assert {{ Γ ⊢ MZ : A[Id,,zero] }} by mauto 2.
  invert_glu_rel_exp HMZ.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ : sts }} by (eexists; eassumption).
  assert (exists sn', {{ ⟪ pred_P ⟫ Γ : sts ⊩ ℕ : Sort@sn : sn' }}) as [sn' Hℕ] by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred pred_P sn Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P (sn :: sts) ↘ SbΓℕ }}.
  {
    invert_glu_rel_exp Hℕ; econstructor; mauto 3; try reflexivity.
    destruct_conjs; handle_functional_glu_ctx_env P.
    intros.
    rewrite H15 in H.
    eapply glu_rel_exp_typ_implies_glu_rel_typ; mauto 2.
  }

  assert {{ Γ, ℕ ⊢ A : Sort@s }} by mauto 2.
  pose proof HA.
  invert_glu_rel_exp HA.
  pose (SbΓℕA := cons_glu_sub_pred pred_P s {{{ Γ, ℕ }}} A SbΓℕ).
  assert {{ EG Γ, ℕ, A ∈ glu_ctx_env pred_P (s :: (sn :: sts)) ↘ SbΓℕA }}.
  {
    econstructor; mauto 3; try reflexivity.
    destruct_conjs; handle_functional_glu_ctx_env P.
    intros.
    rewrite H16 in H.
    eapply glu_rel_exp_typ_implies_glu_rel_typ; mauto 2.    
  }

  assert {{ Δ ⊢s σ,,M ® ρ ↦ ⇑ a m ∈ SbΓℕ }}.
  {
    unfold SbΓℕ.
    eapply (@cons_glu_sub_pred_nat_helper _ _ full_P _ _ _ _ _ _ _ _ _ r); mauto 2.
  }
  
  assert {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} by mauto 2.
  invert_glu_rel_exp HMS.
  destruct_conjs.
  apply_functional_glu_ctx_env.
  simpl in H15.
  rewrite H23 in H15.
  assert (glu_rel_exp_with_sub pred_P s' Δ A {{{ Sort@s }}} {{{ σ,,M }}} {{{ ρ, ^ d{{{ ⇑ a m }}} }}}) by mauto 2.
  simpl in H4.
  rewrite H25 in H4.
  assert (glu_rel_exp_with_sub pred_P s Δ MZ {{{ A[Id,,zero] }}} σ ρ) by mauto 2.

  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
  unfold sort_glu_exp_pred' in *.
  unfold glu_sort_typ_rec in *.
  rewrite H28 in H30.
  destruct_conjs.
  apply_functional_glu_sort_elem.
  (* handle_functional_glu_sort_elem P. *)
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
  assert {{ ⊢ Δ, ℕ, A[q σ] }} by mauto 2.
  (* Not sure why: mauto 3 solves this goal, but leaves 3 shelved goals *)
  assert {{ Δ ⊢ M : ℕ }}.
  {
    assert {{ Δ ⊢s σ,,M : Γ, ℕ }} by mauto 3.
    assert (exists Γ' A', {{ ⊢ Γ', A' ≈ Γ, ℕ }} /\ {{ Δ ⊢s σ : Γ' }} /\ {{ Δ ⊢ M : A'[σ] }}) as [Γ' [A' [? []]]] by mauto 2.
    inversion_clear H47.
    assert {{ Δ ⊢ A'[σ] ≈ ℕ }} by (transitivity {{{ ℕ[σ] }}}; mauto 3).
    eapply wf_conv; mauto 2.
    econstructor; mauto 2.
  }
  
  assert {{ Δ ⊢ ℕ : Sort@sn }} by mauto 3.
  assert {{ Δ ⊢ ℕ[σ] ≈ ℕ : Sort@sn }} by (econstructor; mauto 2).
  assert {{ Δ ⊢ M : ℕ[σ] }} by mauto 3.
  assert {{ Δ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢ zero[σ] ≈ zero : ℕ }} by mauto 3.
  assert {{ Δ, ℕ ⊢s q σ : Γ, ℕ }} by mauto 3.

  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[(q σ)∘(Id,,zero)] : Sort@s }} by (symmetry; mauto 4).
  assert {{ Δ ⊢s (q σ)∘(Id,,zero) ≈ σ,,zero : Γ, ℕ }} by mauto 4.
  assert {{ Δ ⊢ A[(q σ)∘(Id,,zero)] ≈ A[σ,,zero] : Sort@s }} by (eapply eq_exp_eq_sub_typ; mauto 3).
  assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢s σ,,zero ≈ σ,,zero[σ] : Γ, ℕ }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,zero] ≈ A[σ,,zero[σ]] : Sort@s }} by (eapply eq_exp_eq_sub_typ; mauto 3).
  assert {{ Γ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Δ ⊢s σ,,zero[σ] ≈ (Id,,zero)∘σ : Γ, ℕ }} by mauto 4.
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[(Id,,zero)∘σ] : Sort@s }} by (eapply eq_exp_eq_sub_typ; mauto 3).
  assert {{ Δ ⊢ A[(Id,,zero)∘σ] ≈ A[Id,,zero][σ] : Sort@s }} by (eapply exp_eq_sub_compose_typ_sort; mauto 3).
  assert {{ Δ ⊢ A[σ,,zero[σ]] ≈ A[Id,,zero][σ] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ MZ[σ] : A[q σ][Id,,zero] }} by bulky_rewrite.
  assert {{ Δ, ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Δ, ℕ }} by (eapply (@sub_weak_compose_weak_extend_succ_var_1 _ _ _ _ _ r); mauto 3).
  assert {{ Δ, ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,, succ #1][q (q σ)] }} by (eapply (@exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1 _ _ _ _ _ _ _ r); mauto 3). 
  assert {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by (eapply wf_conv; mauto 3).
  pose (R := {{{ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}}).
  enough {{ Δ ⊢ R : A[σ,,M] ® rec m under ρ return A | zero -> mz | succ -> MS end ∈ glu_elem_bot pred_P s am }} by (eapply realize_glu_elem_bot; mauto 3).
  econstructor; mauto 3.
  - assert {{ Δ ⊢ A[q σ][Id,,M] ≈ A[σ,,M] }} by (eapply exp_eq_elim_sub_rhs_typ; mauto 2).
    eapply wf_conv; mauto 2.    
    econstructor; mauto 3.
  - assert {{ Δ ⊢ MZ[σ] : A[Id,,zero][σ] ® mz ∈ glu_elem_top pred_P s az }} as [] by (eapply realize_glu_elem_top; eassumption).
    apply_functional_glu_sort_elem.
    (* handle_functional_glu_sort_elem P. *)
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
    destruct_rel_typ.
    assert (rel_typ_unsorted pred_P {{{ ℕ }}} ρ {{{ ℕ }}} ρ (head_rel0 ρ ρ H82)) by mauto 2.
    inversion_clear H83.
    assert {{ Dom ! k ≈ ! k ∈ (@per_bot P) }} by mauto 3.
    assert {{ Dom ρ ↦ ⇑! ℕ k ≈ ρ ↦ ⇑! ℕ k ∈ env_relΓℕ }}.
    {
      apply_relation_equivalence.
      econstructor; mauto 3.
      simpl.
      simplify_evals.
      inversion_clear H86.
      invert_per_sort_elem H84.
      eapply H84.
      eapply (@per_bot_then_per_typ_elem _ pred_P); mauto 2.
      econstructor; mauto 3.
      per_sort_elem_econstructor; try reflexivity.
      eassumption.
    }

    assert {{ Dom ρ ↦ succ ⇑! ℕ k ≈ ρ ↦ succ ⇑! ℕ k ∈ env_relΓℕ }}.
    {
      apply_relation_equivalence.
      econstructor; mauto 3.
      simpl.
      simplify_evals.
      inversion_clear H86.
      invert_per_sort_elem H84.
      eapply H84.
      eapply per_nat_succ.
      eapply (@per_bot_then_per_typ_elem _ pred_P); mauto 2.
      econstructor; mauto 3.
      per_sort_elem_econstructor; try reflexivity.
      eassumption.
    }

    destruct_rel_typ.
    destruct_rel_typ_unsorted.
    invert_rel_typ_body.
    match goal with
    | _: {{ ⟦ A ⟧ ρ ↦ ⇑! ℕ k ↘ ^?a }}, _: {{ ⟦ A ⟧ ρ ↦ (succ ⇑! ℕ k) ↘ ^?a' }} |- _ =>
        rename a into as'; (** We cannot use [as] as a name *)
        rename a' into asucc
    end.

    assert (exists s', per_sort_elem pred_P s' (head_rel d{{{ ρ ↦ ⇑! ℕ k }}} d{{{ ρ ↦ ⇑! ℕ k }}} H87) as' as') as [s3] by (eapply full_per_typ_elem_implies_per_sort_elem; eassumption).
    
    assert {{ Dom (ρ ↦ ⇑! ℕ k) ↦ ⇑! as' (S k) ≈ (ρ ↦ ⇑! ℕ k) ↦ ⇑! as' (S k) ∈ env_relΓℕA }} as HΓℕA.
    {
      apply_relation_equivalence.
      econstructor; mauto 3.
      simpl.
      eapply (@per_bot_then_per_elem P pred_P); mauto 3.      
    }

    apply_relation_equivalence.
    (on_all_hyp_rev: fun H => destruct (H _ _ HΓℕA)).
    destruct_conjs.
    destruct_by_head (@rel_typ_unsorted P).
    (* invert_rel_typ_body. *)
    (* invert_rel_typ_unsorted_body. *)
    destruct_by_head (@rel_exp P).
    functional_eval_rewrite_clear.
    rename m0 into ms.
    (* match goal with *)
    (* | _: {{ ⟦ MS ⟧ ρ ↦ ⇑! ℕ k ↦ ⇑! as' (S k) ↘ ^?m }} |- _ => *)
    (*     rename m into ms *)
    (* end. *)
    simplify_evals.
    
    
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
    assert {{ Δ' ⊢s σ∘τ ® ρ ∈ SbΓ }} by (eapply glu_ctx_env_sub_monotone; only 1-2: rewrite H25; eassumption).
    assert {{ Δ', ℕ ⊢s q (σ∘τ) ® ρ ↦ ⇑! ℕ (length Δ') ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 3).
    destruct_glu_rel_exp_with_sub.
    simplify_evals.
    match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
    (* apply_predicate_equivalence. *)
    unfold sort_glu_exp_pred' in *.
    unfold glu_sort_typ_rec in *.
    rewrite H77 in H79.
    destruct_conjs.
    apply_functional_glu_sort_elem.
    (* handle_functional_glu_sort_elem P. *)
    match_by_head (@read_ne P) ltac:(fun H => directed inversion_clear H).
    apply_functional_glu_sort_elem.
    (* handle_functional_glu_sort_elem P. *)
    match goal with
    | _: {{ ⟦ A ⟧ ^?ρ' ↦ ⇑! ℕ (length Δ') ↘ ^?a }} |- _ =>
        rename ρ' into ρ;
        rename a into aΔ'
    end.
    assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q (σ∘τ)) ® (ρ ↦ ⇑! ℕ (length Δ')) ↦ ⇑! aΔ' (length {{{ Δ', ℕ }}}) ∈ SbΓℕA }} by (unfold SbΓℕA; mauto 3).
    destruct_glu_rel_exp_with_sub.
    simplify_evals.
    match_by_head glu_sort_elem ltac:(fun H => directed invert_glu_sort_elem H).
    apply_predicate_equivalence.
    unfold sort_glu_exp_pred' in *.
    destruct_conjs.
    clear_dups.
    handle_functional_glu_sort_elem.
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
    assert {{ Δ', ℕ ⊢ A[q (σ∘τ)] ® glu_typ_top i aΔ' }} as [] by (eapply realize_glu_typ_top; eassumption).
    assert {{ Δ ⊢ MZ[σ] : A[Id,,zero][σ] ® mz ∈ glu_elem_top i az }} as [] by (eapply realize_glu_elem_top; eassumption).
    assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q (σ∘τ))] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] ® ms ∈ glu_elem_top i asucc }} as []
        by (eapply realize_glu_elem_top; eassumption).
    assert {{ Δ ⊢s σ,,M : Γ, ℕ }} by mauto 4.
    assert {{ Δ' ⊢s σ∘τ,,M[τ] : Γ, ℕ }} by mauto 4.
    assert {{ Δ' ⊢ A[σ,,M][τ] ≈ A[(σ,,M)∘τ] : Type@i }} as -> by mauto 3.
    assert {{ Δ' ⊢ A[(σ,,M)∘τ] ≈ A[σ∘τ,,M[τ]] : Type@i }} as -> by mauto 3.
    assert {{ Δ' ⊢ A[σ∘τ,,M[τ]] ≈ A[q σ][τ,,M[τ]] : Type@i }} as -> by (eapply sub_decompose_q_typ; mauto 2).
    assert {{ Δ' ⊢ R[τ] ≈ rec M[τ] return A[q σ][q τ] | zero -> MZ[σ][τ] | succ -> MS[q (q σ)][q (q τ)] end : A[q σ][τ,,M[τ]] }} as -> by mauto 3.
    assert {{ Δ' ⊢ A[q σ][q τ][Id,,M[τ]] ≈ A[q σ][τ,,M[τ]] : Type@i }} as <- by mauto 3.
    assert {{ Δ', ℕ ⊢w Id : Δ', ℕ }} by mauto 3.
    eapply wf_exp_eq_natrec_cong'; fold ne_to_exp nf_to_exp; [| | | mautosolve 3].
    + assert {{ Δ', ℕ ⊢s q σ∘q τ : Γ, ℕ }} by mauto 3.
      assert {{ Δ', ℕ ⊢ A[q σ∘q τ] : Type@i }} by mauto 3.
      assert {{ Δ', ℕ ⊢ A[q (σ∘τ)][Id] ≈ A' : Type@i }} as <- by mauto 3.
      transitivity {{{ A[q σ∘q τ] }}}; mauto 3.
      transitivity {{{ A[q σ∘q τ][Id] }}}; mauto 3.
      eapply exp_eq_sub_cong_typ1; mauto 3.
    + assert {{ Δ, ℕ ⊢ A[q σ] : Type@i }} by mauto 3.
      assert {{ Δ', ℕ ⊢s q τ : Δ, ℕ }} by mauto 3.
      assert {{ Δ' ⊢ zero : ℕ }} by mauto 3.
      assert {{ Δ' ⊢ A[q σ][q τ][Id,,zero] ≈ A[q σ][τ,,zero] : Type@i }} as -> by mauto 3.
      assert {{ Δ' ⊢ zero ≈ zero[τ] : ℕ }} by mauto 3.
      assert {{ Δ' ⊢ zero ≈ zero[τ] : ℕ[τ] }} by mauto 4.
      assert {{ Δ' ⊢s τ,,zero ≈ τ,,zero[τ] : Δ, ℕ }} by mauto 3.
      assert {{ Δ' ⊢ A[q σ][τ,,zero] ≈ A[q σ][τ,,zero[τ]] : Type@i }} by (symmetry; mauto 4).
      assert {{ Δ' ⊢ A[q σ][τ,,zero] ≈ A[q σ][Id,,zero][τ] : Type@i }} as -> by mauto 4.
      assert {{ Δ ⊢ A[q σ][Id,,zero] ≈ A[Id,,zero][σ] : Type@i }} by mauto 3.
      assert {{ Δ' ⊢ A[q σ][Id,,zero][τ] ≈ A[Id,,zero][σ][τ] : Type@i }} as -> by mauto 3.
      mauto 3.
    + assert {{ Δ, ℕ ⊢ A[q σ] : Type@i }} by mauto 3.
      assert {{ Δ', ℕ ⊢s q τ : Δ, ℕ }} by mauto 2.
      assert {{ Δ, ℕ, A[q σ] ⊢s q (q σ) : Γ, ℕ, A }} by mauto 2.
      assert {{ Δ', ℕ, A[q σ][q τ] ⊢s q (q τ) : Δ, ℕ, A[q σ] }} by mauto 2.
      assert {{ Δ', ℕ ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, ℕ }} by mauto 4.
      assert {{ ⊢ Δ', ℕ, A[q (σ∘τ)] }} by mauto 2.
      assert {{ Δ', ℕ ⊢ A[q σ][q τ] ≈ A[q σ∘q τ] : Type@i }} by mauto 2.
      assert {{ Δ', ℕ ⊢ A[q σ∘q τ] ≈ A[q (σ∘τ)] : Type@i }} by mauto 2.
      assert {{ ⊢ Δ', ℕ, A[q σ∘q τ] ≈ Δ', ℕ, A[q (σ∘τ)] }} by mauto 3.
      assert {{ ⊢ Δ', ℕ, A[q σ][q τ] ≈ Δ', ℕ, A[q (σ∘τ)] }} by mauto 4.
      assert {{ ⊢ Δ', ℕ, A[q σ][q τ] ≈ Δ', ℕ, A[q (σ∘τ)] }} as -> by eassumption.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s Wk∘Wk,,succ #1 : Δ', ℕ }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[q σ][q τ][Wk∘Wk,,succ #1] ≈ A[q (σ∘τ)][Wk∘Wk,,succ #1] : Type@i }} as -> by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[q (σ∘τ)][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q (σ∘τ))] : Type@i }} as -> by mauto 3 using exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1.
      assert {{ Δ', ℕ ⊢s q (σ∘τ) : Γ, ℕ }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q (σ∘τ)) : Γ, ℕ, A }} by mauto 2.
      assert {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q τ) : Δ, ℕ, A[q σ] }} by mauto 2.
      assert {{ Δ', ℕ, A[q σ][q τ] ⊢ MS[q (q σ)][q (q τ)] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 3.
      assert {{ Δ', ℕ, A[q σ∘q τ] ⊢s q (q σ)∘q (q τ) ≈ q (q σ∘q τ) : Γ, ℕ, A }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q σ)∘q (q τ) ≈ q (q σ∘q τ) : Γ, ℕ, A }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q σ∘q τ) ≈ q (q (σ∘τ)) : Γ, ℕ, A }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢s q (q σ)∘q (q τ) ≈ q (q (σ∘τ)) : Γ, ℕ, A }} by mauto 2.
      assert {{ Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1] : Type@i }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] ≈ A[Wk∘Wk,,succ #1][q (q (σ∘τ))] : Type@i }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q σ)][q (q τ)] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q σ)][q (q τ)] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as -> by mauto 2.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q σ)∘q (q τ)] ≈ MS[q (q (σ∘τ))] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q (σ∘τ))] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as <- by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ MS[q (q (σ∘τ))][Id] ≈ MS[q (q (σ∘τ))] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as <- by mauto 3.
      assert {{ Δ', ℕ, A[q (σ∘τ)] ⊢ A[Wk∘Wk,,succ #1][q (q (σ∘τ))][Id] ≈ A[Wk∘Wk,,succ #1][q (q (σ∘τ))] : Type@i }} as <- by mauto 3.
      mauto 3.
Qed.

Lemma glu_rel_exp_natrec_helper {P} (pred_P : PredicativeSig P) : forall {i Γ SbΓ A MZ MS},
    {{ EG Γ ∈ glu_ctx_env ↘ SbΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ ⊩ A : Type@i }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ MZ : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A ⊩ MS : A[Wk∘Wk,,succ #1] }} ->
    forall {Δ M m},
      glu_nat Δ M m ->
      forall {σ ρ am P El},
        {{ Δ ⊢s σ ® ρ ∈ SbΓ }} ->
        {{ ⟦ A ⟧ ρ ↦ m ↘ am }} ->
        {{ DG am ∈ glu_sort_elem i ↘ P ↘ El }} ->
        exists r,
          {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
            {{ Δ ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ El }}.
Proof.
  intros * ? HA ? ?.
  assert {{ ⊩ Γ }} by mauto 2.
  assert {{ Γ ⊩ ℕ : Type@i }} as Hℕ by mauto 3.
  assert {{ Γ ⊩ A[Id,,zero] : Type@i }}.
  {
    assert {{ Γ ⊢ ℕ : Type@i }} by mauto 2.
    assert {{ Γ ⊢ ℕ ⊆ ℕ[Id] }} by mauto 4.
    mauto.
  }
  pose (SbΓℕ := cons_glu_sub_pred i Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env ↘ SbΓℕ }} by (invert_glu_rel_exp Hℕ; econstructor; mauto 3; reflexivity).
  pose proof HA.
  invert_glu_rel_exp HA.
  assert {{ Γ, ℕ, A ⊩ A[Wk∘Wk,,succ #1] : Type@i }}.
  {
    assert {{ ⊩ Γ, ℕ, A }} by mauto 3.
    assert {{ Γ, ℕ ⊩s Wk : Γ }} by mauto 3.
    assert {{ Γ, ℕ, A ⊩s Wk : Γ, ℕ }} by mauto 3.
    assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 3.
    assert {{ Γ, ℕ, A ⊢ ℕ[Wk][Wk] ≈ ℕ : Type@0 }} by mauto 3.
    assert {{ Γ, ℕ, A ⊩ #1 : ℕ[Wk][Wk] }} by mauto 3.
    assert {{ Γ, ℕ, A ⊩ #1 : ℕ }} by mauto 3.
    mauto.
  }
  induction 1; intros; rename Γ0 into Δ.
  - (** [glu_nat_zero] *)
    mauto 4 using glu_rel_exp_natrec_zero_helper.
  - (** [glu_nat_succ] *)
    mauto 3 using glu_rel_exp_natrec_succ_helper.
  - (** [glu_nat_neut] *)
    mauto 3 using glu_rel_exp_natrec_neut_helper.
Qed.

Lemma glu_rel_exp_natrec {P} (pred_P : PredicativeSig P) : forall {Γ i A MZ MS M},
    {{ ⟪ pred_P ⟫ Γ, ℕ ⊩ A : Type@i }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ MZ : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A ⊩ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ M : ℕ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }}.
Proof.
  intros * HA HMZ HMS HM.
  assert {{ ⊩ Γ }} as [SbΓ] by mauto 2.
  assert {{ Γ ⊩ ℕ : Type@i }} as Hℕ by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred i Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env ↘ SbΓℕ }} by (invert_glu_rel_exp Hℕ; econstructor; mauto 3; try reflexivity).
  assert {{ Γ, ℕ ⊩ Type@i : Type@(S i) }} by mauto 3.
  pose proof HM.
  invert_glu_rel_exp HM.
  pose proof HA.
  invert_glu_rel_exp HA.
  eexists; split; [eassumption |].
  eexists.
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_sort_elem ltac:(fun H => directed invert_glu_sort_elem H).
  apply_predicate_equivalence.
  clear_dups.
  inversion_clear_by_head nat_glu_exp_pred.
  assert {{ Δ ⊢s σ,,M[σ] ® ρ ↦ m ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 2).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head glu_sort_elem ltac:(fun H => directed invert_glu_sort_elem H).
  apply_predicate_equivalence.
  inversion_clear_by_head nat_glu_exp_pred.
  unfold sort_glu_exp_pred' in *.
  destruct_conjs.
  clear_dups.
  match_by_head nat_glu_typ_pred ltac:(fun H => clear H).
  match goal with
  | _: {{ ⟦ A ⟧ ρ ↦ m ↘ ^?a' }},
      _: {{ DG ^?a' ∈ glu_sort_elem i ↘ ?P' ↘ ?El' }} |- _ =>
      rename a' into a;
      rename P' into P;
      rename El' into El
  end.
  assert (exists r, {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\ El Δ {{{ A[σ,, M[σ]] }}} {{{ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}} r) as [? []] by (eapply glu_rel_exp_natrec_helper; revgoals; mauto 4).
  econstructor; mauto 3.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ Γ ⊢ M : ℕ }} by mauto 2.
  assert {{ Γ, ℕ ⊢ A : Type@i }} by mauto 3.
  assert {{ Δ ⊢ A[σ,,M[σ]] ≈ A[Id,,M][σ] : Type@i }} as <- by (symmetry; mauto 2).
  assert {{ Δ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }} as -> by (econstructor; mauto 3).
  eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_natrec : mcpts.
