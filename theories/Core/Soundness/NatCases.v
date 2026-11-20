From McPTS Require Import PtsSignature LibTactics Base.
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
    {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ ℕ : Sort@s @ ^so_None }}.
Proof.
  intros * ? [Sb].
  assert {{ ⊢ Γ }} by mauto 2.
  eapply glu_rel_exp_of_typ; mauto 3.
  intros.
  rename Δ into Γ'.
  assert {{ Γ' ⊢s σ : Γ }} by mauto 3.
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


Lemma glu_rel_exp_sub_nat {P} (pred_P : PredicativeSig P) : forall {anns Γ σ anns' Γ' M s} {r : Ru_nat P s},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩s σ : Γ' @ anns' }} ->
    {{ ⟪ pred_P ⟫ Γ' @ anns' ⊩ M : ℕ @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M[σ] : ℕ @ ^(so_Some s) }}.
Proof.
  intros.
  assert {{ Γ ⊢s σ : Γ' }} by mauto 3.
  assert {{ Γ ⊢ ℕ[σ] ≈ ℕ : Sort@s }} by (econstructor; mauto 2).
  assert {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M[σ] : ℕ[σ] @ ^(so_Some s) }} as [SbΓ [HgluΓ]] by (eapply glu_rel_exp_sub; mauto 3).
  eexists; split; [eassumption |].
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  econstructor; mauto 3.
  assert {{ Γ'0 ⊢ ℕ[σ0] ≈ ℕ[σ][σ0] : Sort@s }} as -> by mauto 4.
  eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_sub_nat : mcpts.


Lemma glu_rel_exp_of_nat {P} (pred_P : PredicativeSig P) : forall {s} {r : Ru_nat P s} {anns Γ Sb M},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    (forall Γ' σ ρ, {{ Γ' ⊢s σ ® ρ ∈ Sb }} -> exists m, {{ ⟦ M ⟧ ρ ↘ m }} /\ glu_nat r Γ' {{{ M[σ] }}} m) ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : ℕ @ ^(so_Some s) }}.
Proof.
  intros * ? Hbody.
  eexists; split; mauto 3.
  intros.
  assert (st_subtyp s s) by mauto 2.
  edestruct Hbody as [? []]; mauto 3.
  econstructor; mauto 3.
  - econstructor.
    unshelve (glu_sort_elem_econstructor; mauto 3; reflexivity);
      mauto 2.    
  - simpl; split; mauto 3.    
Qed.


Lemma glu_rel_exp_zero {P} (pred_P : PredicativeSig P) : forall {s} {r : Ru_nat P s} {anns Γ},
    {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ zero : ℕ @ ^(so_Some s) }}.
Proof.
  intros * ? * [SbΓ].
  eapply glu_rel_exp_of_nat with (r := r); mauto 3.
  intros.
  eexists; split; mauto 4.
Qed.

#[export]
Hint Resolve glu_rel_exp_zero : mcpts.


Lemma glu_rel_exp_succ {P} (pred_P : PredicativeSig P) : forall {s} {r : Ru_nat P s} {anns Γ M},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : ℕ @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ succ M : ℕ @ ^(so_Some s) }}.
Proof.
  intros * ? * HM.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} as [SbΓ] by mauto 3.
  assert {{ Γ ⊢ M : ℕ }} by mauto 3.
  invert_glu_rel_exp HM.
  eapply glu_rel_exp_of_nat with (r := r); mauto.
  intros.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  match_by_head1 @glu_typ_elem ltac:(fun H => directed inversion H; subst).
  match_by_head1 @glu_sort_elem invert_glu_sort_elem.
  apply_predicate_equivalence.
  inversion_clear_by_head (@nat_glu_exp_pred P).
  eexists; split; mauto 3.
  econstructor; mauto.
  eapply glu_nat_rule_irrelevance; mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_exp_succ : mcpts.

Lemma glu_rel_sub_extend_nat {P} (pred_P : PredicativeSig P) : forall {s} {r : Ru_nat P s} {anns Γ σ anns' Γ' M},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩s σ : Γ' @ anns' }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : ℕ @ ^(so_Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩s σ,,M : Γ', ℕ @ anns', ^(so_Some s) }}.
Proof.
  intros.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ' @ anns' }} by mauto 2.
  assert {{ ⟪ pred_P ⟫ Γ @ anns ⊩ ℕ[σ] : Sort@s @ ^so_None }} by mauto 4.
  assert {{ Γ ⊢s σ : Γ' }} by mauto 3.
  assert {{ Γ ⊢ ℕ ≈ ℕ[σ] : Sort@s }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : ℕ[σ] @ ^(so_Some s) }} by mauto 4.
  assert {{ ⟪ pred_P ⟫ Γ' @ anns' ⊩ ℕ : Sort@s @ ^so_None }} by mauto 3.
  eapply glu_rel_sub_extend; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_sub_extend_nat : mcpts.


(* The next few lemmas should move to LogicalRelation/Lemmas.v *)
Lemma glu_typ_elem_exp_rel_trm_sub_sub_compose {P} (pred_P : PredicativeSig P) : forall {so a typ_rel exp_rel Γ A M σ σ' m},
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ M[σ][σ'] : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M[σ∘σ'] : A ® m ∈ exp_rel }}.
Proof.
  intros.
  assert {{ Γ ⊢ M[σ][σ'] : A }} by (eapply glu_typ_elem_trm_escape; mauto 2).
  assert {{ Γ ⊢ M[σ][σ'] ≈ M[σ∘σ'] : A }} by mauto 3.
  eapply glu_typ_elem_trm_resp_exp_eq; mauto 2.
Qed.

Lemma glu_typ_elem_exp_rel_trm_compose_decompose {P} (pred_P : PredicativeSig P) : forall {so a typ_rel exp_rel Γ A M σ σ' m},
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ M[σ∘σ'] : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M[σ][σ'] : A ® m ∈ exp_rel }}.
Proof.
  intros.
  assert {{ Γ ⊢ M[σ∘σ'] : A }} by (eapply glu_typ_elem_trm_escape; mauto 2).
  assert {{ Γ ⊢ M[σ][σ'] ≈ M[σ∘σ'] : A }} by mauto 3.
  eapply glu_typ_elem_trm_resp_exp_eq; mauto 2.
Qed.

Lemma glu_typ_elem_exp_rel_typ_sub_sub_compose {P} (pred_P : PredicativeSig P) : forall {so a typ_rel exp_rel Γ A M σ σ' m},
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ M : A[σ][σ'] ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M : A[σ∘σ'] ® m ∈ exp_rel }}.
Proof.
  intros * [] HM.
  - simpl_glu_rel.
    split; mauto 3.
    eauto.
  - assert {{ Γ ⊢ A[σ][σ'] : Sort@s }} by (eapply glu_sort_elem_trm_sort_lvl; mauto 2).
    assert {{ Γ ⊢ A[σ][σ'] ≈ A[σ∘σ'] : Sort@s }} by mauto 3.
    eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 2.
Qed.

Lemma glu_typ_elem_exp_rel_typ_compose_decompose {P} (pred_P : PredicativeSig P) : forall {so a typ_rel exp_rel Γ A M σ σ' m},
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ M : A[σ∘σ'] ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M : A[σ][σ'] ® m ∈ exp_rel }}.
Proof.
  intros * [] HM.
  - simpl_glu_rel.
    split; mauto 4.
  - assert {{ Γ ⊢ A[σ∘σ'] : Sort@s }} by (eapply glu_sort_elem_trm_sort_lvl; mauto 2).
    assert {{ Γ ⊢ A[σ][σ'] ≈ A[σ∘σ'] : Sort@s }} by mauto 3.
    eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 2.
Qed.

Lemma wf_typ_ann_of_sort_implies_wf_exp_ann {P} : forall {Γ : ctx P} {anns A s},
    {{ Γ @ anns ⊫ A @ ^(so_Some s) }} ->
    {{ Γ @ anns ⊫ A : Sort@s @ ^(so_None) }}.
Proof.
  intros * HA.
  assert {{ ⊫ Γ @ anns }} by (eapply presup_wf_typ_ann; mauto 2).
  dependent induction HA; mauto 3.
  assert {{ ⊫ Γ' @ annsΓ' }} by (eapply presup_wf_typ_ann; mauto 2).
  specialize (IHHA annsΓ' A0 s ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(eassumption)).  
  assert {{ Γ' @ annsΓ' ⊫ Sort@s @ ^so_None }} by mauto 3.
  assert {{ Γ @ anns ⊫ Sort@s @ ^so_None }} by mauto 3.
  eapply wf_exp_conv_ann with (A := {{{ Sort@s[σ] }}}); mauto 3.
Qed.

Corollary wf_typ_ann_of_sort_implies_wf_exp_of_sort {P} : forall {Γ : ctx P} {anns A s},
    {{ Γ @ anns ⊫ A @ ^(so_Some s) }} ->
    {{ Γ ⊢ A : Sort@s }}.
Proof.
  intros * ?%wf_typ_ann_of_sort_implies_wf_exp_ann; mauto 2.
Qed.

Lemma glu_rel_typ_to_wf_typ_or_wf_exp_of_sort {P} {pred_P : PredicativeSig P} : forall {Γ anns A sa},
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A @ sa }} ->
    (sa = so_None) \/ (exists s, sa = so_Some s /\ {{ Γ ⊢ A : Sort@s }}).
Proof.
  intros.
  destruct sa.
  - left; reflexivity.
  - right; eexists; split; try reflexivity.
    mauto 3.
Qed.

Lemma glu_rel_exp_natrec_zero_helper {P} (pred_P : PredicativeSig P) : forall {sn sa anns Γ SbΓ A MZ MS Γ' M σ ρ am typ_rel exp_rel} {r : Ru_nat P sn},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ @ anns, ^(so_Some sn) ⊩ A @ sa }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A[Id,,zero] @ sa }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ MZ : A[Id,,zero] @ sa }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ' ⊢ M ≈ zero : ℕ }} ->
    {{ Γ' ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟦ A ⟧ ρ ↦ zero ↘ am }} ->
    {{ DG am ∈ glu_typ_elem pred_P sa ↘ typ_rel ↘ exp_rel }} ->
    exists r,
      {{ rec zero ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
        {{ Γ' ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ exp_rel }}.
Proof.
  intros * ? ? HA' HA HMZ **.
  pose proof glu_rel_typ_to_wf_typ_or_wf_exp_of_sort HA' as HAofSort.
  assert {{ Γ ⊢ MZ : A[Id,,zero] }} by mauto 3.
  inversion HA as [SbΓ' []].
  assert {{ ⟪ pred_P ⟫ Γ @ anns ⊩ ℕ : Sort@sn @ ^so_None }} as [SbΓ'' []] by mauto 3.
  handle_functional_glu_ctx_env P.
  pose (SbΓℕ := cons_glu_sub_pred pred_P (so_Some sn) Γ {{{ ℕ }}} SbΓ'').
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P ((so_Some sn)::anns) ↘ SbΓℕ }} by (econstructor; mauto 4; try reflexivity).
  handle_functional_glu_ctx_env P.
  invert_glu_rel_exp HMZ.
  assert (forall (Γ' : list (exp P)%type) (σ : sub P) (ρ : list (domain P)), SbΓ'' Γ' σ ρ -> glu_rel_typ_with_sub pred_P (so_Some sn) Γ' {{{ ℕ }}} σ ρ) by mauto 3.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.    
  handle_functional_glu_typ_elem P.
  rename m into mz.
  eexists; split; mauto 3.
  
  assert {{ Γ' ⊢s σ : Γ }} by mauto 2.
  assert {{ Γ ⊢ ℕ }} by mauto 3.
  assert {{ Γ' ⊢s (Id,,zero)∘σ ≈ σ,,zero : Γ, ℕ }} by mauto 3.
  assert {{ Γ' ⊢s σ,,M ≈ σ,,zero : Γ, ℕ }} by mauto 3.
  assert {{ Γ' ⊢s (Id,,zero)∘σ ≈ σ,,M : Γ,ℕ }} by mauto 3.
  assert {{ Γ, ℕ ⊢ A }} by mauto 3.
  assert {{ Γ ⊢ MZ : A[Id,,zero] }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,, succ #1] }} by mauto 3.
  assert {{ Γ' ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ MZ[σ] : A[σ,,M] }} as -> by mauto 2.

  assert (exp_rel0 Γ' {{{ A[(Id,,zero)∘σ] }}} {{{ MZ[σ] }}} mz) by (eapply glu_typ_elem_exp_rel_typ_sub_sub_compose; mauto 2).
  destruct sa; match_by_head @glu_typ_elem ltac:(fun H => directed inversion H; subst).
  - enough {{ Γ' ⊢ A[(Id,,zero)∘σ] ≈ A[σ,,M] }} as Heq by (rewrite <- Heq; eassumption). 
    transitivity {{{ A[σ,,zero] }}}; mauto 3.
  - enough {{ Γ' ⊢ A[(Id,,zero)∘σ] ≈ A[σ,,M] : Sort@s }} as Heq by (rewrite <- Heq; eassumption).
    destruct HAofSort as [Heq | [s' [Heq HAs']]];
      inversion Heq; subst.
    assert {{ Γ ⊢ MZ : A[Id,,zero] }} by mauto 3.
    assert {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,, succ #1] }} by mauto 3.    
    transitivity {{{ A[σ,,zero] }}}; mauto 3.
Qed.    

Lemma cons_glu_sub_pred_nat_helper {P} (pred_P : PredicativeSig P) : forall {anns Γ SbΓ Γ' σ ρ s M m} {r : Ru_nat P s},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ Γ' ⊢s σ ® ρ ∈ SbΓ }} ->
    glu_nat r Γ' M m ->
    {{ Γ' ⊢s σ,,M ® ρ ↦ m ∈ cons_glu_sub_pred pred_P (so_Some s) Γ {{{ ℕ }}} SbΓ }}.
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

(* This should go in LogicalRelation/Definitions.v *)
Definition glu_rel_typ_resp_sub_env {P} (pred_P : PredicativeSig P) so Sb A :=
  forall Γ' σ ρ,
    {{ Γ' ⊢s σ ® ρ ∈ Sb }} ->
    glu_rel_typ_with_sub pred_P so Γ' A σ ρ.
Arguments glu_rel_typ_resp_sub_env {P} pred_P so Sb A/.

(* This goes to LogicalRelation/Lemmas *)
Lemma glu_rel_typ_clean_inversion1 {P} (pred_P : PredicativeSig P) : forall {anns so Γ Sb A},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A @ so }} ->
    glu_rel_typ_resp_sub_env pred_P so Sb A.
Proof.
  intros * ? [SbΓ []].
  intros ? **.
  handle_functional_glu_ctx_env P.
  mauto.
Qed.

(* This goes to LogicalRelation/Lemmas *)
#[global]
Ltac invert_glu_rel_typ H :=
 (unshelve eapply (glu_rel_typ_clean_inversion1 _ _) in H; shelve_unifiable; [eassumption |];
  unfold glu_rel_typ_resp_sub_env in H)
  + (inversion H as [? [? [? ?]]]; subst).


(* This goes to syntactic corollaries *)
(* Lemma wf_sub_eq_extend_id_zero_compose_sigma {P} : forall {Γ : ctx P} {Γ' σ}, *)
(*     {{ Γ' ⊢s σ : Γ }} -> *)
(*     {{ Γ ⊢ ℕ }} -> *)
(*     {{ Γ' ⊢s (Id,,zero)∘σ ≈ σ,,zero : Γ, ℕ }}. *)
(* Proof. *)
(*   intros * Hσ Hℕ. *)
(*   pose proof wf_typ_nat_inversion Hℕ as [s [r Htriv]]; clear Htriv. *)
(*   assert {{ Γ ⊢ zero : ℕ }} by mauto 3. *)
(*   transitivity {{{ σ,,zero[σ] }}}; mauto 3. *)
(*   assert {{ Γ' ⊢ zero[σ] ≈ zero : ℕ }} by mauto 3. *)
(*   mauto 3. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve wf_sub_eq_extend_id_zero_compose_sigma : mcpts. *)

(* Lemma wf_exp_natrec_under_sub {P} : forall {Γ : ctx P} {Γ' A σ M MZ MS}, *)
(*     {{ Γ' ⊢s σ : Γ }} -> *)
(*     {{ Γ' ⊢ M : ℕ }} -> *)
(*     {{ Γ, ℕ ⊢ A }} -> *)
(*     {{ Γ ⊢ MZ : A[Id,,zero] }} -> *)
(*     {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,, succ #1] }} -> *)
(*     {{ Γ' ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] }}. *)
(* Proof. *)
(*   intros. *)
(*   gen_presups. *)
(*   inversion_clear HAwf1. *)
(*   pose proof wf_exp_nat_inversion ltac:(eassumption) as [s' [r]]. *)
(*   assert {{ Γ', ℕ ⊢s q σ : Γ, ℕ }} by mauto 2. *)
(*   assert {{ Γ', ℕ ⊢ A[q σ] }} by mauto 2. *)
(*   assert {{ Γ' ⊢ ℕ[σ] ≈ ℕ }} by mauto 3. *)
(*   assert {{ Γ ⊢s Id,,zero : Γ, ℕ }} by mauto 3. *)
(*   assert {{ Γ' ⊢ A[q σ][Id,,zero] ≈ A[(q σ)∘(Id,,zero)] }} by mauto 3. *)
(*   assert {{ Γ' ⊢s (q σ)∘(Id,,zero) ≈ σ,, zero : Γ, ℕ }} by (eapply wf_sub_eq_q_sigma_id_extend; mauto 3). *)
(*   assert {{ Γ' ⊢ A[(q σ)∘(Id,,zero)] ≈ A[σ,,zero] }} by mauto 2. *)
(*   assert {{ Γ' ⊢ MZ[σ] : A[Id,,zero][σ] }} by mauto 2. *)
(*   assert {{ Γ' ⊢s (Id,,zero)∘σ ≈ σ,,zero : Γ, ℕ }} by mauto 3. *)
(*   assert {{ Γ' ⊢ A[Id,,zero][σ] ≈ A[σ,,zero] }} by (transitivity {{{ A[(Id,,zero)∘σ] }}}; mauto 3). *)
(*   assert {{ Γ' ⊢ A[q σ][Id,,zero] ≈ A[Id,,zero][σ] }} by (do 3 etransitivity; mauto 3). *)
(*   assert {{ Γ' ⊢ MZ[σ] : A[q σ][Id,,zero] }} by mauto 3. *)

(*   assert {{ Γ', ℕ, A[q σ] ⊢s q (q σ) : Γ, ℕ, A }} by mauto 3. *)
(*   assert {{ Γ', ℕ, A[q σ] ⊢s (q σ)∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘(q (q σ)) : Γ, ℕ }} by mauto 3. *)
(*   assert {{ Γ', ℕ, A[q σ] ⊢ MS[q (q σ)] : A[Wk∘Wk,,succ #1][q (q σ)] }} by mauto 3. *)
(*   assert {{ Γ', ℕ, A[q σ] ⊢ A[Wk∘Wk,,succ #1][q (q σ)] ≈ A[(Wk∘Wk,,succ #1)∘(q (q σ))] }} by mauto 3. *)
(*   assert {{ Γ', ℕ, A[q σ] ⊢ A[(Wk∘Wk,,succ #1)∘(q (q σ))] ≈ A[(q σ)∘(Wk∘Wk,,succ #1)] }} by mauto 3. *)
(*   assert {{ Γ', ℕ, A[q σ] ⊢ A[(q σ)∘(Wk∘Wk,,succ #1)] ≈ A[q σ][Wk∘Wk,,succ #1] }} by mauto 3. *)
(*   assert {{ Γ', ℕ, A[q σ] ⊢ A[Wk∘Wk,,succ #1][q (q σ)] ≈ A[q σ][Wk∘Wk,,succ #1] }} by (do 2 etransitivity; mauto 3). *)
(*   assert {{ Γ', ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by mauto 3. *)
(*   enough {{ Γ' ⊢ A[q σ][Id,,M] ≈ A[σ,,M] }} as <-; mauto 3. *)
(* Qed.   *)

 
(* Lemma wf_exp_eq_natrec_beta_succ_cong {P} : forall {Γ : ctx P} {A M M' MZ MS}, *)
(*     {{ Γ, ℕ ⊢ A }} -> *)
(*     {{ Γ ⊢ M ≈ succ M' : ℕ }} -> *)
(*     {{ Γ ⊢ MZ : A[Id,,zero] }} -> *)
(*     {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,, succ #1] }} -> *)
(*     {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M',,rec M' return A | zero -> MZ | succ -> MS end] : A[Id,,M] }}. *)
(* Proof. *)
(*   intros. *)
(*   gen_presups. *)
(*   pose proof wf_typ_nat_inversion HA as [s [r Htriv]]; clear Htriv. *)
(*   pose proof wf_exp_succ_inversion HN as []. *)
(*   assert {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈  rec succ M' return A | zero -> MZ | succ -> MS end : A[Id,,M] }} as -> by (eapply wf_exp_eq_natrec_cong; mauto 3). *)
(*   assert {{ Γ ⊢s Id,,M ≈ Id,,succ M' : Γ, ℕ }} as -> by mauto 3. *)
(*   mauto 2. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve wf_exp_eq_natrec_beta_succ_cong : mcpts. *)



(* Lemma wf_exp_eq_natrec_beta_succ_cong_under_sub {P} : forall {Γ : ctx P} {Γ' A σ M M' MZ MS}, *)
(*     {{ Γ' ⊢s σ : Γ }} -> *)
(*     {{ Γ' ⊢ M ≈ succ M' : ℕ }} -> *)
(*     {{ Γ, ℕ ⊢ A }} -> *)
(*     {{ Γ ⊢ MZ : A[Id,,zero] }} -> *)
(*     {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,, succ #1] }} -> *)
(*     {{ Γ' ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ MS[q (q σ)][Id,,M',,rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end] : A[σ,,M] }}. *)
(* Proof. *)
(*   intros. *)
(*   gen_presups. *)
(*   pose proof wf_typ_nat_inversion HA as [s [r Htriv]]; clear Htriv. *)
(*   pose proof wf_exp_succ_inversion HN as []. *)

(*   assert {{ Γ' ⊢s (q σ)∘(Id,,M) ≈ σ,,M : Γ, ℕ }} as <- by mauto 4. *)
(*   assert {{ Γ' ⊢ A[(q σ)∘(Id,,M)] ≈ A[q σ][Id,,M] }} as -> by mauto 4. *)

(*   assert {{ Γ' ⊢ MZ[σ] : A[Id,,zero][σ] }} by mauto 3. *)
(*   assert {{ Γ' ⊢ ℕ[σ] ≈ ℕ }} by mauto 3. *)
(*   assert {{ Γ' ⊢s (Id,,zero)∘σ ≈ σ,,zero : Γ, ℕ }} by mauto 3. *)
(*   assert {{ Γ' ⊢s σ,, zero ≈ (q σ)∘(Id,,zero) : Γ, ℕ }} by (symmetry; eapply wf_sub_eq_q_sigma_id_extend; mauto 3). *)
(*   assert {{ Γ' ⊢s (Id,,zero)∘σ ≈ (q σ)∘(Id,,zero) : Γ, ℕ }} by (etransitivity; mauto 3). *)
(*   assert {{ Γ' ⊢ A[Id,,zero][σ] ≈ A[(Id,,zero)∘σ] }} by mauto 3. *)
(*   assert {{ Γ' ⊢ A[(Id,,zero)∘σ] ≈ A[(q σ)∘(Id,,zero)] }} by mauto 3. *)
(*   assert {{ Γ' ⊢ A[(q σ)∘(Id,,zero)] ≈ A[q σ][Id,,zero] }} by mauto 4. *)
(*   assert {{ Γ' ⊢ A[Id,,zero][σ] ≈ A[q σ][Id,,zero] }} by (do 2 etransitivity; mauto 3).   *)
(*   assert {{ Γ' ⊢ MZ[σ] : A[q σ][Id,,zero] }} by mauto 3. *)

(*   assert {{ Γ', ℕ, A[q σ] ⊢ MS[q (q σ)] : A[Wk∘Wk,,succ #1][q (q σ)] }} by mauto 3. *)
(*   assert {{ Γ', ℕ ⊢s q σ : Γ, ℕ }} by mauto 3. *)
(*   assert {{ Γ', ℕ, A[q σ] ⊢s q (q σ) : Γ, ℕ, A }} by mauto 3. *)
(*   assert {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 3. *)
(*   assert {{ Γ', ℕ, A[q σ] ⊢ A[Wk∘Wk,,succ #1][q (q σ)] ≈ A[(Wk∘Wk,,succ #1)∘(q (q σ))] }} by mauto 3. *)
(*   assert {{ Γ', ℕ, A[q σ] ⊢s q σ∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘q (q σ) : Γ, ℕ }} by mauto 3. *)
(*   assert {{ Γ', ℕ, A[q σ] ⊢ A[q σ∘(Wk∘Wk,,succ #1)] ≈ A[(Wk∘Wk,,succ #1)∘q (q σ)] }} by mauto 3. *)
(*   assert {{ Γ', ℕ, A[q σ] ⊢ A[q σ∘(Wk∘Wk,,succ #1)] ≈ A[q σ][Wk∘Wk,,succ #1] }} by mauto 4. *)
(*   assert {{ Γ', ℕ, A[q σ] ⊢ A[Wk∘Wk,,succ #1][q (q σ)] ≈ A[q σ][Wk∘Wk,,succ #1] }} by (do 2 etransitivity; mauto 3). *)
(*   assert {{ Γ', ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by mauto 3. *)
(*   eapply wf_exp_eq_natrec_beta_succ_cong; mauto 3. *)
(* Qed. *)
  
(* #[export] *)
(* Hint Resolve wf_exp_eq_natrec_beta_succ_cong_under_sub : mcpts. *)

(* Lemma wf_typ_eq_nat_beta_succ_rhs_typ_gen_of_sort {P} : forall {Γ : ctx P} {Γ' σ A M N s}, *)
(*     {{ Γ ⊢s σ : Γ' }} -> *)
(*     {{ Γ', ℕ ⊢ A : Sort@s }} -> *)
(*     {{ Γ ⊢ M : ℕ }} -> *)
(*     {{ Γ ⊢ N : A[σ,,M] }} -> *)
(*     {{ Γ ⊢ A[Wk∘Wk,,succ #1][σ,,M,,N] ≈ A[σ,,succ M] : Sort@s }}. *)
(* Proof. *)
(*   intros. *)
(*   gen_presup H1. *)
(*   pose proof wf_typ_nat_inversion HAwf as [sn [r Htriv]]; clear Htriv. *)
(*   assert {{ ⊢ Γ' }} by mauto 3. *)
(*   assert {{ Γ', ℕ ⊢s Wk : Γ' }} by mauto 3. *)
(*   assert {{ Γ', ℕ, A ⊢s Wk : Γ', ℕ }} by mauto 4. *)
(*   assert {{ Γ', ℕ, A ⊢s Wk∘Wk : Γ' }} by mauto 3. *)
(*   assert {{ Γ', ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ', ℕ }} by mauto 4. *)
(*   assert {{ Γ ⊢s σ,,M : Γ', ℕ }} by mauto 4. *)
(*   assert {{ Γ ⊢s σ,,M,,N : Γ', ℕ, A }} by mauto 3. *)
(*   autorewrite with mcpts. *)
(*   assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M,,N) : Γ', ℕ }} by mauto 3. *)
(*   assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M,,N) ≈ ((Wk∘Wk)∘(σ,,M,,N)),,(succ #1)[σ,,M,,N] : Γ', ℕ }} by mauto. *)
(*   assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ Wk∘(Wk∘(σ,,M,,N)) : Γ' }} by mauto 3. *)
(*   assert {{ Γ ⊢s Wk∘(σ,,M,,N) ≈ σ,,M : Γ', ℕ }} by (unshelve autorewrite with mcpts; mauto 3). *)
(*   assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ Wk∘(σ,,M) : Γ' }} by (unshelve bulky_rewrite; constructor). *)
(*   assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ σ : Γ' }} by bulky_rewrite. *)
(*   assert {{ Γ ⊢ (succ #1)[σ,,M,,N] ≈ succ (#1[σ,,M,,N]) : ℕ }} by mauto 4. *)
(*   assert {{ Γ ⊢ (succ #1)[σ,,M,,N] ≈ succ (#0[σ,,M]) : ℕ }} by (bulky_rewrite; mauto 4). *)
(*   assert {{ Γ ⊢ (succ #1)[σ,,M,,N] ≈ succ M : ℕ }} by (bulky_rewrite; mauto 3). *)
(*   assert {{ Γ ⊢s (Wk∘Wk)∘(σ,,M,,N),,(succ #1)[σ,,M,,N] ≈ σ,,succ M : Γ', ℕ }} by mauto 3. *)
(*   assert {{ Γ ⊢ A[(Wk∘Wk,,succ #1)∘(σ,,M,,N)] ≈ A[(Wk∘Wk)∘(σ,,M,,N),,(succ #1)[σ,,M,,N]] }} by mauto 3. *)
(*   assert {{ Γ ⊢s (Wk∘Wk,,succ #1)∘(σ,,M,,N) ≈ σ,,(succ M) : Γ', ℕ }} by mauto 3. *)
(*   transitivity {{{ A[(Wk∘Wk)∘(σ,,M,,N),,(succ #1)[σ,,M,,N]] }}}; mauto 4. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve wf_typ_eq_nat_beta_succ_rhs_typ_gen_of_sort : mcpts. *)

(* Move to LogicalRelation/Lemmas *)
Lemma cons_glu_sub_pred_helper {P} (pred_P : PredicativeSig P) : forall {anns Γ Sb Γ' σ ρ A a sa typ_rel exp_rel M c},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ Γ' ⊢s σ ® ρ ∈ Sb }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A @ sa }} ->
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ DG a ∈ glu_typ_elem pred_P sa ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ' ⊢ M : A[σ] ® c ∈ exp_rel }} ->
    {{ Γ' ⊢s σ,,M ® ρ ↦ c ∈ cons_glu_sub_pred pred_P sa Γ A Sb }}.
Proof.
  intros * ? ? HA **.
  pose proof glu_rel_typ_to_wf_typ_or_wf_exp_of_sort HA as HAofSort.
  destruct sa;
    destruct HAofSort as [Heq | [s' [Heq HAs']]]; inversion Heq; subst;
    mauto 3.
Qed.

#[export]
Hint Resolve cons_glu_sub_pred_helper : mcpts.


Lemma glu_rel_exp_natrec_succ_helper {P} (pred_P : PredicativeSig P) : forall {sa anns Γ SbΓ A MZ MS Γ' M M' m' σ ρ am typ_rel exp_rel sn} {r : Ru_nat P sn},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ @ anns, ^(so_Some sn) ⊩ A @ sa }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩ A[Wk∘Wk,,succ #1] @ sa }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩ MS : A[Wk∘Wk,,succ #1] @ sa }} ->
    {{ Γ' ⊢ M ≈ succ M' : ℕ }} ->
    glu_nat r Γ' M' m' ->
    (forall σ ρ am typ_rel exp_rel,
        {{ Γ' ⊢s σ ® ρ ∈ SbΓ }} ->
        {{ ⟦ A ⟧ ρ ↦ m' ↘ am }} ->
        {{ DG am ∈ glu_typ_elem pred_P sa ↘ typ_rel ↘ exp_rel }} ->
        exists e,
          {{ rec m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\
            {{ Γ' ⊢ rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M'] ® e ∈ exp_rel }}) ->
    {{ Γ' ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟦ A ⟧ ρ ↦ succ m' ↘ am }} ->
    {{ DG am ∈ glu_typ_elem pred_P sa ↘ typ_rel ↘ exp_rel }} ->
    exists e,
      {{ rec succ m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\
        {{ Γ' ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® e ∈ exp_rel }}.
Proof.
  intros * ? HA ? ? HMS **.
  pose proof glu_rel_typ_to_wf_typ_or_wf_exp_of_sort HA as HAofSort.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} by (eexists; eassumption).
  assert {{ ⟪ pred_P ⟫ Γ @ anns ⊩ ℕ : Sort@sn @ ^so_None }} as Hℕ by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred pred_P (so_Some sn) Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ  ∈ glu_ctx_env pred_P ((so_Some sn)::anns) ↘ SbΓℕ }} by (invert_glu_rel_exp Hℕ; econstructor; mauto 4; try reflexivity).

  assert {{ Γ, ℕ ⊢ A }} by mauto 3.
  pose proof HA as HA'.
  invert_glu_rel_typ HA'.

  pose (SbΓℕA := cons_glu_sub_pred pred_P sa {{{ Γ, ℕ }}} A SbΓℕ).
  assert {{ EG Γ, ℕ, A ∈ glu_ctx_env pred_P (sa::(so_Some sn)::anns) ↘ SbΓℕA }} by (econstructor; mauto 3; reflexivity).

  assert {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} by mauto 2.
  invert_glu_rel_exp HMS.
  assert {{ Γ' ⊢s σ,,M' ® ρ ↦ m' ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 3).
  
  assert (glu_rel_typ_with_sub pred_P sa Γ' A {{{ σ,,M' }}} d{{{ ρ ↦ m' }}}) as [am' typ_rel' exp_rel'] by mauto 3; subst.
  pose (R := {{{ rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}}).
  assert (exists e, {{ rec m' ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\ {{ Γ' ⊢ R : A[σ,,M'] ® e ∈ exp_rel' }}) as [e' []] by mauto 2.

  assert {{ Γ' ⊢ R : A[σ,,M'] }} by (eapply glu_typ_elem_trm_escape; mauto 2).
  assert {{ Γ' ⊢s Wk∘(σ,,M',,R) ≈ σ,,M' : Γ, ℕ }} as HWkσM'R by mauto 3.
  
  
  assert (SbΓℕ Γ' {{{ Wk∘(σ,,M',,R) }}} d{{{ ((ρ ↦ m') ↦ e') ↯ }}}) by (rewrite HWkσM'R; mauto 2).
  assert {{ Γ' ⊢s σ,,M',,R ® (ρ ↦ m') ↦ e' ∈ SbΓℕA }} by (eapply cons_glu_sub_pred_helper; mauto 3).
  destruct_glu_rel_typ_with_sub.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  handle_functional_glu_typ_elem P.
  eexists; split; mauto 3.

  assert {{ Γ' ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end ≈ MS[q (q σ)][Id,,M',,rec M' return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end] : A[σ,,M] }} as -> by mauto 3.
  fold R.

  assert {{ Γ', ℕ ⊢s q σ : Γ, ℕ }} by mauto 3.
  assert {{ Γ', ℕ, A[q σ] ⊢s q (q σ) : Γ, ℕ, A }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 3.

  assert {{ Γ' ⊢ M' : ℕ }} by mauto 3.
  assert {{ Γ' ⊢s Id,,M' : Γ', ℕ }} by mauto 4.
  assert {{ Γ' ⊢s (q σ)∘(Id,,M') ≈ σ,,M' : Γ, ℕ }} by (eapply wf_sub_eq_q_sigma_id_extend; mauto 3).
  assert {{ Γ' ⊢ A[q σ][Id,,M'] ≈ A[(q σ)∘(Id,,M')] }} by mauto 3.
  assert {{ Γ' ⊢ A[q σ][Id,,M'] ≈ A[σ,,M'] }} by mauto 3.
  assert {{ Γ' ⊢s (q (q σ))∘(Id,,M',,R) ≈ ((q σ)∘(Id,,M')),,R : Γ, ℕ, A }} by (eapply wf_sub_eq_q_sigma_extend_tau; mauto 3).  
  assert {{ Γ' ⊢s ((q σ)∘(Id,,M')),,R ≈ σ,,M',,R : Γ, ℕ, A }}. (* This should be a lemma *)
  {
    eapply wf_sub_eq_extend_cong; mauto 2.
    rewrite -> H39.
    mauto 2.
  }
  assert {{ Γ' ⊢s (q (q σ))∘(Id,,M',,R) ≈ σ,,M',,R : Γ, ℕ, A }} by mauto 4.

  assert {{ Γ', ℕ, A[q σ] ⊢ MS[q (q σ)] : A[Wk∘Wk,,succ #1][q (q σ)] }} by mauto 3.
  assert {{ Γ' ⊢s Id,,M',,R : Γ', ℕ, A[q σ] }} by (eapply wf_sub_extend; mauto 3).
  assert {{ Γ' ⊢ MS[q (q σ)][Id,,M',,R] : A[Wk∘Wk,,succ #1][q (q σ)][Id,,M',,R] }} by mauto 4.
  assert {{ Γ' ⊢ A[Wk∘Wk,,succ #1][q (q σ)][Id,,M',,R] ≈ A[Wk∘Wk,,succ #1][(q (q σ))∘(Id,,M',,R)] }} by mauto 3.
  assert {{ Γ' ⊢ A[Wk∘Wk,,succ #1][(q (q σ))∘(Id,,M',,R)] ≈ A[Wk∘Wk,,succ #1][σ,,M',,R] }} by mauto 3.
  assert {{ Γ' ⊢ A[Wk∘Wk,,succ #1][σ,,M',,R] ≈ A[σ,, succ M'] }} by mauto 3.
  assert {{ Γ' ⊢ ℕ[σ] ≈ ℕ }} by mauto 4.
  assert {{ Γ' ⊢s σ,,M ≈ σ,,succ M' : Γ, ℕ }} by (eapply wf_sub_eq_extend_cong; mauto 3).
  assert {{ Γ' ⊢ A[σ,,succ M'] ≈ A[σ,,M] }} by mauto 4.
  assert {{ Γ' ⊢ A[Wk∘Wk,,succ #1][q (q σ)][Id,,M',,R] ≈ A[σ,,M] }} by (do 4 etransitivity; mauto 2).
  assert {{ Γ' ⊢ MS[q (q σ)][Id,,M',,R] : A[σ,,M] }} by mauto 3.
  assert {{ Γ' ⊢ MS[q (q σ)][Id,,M',,R] ≈ MS[(q (q σ))∘(Id,,M',,R)] : A[σ,,M] }} as -> by mauto 3.

  assert {{ Γ' ⊢ MS[(q (q σ))∘(Id,,M',,R)] ≈ MS[σ,,M',,R] : A[Wk∘Wk,,succ #1][(q (q σ))∘(Id,,M',,R)] }} by mauto 4.
  assert {{ Γ' ⊢ A[Wk∘Wk,,succ #1][(q (q σ))∘(Id,,M',,R)] ≈ A[σ,,M] }} by mauto 3.
  assert {{ Γ' ⊢ MS[(q (q σ))∘(Id,,M',,R)] ≈ MS[σ,,M',,R] : A[σ,,M] }} as -> by mauto 3.
  
  destruct sa.
  - assert {{ Γ' ⊢ A[Wk∘Wk,,succ #1][σ,,M',,R] ≈ A[σ,,M] }} as <- by mauto 3.
    mauto 2.
  - destruct HAofSort as [Heq | [s' [Heq HAs']]]; inversion Heq; subst.
    rename s' into s.
    
    assert {{ Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1] : Sort@s }} by mauto 3.
    assert {{ Γ' ⊢ A[Wk∘Wk,,succ #1][σ,,M',,R] : Sort@s }} by mauto 3.
    assert {{ Γ' ⊢ A[Wk∘Wk,,succ #1][σ,,M',,R] ≈ A[σ,,succ M'] : Sort@s }} by mauto 3.
    assert {{ Γ' ⊢ A[σ,,succ M'] ≈ A[σ,,M] : Sort@s }} by mauto 3.
    assert {{ Γ' ⊢ A[Wk∘Wk,,succ #1][σ,,M',,R] ≈ A[σ,,M] : Sort@s }} as <- by mauto 3.    
    mauto 2.
Qed.


Lemma cons_glu_sub_pred_q_helper {P} (pred_P : PredicativeSig P) : forall {so anns Γ SbΓ Γ' σ ρ A a},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ Γ' ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A @ so }} ->
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ Γ', A[σ] ⊢s q σ ® ρ ↦ ⇑! a (length Γ') ∈ cons_glu_sub_pred pred_P so Γ A SbΓ }}.
Proof.
  intros * ? ? HA ?.
  destruct so;
    [ assert {{ Γ ⊢ A }} by mauto 2 | assert {{ Γ ⊢ A : Sort@s }} by mauto 3];
    invert_glu_rel_typ HA;
    handle_functional_glu_ctx_env P;

    assert {{ Γ' ⊢s σ : Γ }} by mauto 2;
    assert {{ ⊢ Γ', A[σ] }} by mauto 4;
    assert {{ Γ', A[σ] ⊢w Wk : Γ' }} by mauto 2;
    [assert (glu_rel_typ_with_sub pred_P so_None Γ' A σ ρ) by mauto 2 |
      assert (glu_rel_typ_with_sub pred_P (so_Some s) Γ' A σ ρ) by mauto 2];
    inversion H6;
    simplify_evals.
  - eapply cons_glu_sub_pred_helper_unsorted; mauto 2.
    + eapply glu_ctx_env_sub_monotone; eassumption.
    + assert {{ Γ', A[σ] ⊢s Wk : Γ' }} by mauto 2.
      assert {{ Γ', A[σ] ⊢ A[σ∘Wk] ≈ A[σ][Wk] }} as -> by mauto 3.
      eapply var0_glu_typ_elem; eassumption.
  - eapply cons_glu_sub_pred_helper_sorted; mauto 2.
    + eapply glu_ctx_env_sub_monotone; eassumption.
    + assert {{ Γ', A[σ] ⊢s Wk : Γ' }} by mauto 2.
      assert {{ Γ', A[σ] ⊢ A[σ∘Wk] ≈ A[σ][Wk] : Sort@s }} as -> by mauto 3.
      inversion H8; subst.
      eapply var0_glu_elem; eassumption.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_q_helper : mcpts.

Lemma cons_glu_sub_pred_q_nat_helper {P} (pred_P : PredicativeSig P) : forall {anns Γ SbΓ Γ' σ ρ s} {r : Ru_nat P s},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ Γ' ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ Γ', ℕ ⊢s q σ ® ρ ↦ ⇑! ℕ (length Γ') ∈ cons_glu_sub_pred pred_P (so_Some s) Γ {{{ ℕ }}} SbΓ }}.
Proof.
  intros.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} by (eexists; eassumption).
  assert {{ ⟪ pred_P ⟫ Γ @ anns ⊩ ℕ : Sort@s @ ^so_None }} as Hℕ by mauto 3.
  assert {{ ⟦ ℕ ⟧ ρ ↘ ℕ }} by mauto 3.
  assert {{ Γ', ℕ[σ] ⊢s q σ ® ρ ↦ ⇑! ℕ (length Γ') ∈ cons_glu_sub_pred pred_P (so_Some s) Γ {{{ ℕ }}} SbΓ }} by mauto 3.
  assert {{ Γ' ⊢ ℕ[σ] ≈ ℕ : Sort@s }} by (econstructor; mauto 4).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P ((so_Some s)::anns) ↘ cons_glu_sub_pred pred_P (so_Some s) Γ {{{ ℕ }}} SbΓ }}.
  {
    assert {{ ⊢ Γ }} by mauto 3.    
    invert_glu_rel_exp Hℕ; destruct_conjs; econstructor; mauto 3.
    assert (forall (Γ' : list (exp P)%type) (σ : sub P) (ρ : list (domain P)), SbΓ Γ' σ ρ -> glu_rel_typ_with_sub pred_P (so_Some s) Γ' {{{ ℕ }}} σ ρ) by mauto 3.
    split; intros * Hglu; invert_glu_ctx_env Hglu; econstructor; mauto 2.
  }
  assert {{ ⊢ Γ' }} by mauto 2.
  cbn.
  assert {{ ⊢ Γ', ℕ[σ] ≈ Γ', ℕ }} as <- by mauto 4.
  eassumption.
Qed.

#[local]
Hint Resolve cons_glu_sub_pred_q_nat_helper : mcpts.

Lemma glu_rel_exp_natrec_neut_helper {P} (pred_P : PredicativeSig P) : forall {sa anns Γ SbΓ A MZ MS Γ' M a m σ ρ am typ_rel exp_rel sn} {r : Ru_nat P sn},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ @ anns, ^(so_Some sn) ⊩ A @ sa }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A[Id,,zero] @ sa }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ MZ : A[Id,,zero] @ sa }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩ A[Wk∘Wk,,succ #1] @ sa }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩ MS : A[Wk∘Wk,,succ #1] @ sa }} ->
    {{ Dom m ≈ m ∈ per_bot }} ->
    (forall Γ'' τ V, {{ Γ'' ⊢w τ : Γ' }} -> {{ Rne m in length Γ'' ↘ V }} -> {{ Γ'' ⊢ M[τ] ≈ V : ℕ }}) ->
    {{ Γ' ⊢s σ ® ρ ∈ SbΓ }} ->
    {{ ⟦ A ⟧ ρ ↦ ⇑ a m ↘ am }} ->
    {{ DG am ∈ glu_typ_elem pred_P sa ↘ typ_rel ↘ exp_rel }} ->
    exists e,
      {{ rec ⇑ a m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ e }} /\
        {{ Γ' ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® e ∈ exp_rel }}.
Proof.
  intros * ? ? HA ? HMZ ? HMS **.
  assert (sa = so_None \/ exists s, sa = so_Some s /\ {{ Γ, ℕ ⊢ A : Sort@s }}) as HAofSort.
  {
    destruct sa.
    - left; reflexivity.
    - right; eexists; split; try reflexivity.
      mauto 3.
  }
  
  assert {{ Γ ⊢ MZ : A[Id,,zero] }} by mauto 2.
  invert_glu_rel_exp HMZ.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} by (eexists; eassumption).
  assert {{ ⟪ pred_P ⟫ Γ @ anns ⊩ ℕ : Sort@sn @ ^so_None }} as Hℕ by mauto 3.
  pose (SbΓℕ := cons_glu_sub_pred pred_P (so_Some sn) Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P ((so_Some sn)::anns) ↘ SbΓℕ }} by (invert_glu_rel_exp Hℕ; econstructor; mauto 4; try reflexivity).
  assert {{ Γ, ℕ ⊢ A }} by mauto 3.
  pose proof HA.
  invert_glu_rel_typ HA.
  assert (forall Γ' σ ρ, SbΓℕ Γ' σ ρ -> glu_rel_typ_with_sub pred_P sa Γ' A σ ρ) by mauto 3.
  pose (SbΓℕA := cons_glu_sub_pred pred_P sa {{{ Γ, ℕ }}} A SbΓℕ).
  assert {{ EG Γ, ℕ, A ∈ glu_ctx_env pred_P (sa::(so_Some sn)::anns) ↘ SbΓℕA }} by (econstructor; mauto 3; reflexivity).

  assert {{ Γ' ⊢s σ,,M ® ρ ↦ ⇑ a m ∈ SbΓℕ }} by (unshelve eapply cons_glu_sub_pred_nat_helper; mauto 3).

  
  assert {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} by mauto 2.
  invert_glu_rel_exp HMS.  
  assert (glu_rel_typ_with_sub pred_P sa Γ' A {{{ σ,,M }}} d{{{ ρ ↦ ⇑ a m }}}) by mauto 2.
  assert (glu_rel_exp_with_sub pred_P sa Γ' MZ {{{ A[Id,,zero] }}} σ ρ) by mauto 2.
  
  destruct_glu_rel_typ_with_sub.
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  handle_functional_glu_typ_elem P.
  match goal with
  | _: {{ ⟦ MZ ⟧ ^?ρ0 ↘ ^?m }}, _: {{ ⟦ A ⟧ ^?ρ0 ↦ zero ↘ ^?a }} |- _ =>
      rename ρ0 into ρ;
      rename m into mz;
      rename a into az
  end.
  eexists; split; mauto 3.
  
  assert {{ Γ' ⊢s σ : Γ }} by mauto 3.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ ⊢ Γ', ℕ }} by mauto 3.
  assert {{ Γ', ℕ ⊢ A[q σ] }} by mauto 3.
  assert {{ ⊢ Γ', ℕ, A[q σ] }} by mauto 3.
  assert {{ Γ' ⊢ M : ℕ }} by (unshelve mauto 3; mauto 2).

  assert {{ Γ' ⊢ ℕ : Sort@sn }} by mauto 3.
  assert {{ Γ' ⊢ ℕ[σ] ≈ ℕ : Sort@sn }} by (econstructor; mauto 2).
  assert {{ Γ' ⊢ M : ℕ[σ] }} by mauto 3.
  assert {{ Γ' ⊢ zero : ℕ }} by mauto 3.
  assert {{ Γ' ⊢ zero[σ] ≈ zero : ℕ }} by mauto 3.
  assert {{ Γ', ℕ ⊢s q σ : Γ, ℕ }} by mauto 3.

  assert {{ Γ' ⊢ A[q σ][Id,,zero] ≈ A[(q σ)∘(Id,,zero)] }} by mauto 3.
  assert {{ Γ' ⊢s (q σ)∘(Id,,zero) ≈ σ,,zero : Γ, ℕ }} by (eapply wf_sub_eq_q_sigma_id_extend; mauto 3).
  assert {{ Γ' ⊢ A[(q σ)∘(Id,,zero)] ≈ A[σ,,zero] }} by mauto 4.
  assert {{ Γ' ⊢ A[q σ][Id,,zero] ≈ A[σ,,zero] }} by mauto 4.
  assert {{ Γ' ⊢s σ,,zero ≈ σ,,zero[σ] : Γ, ℕ }} by mauto 4.
  assert {{ Γ' ⊢ A[σ,,zero] ≈ A[σ,,zero[σ]] }} by mauto 4.
  assert {{ Γ ⊢ zero : ℕ }} by mauto 3.
  assert {{ Γ' ⊢s σ,,zero[σ] ≈ (Id,,zero)∘σ : Γ, ℕ }} by mauto 5.
  assert {{ Γ' ⊢ A[σ,,zero[σ]] ≈ A[(Id,,zero)∘σ] }} by mauto 4.
  assert {{ Γ' ⊢ A[(Id,,zero)∘σ] ≈ A[Id,,zero][σ] }} by mauto 4.
  assert {{ Γ' ⊢ A[σ,,zero[σ]] ≈ A[Id,,zero][σ] }} by mauto 4.
  assert {{ Γ' ⊢ A[q σ][Id,,zero] ≈ A[Id,,zero][σ] }} by mauto 3.
  assert {{ Γ' ⊢ MZ[σ] : A[Id,,zero][σ] }} by mauto 3.  
  assert {{ Γ' ⊢ MZ[σ] : A[q σ][Id,,zero] }} by mauto 3. 
  assert {{ Γ', ℕ, A[q σ] ⊢s Wk∘Wk,,succ #1 : Γ', ℕ }} by mauto 3.
  assert {{ Γ', ℕ, A[q σ] ⊢ A[q σ][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,, succ #1][q (q σ)]  }} by mauto 3.
  assert {{ Γ', ℕ, A[q σ] ⊢ MS[q (q σ)] : A[Wk∘Wk,,succ #1][q (q σ)] }} by mauto 4.
  assert {{ Γ', ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }} by mauto 3.
  pose (R := {{{ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}}).
  enough {{ Γ' ⊢ R : A[σ,,M] ® rec m under ρ return A | zero -> mz | succ -> MS end ∈ glu_elem_bot pred_P sa am }} by (eapply realize_glu_typ_elem_bot; mauto 3).
  econstructor; mauto 3.
  - assert {{ Γ' ⊢ A[q σ][Id,,M] ≈ A[σ,,M] }} by mauto 2.
    mauto 3.
  - assert {{ Γ' ⊢ MZ[σ] : A[Id,,zero][σ] ® mz ∈ glu_elem_top pred_P sa az }} as [] by (eapply realize_glu_typ_elem_top; eassumption).
    handle_functional_glu_typ_elem P.
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
    mark HAofSort.
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
      match_by_head @cons_per_ctx_env ltac:(fun H => inversion H; subst).
      econstructor; mauto 4.
      simpl in *.
      simplify_evals.
      match_by_head @per_typ_elem ltac:(fun H => directed inversion H; subst).
      invert_per_sort_elems.
      intuition.
    }

    mark HAofSort.
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
    
    handle_per_typ_elem_irrel.
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
  - intros Γ'' τ w **.
    assert {{ ⊢ Γ'' }} by mauto 3.
    assert {{ ⊢ Γ'', ℕ }} by mauto 3.
    assert {{ Γ'' ⊢s τ : Γ' }} by mauto 3.
    assert {{ Γ'' ⊢s σ∘τ : Γ }} by mauto 3.
    assert {{ Γ'' ⊢s σ∘τ ® ρ ∈ SbΓ }} by (eapply glu_ctx_env_sub_monotone; mauto 4).
    assert {{ Γ'', ℕ ⊢s q (σ∘τ) ® ρ ↦ ⇑! ℕ (length Γ'') ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 3).
    assert (forall (Γ' : list (exp P)%type) (σ : sub P) (ρ : list (domain P)), SbΓℕ Γ' σ ρ -> glu_rel_typ_with_sub pred_P sa Γ' A σ ρ) by mauto 3.
    destruct_glu_rel_typ_with_sub.
    simplify_evals.
    dir_inversion_clear_by_head (@read_ne P).
    handle_functional_glu_sort_elem P.
    match goal with
    | _: {{ ⟦ A ⟧ ^?ρ' ↦ ⇑! ℕ (length Γ'') ↘ ^?a }} |- _ =>
        rename ρ' into ρ;
        rename a into aΓ''
    end.
    assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢s q (q (σ∘τ)) ® (ρ ↦ ⇑! ℕ (length Γ'')) ↦ ⇑! aΓ'' (length {{{ Γ'', ℕ }}}) ∈ SbΓℕA }} by (unfold SbΓℕA; mauto 3).
    assert (glu_rel_typ_with_sub pred_P sa {{{ Γ'', ℕ }}} A {{{ q (σ∘τ) }}}
              d{{{ ρ ↦ ⇑! ℕ (length Γ'') }}}) as Hglu_typ_unsorted by mauto 2.
    inversion Hglu_typ_unsorted; subst.
    destruct_glu_rel_exp_with_sub.
    simplify_evals.
    handle_functional_glu_typ_elem P.

    match goal with
    | _: {{ ⟦ A ⟧ ^?ρ' ↦ succ (⇑! ℕ (length Γ'')) ↘ ^?a }},
        _: {{ Rtyp aΓ'' in S (length Γ'') ↘ ^?A }},
        _: {{ Rnf ⇓ az mz in length Γ'' ↘ ^?MZ }},
            _: {{ Rne m in length Γ'' ↘ ^?M }} |- _ =>
        rename A into A';
        rename ρ' into ρ;
        rename a into asucc;
        rename MZ into MZ';
        rename M into M'
    end.
    assert {{ Γ'', ℕ ⊢ A[q (σ∘τ)] ® glu_typ_top pred_P aΓ'' }} as Hglu_typ_top by (eapply realize_glu_typ_typ_top; mauto 3; econstructor; mauto 2).
    inversion Hglu_typ_top; subst.
    assert {{ Γ' ⊢ MZ[σ] : A[Id,,zero][σ] ® mz ∈ glu_elem_top pred_P sa az }} as [] by (eapply realize_glu_typ_elem_top; eassumption).
    assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢ MS[q (q (σ∘τ))] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] ® ms ∈ glu_elem_top pred_P sa asucc }} as []
        by (eapply realize_glu_typ_elem_top; eassumption).
    assert {{ Γ' ⊢s σ,,M : Γ, ℕ }} by mauto 4.
    assert {{ Γ'' ⊢s σ∘τ,,M[τ] : Γ, ℕ }} by mauto 4.
    assert {{ Γ'' ⊢ A[σ,,M][τ] ≈ A[(σ,,M)∘τ] }} as -> by mauto 3.
    assert {{ Γ'' ⊢ A[(σ,,M)∘τ] ≈ A[σ∘τ,,M[τ]] }} as -> by mauto 3.
    assert {{ Γ'' ⊢ A[σ∘τ,,M[τ]] ≈ A[q σ][τ,,M[τ]] }} as -> by (eapply sub_decompose_q_typ; mauto 4).
    assert {{ Γ'' ⊢ R[τ] ≈ rec M[τ] return A[q σ][q τ] | zero -> MZ[σ][τ] | succ -> MS[q (q σ)][q (q τ)] end : A[q σ][τ,,M[τ]] }} as -> by mauto 3.
    assert {{ Γ'' ⊢ A[q σ][q τ][Id,,M[τ]] ≈ A[q σ][τ,,M[τ]] }} as <- by mauto 4.
    assert {{ Γ'', ℕ ⊢w Id : Γ'', ℕ }} by mauto 3.
    assert {{ Γ'', ℕ ⊢ A[q (σ∘τ)][Id] ≈ A' }} as HA' by mauto 4.
    gen_presup HA'.
    eapply (@wf_exp_eq_natrec_cong' _ _ _ _ _ _ _ _ _ _ _ r); fold (@ne_to_exp P) (@nf_to_exp P); only 1, 2: mauto 4.
    + assert {{ Γ'', ℕ ⊢s q σ∘q τ : Γ, ℕ }} by mauto 3.
      assert {{ Γ'', ℕ ⊢ A[q σ∘q τ] }} by mauto 3.
      assert {{ Γ'', ℕ ⊢ A[q σ][q τ] ≈ A' }}.
      {
        rewrite <- HA'.
        transitivity {{{ A[q σ∘q τ] }}}; mauto 3.
        transitivity {{{ A[q σ∘q τ][Id] }}}; mauto 3.
        eapply wf_typ_eq_sub_cong1; mauto 3.
        }
        mauto 2.
    + assert {{ Γ', ℕ ⊢ A[q σ] }} by mauto 3.
      assert {{ Γ'', ℕ ⊢s q τ : Γ', ℕ }} by mauto 3.
      assert {{ Γ'' ⊢ zero : ℕ }} by mauto 3.
      assert {{ Γ'' ⊢ A[q σ][q τ][Id,,zero] ≈ A[q σ][τ,,zero] }} as -> by mauto 3.
      assert {{ Γ'' ⊢ zero ≈ zero[τ] : ℕ }} by mauto 3.
      assert {{ Γ'' ⊢ zero ≈ zero[τ] : ℕ[τ] }} by mauto 4.
      assert {{ Γ'' ⊢s τ,,zero ≈ τ,,zero[τ] : Γ', ℕ }} by mauto 3.
      assert {{ Γ'' ⊢ A[q σ][τ,,zero] ≈ A[q σ][τ,,zero[τ]] }} by (symmetry; mauto 4).
      assert {{ Γ'' ⊢ A[q σ][τ,,zero] ≈ A[q σ][Id,,zero][τ] }} as -> by mauto 4.
      assert {{ Γ' ⊢ A[q σ][Id,,zero] ≈ A[Id,,zero][σ] }} by mauto 3.
      assert {{ Γ'' ⊢ A[q σ][Id,,zero][τ] ≈ A[Id,,zero][σ][τ] }} as -> by mauto 3.
      mauto 3.
    + assert {{ Γ', ℕ ⊢ A[q σ] }} by mauto 3.
      assert {{ Γ'', ℕ ⊢s q τ : Γ', ℕ }} by mauto 2.
      assert {{ Γ', ℕ, A[q σ] ⊢s q (q σ) : Γ, ℕ, A }} by mauto 3.
      assert {{ Γ'', ℕ, A[q σ][q τ] ⊢s q (q τ) : Γ', ℕ, A[q σ] }} by mauto 3.
      assert {{ Γ'', ℕ ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, ℕ }} by mauto 4.
      assert {{ ⊢ Γ'', ℕ, A[q (σ∘τ)] }} by mauto 2.
      assert {{ Γ'', ℕ ⊢ A[q σ][q τ] ≈ A[q σ∘q τ] }} by mauto 2.
      assert {{ Γ'', ℕ ⊢ A[q σ∘q τ] ≈ A[q (σ∘τ)] }} by mauto 2.
      assert {{ ⊢ Γ'', ℕ, A[q σ∘q τ] ≈ Γ'', ℕ, A[q (σ∘τ)] }} by mauto 4.
      assert {{ ⊢ Γ'', ℕ, A[q σ][q τ] ≈ Γ'', ℕ, A[q (σ∘τ)] }} by mauto 5.
      assert {{ ⊢ Γ'', ℕ, A[q σ][q τ] ≈ Γ'', ℕ, A[q (σ∘τ)] }} as -> by eassumption.
      assert {{ Γ'', ℕ ⊢s Wk : Γ'' }} by mauto 3.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢s Wk : Γ'', ℕ }} by mauto 3.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢ #1 : ℕ }} by mauto 3.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢ succ #1 : ℕ }} by mauto 3.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢s Wk∘Wk,,succ #1 : Γ'', ℕ }} by mauto 3.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢ A[q σ][q τ][Wk∘Wk,,succ #1] ≈ A[q (σ∘τ)][Wk∘Wk,,succ #1] }} as -> by mauto 3.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢ A[q (σ∘τ)][Wk∘Wk,,succ #1] ≈ A[Wk∘Wk,,succ #1][q (q (σ∘τ))]  }} as -> by mauto 3.
      assert {{ Γ'', ℕ ⊢s q (σ∘τ) : Γ, ℕ }} by mauto 2.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢s q (q (σ∘τ)) : Γ, ℕ, A }} by mauto 2.
      assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
      assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 3.
      assert {{ Γ, ℕ, A ⊢ #1 : ℕ }} by mauto 3.
      assert {{ Γ, ℕ, A ⊢ succ #1 : ℕ }} by mauto 3.
      assert {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 3.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢s q (q τ) : Γ', ℕ, A[q σ] }} by mauto 2.
      assert {{ Γ'', ℕ, A[q σ][q τ] ⊢ MS[q (q σ)∘q (q τ)] ≈ MS[q (q σ)][q (q τ)] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 3.
      assert {{ Γ'', ℕ, A[q σ][q τ] ⊢ MS[q (q σ)][q (q τ)] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 3.
      assert {{ Γ'', ℕ, A[q σ∘q τ] ⊢s q (q σ)∘q (q τ) ≈ q (q σ∘q τ) : Γ, ℕ, A }} by mauto 3.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢s q (q σ)∘q (q τ) ≈ q (q σ∘q τ) : Γ, ℕ, A }} by mauto 2.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢s q (q σ∘q τ) ≈ q (q (σ∘τ)) : Γ, ℕ, A }} by mauto 4.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢s q (q σ)∘q (q τ) ≈ q (q (σ∘τ)) : Γ, ℕ, A }} by mauto 2.
      assert {{ Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1] }} by mauto 2.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢ A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] ≈ A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} by mauto 3.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢ MS[q (q σ)][q (q τ)] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 2.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢ MS[q (q σ)][q (q τ)] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as -> by mauto 2.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢ MS[q (q σ)∘q (q τ)] ≈ MS[q (q (σ∘τ))] : A[Wk∘Wk,,succ #1][q (q σ)∘q (q τ)] }} by mauto 4.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢ MS[q (q (σ∘τ))] ≈ MS[q (q σ)∘q (q τ)] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as <- by mauto 3.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢ MS[q (q (σ∘τ))][Id] ≈ MS[q (q (σ∘τ))] : A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as <- by mauto 3.
      assert {{ Γ'', ℕ, A[q (σ∘τ)] ⊢ A[Wk∘Wk,,succ #1][q (q (σ∘τ))][Id] ≈ A[Wk∘Wk,,succ #1][q (q (σ∘τ))] }} as <- by mauto 3.
      mauto 3.
    + intuition.
Qed.


Lemma glu_rel_exp_natrec_helper {P} (pred_P : PredicativeSig P) : forall {sn sa anns Γ SbΓ A MZ MS} {r : Ru_nat P sn},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ SbΓ }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ @ anns, ^(so_Some sn) ⊩ A @ sa }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ MZ : A[Id,,zero] @ sa }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩ MS : A[Wk∘Wk,,succ #1] @ sa }} ->
    forall {Γ' M m},
      glu_nat r Γ' M m ->
      forall {σ ρ am P El},
        {{ Γ' ⊢s σ ® ρ ∈ SbΓ }} ->
        {{ ⟦ A ⟧ ρ ↦ m ↘ am }} ->
        {{ DG am ∈ glu_typ_elem pred_P sa ↘ P ↘ El }} ->
        exists r,
          {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\
            {{ Γ' ⊢ rec M return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M] ® r ∈ El }}.
Proof.
  intros * ? HA ? ?.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ @ anns ⊩ ℕ : Sort@sn @ ^so_None }} as Hℕ by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A[Id,,zero] @ sa }}.
  {
    assert {{ Γ ⊢ ℕ : Sort@sn }} by mauto 2.
    assert {{ Γ ⊢ ℕ ≈ ℕ[Id] : Sort@sn }} by mauto 4.
    mauto.
  }
  pose (SbΓℕ := cons_glu_sub_pred pred_P (so_Some sn) Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P ((so_Some sn)::anns) ↘ SbΓℕ }} by (invert_glu_rel_exp Hℕ; econstructor; mauto 4; try reflexivity).
  pose proof HA.
  invert_glu_rel_typ HA.
  assert (forall Γ' σ ρ, SbΓℕ Γ' σ ρ -> glu_rel_typ_with_sub pred_P sa Γ' A σ ρ) by mauto 3.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ, ℕ, A @ sa::(so_Some sn)::anns }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ, ℕ @ anns, ^(so_Some sn) ⊩s Wk : Γ @ anns }} by mauto 4.
  assert {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩s Wk : Γ, ℕ @ anns, ^(so_Some sn) }} by mauto 3.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢ ℕ[Wk][Wk] ≈ ℕ : Sort@sn }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢ ℕ[Wk][Wk] ⊆ ℕ }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩ ℕ : Sort@sn @ ^so_None }} by mauto 3.
  assert {{ #1 : ℕ[Wk][Wk] @ (so_Some sn) ∈ Γ, ℕ, A @ anns, ^(so_Some sn), sa }} by mauto 2.
  assert {{ #1 : ℕ[Wk][Wk] @ (so_Some sn) ∈ Γ, ℕ, A @ anns, ^(so_Some sn), sa }} by mauto 2.
  assert {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩ #1 : ℕ[Wk][Wk] @ ^(so_Some sn) }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩ #1 : ℕ @ ^(so_Some sn) }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa  ⊩ succ #1 : ℕ @ ^(so_Some sn) }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩ A[Wk∘Wk,,succ #1] @ sa }} by mauto 3.
  induction 1; intros; rename Γ0 into Γ'.
  - (** [glu_nat_zero] *)
    eapply glu_rel_exp_natrec_zero_helper; revgoals; mauto 3.
  - (** [glu_nat_succ] *)
    eapply glu_rel_exp_natrec_succ_helper; revgoals; mauto 3.
  - (** [glu_nat_neut] *)
    eapply glu_rel_exp_natrec_neut_helper; revgoals; mauto 3.  
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


Lemma glu_rel_exp_natrec {P} (pred_P : PredicativeSig P) : forall {sn sa sa' sa'' anns Γ A MZ MS M} {r : Ru_nat P sn},
    {{ ⟪ pred_P ⟫ Γ, ℕ @ anns, ^(so_Some sn) ⊩ A @ sa }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ MZ : A[Id,,zero] @ sa' }} ->
    {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩ MS : A[Wk∘Wk,,succ #1] @ sa'' }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ M : ℕ @ ^(so_Some sn) }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] @ sa }}.
Proof.
intros * r HA HMZ HMS HM.
  assert {{ Γ, ℕ ⊢ A }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} as [SbΓ] by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ @ anns ⊩ ℕ : Sort@sn @ ^so_None }} as Hℕ by mauto 4.
  pose (SbΓℕ := cons_glu_sub_pred pred_P (so_Some sn) Γ {{{ ℕ }}} SbΓ).
  assert {{ EG Γ, ℕ ∈ glu_ctx_env pred_P ((so_Some sn)::anns)↘ SbΓℕ }} by (invert_glu_rel_exp Hℕ; econstructor; mauto 4; reflexivity).
  pose (SbΓℕA := cons_glu_sub_pred pred_P sa {{{ Γ, ℕ }}} {{{ A }}} SbΓℕ).
  assert {{ EG Γ, ℕ, A ∈ glu_ctx_env pred_P (sa::(so_Some sn)::anns) ↘ SbΓℕA }} by (invert_glu_rel_typ HA; econstructor; mauto 4; try reflexivity).
  pose proof HM.
  invert_glu_rel_exp HM.
  pose proof HA.
  invert_glu_rel_typ HA.
  eexists; split; [eassumption |].
  intros.
  destruct_glu_rel_by_assumption SbΓ HM.
  simplify_evals.
  match_by_head (@glu_typ_elem) ltac:(fun H => directed inversion H; subst).
  match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H).
  apply_predicate_equivalence.
  inversion_clear_by_head (@nat_glu_exp_pred P).
  assert (glu_nat r Γ' {{{ M[σ] }}} m) by mauto 2.
  assert {{ Γ' ⊢s σ,,M[σ] ® ρ ↦ m ∈ SbΓℕ }} by (unfold SbΓℕ; mauto 3).
  assert (glu_rel_typ_with_sub pred_P sa Γ' A {{{ σ,,M[σ] }}} d{{{ ρ ↦ m }}}) as [] by mauto 2.

  assert {{ ⟪ pred_P ⟫ Γ @ anns ⊩s Id,,zero : Γ, ℕ @ anns, ^(so_Some sn) }} by (eapply glu_rel_sub_extend_nat; mauto 3).
  assert {{ ⟪ pred_P ⟫ Γ @ anns ⊩ MZ : A[Id,,zero] @ sa }} by mauto 3.

  assert {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩s Wk : Γ, ℕ @ anns, ^(so_Some sn) }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ, ℕ @ anns, ^(so_Some sn) ⊩s Wk : Γ @ anns }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩s Wk∘Wk : Γ @ anns }} by mauto 3.

  assert {{ #1 : ℕ[Wk][Wk] ∈ Γ, ℕ, A }} by mauto 3.
  assert {{ #1 : ℕ[Wk][Wk] @ (so_Some sn) ∈ Γ, ℕ, A @ anns, ^(so_Some sn), sa }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ ⊩ Γ, ℕ, A @ (sa :: (so_Some sn) :: anns) }} by mauto 3.
  assert {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩ #1 : ℕ[Wk][Wk] @ ^(so_Some sn) }} by mauto 3.
  assert {{ ⊢ Γ, ℕ, A }} by mauto 3.
  assert {{ Γ, ℕ, A ⊢ ℕ[Wk][Wk] ⊆ ℕ }} by mauto.
  assert {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩ #1 : ℕ @ ^(so_Some sn) }} by (eapply glu_rel_exp_conv; mauto).
  assert {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩ succ #1 : ℕ @ ^(so_Some sn) }} by mauto 4.
  assert {{ ⟪ pred_P ⟫ Γ, ℕ, A @ anns, ^(so_Some sn), sa ⊩s Wk∘Wk,, succ #1 : Γ, ℕ @ anns, ^(so_Some sn) }} by mauto 4.
  
  assert (exists r, {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} /\ exp_rel0 Γ' {{{ A[σ,, M[σ]] }}} {{{ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end }}} r) as [? []] by (eapply glu_rel_exp_natrec_helper; revgoals; mauto 4).

  econstructor; mauto 3.
  assert {{ Γ' ⊢s σ : Γ }} by mauto 2.
  assert {{ Γ ⊢ M : ℕ }} by mauto 2.
  assert {{ Γ, ℕ ⊢ A }} by mauto 3.
  destruct sa.
  - assert {{ Γ' ⊢ A[σ,,M[σ]] ≈ A[Id,,M][σ] }} as <- by (symmetry; mauto 2).
    assert {{ Γ' ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }} as -> by (econstructor; mauto 4).
    eassumption.
  - assert {{ Γ, ℕ ⊢ A : Sort@s }} by mauto 3.
    assert {{ Γ' ⊢ A[σ,,M[σ]] ≈ A[Id,,M][σ] : Sort@s }} as <- by (symmetry; mauto 2).
    assert {{ Γ' ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }} as -> by (econstructor; mauto 4).
    eassumption.
Qed.

#[export]
Hint Resolve glu_rel_exp_natrec : mcpts.
