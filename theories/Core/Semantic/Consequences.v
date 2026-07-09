From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core Require Export Soundness.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Completeness.Consequences Require Export Types.
Import Domain_Notations.

Lemma idempotent_nbe {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A M N L},
    {{ Γ ⊢ M : A }} ->
    nbe Γ M A N ->
    nbe Γ N A L ->
    N = L.
Proof.
  intros.
  assert {{ Γ ⊢ M ≈ N : A }} as [? []]%(@completeness P pred_P) by mauto 2 using soundness'.
  functional_nbe_rewrite_clear.
  reflexivity.
Qed.
#[export]
Hint Resolve idempotent_nbe : mcpts.

Lemma idempotent_nbe' {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {s A A' M N L},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }} ->
    nbe Γ M A N ->
    nbe Γ N A' L ->
    N = L.
Proof.
  intros * ? [env_relΓ [?]]%(completeness_fundamental_exp_eq P pred_P) **.
  assert {{ Γ ⊢ M ≈ N : A }} as [? [?]]%(completeness_fundamental_exp_eq P pred_P) by mauto 3 using soundness'.
  handle_per_ctx_env_irrel.
  destruct_by_head @nbe.
  pose proof (per_ctx_then_per_env_initial_env ltac:(eassumption)); destruct_all.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: fun H => directed (pose proof (H _ _ ltac:(eassumption)); destruct_all)).
  destruct_by_head @rel_typ_unsorted.
  invert_rel_typ_body.
  destruct_by_head @rel_exp.
  assert (per_typ_elem pred_P (per_sort pred_P s) d{{{ Sort@s }}} d{{{ Sort@s }}}) by (econstructor; reflexivity).
  handle_per_typ_elem_irrel.
  unfold per_sort in *.
  destruct_all.
  assert (per_typ_elem pred_P R' a0 a) by mauto 2.
  handle_per_typ_elem_irrel.
  pose proof (per_typ_elem_then_per_top ltac:(eassumption) ltac:(eassumption) (length Γ)); destruct_all.
  functional_read_rewrite_clear.
  reflexivity.
Qed.
#[export]
Hint Resolve idempotent_nbe' : mcpts.

Lemma idempotent_nbe_ty {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {s A B C},
    {{ Γ ⊢ A : Sort@s }} ->
    nbe_ty Γ A B ->
    nbe_ty Γ B C ->
    B = C.
Proof.
  intros.
  inversion H0; subst.
  assert (nbe Γ A {{{ Sort@s }}} B) by mauto 3.
  assert {{ Γ ⊢ A ≈ B : Sort@s }} as [? []]%(@completeness_ty P pred_P) by mauto 2 using soundness'.

  functional_nbe_rewrite_clear.
  reflexivity.
Qed.

#[export]
Hint Resolve idempotent_nbe_ty : mcpts.

Lemma idempotent_nbe_ty_unsorted {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A B C},
    {{ Γ ⊢ A  }} ->
    nbe_ty Γ A B ->
    nbe_ty Γ B C ->
    B = C.
Proof.
  intros.
  inversion H0; subst.
  assert (nbe_ty Γ A B) by mauto 3.
  assert {{ Γ ⊢ A ≈ B }} as [? []]%(@completeness_typ_unsorted P pred_P) by mauto 2 using soundness_ty'.

  functional_nbe_rewrite_clear.
  reflexivity.
Qed.

#[export]
Hint Resolve idempotent_nbe_ty_unsorted : mcpts.

Lemma adjust_exp_eq_level {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A A' s s'},
    {{ Γ ⊢ A ≈ A' : Sort@s }} ->
    {{ Γ ⊢ A : Sort@s' }} ->
    {{ Γ ⊢ A' : Sort@s' }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s' }}.
Proof.
  intros * ?%(@completeness P pred_P) ?%(@soundness P pred_P) ?%(@soundness P pred_P).
  destruct_conjs.
  dir_inversion_by_head @nbe; dir_inversion_by_head @nbe_ty; subst.
  match_by_head @eval_exp ltac:(fun H => progressive_invert H).
  match_by_head @read_nf ltac:(fun H => progressive_invert H).
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  functional_read_rewrite_clear.
  etransitivity; [| symmetry]; eauto.
Qed.

Lemma adjust_typ_eq_level {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A A' s},
    {{ Γ ⊢ A ≈ A' }} ->
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ A' : Sort@s }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }}.
Proof.
  intros * ?%(@completeness_typ_unsorted P pred_P) ?%(@soundness P pred_P) ?%(@soundness P pred_P).
  destruct_conjs.
  dir_inversion_by_head @nbe; dir_inversion_by_head @nbe_ty; subst.
  match_by_head @eval_exp ltac:(fun H => progressive_invert H).
  match_by_head @read_nf ltac:(fun H => progressive_invert H).
  functional_initial_env_rewrite_clear.
  functional_eval_rewrite_clear.
  functional_read_rewrite_clear.
  etransitivity; [| symmetry]; eauto.
Qed.

Lemma wf_var_inversion_helper {P} : forall {Γ : ctx P} {x A},
    {{ Γ ⊢ #x : A }} ->
    exists B, {{ #x : B ∈ Γ }} /\ {{ Γ ⊢ B ⊆ A }}.
Proof.
  intros * HA.
  dependent induction HA.
  - eexists; split; mauto 3.
  - specialize (IHHA x A0 ltac:(reflexivity) ltac:(reflexivity)) as [B []].
    eexists; split; mauto 3.
Qed.


Lemma subtyp_sort_is_sort_helper {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A B},
    {{ Γ ⊢ A ⊆ B }} ->
    forall s, {{ Γ ⊢ B ≈ Sort@s }} ->
    exists s', {{ Γ ⊢ A ≈ Sort@s' }} /\ st_subtyp s' s.
Proof.
  intros * Hsub.
  induction Hsub; intros.
  - eexists; split; mauto 2.
  - specialize (IHHsub2 s ltac:(eassumption)) as [s' []].
    specialize (IHHsub1 s' ltac:(eassumption)) as [s'' []].
    eexists; split; mauto 3.
    etransitivity; eassumption.
  - assert (s2 = s) by mauto 2. 
    subst.
    exists s1; split; mauto 3.
  - assert ({{{ Π r A' B' }}} = {{{ Sort@s }}}) by mauto 2.
    inversion H5.
Qed.

Lemma subtyp_sort_is_sort {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A s},
    {{ Γ ⊢ A ⊆ Sort@s }} ->
    exists s', {{ Γ ⊢ A ≈ Sort@s' }} /\ st_subtyp s' s.
Proof.
  intros.
  gen_presup H.
  eapply subtyp_sort_is_sort_helper; mauto 2.
Qed.

Lemma subtyp_sort_sort_implies_st_subtyp {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {s s'},
    {{ Γ ⊢ Sort@s ⊆ Sort@s' }} ->
    st_subtyp s s'.
Proof.
  intros.
  epose proof subtyp_sort_is_sort pred_P H as [s''].
  destruct_conjs.
  assert (s = s'') by mauto 2; subst.
  mauto 2.
Qed.


Lemma wf_exp_sort_sub_implies_wf_exp_sort {P} (pred_P : PredicativeSig P) : forall {Γ Δ : ctx P} {s s' σ},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ Sort@s[σ] : Sort@s' }} ->
    {{ Γ ⊢ Sort@s : Sort@s' }}.
Proof.
  intros * ? []%(@soundness P pred_P).
  destruct_conjs.
  dependent destruction H0.
  simplify_evals.
  inversion H4; subst.
  inversion H8; subst.
  gen_presups.
  mauto 2.
Qed.

Lemma wf_sort_sort_any_context {P}(pred_P : PredicativeSig P) : forall {Γ Δ : ctx P} {s s'},
    {{ Γ ⊢ Sort@s : Sort@s' }} ->
    {{ ⊢ Δ }} -> 
    {{ Δ ⊢ Sort@s : Sort@s' }}.
Proof.
  intros.
  destruct (wf_exp_sort_sort_implies_axiom H) as [s2 []].
  assert (st_subtyp s2 s') by mauto 2 using subtyp_sort_sort_implies_st_subtyp.
  mauto 4.
Qed.              
    
Lemma exp_eq_pi_inversion {P} (pred_P : PredicativeSig P) : forall {Γ A B A' B' s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ Π r A B ≈ Π r A' B' : Sort@s3 }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s1 }} /\ {{ Γ, A ⊢ B ≈ B' : Sort@s2 }}.
Proof.
  intros * H.
  gen_presups.
  (on_all_hyp: fun H => apply wf_pi_inversion' in H; destruct H).
  (on_all_hyp: fun H => apply (@completeness P pred_P) in H).
  (on_all_hyp: fun H => apply (@soundness P pred_P) in H).
  destruct_conjs.
  dir_inversion_clear_by_head @nbe.
  dir_inversion_clear_by_head @nbe_ty.
  dir_inversion_by_head @initial_env; subst.
  functional_initial_env_rewrite_clear.
  invert_rel_typ_body.
  dir_inversion_clear_by_head @read_nf.
  dir_inversion_by_head @read_typ; subst.
  functional_eval_rewrite_clear.
  functional_read_rewrite_clear.
  autoinjections.
  assert {{ Γ ⊢ A' ≈ A : Sort@s1 }} by mauto 3.
  assert {{ ⊢ Γ, A' ≈ Γ, A }} by mauto 4.
  split; [mauto 3 |].
  etransitivity; [| symmetry]; mauto 2.
Qed.

Lemma subtyp_pi_inversion {P} (pred_P : PredicativeSig P) : forall {Γ A B A' B' s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ Π r A B ⊆ Π r A' B' }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s1 }} /\ {{ Γ, A' ⊢ B ⊆ B' }}.
Proof.
  intros * H.
  assert {{ ⟪ pred_P ⟫ Γ ⊨ Π r A B ⊆ Π r A' B' }} by mauto 3 using completeness_fundamental_typ_subtyp.
  destruct H0 as [env_relΓ []].
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) as [ρ [ρ' ?]] by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head @rel_typ_unsorted.
  destruct_by_head @rel_exp.
  functional_eval_rewrite_clear.
  invert_rel_typ_unsorted_body.
  dependent destruction H12.
  dependent destruction H6.

  gen_presups.
  (on_all_hyp: fun H => apply wf_typ_pi_inversion in H; destruct H).
  (on_all_hyp: fun H => apply (@soundness P pred_P) in H).
  destruct_conjs.
  dir_inversion_clear_by_head @nbe.
  dir_inversion_by_head @initial_env; subst.
  functional_initial_env_rewrite_clear.
  invert_rel_typ_body.
  dir_inversion_clear_by_head @read_nf.
  
  destruct_conjs.
  assert (per_top_typ a a0) by mauto 2.
  destruct (H40 (length Γ)) as [WA []].
  functional_read_rewrite_clear.
  assert {{ Γ ⊢ A ≈ A' : Sort@s1 }} by mauto 3.

  gen_presups.
  assert {{ ⊢ Γ, A ≈ Γ, A' }} by mauto 4.
  assert {{ Γ, A' ⊢ B : Sort@s2 }} by mauto 2.

  
  destruct (soundness_fundamental_exp pred_P _ _ _ H42) as [anns [so [Sb []]]].
  destruct (soundness_fundamental_exp pred_P _ _ _ HM0) as [anns' [so' [Sb' []]]].
  assert {{ Γ, A' ⊢s Id ® (ρ ↦ ⇑! a0 (length Γ))  ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto).
  assert {{ Γ, A' ⊢s Id ® (ρ ↦ ⇑! a0 (length Γ)) ∈ Sb' }} by (eapply initial_env_glu_rel_exp; mauto).

  assert (glu_rel_typ_with_sub pred_P s2 {{{ Γ, A' }}} B {{{ Id }}} d{{{ ρ ↦ ⇑! a0 (length Γ) }}}) by mauto 3.
  assert (glu_rel_typ_with_sub pred_P s2 {{{ Γ, A' }}} B' {{{ Id }}} d{{{ ρ ↦ ⇑! a0 (length Γ) }}}) by mauto 3.
  destruct_glu_rel_typ_with_sub.

  handle_per_sort_elem_lower.
  handle_per_sort_elem_irrel.
  assert (@per_bot P d{{{ !(length Γ) }}} d{{{ !(length Γ) }}}) by mauto 3.
  assert (in_rel0 d{{{ ⇑! a0 (length Γ) }}}  d{{{ ⇑! a0 (length Γ) }}}) by (eapply per_bot_then_per_elem; mauto 2).
  assert {{ ⟪ pred_P ⟫ Subs a1 <: m at s2 }} by mauto 3.

  autorewrite with mcpts in H51.
  autorewrite with mcpts in H54.
  assert {{ Γ, A' ⊢ B ⊆ B' }}.
  eapply glu_sort_elem_per_subtyp_typ_sorted_escape; mauto 3.
  split; eassumption.
Qed.

Lemma nf_of_pi {P} (pred_P : PredicativeSig P) : forall {Γ M A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ M : Π r A B }} ->
    exists W1 W2 W3, nbe Γ M {{{ Π r A B }}} n{{{ λ r W1 W2 W3 }}}.
Proof.
  intros * [? []]%(@soundness P pred_P).
  dir_inversion_clear_by_head @nbe.
  invert_rel_typ_body.
  dir_inversion_clear_by_head @read_nf.
  do 3 eexists; mauto 4.
Qed.

#[export]
Hint Resolve nf_of_pi : mcpts.

Theorem canonical_form_of_pi {P} (pred_P : PredicativeSig P) : forall {M A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ ⋅ ⊢ M : Π r A B }} ->
    exists W1 W2 W3, nbe {{{ ⋅ }}} M {{{ Π r A B }}} n{{{ λ r W1 W2 W3 }}}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve canonical_form_of_pi : mcpts.


Inductive canonical_nat {P} : nf P -> Prop :=
| canonical_nat_zero : canonical_nat n{{{ zero }}}
| canonical_nat_succ : forall W, canonical_nat W -> canonical_nat n{{{ succ W }}}
.

#[export]
  Hint Constructors canonical_nat : mcpts.

Theorem canonical_form_of_nat {P} (pred_P : PredicativeSig P) : forall {M : exp P},
    {{ ⋅ ⊢ M : ℕ }} ->
    exists W, nbe {{{ ⋅ }}} M {{{ ℕ }}} W /\ canonical_nat W.
Proof with mautosolve 4.
  intros * [? []]%(@soundness P pred_P).
  eexists; split; [eassumption |].
  dir_inversion_clear_by_head @nbe.
  invert_rel_typ_body.
  match_by_head1 @eval_exp ltac:(fun H => clear H).
  gen M.
  match_by_head1 @read_nf ltac:(fun H => dependent induction H);
    intros; mauto 3;
    gen_presups.
  - eassert ({{ ⋅ ⊢ ^_ : ℕ }} /\ {{ ⋅ ⊢ ℕ ⊆ ℕ }}) as [? _]...
  - match_by_head1 (@wf_exp P {{{ ⋅ }}} {{{ ℕ }}}) ltac:(fun H => contradict H)...
Qed.

#[export]
Hint Resolve canonical_form_of_nat : mcpts.

Theorem canonical_form_of_typ {P} (pred_P : PredicativeSig P) : forall {s : P} {M},
    {{ ⋅ ⊢ M : Sort@s }} ->
    exists W, nbe {{{ ⋅ }}} M {{{ Sort@s }}} W /\ is_typ_constr W /\ (forall V, W <> n{{{ ⇑ V }}}).
Proof with mautosolve 4.
  intros * [? []]%(@soundness P pred_P).
  eexists; split; [eassumption |].
  dir_inversion_clear_by_head @nbe.
  invert_rel_typ_body.
  match_by_head1 @eval_exp ltac:(fun H => clear H).
  gen M.
  dir_inversion_clear_by_head @read_nf.
  match_by_head1 @read_typ ltac:(fun H => dependent induction H);
    intros; split; intros; mauto 3; try congruence;
    gen_presups;
    match_by_head1 (wf_exp {{{ ⋅ }}} {{{ Sort@s }}}) ltac:(fun H => contradict H)...
Qed.

#[export]
  Hint Resolve canonical_form_of_typ : mcpts.

Theorem subtyp_sort_implies_eq_typ_left {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {s A},
    {{ Γ ⊢ A ⊆ Sort@s }} ->
    exists s', {{ Γ ⊢ A ≈ Sort@s' }}.
Proof.
  intros.
  assert {{ ⟪ pred_P ⟫ Γ ⊨ A ⊆ Sort@s }} as [env_relΓ] by mauto using completeness_fundamental_typ_subtyp.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) as [ρ [ρ' ?]] by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted).
  destruct_by_head (@rel_exp).
  invert_rel_typ_body.
  destruct (per_subtyp_sort_inv_right pred_P H12) as [s' []].
  inversion H5; subst.
  
  assert (per_typ_elem pred_P (per_sort pred_P s) d{{{ Sort@s }}} d{{{ Sort@s }}}) by (econstructor; reflexivity).
  handle_per_typ_elem_irrel.
  assert (is_typ_constr {{{ Sort@s }}}) as Histyp' by mauto 1.

  gen_presups.
  destruct (soundness_ty pred_P HA) as [W []].
  dir_inversion_clear_by_head @nbe_ty.
  functional_initial_env_rewrite_clear.
  invert_rel_typ_body.
  dir_inversion_by_head @read_typ; subst.
  eexists; eassumption.
Qed.

Theorem subtyp_sort_implies_eq_typ_right {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {s A},
    {{ Γ ⊢ Sort@s ⊆ A }} ->
    exists s', {{ Γ ⊢ A ≈ Sort@s' }}.
Proof.
  intros.
  assert {{ ⟪ pred_P ⟫ Γ ⊨ Sort@s ⊆ A }} as [env_relΓ] by mauto using completeness_fundamental_typ_subtyp.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) as [ρ [ρ' ?]] by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted).
  destruct_by_head (@rel_exp).
  invert_rel_typ_body.
  destruct (per_subtyp_sort_inv_left pred_P H12) as [s' []].
  inversion H3; subst.
  
  assert (per_typ_elem pred_P (per_sort pred_P s) d{{{ Sort@s }}} d{{{ Sort@s }}}) by (econstructor; reflexivity).
  handle_per_typ_elem_irrel.
  assert (is_typ_constr {{{ Sort@s }}}) as Histyp' by mauto 1.

  gen_presups.
  destruct (soundness_ty pred_P HB) as [W []].
  dir_inversion_clear_by_head @nbe_ty.
  functional_initial_env_rewrite_clear.
  invert_rel_typ_body.
  dir_inversion_by_head @read_typ; subst.
  eexists; eassumption.
Qed.

#[export]
Hint Resolve subtyp_sort_implies_eq_typ_left subtyp_sort_implies_eq_typ_right : mcpts.

Lemma consistency_ne_helper {P} (pred_P : PredicativeSig P) : forall {s : P} {A A'} {W : ne P},
    is_typ_constr A' ->
    (forall s', A' <> {{{ Sort@s' }}}) ->
    {{ ⋅, Sort@s ⊢ A ⊆ A' }} ->
    ~ {{ ⋅, Sort@s ⊢ W : A }}.
Proof with (congruence + mautosolve 3).
  intros * HA' HA'eq Heq HW. gen A'.
  dependent induction HW; intros; mauto 3; try directed dependent destruction HA';
    try (destruct W; simpl in *; congruence).
  - destruct W; simpl in *; autoinjections.
    eapply (IHHW3 _ _ _ ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) {{{ Π r A0 B }}}).
    + econstructor.
    + intros * H.
      inversion H.
    + gen_presup HW3.
      econstructor; mauto 2.

  - destruct W; simpl in *; autoinjections.
    do 2 match_by_head @ctx_lookup ltac:(fun H => dependent destruction H).
    inversion_clear H.
    
    assert {{ ⋅, Sort@s ⊢s Wk : ⋅ }} by mauto 3.
    assert {{ ⋅, Sort@s ⊢ Sort@s[Wk] ≈ Sort@s }} by mauto 3.
    assert {{ ⋅, Sort@s ⊢ Sort@s ⊆ Sort@s[Wk] }} by mauto 3.
    assert {{ ⋅, Sort@s ⊢ Sort@s ⊆ A' }} by mauto 3.
    assert (exists s', A' = {{{ Sort@s' }}}) as [s'] by mauto 2.
    eapply HA'eq; eassumption.
    
  - destruct W; simpl in *; autoinjections.
    eapply (IHHW3 _ _ _ ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) {{{ ℕ }}}).
    + econstructor.
    + intros * Hnateq.
      inversion Hnateq.
    + assert {{ ⋅, Sort@s ⊢ ℕ }} by mauto 4.
      econstructor; mauto 2.
Qed.

Theorem consistency {P} (pred_P : PredicativeSig P) : forall s1 s2 s3 s (r : Ru_pi P s1 s2 s3) M,
    ~ {{ ⋅ ⊢ M : Π r Sort@s #0 }}.
Proof with (congruence + mautosolve 3).
  intros * HW.
  assert (exists W1 W2 W3, nbe {{{ ⋅ }}} M {{{ Π r Sort@s #0 }}} n{{{ λ r W1 W2 W3 }}}) as [W1 [W2 [W3 Hnbe]]] by mauto 3.
  assert (exists W, nbe {{{ ⋅ }}} M {{{ Π r Sort@s #0 }}} W /\ {{ ⋅ ⊢ M ≈ W : Π r Sort@s #0 }}) as [? []] by mauto 3 using soundness.
  gen_presups.
  functional_nbe_rewrite_clear.
  dependent destruction Hnbe.
  invert_rel_typ_body.
  match_by_head @read_nf ltac:(fun H => directed dependent destruction H).
  match_by_head @read_typ ltac:(fun H => directed dependent destruction H).
  invert_rel_typ_body.
  match_by_head @read_nf ltac:(fun H => directed dependent destruction H).
  simpl in *.
  assert (exists B, {{ ⋅, Sort@s ⊢ M0 : B }} /\ {{ ⋅ ⊢ Π r Sort@s B ⊆ Π r Sort@s #0 }}) as [B []] by mauto 3.

  assert {{ ⋅, Sort@s ⊢ B ⊆ #0 }}.
  {
    gen_presup H5.
    assert {{ ⋅ ⊢ Π r Sort@s B : Sort@s3 }} by mauto 3.
    assert {{ ⋅ ⊢ Π r Sort@s #0 : Sort@s3 }} by mauto 3.
    eapply subtyp_pi_inversion; mauto 2.
  }
  eapply consistency_ne_helper...  
Qed.

Theorem pi_subtyp_typ_implies_eq_pi {P} (pred_P : PredicativeSig P) : forall Γ A B C s1 s2 s3 (r : Ru_pi P s1 s2 s3),
    {{ Γ ⊢ Π r B C ⊆ A }} ->
    exists B' C',  {{ Γ ⊢ A ≈  Π r B' C' }}.
Proof.
  intros.
  gen_presups.
  assert {{ ⟪ pred_P ⟫ Γ ⊨ Π r B C ⊆ A }} as [env_relΓ] by mauto using completeness_fundamental_typ_subtyp.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) as [ρ [ρ' ?]] by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head @rel_typ_unsorted.
  destruct_by_head @rel_exp.
  invert_rel_typ_body.

  destruct (per_subtyp_pi_inv_left pred_P H12) as [a' [ρ' [B']]].
  subst.
  epose proof soundness_ty pred_P HB as [W []].
  dir_inversion_clear_by_head @nbe_ty.
  functional_initial_env_rewrite_clear.
  invert_rel_typ_body.
  match_by_head @read_typ ltac:(fun H => progressive_invert H).
  eexists; mauto 3.
Qed.

Theorem typ_subtyp_pi_implies_eq_pi {P} (pred_P : PredicativeSig P) : forall Γ A B C s1 s2 s3 (r : Ru_pi P s1 s2 s3),
    {{ Γ ⊢ A ⊆ Π r B C }} ->
    exists B' C',  {{ Γ ⊢ A ≈  Π r B' C' }}.
Proof.
  intros.
  gen_presups.
  assert {{ ⟪ pred_P ⟫ Γ ⊨ A ⊆ Π r B C }} as [env_relΓ] by mauto using completeness_fundamental_typ_subtyp.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) as [ρ [ρ' ?]] by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head @rel_typ_unsorted.
  destruct_by_head @rel_exp.
  invert_rel_typ_body.

  destruct (per_subtyp_pi_inv_right pred_P H12) as [a' [ρ' [B']]].
  subst.
  epose proof soundness_ty pred_P HA as [W []].
  dir_inversion_clear_by_head @nbe_ty.
  functional_initial_env_rewrite_clear.
  invert_rel_typ_body.
  match_by_head @read_typ ltac:(fun H => progressive_invert H).
  eexists; mauto 3.
Qed.

#[export]
Hint Resolve pi_subtyp_typ_implies_eq_pi typ_subtyp_pi_implies_eq_pi : mcpts.
