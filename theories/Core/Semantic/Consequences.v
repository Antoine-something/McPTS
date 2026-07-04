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

(* Lemma wf_var_inversion {P} : forall {Γ : ctx P} {x A s}, *)
(*     {{ #x : A @ s ∈ Γ }} -> *)
(*     forall B, {{ Γ ⊢ #x : B }} -> *)
(*          {{ Γ ⊢ B : Sort@s }}. *)
(* Proof. *)
(*   intros * HA B HB. *)
(*   dependent induction HB. *)
(*   - assert (A = B /\ s = s0) as [] by (eapply functional_ctx_lookup; mauto 2); subst. *)
(*     eassumption. *)
(*   - assert (exists B' s', {{ #x : B'@s' ∈ Γ }} /\ {{ Γ ⊢ A0 ≈ B' }}) as [B' [s' []]] by (eapply wf_var_inversion_helper; mauto 2). *)
(*     assert  *)
    
(* Lemma wf_var_inversion {P} : forall {Γ : ctx P} {x A}, *)
(*     {{ Γ ⊢ #x : A }} -> *)
(*     exists B s, {{ #x : B@s ∈ Γ }} /\ {{ Γ ⊢ A ≈ B : Sort@s }}. *)
(* Proof. *)
(*   intros * HA. *)
(*   assert (exists B s, {{ #x : B@s ∈ Γ }} /\ {{ Γ ⊢ A ≈ B }}) as [B [s []]] by (eapply wf_var_inversion_helper; mauto 2). *)
(*   dependent induction HA. *)
(*   - assert (A = B /\ s = s0) as [] by (eapply functional_ctx_lookup; mauto 2); subst. *)
(*     do 2 eexists; split; mauto 2. *)
(*   - assert {{ Γ ⊢ A0 ≈ B }} by mauto 3. *)
(*     specialize (IHHA1 x A0 ltac:(reflexivity) ltac:(reflexivity) B s0 ltac:(eassumption) ltac:(eassumption)) as [B' [s' []]]. *)
(*     assert (B = B' /\ s0 = s') as [] by (eapply functional_ctx_lookup; mauto 2); subst. *)
(* Admitted. *)

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
  - (* This is part of Completeness.Consequences.Types, not yet merged *)
    assert (s2 = s) by mauto 2. 
    subst.
    exists s1; split; mauto 3.
  - (* This also need the consequences *)
    assert ({{{ Π r A' B' }}} = {{{ Sort@s }}}) by mauto 2.
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

(* #[local] *)
(* Ltac gen_l_IH pred_P l l' H := *)
(*   match type of H with *)
(*   | {{ ^?Γ ⊢ ^?A ≈ ^?B }} => *)
(*       let IHAB := fresh "HAB" in *)
(*       pose proof l _ pred_P _ _ _ H as IHAB *)
(*   | {{ ^?Γ ⊢ ^?A ≈ ^?B : ^?C }} => *)
(*       let IHAB := fresh "HABC" in *)
(*       pose proof l' _ pred_P _ _ _ _ H as IHAB *)
(*   end. *)


(* Lemma l {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A B}, *)
(*     {{ Γ ⊢ A ≈ B }} -> *)
(*     forall s, *)
(*       ({{ Γ ⊢ A : Sort@s }} -> *)
(*        {{ Γ ⊢ B : Sort@s }}) /\ *)
(*         ({{ Γ ⊢ B : Sort@s }} -> *)
(*          {{ Γ ⊢ A : Sort@s }}) *)
(* with l' {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A B C}, *)
(*     {{ Γ ⊢ A ≈ B : C }} -> *)
(*     forall C', *)
(*       ({{ Γ ⊢ A : C' }} -> *)
(*        {{ Γ ⊢ B : C' }}) /\ *)
(*         ({{ Γ ⊢ B : C' }} -> *)
(*          {{ Γ ⊢ A : C' }}). *)
(* Proof. *)
(*   all: inversion_clear 1; *)
(*     (on_all_hyp: gen_l_IH pred_P l l'); *)
(*     clear l l'; *)
(*     intros; *)
(*     try pose proof HAB s as []; *)
(*     try pose proof HAB0 s as []; *)
(*     mauto 4. *)

(*   - split; mauto 4. *)
(*   -  *)
  
(*   - intros. *)
(*     split; intros. *)
(*     + destruct (subtyp_sort_is_sort pred_P H2) as [s2 []].  *)
    
  

  
(*   intros * H. *)
(*   dependent induction H; intros; gen_presups; mauto 3. *)
(*   - split; intros. *)
(*     + rewrite <- x. *)
(*       eassumption. *)
(*     + rewrite x; eassumption. *)
(*   - split; intros. *)
(*     + rewrite <- x in H0. *)
(*       mauto 2. *)
(*     + rewrite <- x. *)
(*       mauto 3. *)
(*   - split; intros. *)
(*     + rewrite <- x0 in H0. *)
(*       rewrite <- x. *)
(*       mauto 2 using wf_exp_sort_sub_implies_wf_exp_sort. *)
(*     + rewrite <- x0. *)
(*       rewrite <- x in H0.       *)
(*       assert {{ Δ ⊢ Sort@s1 : Sort@s }} by mauto 2 using wf_sort_sort_any_context. *)
(*       mauto 2. *)
(*   -  *)

(*       mauto. *)
(*   intros * H. *)
(*   dependent induction H; intros; gen_presups; mauto 3. *)
  
  
(*   - specialize (IHwf_typ_eq s). *)
(*     destruct_conjs. *)
(*     split; mauto 3. *)
(*   -  *)

  
(* Lemma exp_eq_sort_wf_sort_wf {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {M A}, *)
(*     {{ Γ ⊢ M : A }} -> *)
(*     forall M' A', *)
(*       {{ Γ ⊢ M ≈ M' : A' }} -> *)
(*       {{ Γ ⊢ M' : A }}. *)
(* Proof. *)
(*   intros * HA. *)
(*   dependent induction HA; intros; gen_presups; mauto . *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - assert {{ Γ ⊢ Sort@s0 ≈ Sort@s' }} by mauto 3. *)
(*     assert (s = s') by mauto 2. *)
(*     subst. *)
(*     eassumption. *)
(*   - *)


    
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

    

(* Lemma t {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {s B}, *)
(*     {{ Γ ⊢ B : Sort@s }} -> *)
(*     forall s', *)
(*       {{ Γ ⊢ B : Sort@s' }} -> *)
(*       (exists s'', {{ Γ ⊢ B : Sort@s'' }} /\ st_subtyp s'' s /\ st_subtyp s'' s'). *)
(* Proof. *)
(*   intros * H. *)
(*   dependent induction H. *)
(*   - intros. *)
(*     destruct (wf_exp_sort_sort_implies_axiom H1) as [s2 []]. *)
(*     assert (st_subtyp s2 s') by mauto using subtyp_sort_sort_implies_st_subtyp. *)
(*     assert {{ Γ ⊢ Sort@s1 : Sort@s2 }} by mauto 2. *)
(*     exists s2. *)
    
(*     repeat eexists; mauto 3. *)
  

(* Lemma glu_rel_exp_unsorted_implies_glu_typ_elem {P} (pred_P : PredicativeSig P) : forall {Γ Δ : ctx P} {A M a σ ρ so}, *)
(*     {{ ⟦ A ⟧ ρ ↘ a }} -> *)
(*     glu_rel_exp_unsorted pred_P so Γ M A σ ρ -> *)
(*     exists typ_rel exp_rel, {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }}. *)

(* Lemma glu_rel_exp_with_sub_unsorted_inversion {P} (pred_P : PredicativeSig P) : forall {so Δ M A σ ρ}, *)
(*   glu_rel_exp_with_sub_unsorted pred_P so Δ M A σ ρ -> *)
(*   exists a m typ_rel exp_rel, *)
(*     {{ ⟦ A ⟧ ρ ↘ a }} /\ {{ ⟦ M ⟧ ρ ↘ m }} /\ {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} /\ {{ Δ ⊢ M[σ] : A[σ] ® m ∈ exp_rel }}. *)
(* Proof. *)
(*   inversion_clear 1; repeat eexists; mauto 2. *)
(*   econstructor; mauto 2. *)
(* Qed. *)
    
(* Lemma typ_eq_spec_helper {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A B C s s'}, *)
(*     {{ Γ ⊢ A ≈ B : Sort@s }} -> *)
(*     {{ Γ ⊢ B ≈ C : Sort@s' }} -> *)
(*     (* {{ Γ ⊢ B : Sort@s' }} -> *) *)
(*     (exists s'', {{ Γ ⊢ A ≈ C : Sort@s'' }}). *)
(* Proof. *)
(*   intros. *)
(*   epose proof (completeness_fundamental_exp_eq P pred_P _ _ _ _ H) as [env_relΓ []]. *)
(*   epose proof (completeness_fundamental_exp_eq P pred_P _ _ _ _ H0) as [env_relΓ' []]. *)
(*   handle_per_ctx_env_irrel. *)
(*   assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) as [ρ [ρ' ?]] by mauto using per_ctx_then_per_env_initial_env. *)
(*   destruct_conjs. *)
(*   functional_initial_env_rewrite_clear. *)
(*   (on_all_hyp: destruct_rel_by_assumption env_relΓ). *)
(*   destruct_by_head @rel_typ_unsorted. *)
(*   invert_rel_typ_body. *)
(*   destruct_by_head @rel_exp. *)

(*   simplify_evals. *)
(*   assert (elem_rel0 <~> per_sort pred_P s) by (inversion H11; subst; [eassumption|]; invert_per_sort_elem H8; mauto 2). *)
(*   assert (elem_rel <~> per_sort pred_P s') by (inversion H13; subst; [eassumption|]; invert_per_sort_elem H14; mauto 2). *)
(*   apply_relation_equivalence. *)
(*   match_by_head @per_sort ltac:(fun H => destruct H as []). *)
(*   assert (per_typ_elem pred_P x m m0) by mauto 3. *)
(*   symmetry in H12. *)
(*   epose proof per_typ_elem_and_per_sort_elem_implies_per_sort_elem pred_P H12 H9. *)
(*   handle_per_sort_elem_irrel. *)
(*   assert (per_sort_elem pred_P s' x0 m m'0) by (transitivity m0; [symmetry|]; eassumption). *)

(*   gen_presups. *)
(*   epose proof soundness_fundamental_exp pred_P _ _ _ HM as [so1 [Sb1 []]]. *)
(*   epose proof soundness_fundamental_exp pred_P _ _ _ HN as [so2 [Sb2 []]]. *)
(*   epose proof soundness_fundamental_exp pred_P _ _ _ HM0 as [so3 [Sb3 []]]. *)
(*   epose proof soundness_fundamental_exp pred_P _ _ _ HN0 as [so4 [Sb4 []]]. *)

(*   handle_functional_glu_ctx_env P. *)

(*   epose proof initial_env_glu_rel_exp pred_P H1 H22. *)
(*   assert (Sb1 Γ {{{ Id }}} ρ) by intuition. *)
(*   assert (Sb2 Γ {{{ Id }}} ρ) by intuition. *)
(*   assert (Sb4 Γ {{{ Id }}} ρ) by intuition. *)

(*   assert (glu_rel_exp_with_sub_unsorted pred_P so1 Γ B {{{ Sort@s' }}} {{{ Id }}} ρ) by mauto 2. *)
(*   assert (glu_rel_exp_with_sub_unsorted pred_P so2 Γ C {{{ Sort@s' }}} {{{ Id }}} ρ) by mauto 2. *)
(*   assert (glu_rel_exp_with_sub_unsorted pred_P so3 Γ A {{{ Sort@s }}} {{{ Id }}} ρ) by mauto 2. *)
(*   assert (glu_rel_exp_with_sub_unsorted pred_P so4 Γ B {{{ Sort@s }}} {{{ Id }}} ρ) by mauto 2. *)


(*   epose proof glu_rel_exp_with_sub_unsorted_inversion pred_P H25 as [? [b [typ_rel [exp_rel]]]]. *)
(*   epose proof glu_rel_exp_with_sub_unsorted_inversion pred_P H26 as [? [c [typ_rel0 [exp_rel0]]]]. *)
(*   epose proof glu_rel_exp_with_sub_unsorted_inversion pred_P H27 as [? [a [typ_rel1 [exp_rel1]]]]. *)
(*   epose proof glu_rel_exp_with_sub_unsorted_inversion pred_P H28 as [? [b' [typ_rel2 [exp_rel2]]]]. *)
(*   destruct_conjs. *)
(*   simplify_evals. *)
  
(*   assert (glu_rel_typ_with_sub pred_P s' Γ B {{{ Id }}} ρ) by mauto 3. *)
(*   assert (glu_rel_typ_with_sub pred_P s' Γ C {{{ Id }}} ρ) by mauto 3. *)
(*   assert (glu_rel_typ_with_sub pred_P s Γ B {{{ Id }}} ρ) by mauto 3. *)
(*   assert (glu_rel_typ_with_sub pred_P s Γ A {{{ Id }}} ρ) by mauto 3. *)
(*   destruct_glu_rel_typ_with_sub. *)
(*   simplify_evals. *)
  
    
  
(*   (* symmetry in H12. *) *)
  (* assert (per_sort_elem pred_P s' x0 m m0) by mauto 4. *)
  (* handle_per_sort_elem_irrel. *)
  (* assert (per_sort pred_P s' m'0 m). *)
  (* symmetry in H11. *)
  (* eapply per_sort_trans'; mauto 2. *)
  (* inversion H11; subst. *)

  (* functional_eval_rewrite_clear. *)
  (* invert_rel_typ_unsorted_body. *)
  
  
(*   epose proof completeness_typ_unsorted H as [W []]. *)
(*   epose proof soundness pred_P H0 as [WA []]. *)
(*   epose proof soundness pred_P H1 as [WB []]. *)
(*   assert (nbe_ty Γ A WA) by mauto 3. *)
(*   assert (nbe_ty Γ B WB) by mauto 3. *)
(*   functional_nbe_rewrite_clear. *)



  (*
    {{ Γ ⊢ A ≈ B : Sort@s }} ->
    {{ Γ ⊢ B : Sort@s' }} ->
    {{ Γ ⊢ A ≈ B : Sort@s' }}
    glu_sort_elem s' typ_rel exp_rel b
    glu_sort_elem s typ_rel0 exp_rel0 a
    glu_sort_elem s' typ_rel exp_rel a
    typ_rel Γ B
    typ_rel0 Γ A
    
*)

  
 

  

  
(*   (* intros * H. *) *)
(*   (* induction H; intros; mauto 3. *) *)
(*   (* - assert (exists s'' : P, {{ Γ ⊢ A ≈ B : Sort@s'' }}) by mauto 3. *) *)
(*   (*   destruct_conjs. *) *)
(*   (*   symmetry in H3. *) *)
(*   (*   eauto. *) *)
(*   (* -  *) *)
    

(*   (*   specialize (IHwf_typ_eq s' s). *) *)
(* Abort. *)

(* Move this*)
(* Generalizable All Variables. *)
(* Inductive is_sort {P} (s : St P) : exp P -> Prop := *)
(*   | is_sort_sort : is_sort s {{{ Sort@s }}} *)
(*   | is_sort_sub : `{ is_sort s M -> is_sort s {{{ M[σ] }}} }. *)

(* Lemma typ_eq_spec {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A B}, *)
(*     {{ Γ ⊢ A ≈ B }} -> *)
(*     (exists s, {{ Γ ⊢ A ≈ B : Sort@s }}) \/ *)
(*       (exists s, is_sort s A /\ is_sort s B). *)
(* Proof with (congruence + firstorder (mautosolve 4)). *)
(*   intros. *)
(*   induction H; mauto 3. *)
(*   - admit. *)
(*   (* - destruct (wf_typ_inversion H) as [s' []]. *) *)
(*   (*   + right; repeat eexists; mauto 3. *) *)
(*   (*   + left; eexists; mauto 2. *) *)
(*   - admit. *)
(*     (* destruct IHwf_typ_eq as [[s']|[s']]; destruct_conjs; mauto 4. *) *)
(*   - destruct IHwf_typ_eq1 as [[s]|[s]]; *)
(*       destruct IHwf_typ_eq2 as [[s']|[s']]. *)
(*     +  *)

(*     admit. *)
(*   - destruct (wf_typ_inversion H) as [s' []]. *)
(*     + right; repeat eexists; mauto 3. *)
(*     + left; eexists; mauto 2. *)
(*   - right; repeat eexists; mauto 4. *)
(*   - destruct IHwf_typ_eq as [[s'] | [s']]. *)
(*     + gen_presups. *)
(*       left; eexists; mauto 4. *)
(*     + destruct_conjs; gen_presups. *)
(*       right; repeat eexists; mauto 4. *)
(*   - destruct (wf_typ_inversion H1) as [s' []]. *)
(*     + gen_presups. *)
(*       assert {{ Γ ⊢s σ∘τ : Γ'' }} by mauto 3. *)
(*       assert {{ Γ ⊢ Sort@s'[σ][τ] ≈ Sort@s' }} by mauto 3. *)
(*       right; repeat eexists; mauto 4. *)
(*     + gen_presups. *)
(*       left; eexists; mauto 4. *)
(* Abort.st_subtyp s1 s2) *)

(* #[export] *)
(* Hint Resolve typ_eq_spec : mcpts. *)

(* Lemma subtyp_spec {P} (pred_P : PredicativeSig P) : forall {Γ A B}, *)
(*     {{ Γ ⊢ A ⊆ B }} -> *)
(*     {{ Γ ⊢ A ≈ B }} \/ *)
(*       (exists s1 s2, {{ Γ ⊢ A ≈ Sort@s1 }} /\ {{ Γ ⊢ Sort@s2 ≈ B }} /\ st_subtyp s1 s2) \/ *)
(*       (exists A1 A2 B1 B2 s1 s2 s3 (r : Ru_pi P s1 s2 s3), *)
(*           (exists s, {{ Γ ⊢ A ≈ Π r A1 A2 : Sort@s }} /\ st_subtyp s3 s) *)
(*           /\ (exists s, {{ Γ ⊢ Π r B1 B2 ≈ B : Sort@s }} /\ st_subtyp s3 s) *)
(*           /\ {{ Γ ⊢ A1 ≈ B1 : Sort@s1 }} /\ {{ Γ, B1@s1 ⊢ A2 ⊆ B2 }}).  *)
(* Proof with (congruence + firstorder (mautosolve 4 + lia)). *)
(*   induction 1; mauto 3. *)
(*   -  *)


(*     destruct_all; (mauto 3); *)
(*       try (right; left; repeat eexists; mautosolve 4). *)
(*     + match goal with *)
(*       | _: {{ Γ ⊢ M' ≈ Sort@?i : Sort@_ }}, *)
(*           _: {{ Γ ⊢ Sort@?j ≈ M' : Sort@_ }} |- _ => *)
(*           assert {{ Γ ⊢ Sort@j ≈ Sort@i : Sort@_ }} by mauto 3; *)
(*           assert (j = i) as -> by mauto 3 *)
(*       end... *)
(*     + assert {{ Γ ⊢ Π ^_ ^_ ≈ Sort@_ : Sort@_ }} by mauto 3. *)
(*       assert ({{{ Π ^_ ^_ }}} = {{{ Sort@_ }}}) by mauto 3... *)
(*     + assert {{ Γ ⊢ Σ ^_ ^_ ≈ Sort@_ : Sort@_ }} by mauto 3. *)
(*       assert ({{{ Σ ^_ ^_ }}} = {{{ Sort@_ }}}) by mauto 3... *)
(*     + assert {{ Γ ⊢ Π ^_ ^_ ≈ Sort@_ : Sort@_ }} by mauto 3. *)
(*       assert ({{{ Π ^_ ^_ }}} = {{{ Sort@_ }}}) by mauto 3... *)
(*     + match goal with *)
(*       | _: {{ Γ ⊢ M' ≈ Π r ^?A1 ^?A2 : Sort@?s }}, *)
(*           _: {{ Γ ⊢ Π r ^?B1 ^?B2 ≈ M' : Sort@_ }} |- _ => *)
(*           assert {{ Γ ⊢ Π r A1 A2 ≈ Π r B1 B2 : Sort@s }} by mauto 3; *)
(*           assert ({{ Γ ⊢ A1 ≈ B1 : Sort@_ }} /\ {{ Γ, A1@s1 ⊢ A2 ≈ B2 : Sort@_ }}) as [] by mauto 3 using exp_eq_pi_inversion *)
(*       end. *)
(*       assert {{ ⊢ Γ ≈ Γ }} by mauto 3. *)
(*       right; right; left. *)
(*       do 4 eexists; repeat split; mauto 3. *)
(*       * eexists; eapply exp_eq_trans_typ_max... *)
(*       * etransitivity; [| eassumption]. *)
(*         etransitivity; eapply ctxeq_subtyp... *)
(*     + assert {{ Γ ⊢ Π ^_ ^_ ≈ Σ ^_ ^_ : Sort@_ }} as Hcontra by mauto 3. *)
(*       eapply is_typ_constr_and_exp_eq_sigma_implies_eq_sigma in Hcontra; mauto 3. *)
(*       destruct_all... *)
(*     + assert {{ Γ ⊢ Σ ^_ ^_ ≈ Sort@_ : Sort@_ }} by mauto 3. *)
(*       assert ({{{ Σ ^_ ^_ }}} = {{{ Sort@_ }}}) by mauto 3... *)
(*     + assert {{ Γ ⊢ Π ^_ ^_ ≈ Σ ^_ ^_ : Sort@_ }} as Hcontra by mauto 3. *)
(*       eapply is_typ_constr_and_exp_eq_sigma_implies_eq_sigma in Hcontra; mauto 3. *)
(*       destruct_all... *)
(*     + match goal with *)
(*       | _: {{ Γ ⊢ M' ≈ Σ ^?A1 ^?A2 : Sort@_ }}, *)
(*           _: {{ Γ ⊢ Σ ^?B1 ^?B2 ≈ M' : Sort@_ }} |- _ => *)
(*           assert {{ Γ ⊢ Σ A1 A2 ≈ Σ B1 B2 : Sort@_ }} by mauto 3; *)
(*           assert ({{ Γ ⊢ A1 ≈ B1 : Sort@_ }} /\ {{ Γ, A1 ⊢ A2 ≈ B2 : Sort@_ }}) as [] by mauto 3 using exp_eq_sigma_inversion *)
(*       end. *)
(*       assert {{ ⊢ Γ ≈ Γ }} by mauto 3. *)
(*       right; right; right. *)
(*       do 4 eexists; repeat split; mauto 3. *)
(*       * eexists; eapply exp_eq_trans_typ_max... *)
(*       * etransitivity; [| eassumption]. *)
(*         etransitivity; eapply ctxeq_subtyp... *)
(*   - right; left. *)
(*     do 2 eexists... *)
(*   - right; right; left. *)
(*     do 4 eexists... *)
(*   - right; right; right. *)
(*     do 4 eexists... *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve subtyp_spec : mcpts. *)


(* STOPPED HERE
 * proof does not work as is because the dependent induction does not generate the same IH as in McTT  *)
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
    (* assert (exists s', {{ ⋅, Sort@s ⊢ A' ≈ Sort@s' }}) by mauto 2. *)
    (* assert  *)
    
    (* assert {{ ⋅, Sort@s ⊢ Sort@s2' ⊆ Sort@s2 }} by (eapply wf_subtyp_sort_weaken; mauto 2). *)
    (* assert {{ ⋅, Sort@s1 @ s2 ⊢ Sort@s1[Wk] ≈ Sort@s1 : Sort@s2 }} by (eapply wf_exp_eq_sort_sub'; mauto 3). *)
    
    (* assert (exists s', Ax_typ P s s' /\ {{ ⋅ ⊢ Sort@s ⊆ Sort@s' }}) as [s' []] by mauto 2. *)
    (* (* assert (s2 = s2') as <- by mauto 3. *) *)
    (* assert {{ ⋅, Sort@s1 @ s2 ⊢s Wk : ⋅ }} by mauto 3. *)
    (* gen_presup HW. *)
    (* assert {{ ⋅, Sort@s1@s2 ⊢ Sort@s2' ⊆ Sort@s2 }} by (eapply wf_subtyp_sort_weaken; mauto 2). *)
    (* assert {{ ⋅, Sort@s1 @ s2 ⊢ Sort@s1[Wk] ≈ Sort@s1 : Sort@s2 }} by (eapply wf_exp_eq_sort_sub'; mauto 3). *)
    (* assert {{ ⋅, Sort@s1 @ s2 ⊢ Sort@s1[Wk] ≈ Sort@s1 }} by mauto 2. *)
    (* assert {{ ⋅, Sort@s1@s2 ⊢ Sort@s1 ⊆ A' }} by mauto 4. *)
    (* assert (exists s', A' = {{{ Sort@s' }}}) as [s'] by mauto 3. *)
    (* eapply HA'eq; eassumption. *)
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
