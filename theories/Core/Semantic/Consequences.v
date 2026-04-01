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
  
Lemma exp_eq_pi_inversion {P} (pred_P : PredicativeSig P) : forall {Γ A B A' B' s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ Π r A B ≈ Π r A' B' : Sort@s3 }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B ≈ B' : Sort@s2 }}.
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
  assert {{ ⊢ Γ, A'@s1 ≈ Γ, A@s1 }} by mauto 3.
  split; [mauto 3 |].
  etransitivity; [| symmetry]; mauto 2.
Qed.

Lemma nf_of_pi {P} (pred_P : PredicativeSig P) : forall {Γ M A B s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ M : Π r A B }} ->
    exists W1 W2, nbe Γ M {{{ Π r A B }}} n{{{ λ r W1 W2 }}}.
Proof.
  intros * [? []]%(@soundness P pred_P).
  dir_inversion_clear_by_head @nbe.
  invert_rel_typ_body.
  dir_inversion_clear_by_head @read_nf.
  do 2 eexists; mauto 4.
Qed.

#[export]
Hint Resolve nf_of_pi : mcpts.

Theorem canonical_form_of_pi {P} (pred_P : PredicativeSig P) : forall {M A B s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ ⋅ ⊢ M : Π r A B }} ->
    exists W1 W2, nbe {{{ ⋅ }}} M {{{ Π r A B }}} n{{{ λ r W1 W2 }}}.
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
  - eassert ({{ ⋅ ⊢ ^_ : ℕ }} /\ {{ ⋅ ⊢ ℕ ≈ ℕ }}) as [? _]...
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

(* Lemma typ_eq_spec {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A B}, *)
(*     {{ Γ ⊢ A ≈ B }} -> *)
(*     (exists s, {{ Γ ⊢ A ≈ B : Sort@s }}) \/ *)
(*       (exists s, A = {{{ Sort@s }}} /\ B = {{{ Sort@s }}}). *)
(* Proof with (congruence + firstorder (mautosolve 4)). *)
(*   intros. *)
(*   induction H. *)
(*   - inversion H; subst. *)
(*     + right; repeat eexists; reflexivity. *)
(*     + left; eexists; mauto 2. *)
(*   - left; eauto. *)
(*   - destruct IHwf_typ_eq as [[s'] | [s']]. *)
(*     + gen_presups. *)
(*       assert {{ Γ ⊢ A ≈ B : Sort@s }} by admit. (* (eapply adjust_exp_eq_level; mauto 2). using adjust_exp_eq_level. *) *)
(*       left. *)
(*       eexists; etransitivity; eauto. *)
(*     + destruct_conjs. *)
(*       subst. *)
(*       left; eauto. *)
(* Admitted. *)

(* #[export] *)
(* Hint Resolve typ_eq_spec : mcpts. *)

(* Lemma subtyp_spec : forall {Γ A B}, *)
(*     {{ Γ ⊢ A ⊆ B }} -> *)
(*     (exists k, {{ Γ ⊢ A ≈ B : Sort@k }}) \/ *)
(*       (exists i j, (exists k, {{ Γ ⊢ A ≈ Sort@i : Sort@k }}) /\ (exists k, {{ Γ ⊢ Sort@j ≈ B : Sort@k }}) /\ i <= j) \/ *)
(*       (exists A1 A2 B1 B2, (exists k, {{ Γ ⊢ A ≈ Π A1 A2 : Sort@k }}) /\ (exists k, {{ Γ ⊢ Π B1 B2 ≈ B : Sort@k }}) /\ (exists k, {{ Γ ⊢ A1 ≈ B1 : Sort@k }}) /\ {{ Γ, B1 ⊢ A2 ⊆ B2 }}) \/ *)
(*       (exists A1 A2 B1 B2, (exists k, {{ Γ ⊢ A ≈ Σ A1 A2 : Sort@k }}) /\ (exists k, {{ Γ ⊢ Σ B1 B2 ≈ B : Sort@k }}) /\ (exists k, {{ Γ ⊢ A1 ≈ B1 : Sort@k }}) /\ {{ Γ, B1 ⊢ A2 ⊆ B2 }}). *)
(* Proof with (congruence + firstorder (mautosolve 4 + lia)). *)
(*   induction 1; mauto 3. *)
(*   - destruct_all; firstorder (mauto 3); *)
(*       try (right; right; left; do 4 eexists; firstorder mautosolve 3); *)
(*       try (right; right; right; do 4 eexists; firstorder mautosolve 3). *)
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
(*       | _: {{ Γ ⊢ M' ≈ Π ^?A1 ^?A2 : Sort@_ }}, *)
(*           _: {{ Γ ⊢ Π ^?B1 ^?B2 ≈ M' : Sort@_ }} |- _ => *)
(*           assert {{ Γ ⊢ Π A1 A2 ≈ Π B1 B2 : Sort@_ }} by mauto 3; *)
(*           assert ({{ Γ ⊢ A1 ≈ B1 : Sort@_ }} /\ {{ Γ, A1 ⊢ A2 ≈ B2 : Sort@_ }}) as [] by mauto 3 using exp_eq_pi_inversion *)
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


(** STOPPED HERE, 
    proof does not work as is because the dependent induction does not generate the same IH as in McTT
 *)
Lemma consistency_ne_helper {P} (pred_P : PredicativeSig P) : forall {s s' : P} {A A'} {W : ne P},
    is_typ_constr A' ->
    (forall s'', A' <> {{{ Sort@s'' }}}) ->
    {{ ⋅, Sort@s @ s' ⊢ A ≈ A' }} ->
    ~ {{ ⋅, Sort@s @ s' ⊢ W : A }}.
Proof with (congruence + mautosolve 3).
  intros * HA' HA'eq Heq HW. gen A'.  
  dependent induction HW; intros; mauto 3; try directed dependent destruction HA';
    try (destruct W; simpl in *; congruence).
  - destruct W; simpl in *; autoinjections.
    eapply IHHW3; [| | | | mauto 4]...
  - destruct W; simpl in *; autoinjections.
    eapply IHHW3; [| | | | mauto 4]...
  - destruct W; simpl in *; autoinjections.
    eapply IHHW3; [| | | | mauto 4]...
  - destruct W; simpl in *; autoinjections.
    eapply IHHW3; [| | | | mauto 4]...
  - destruct W; simpl in *; autoinjections.
    do 2 match_by_head ctx_lookup ltac:(fun H => dependent destruction H).
    assert {{ ⋅, Sort@i ⊢ Sort@i[Wk] ≈ Sort@i : Sort@(S i) }} by mauto 3.
    eapply subtyp_spec in Heq as [| []]; destruct_conjs;
      try (eapply HA'eq; mautosolve 4).
    destruct H1.
    + destruct_all.
      assert {{ ⋅, Sort@i ⊢ Sort@i ≈ Π ^_ ^_ : Sort@_ }} by mauto 3.
      assert ({{{ Π ^_ ^_ }}} = {{{ Sort@i }}}) by mauto 3...
    + destruct_all.
      assert {{ ⋅, Sort@i ⊢ Sort@i ≈ Σ ^_ ^_ : Sort@_ }} by mauto 3.
      assert ({{{ Σ ^_ ^_ }}} = {{{ Sort@i }}}) by mauto 3...
  - destruct W; simpl in *; autoinjections.
    eapply IHHW6; [| | | | mauto 4]...
Qed.

Theorem consistency : forall {i} M,
    ~ {{ ⋅ ⊢ M : Π Sort@i #0 }}.
Proof with (congruence + mautosolve 3).
  intros * HW.
  assert (exists W1 W2, nbe {{{ ⋅ }}} M {{{ Π Sort@i #0 }}} n{{{ λ W1 W2 }}}) as [W1 [W2 Hnbe]] by mauto 3.
  assert (exists W, nbe {{{ ⋅ }}} M {{{ Π Sort@i #0 }}} W /\ {{ ⋅ ⊢ M ≈ W : Π Sort@i #0 }}) as [? []] by mauto 3 using soundness.
  gen_presups.
  functional_nbe_rewrite_clear.
  dependent destruction Hnbe.
  invert_rel_typ_body.
  match_by_head read_nf ltac:(fun H => directed dependent destruction H).
  match_by_head read_typ ltac:(fun H => directed dependent destruction H).
  invert_rel_typ_body.
  match_by_head read_nf ltac:(fun H => directed dependent destruction H).
  simpl in *.
  assert (exists B, {{ ⋅, Sort@i ⊢ M0 : B }} /\ {{ ⋅ ⊢ Π Sort@i B ⊆ Π Sort@i #0 }}) as [B [? [| [|]]%subtyp_spec]] by mauto 3;
    destruct_all;
    try assert ({{{ Π ^_ ^_ }}} = {{{ Sort@_ }}}) by mauto 3;
    try congruence.
  - assert (_ /\ {{ ^_ ⊢ B ≈ #0 : ^_ }}) as [_ ?] by mauto 3 using exp_eq_pi_inversion.
    eapply consistency_ne_helper...
  - assert (_ /\ {{ ^_ ⊢ B ≈ ^_ : ^_ }}) as [_ ?] by mauto 3 using exp_eq_pi_inversion.
    assert (_ /\ {{ ^_ ⊢ ^_ ≈ #0 : ^_ }}) as [? ?] by mauto 3 using exp_eq_pi_inversion.
    assert {{ ^_ ⊢ B ⊆ #0 }} by (etransitivity; [| eapply ctxeq_subtyp]; mauto 4).
    eapply consistency_ne_helper...
  - eapply is_typ_constr_and_exp_eq_pi_implies_eq_pi in H6; mauto 3.
    destruct_all...
Qed.
