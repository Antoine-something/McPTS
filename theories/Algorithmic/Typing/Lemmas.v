From McPTS Require Import PtsSignature LibTactics.
From McPTS.Algorithmic.Typing Require Import Definitions.
From McPTS.Algorithmic Require Import Subtyping.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import Consequences.Rules.
From McPTS.Core.Semantic Require Import Consequences.
From McPTS.Frontend Require Import Elaborator.
Import Domain_Notations.

Record FunctionalSig (P : PtsSig) : Prop :=
  mkFunctionalSig {
      Func_ax_typ : forall s1 s2 s2', Ax_typ P s1 s2 -> Ax_typ P s1 s2' -> s2 = s2';
      Func_ru_pi : forall s1 s2 s3 s3', Ru_pi P s1 s2 s3 -> Ru_pi P s1 s2 s3' -> s3 = s3';
      Func_ru_nat : forall s s', Ru_nat P s -> Ru_nat P s' -> s = s';
    }.

Lemma functional_alg_type_infer {P} (pred_P : PredicativeSig P) (func_P : FunctionalSig P) : forall {Γ : ctx P} {A A' M},
    {{ Γ ⊢a M ⟹ A }} ->
    {{ Γ ⊢a M ⟹ A' }} ->
    A = A'.
Proof.
  intros * HM1 HM2. gen A'.
  induction HM1;
    intros;
    dependent destruction HM2;
    subst;
    functional_nbe_rewrite_clear;
    f_equiv;
    try reflexivity;
    intuition.

  - assert (A = A0) as <- by (eapply functional_ctx_lookup; eassumption).
    functional_nbe_rewrite_clear.
    reflexivity.
  - assert (n{{{ Π r A B }}} = n{{{ Π r0 A0 B0 }}}) by mauto 2.
    dependent destruction H3.
    mauto 3.
  - eapply Func_ru_nat; mauto 2.
Qed.

#[local]
  Hint Resolve functional_alg_type_infer : mcpts.         

Ltac functional_alg_type_infer_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_alg_type_infer equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : {{ ^?Γ ⊢a ^?M ⟹ ^?A1 }}, H2 : {{ ^?Γ ⊢a ^?M ⟹ ^?A2 }} |- _ =>
      clean replace A2 with A1 by first [solve [mauto 2 using functional_alg_type_infer] | tactic_error A2 A1]; clear H2
  end.
Ltac functional_alg_type_infer_rewrite_clear := repeat functional_alg_type_infer_rewrite_clear1.      

Lemma alg_type_sound {P} (pred_P : PredicativeSig P) :
  (forall {Γ : ctx P} {A M}, {{ Γ ⊢a M ⟸ A }} -> {{ ⊢ Γ }} -> {{ Γ ⊢ A }} -> {{ Γ ⊢ M : A }}) /\
    (forall {Γ : ctx P} {A M}, {{ Γ ⊢a M ⟹ A }} -> {{ ⊢ Γ }} -> {{ Γ ⊢ M : A }}).
Proof.
  apply alg_type_mut_ind; intros; try mautosolve 4.

  - assert {{ Γ ⊢ M : A }} by mauto 2.
    gen_presups.
    assert {{ Γ ⊢ A ⊆ B }} by  (eapply alg_subtyping_sound; mauto 2).
    mauto 2.    
  - assert {{ Γ ⊢ A }} by mauto 3.
    assert {{ ⊢ Γ, A@s }} by mauto 3.
    inversion H1; subst.
    assert {{ Γ ⊢ A ≈ B }} as <- by (mauto 2 using soundness_ty').
    mauto 2.
  - assert {{ Γ ⊢ A : Sort@s1 }} by mauto 3.
    assert {{ ⊢ Γ, A@s1 }} by mauto 3.
    assert {{ Γ, A@s1 ⊢ B : Sort@s2 }} by mauto 3.
    mauto 2.
  - assert {{ Γ ⊢ A : Sort@s1 }} by mauto 3.
    assert {{ Γ ⊢ A ≈ C : Sort@s1 }} by mauto 3 using soundness'.
    assert {{ ⊢ Γ, A@s1 }} by mauto 2.
    
    assert {{ Γ, A@s1 ⊢ B : Sort@s2 }} by mauto 3.
    assert {{ Γ, A@s1 ⊢ B ≈ D : Sort@s2 }} by (mauto 2 using soundness').
    assert {{ Γ, A@s1 ⊢ D ⊆ B }} by mauto 4.

    gen_presups.
    assert {{ ⊢ Γ, ^(nf_to_exp C)@s1 ≈ Γ, A@s1 }} by mauto 4.
    assert {{ Γ, ^(nf_to_exp C)@s1 ⊢ B : Sort@s2 }} by mauto 3.
    assert {{ Γ ⊢ Π r A B ⊆ Π r C D }} by mauto 4.

    assert {{ Γ ⊢ λ r A B M : Π r A B }} by mauto 3.
    mauto 3.
  - assert {{ Γ ⊢ M : Π r A B }} by mauto 3.
    gen_presup H2.
    eapply wf_typ_pi_inversion in HAwf as [].
    assert {{ Γ ⊢ N : A }} by mauto 3.
    gen_presups.
    assert {{ Γ ⊢ B[Id,,N] }} by mauto 4.
    assert {{ Γ ⊢ B[Id,,N] ≈ C }} by (mauto 2 using soundness_ty').
    mauto 3.
  - assert {{ Γ ⊢ ℕ : Sort@s }} by mauto 2.
    assert {{ Γ ⊢ M : ℕ }} by mauto 3.
    mauto 3.
  - assert {{ Γ ⊢ ℕ : Sort@s }} by mauto 2.
    assert {{ Γ ⊢ ℕ }} by mauto 2.
    assert {{ ⊢ Γ, ℕ@s }} by mauto 2.
    assert {{ Γ ⊢ Sort@s' ⊆ Sort@s'' }} by mauto 3.    
    assert {{ Γ, ℕ@s ⊢ A : Sort@s' }} by mauto 3.
    assert {{ Γ, ℕ@s ⊢ A : Sort@s'' }} by mauto 3.
    assert {{ ⊢ Γ, ℕ@s, A@s'' }} by mauto 3.
    assert {{ Γ ⊢ N : ℕ }} by mauto 2.
    assert {{ Γ ⊢s Id,,zero : Γ, ℕ@s }} by mauto 3.
    assert {{ Γ ⊢ A[Id,,zero] : Sort@s' }} by mauto 3.
    assert {{ Γ ⊢ A[Id,,zero] : Sort@s'' }} by mauto 3.
    assert {{ Γ, ℕ@s, A@s'' ⊢s Wk∘Wk : Γ }} by (econstructor; mauto 3).
    assert {{ Γ, ℕ@s, A@s'' ⊢s Wk∘Wk,,succ #1 : Γ, ℕ@s }} by mauto 4.
    assert {{ Γ, ℕ@s, A@s'' ⊢ A[Wk∘Wk,,succ #1] : Sort@s' }} by mauto 4.
    assert {{ Γ, ℕ@s, A@s'' ⊢ A[Wk∘Wk,,succ #1] : Sort@s'' }} by mauto 4.
    assert {{ Γ ⊢ A[Id,,N] : Sort@s' }} by mauto 3.
    assert {{ Γ ⊢ A[Id,,N] : Sort@s'' }} by mauto 3.
    assert {{ Γ ⊢ A[Id,,N] ≈ B }} as <- by (mauto 3 using soundness_ty').
    econstructor; mauto 3.
Qed.


Lemma alg_type_check_sound {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A M},
    {{ Γ ⊢a M ⟸ A }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  pose proof (alg_type_sound pred_P); intuition.
Qed.

Lemma alg_type_infer_sound {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A M},
    {{ Γ ⊢a M ⟹ A }} -> {{ ⊢ Γ }} -> {{ Γ ⊢ M : A }}.
Proof.
  pose proof @alg_type_sound; intuition.
Qed.


Lemma alg_type_infer_normal {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A A' M},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢a M ⟹ A }} ->
    nbe_ty Γ A A' ->
    A = A'.
Proof with (f_equiv; mautosolve 4).
  intros * ? Hinfer Hnbe. gen A'.
  assert {{ Γ ⊢ M : A }} by mauto 3 using alg_type_infer_sound.
  induction Hinfer; intros;
    try (dir_inversion_clear_by_head @nbe_ty;
         dir_inversion_by_head @eval_exp; subst;
         dir_inversion_by_head @read_typ; subst;
         reflexivity).
  - assert {{ Γ ⊢ A : Sort@s }} by mauto 2.
    eapply idempotent_nbe_ty; mauto 2.
  - destruct (wf_fn_inversion H0) as [].
    gen_presup H6.
    assert {{ Γ ⊢ A : Sort@s1 }} by mauto 3.
    assert {{ Γ ⊢ A ≈ C : Sort@s1 }} by mauto 3 using soundness'.
    assert {{ Γ, A@s1 ⊢ B : Sort@s2 }} by (eapply alg_type_check_sound; mauto 2).
    assert {{ Γ, A@s1 ⊢ B ≈ D : Sort@s2 }} by mauto 3 using soundness'.
    
    assert {{ Γ, A@s1 ⊢ M : D }} by mauto 2 using alg_type_infer_sound.
    assert {{ ⊢ Γ, A@s1 ≈ Γ, ^(nf_to_exp C)@s1 }} by mauto 3.
    assert {{ Γ, ^(nf_to_exp C)@s1 ⊢ D : Sort@s2 }} by mauto 4.
    assert (nbe_ty Γ A C) by mauto 2 using nbe_type_to_nbe_ty.
    assert (nbe_ty {{{ Γ, A@s1 }}} B D) by mauto 2 using nbe_type_to_nbe_ty.

    dir_inversion_clear_by_head @nbe_ty.
    simplify_evals.
    match_by_head @read_typ ltac:(fun H => progressive_invert H).
    functional_initial_env_rewrite_clear.
    assert (initial_env {{{ Γ, ^(nf_to_exp C)@s1 }}} d{{{ ρ0 ↦ ⇑! a (length Γ) }}}) by mauto 3.
    assert (nbe_ty Γ A C) by mauto 3.
    assert (nbe_ty Γ C A0) by mauto 3.
    replace A0 with C by mauto 2.
    assert (nbe_ty {{{ Γ, ^(nf_to_exp C)@s1 }}} D B') by mauto 3.
    assert (nbe_ty {{{ Γ, A@s1 }}} D B')  by mauto 4 using ctxeq_nbe_ty_eq'...
  - assert {{ Γ ⊢ M : ^n{{{ Π r A B }}} }} by mauto 3 using alg_type_infer_sound.
    simpl in H3.
    gen_presups.    
    destruct (wf_typ_pi_inversion HAwf) as [].
    assert {{ Γ ⊢ Π r A B : Sort@s3 }} by mauto 2.
    assert {{ Γ ⊢ N : A }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ ⊢ B[Id,,N] : Sort@s2 }} by mauto 3...
  - assert {{ Γ ⊢ ℕ : Sort@s }} by mauto 3.
    assert {{ Γ ⊢ N : ℕ }} by mauto 3 using alg_type_check_sound.
    assert {{ ⊢ Γ, ℕ@s }} by mauto 3.
    assert {{ Γ, ℕ@s ⊢ A : ^n{{{ Sort@s' }}} }} by mauto 3 using alg_type_infer_sound...
Qed.

#[export]
Hint Resolve alg_type_infer_normal : mcpts.

Lemma alg_type_check_typ_implies_alg_type_infer_typ {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A s},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢a A ⟸ Sort@s }} ->
    exists s', {{ Γ ⊢a A ⟹ Sort@s' }} /\ st_subtyp s' s.
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  assert {{ Γ ⊢ A : Sort@s }} by mauto using alg_type_check_sound.
  assert {{ Γ ⊢ A : A' }} by mauto 2 using alg_type_infer_sound.
  gen_presups.
  assert {{ Γ ⊢ A' ⊆ Sort@s }} by mauto 2 using alg_subtyping_sound.
  pose proof (subtyp_sort_is_sort pred_P H) as [s' []].
  
  assert (A' = n{{{ Sort@s' }}}).
  {
    pose proof (@completeness_typ_unsorted P pred_P _ _ _ H2) as [W []].
    inversion H5; subst.
    simplify_evals.
    inversion H8; subst.
    mauto 2.
  }
  subst.  
  repeat eexists; mauto 3.
Qed.

(* Lemma alg_type_check_typ_implies_alg_type_infer_typ {P} (pred_P : PredicativeSig P) : forall {Γ A s}, *)
(*     {{ ⊢ Γ }} -> *)
(*     {{ Γ ⊢a A ⟸ Sort@s }} -> *)
(*     exists A' s', {{ Γ ⊢a A ⟹ A' }} /\ {{ Γ ⊢ A' ≈ Sort@s' }} /\ st_subtyp s' s. *)
(* Proof. *)
(*   intros * ? Hcheck. *)
(*   inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst. *)
(*   assert {{ Γ ⊢ A : Sort@s }} by mauto using alg_type_check_sound. *)
(*   assert {{ Γ ⊢ A : A' }} by mauto 2 using alg_type_infer_sound. *)
(*   gen_presups. *)
(*   assert {{ Γ ⊢ A' ⊆ Sort@s }} by mauto 2 using alg_subtyping_sound. *)
(*   pose proof (subtyp_sort_is_sort pred_P H) as [s' []]. *)
(*   repeat eexists; mauto 3. *)
(* Qed. *)

#[export]
Hint Resolve alg_type_check_typ_implies_alg_type_infer_typ : mcpts.

Lemma alg_type_check_pi_implies_alg_type_infer_pi {P} (pred_P : PredicativeSig P) : forall {Γ M A B s1 s2 s3 s} {r : Ru_pi P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ Π r A B : Sort@s }} ->
    {{ Γ ⊢a M ⟸ Π r A B }} ->
    exists A0 B0, {{ Γ ⊢a M ⟹ Π r A0 B0 }} /\ {{ Γ ⊢ A0 ≈ A : Sort@s1 }} /\  {{ Γ, A@s1 ⊢ B0 ⊆ B }}.
Proof.
  intros * ? ? Hcheck.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ⊆ Sort@s }}) as [? []] by mauto 3.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  assert {{ Γ ⊢ M : A' }} by mauto 3 using alg_type_infer_sound.
  gen_presups.
  assert {{ Γ ⊢ A' ⊆ Π r A B }} by mauto 3 using alg_subtyping_sound.

  (* This should follow by consequences of normalization *)
  assert (exists A0 B0,  {{ Γ ⊢ A' ≈  Π r A0 B0 }}) as [A0 [B0]]by mauto 3.
  assert {{ Γ ⊢ Π r A0 B0 ⊆ Π r A B }} by mauto 4.
  assert ({{ Γ ⊢ A0 ≈ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B0 ⊆ B }}) as [] by mauto 2 using subtyp_pi_inversion.
  assert {{ Γ, A@s1 ⊢a B0 ⊆ B }} by mauto 2 using alg_subtyping_complete.

  pose proof (@completeness_typ_unsorted P pred_P _ _ _ H5) as [W []].
  assert (A' = W) by mauto 2.
  subst.
  inversion H11; subst.
  simplify_evals.
  dependent destruction H14.
  subst.

  assert ({{ Γ ⊢ A1 ≈ A : Sort@s1}} /\ {{ Γ, A@s1 ⊢ B' ⊆ B }}) as [] by mauto 2 using subtyp_pi_inversion.
  do 2 eexists; repeat split; mauto 2 using alg_subtyping_complete.
Qed.


(* Lemma alg_type_check_pi_implies_alg_type_infer_pi {P} (pred_P : PredicativeSig P) : forall {Γ M A B s1 s2 s3 s} {r : Ru_pi P s1 s2 s3}, *)
(*     {{ ⊢ Γ }} -> *)
(*     {{ Γ ⊢ Π r A B : Sort@s }} -> *)
(*     {{ Γ ⊢a M ⟸ Π r A B }} -> *)
(*     exists A' A0 B0, {{ Γ ⊢a M ⟹ A' }} /\ {{ Γ ⊢ A' ≈ Π r A0 B0 }} /\ {{ Γ ⊢ A0 ≈ A : Sort@s1 }} /\  {{ Γ, A@s1 ⊢a B0 ⊆ B }}. *)
(* Proof. *)
(*   intros * ? ? Hcheck. *)
(*   assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ⊆ Sort@s }}) as [? []] by mauto 3. *)
(*   inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst. *)
(*   assert {{ Γ ⊢ M : A' }} by mauto 3 using alg_type_infer_sound. *)
(*   gen_presups. *)
(*   assert {{ Γ ⊢ A' ⊆ Π r A B }} by mauto 3 using alg_subtyping_sound. *)

(*   (* This should follow by consequences of normalization *) *)
(*   assert (exists A0 B0,  {{ Γ ⊢ A' ≈  Π r A0 B0 }}) as [A0 [B0]]by mauto 3. *)
(*   assert {{ Γ ⊢ Π r A0 B0 ⊆ Π r A B }} by mauto 4. *)
(*   assert ({{ Γ ⊢ A0 ≈ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B0 ⊆ B }}) as [] by mauto 2 using subtyp_pi_inversion. *)
(*   assert {{ Γ, A@s1 ⊢a B0 ⊆ B }} by mauto 2 using alg_subtyping_complete. *)
(*   do 3 eexists. *)
(*   repeat split; mauto 3. *)
(* Qed. *)

#[export]
Hint Resolve alg_type_check_pi_implies_alg_type_infer_pi : mcpts.

Lemma alg_type_check_subtyp {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A A' M},
    {{ Γ ⊢a M ⟸ A }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ Γ ⊢a M ⟸ A' }}.
Proof.
  intros * [] **.
  assert {{ Γ0 ⊢a B ⊆ A' }} by mauto 3 using alg_subtyping_complete.
  mauto 3 using alg_subtyping_trans.
Qed.

#[export]
Hint Resolve alg_type_check_subtyp : mcpts.

Corollary alg_type_check_conv {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A A' M},
    {{ Γ ⊢a M ⟸ A }} ->
    {{ Γ ⊢ A ≈ A' }} ->
    {{ Γ ⊢a M ⟸ A' }}.
Proof.
  mauto 3.
Qed.

#[export]
Hint Resolve alg_type_check_conv : mcpts.

Lemma alg_type_check_complete {P} (pred_P : PredicativeSig P) : forall {Γ A M},
    user_exp P M ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢a M ⟸ A }}.
Proof.
  intros * Hue.
  induction 1; gen_presups; inversion Hue; subst; clear Hue; mauto 4 using alg_subtyping_complete, alg_type_check_subtyp.
  - econstructor; mauto 3.
    mauto 3 using alg_subtyping_complete.
  - assert {{ Γ ⊢ Sort@s3 ⊆ Sort@s3 }} by mauto 2.
    assert {{ Γ ⊢a Sort@s3 ⊆ Sort@s3 }} by mauto 2 using alg_subtyping_complete.
    econstructor; mauto 4.
  - assert {{ Γ ⊢a A ⟸ Sort@s1 }} by mauto 2.
    assert {{ Γ, A@s1 ⊢a B ⟸ Sort@s2 }} by mauto 2.
    assert {{ Γ, A@s1 ⊢a M ⟸ B }} by mauto 2.
    assert (exists B', {{ Γ, A@s1 ⊢a M ⟹ B' }} /\ {{ Γ, A@s1 ⊢a B' ⊆ B }}) as [B' []] by (inversion_clear_by_head @alg_type_check; firstorder).
    assert (exists W : nf P, nbe Γ A {{{ Sort@s1 }}} W /\ {{ Γ ⊢ A ≈ W : Sort@s1 }}) as [W []] by mauto 2 using soundness.
    assert (exists W : nf P, nbe {{{ Γ, A@s1 }}} B {{{ Sort@s2 }}} W /\ {{ Γ, A@s1 ⊢ B ≈ W : Sort@s2 }}) as [W' []] by mauto 2 using soundness.
    gen_presups.
    assert {{ Γ ⊢ ^n{{{Π r W W'}}} ⊆ Π r A B }} by (eapply wf_subtyp_pi; mauto 4).
    assert {{ Γ ⊢a ^n{{{ Π r W W' }}} ⊆ Π r A B }} by mauto 2 using alg_subtyping_complete.
    econstructor; mauto 4.
  - assert {{ Γ ⊢a M ⟸ Π r A B }} by mauto 2.
    assert {{ Γ ⊢a N ⟸ A }} by mauto 2.

    assert (exists A0 B0, {{ Γ ⊢a M ⟹ Π r A0 B0 }} /\ {{ Γ ⊢ A0 ≈ A : Sort@s1 }} /\  {{ Γ, A@s1 ⊢ B0 ⊆ B }}) as [A0 [B0 [? []]]] by mauto 3.
    assert {{ Γ ⊢a N ⟸ A0 }} by mauto 4.
    assert {{ Γ, A@s1 ⊢a B0 ⊆ B }} by mauto 3 using alg_subtyping_complete.

    gen_presup H9.
    assert {{ Γ ⊢s Id,,N : Γ, A@s1 }} by mauto 3.
    assert {{ Γ ⊢ B0[Id,,N] }} by mauto 3.
    assert {{ Γ ⊢ B0[Id,,N] ≈ B0[Id,,N] }} by mauto 2.
    pose proof (@completeness_typ_unsorted _ pred_P _ _ _ H14) as [W []].
    assert {{ Γ ⊢a M N ⟹ W }} by mauto 3.
    econstructor; mauto 2.

    assert {{ Γ ⊢ B0[Id,,N] ⊆ B[Id,,N] }} by mauto 3.
    assert {{ Γ ⊢ B0[Id,,N] ≈ W }} by mauto 3 using soundness_ty'.
    eapply alg_subtyping_complete; mauto 3.
    transitivity {{{ B0[Id,,N] }}}; mauto 3.
    
  - assert (exists W, nbe_ty Γ A W /\ {{ Γ ⊢ A ≈ W }}) as [W []] by (eapply soundness_ty; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  - assert {{ Γ ⊢ Sort@s ⊆ ^n{{{ Sort@s }}} }} by mauto 2.
    assert {{ Γ ⊢a Sort@s ⊆ ^n{{{ Sort@s }}} }} by mauto 2 using alg_subtyping_complete.
    mauto 3.
  - econstructor; mauto 4 using alg_subtyping_complete.
  - econstructor; mauto 4 using alg_subtyping_complete.
  - assert {{ Γ, ℕ@s ⊢a A ⟸ Sort@s' }} by mauto 2.
    assert {{ Γ ⊢a MZ ⟸ A[Id,,zero] }} by mauto 2.
    assert {{ Γ, ℕ@s, A@s' ⊢a MS ⟸ A[Wk∘Wk,,succ #1] }} by mauto 2.
    assert {{ Γ ⊢a M ⟸ ℕ }} by mauto 2.
    
    assert (exists s'0, {{ Γ, ℕ@s ⊢a A ⟹ Sort@s'0 }} /\ st_subtyp s'0 s') as [s'0 []] by mauto 2.
    assert {{ Γ ⊢ Sort@s'[Id,,M] ≈ Sort@s' }} by mauto 4.
    assert {{ Γ ⊢ A[Id,,M] : Sort@s' }} by mauto 4.
    assert {{ Γ ⊢ A[Id,,M] ≈ A[Id,,M] : Sort@s' }} as [W [? _]]%(@completeness P pred_P) by mauto 3.
    
    assert {{ Γ ⊢ A[Id,,M] ≈ W }} by mauto 4 using soundness_ty'.
    assert {{ Γ ⊢ W ⊆ A[Id,,M] }} by mauto 3.
    assert {{ Γ ⊢a W ⊆ A[Id,,M] }} by mauto 3 using alg_subtyping_complete.
    
    assert {{ Γ ⊢a rec M return A | zero -> MZ | succ -> MS end ⟹ W }} by mauto 3.
    econstructor; mauto 3 using completeness_ty.
Qed.

#[export]
Hint Resolve alg_type_check_complete : mcpts.

Corollary alg_type_infer_complete {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A M},
    user_exp P M ->
    {{ Γ ⊢ M : A }} ->
    exists B, {{ Γ ⊢a M ⟹ B }} /\ {{ Γ ⊢a B ⊆ A }}.
Proof.
  intros.
  assert {{ Γ ⊢a M ⟸ A }} as Hcheck by mauto 4 using alg_type_check_complete.
  inversion_clear Hcheck.
  firstorder.
Qed.

#[export]
Hint Resolve alg_type_infer_complete : mcpts.

Corollary alg_type_infer_typ_complete {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {s A},
    user_exp P A ->
    {{ Γ ⊢ A : Sort@s }} ->
    exists s', {{ Γ ⊢a A ⟹ Sort@s' }} /\ (st_subtyp s' s).
Proof.
  mauto 4 using alg_type_check_complete.
Qed.

#[export]
Hint Resolve alg_type_infer_typ_complete : mcpts.

Corollary alg_type_infer_pi_complete  {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {s A},
    user_exp P A ->
    {{ Γ ⊢ A : Sort@s }} ->
    exists s', {{ Γ ⊢a A ⟹ Sort@s' }} /\ (st_subtyp s' s).
Proof.
  mauto 4 using alg_type_check_complete.
Qed.

#[export]
Hint Resolve alg_type_infer_pi_complete : mcpts.
