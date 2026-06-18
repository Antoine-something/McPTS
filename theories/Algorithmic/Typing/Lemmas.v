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
    {{ ⟪ pred_P ⟫ Γ ⊢a M ⟹ A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊢a M ⟹ A' }} ->
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
  | H1 : {{ ⟪ ?pred_P ⟫ ^?Γ ⊢a ^?M ⟹ ^?A1 }}, H2 : {{ ⟪ ?pred_P ⟫ ^?Γ ⊢a ^?M ⟹ ^?A2 }} |- _ =>
      clean replace A2 with A1 by first [solve [mauto 2 using functional_alg_type_infer] | tactic_error A2 A1]; clear H2
  end.
Ltac functional_alg_type_infer_rewrite_clear := repeat functional_alg_type_infer_rewrite_clear1.      

  
Lemma alg_type_sound {P} (pred_P : PredicativeSig P) :
  (forall {Γ : ctx P} {A M}, {{ ⟪ pred_P ⟫ Γ ⊢a M ⟸ A }} -> {{ ⊢ Γ }} -> {{ Γ ⊢ A }} -> {{ Γ ⊢ M : A }}) /\
    (forall {Γ : ctx P} {A M}, {{ ⟪ pred_P ⟫ Γ ⊢a M ⟹ A }} -> {{ ⊢ Γ }} -> {{ Γ ⊢ M : A }}).
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
  - simpl.
    assert {{ Γ ⊢ A : Sort@s1 }} by mauto 3.
    assert {{ Γ ⊢ A ≈ C }} by mauto 3 using soundness_ty'.
    assert {{ Γ ⊢ A }} by mauto 2.
    assert {{ ⊢ Γ, A@s1 }} by mauto 2.
    
    assert {{ Γ, A@s1 ⊢ B : Sort@s2 }} by mauto 3.
    assert {{ Γ ⊢ Π r A B : Sort@s3 }} by mauto 2.
   
    gen_presups.
    assert {{ Γ, A@s1 ⊢ M : D }} by mauto 2.
    assert {{ Γ, A@s1 ⊢ B }} by (gen_presups; mauto 3).
    assert {{ Γ, A@s1 ⊢ B ≈ D  }} by (mauto 2 using soundness_ty').
    assert {{ Γ, A@s1 ⊢ M : B }} by mauto 3.
    functional_alg_type_infer_rewrite_clear.

    assert {{ Γ ⊢ λ r A M : Π r A B }} by mauto 3.
    admit.
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
    assert {{ Γ, ℕ@s ⊢ A : Sort@s' }} by mauto 3.
    assert {{ ⊢ Γ, ℕ@s, A@s' }} by mauto 3.
    assert {{ Γ ⊢ N : ℕ }} by mauto 2.
    assert {{ Γ ⊢s Id,,zero : Γ, ℕ@s }} by mauto 3.
    assert {{ Γ ⊢ A[Id,,zero] : Sort@s' }} by mauto 3.
    assert {{ Γ, ℕ@s, A@s' ⊢s Wk∘Wk : Γ }} by (econstructor; mauto 3).
    assert {{ Γ, ℕ@s, A@s' ⊢s Wk∘Wk,,succ #1 : Γ, ℕ@s }} by mauto 4.
    assert {{ Γ, ℕ@s, A@s' ⊢ A[Wk∘Wk,,succ #1] : Sort@s' }} by mauto 4.
    assert {{ Γ ⊢ A[Id,,N] : Sort@s' }} by mauto 3.
    assert {{ Γ ⊢ A[Id,,N] ≈ B }} as <- by (mauto 3 using soundness_ty').
    econstructor; mauto 3.
Qed.


Lemma alg_type_check_sound {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A M},
    {{ ⟪ pred_P ⟫ Γ ⊢a M ⟸ A }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  pose proof (alg_type_sound pred_P); intuition.
Qed.

Lemma alg_type_infer_sound {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A M},
    {{ ⟪ pred_P ⟫ Γ ⊢a M ⟹ A }} -> {{ ⊢ Γ }} -> {{ Γ ⊢ M : A }}.
Proof.
  pose proof @alg_type_sound; intuition.
Qed.


Lemma alg_type_infer_normal {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {A A' M},
    {{ ⊢ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊢a M ⟹ A }} ->
    nbe_ty Γ A A' ->
    A = A'.
Proof with (f_equiv; mautosolve 4).
  intros * ? Hinfer Hnbe. gen A'.
  assert {{ Γ ⊢ M : A }} by mauto 3 using alg_type_infer_sound.
  induction Hinfer; intros;
    try (dir_inversion_clear_by_head nbe_ty;
         dir_inversion_by_head eval_exp; subst;
         dir_inversion_by_head read_typ; subst;
         reflexivity).
  - assert {{ Γ ⊢ A : Sort@s }} by mauto 2.
    epose proof idempotent_nbe_ty pred_P H3 H2 Hnbe.
    exact H4.
    epose proof presup_ctx_lookup_typ HΓ H1.
  intros.
  eapply idempotent_nbe_ty_unsorted; mauto 2.
  
  
  intros * ? Hinfer Hnbe. gen A'.
  assert {{ Γ ⊢ M : A }} by mauto 3 using alg_type_infer_sound.
  induction Hinfer; intros;
    try (dir_inversion_clear_by_head nbe_ty;
         dir_inversion_by_head eval_exp; subst;
         dir_inversion_by_head read_typ; subst;
         reflexivity).
  - assert {{ Γ ⊢ ℕ : Type@0 }} by mauto 3.
    assert {{ Γ ⊢ M : ℕ }} by mauto 3 using alg_type_check_sound.
    assert {{ ⊢ Γ, ℕ }} by mauto 3.
    assert {{ Γ, ℕ ⊢ A : ^n{{{ Type@i }}} }} by mauto 3 using alg_type_infer_sound...
  - assert {{ Γ ⊢ A : ^n{{{ Type@i }}} }} by mauto 3 using alg_type_infer_sound.
    assert {{ Γ ⊢ A ≈ C : Type@i }} by mauto 3 using soundness_ty'.
    assert {{ Γ, A ⊢ M : B }} by mauto 3 using alg_type_infer_sound.
    assert (exists j, {{ Γ, A ⊢ B : Type@j }}) as [j] by (gen_presups; eauto 2).
    assert {{ ⊢ Γ, A ≈ Γ, ^(C : exp) }} by mauto 3.
    dir_inversion_clear_by_head nbe_ty.
    simplify_evals.
    dir_inversion_by_head read_typ; subst.
    functional_initial_env_rewrite_clear.
    assert (initial_env {{{ Γ, ^(C : exp) }}} d{{{ ρ ↦ ⇑! a (length Γ) }}}) by mauto 3.
    assert (nbe_ty Γ A C) by mauto 3.
    assert (nbe_ty Γ C A0) by mauto 3.
    replace A0 with C by mauto 2.
    assert (nbe_ty {{{ Γ, ^(C : exp) }}} B B') by mauto 3.
    assert (nbe_ty {{{ Γ, A }}} B B') by mauto 4 using ctxeq_nbe_ty_eq'...
  - assert {{ Γ ⊢ M : ^n{{{ Π A B }}} }} by mauto 3 using alg_type_infer_sound.
    assert (exists i, {{ Γ ⊢ Π A B : Type@i }}) as [i] by (gen_presups; eauto 2).
    assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, ^(A : exp) ⊢ B : Type@i }}) as [] by mauto 3.
    assert {{ Γ ⊢ N : A }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ ⊢ B[Id,,N] : Type@i }} by mauto 3...
  - assert {{ Γ ⊢ A : Type@i }} by (eapply alg_type_sound in Hinfer1; mauto 3).
    assert {{ Γ , A ⊢ B : Type@j }} by (eapply alg_type_sound in Hinfer2; mauto 3).
    assert (exists j, {{ Γ ⊢ Σ A' C : Type@j }}) as [k] by (gen_presups; eauto 2).
    apply wf_sigma_inversion' in H7; fold nf_to_exp in *. destruct_all.
    dir_inversion_clear_by_head nbe_ty.
    simplify_evals.
    dir_inversion_by_head read_typ; subst.
    assert (nbe_ty Γ A A' ) by mauto 3.
    assert (nbe_ty Γ A' A0 ) by mauto 3.
    replace A0 with A' in * by mauto 3.
    assert {{ Γ ⊢ A ≈ A' : Type@i }} by mauto 3 using soundness_ty'.
    functional_initial_env_rewrite_clear.
    simplify_evals.
    assert (nbe_ty {{{ Γ, A }}} B C) by unshelve mauto 3.
    assert (nbe_ty {{{ Γ,  ^(A' : exp)}}} C B') by mauto 4.
    assert {{ ⊢ Γ, A ≈ Γ, ^(A' : exp) }} by mauto 3.
    assert (nbe_ty {{{ Γ, ^(A : exp) }}} C B') by mauto 3 using ctxeq_nbe_ty_eq'.
    replace B' with C in * by mauto 3...
  - assert {{ Γ ⊢ M : ^n{{{ Σ A B }}} }} by mauto 3 using alg_type_infer_sound.
    gen_presups.
    assert (nbe_ty Γ {{{Σ A B }}} n{{{Σ A B}}}). {
      assert {{ Γ ⊢ ^ n{{{ Σ A B }}} ≈ ^ n{{{ Σ A B }}} : Type@i }} by (eapply exp_eq_refl; mauto 3).
      apply completeness_ty in H as IH. destruct_all.
      eapply IHHinfer in H2; subst; auto.
    }
    dir_inversion_clear_by_head nbe.
    dir_inversion_clear_by_head nbe_ty.
    simplify_evals.
    dir_inversion_by_head read_typ; subst.
    functional_initial_env_rewrite_clear.
    simplify_evals.
    functional_read_rewrite_clear. reflexivity.
  - assert {{ Γ ⊢ M : ^n{{{ Σ A B }}} }} by mauto 3 using alg_type_infer_sound.
    gen_presups.
    apply wf_sigma_inversion' in HA; fold nf_to_exp in *.
    destruct_all.
    assert {{ Γ ⊢ fst M : A }} by mauto 3.
    assert {{ Γ ⊢ B[Id,,fst M] : Type@i }} by mauto 3.
    mauto 3.
  - assert {{ Γ ⊢ A : ^n{{{ Type@i }}} }} by mauto 3 using alg_type_infer_sound.
    assert {{ Γ ⊢ M : A }} by mauto 3 using alg_type_check_sound.
    dir_inversion_clear_by_head nbe.
    dir_inversion_clear_by_head nbe_ty.
    simplify_evals.
    dir_inversion_by_head read_typ; subst.
    functional_initial_env_rewrite_clear.
    functional_read_rewrite_clear.
    assert (nbe_ty Γ A C) by mauto 3.
    assert (nbe_ty Γ C A0) by mauto 3.
    replace A0 with C in * by mauto 3.
    assert (nbe Γ M A N) by mauto 3.
    assert {{ Γ ⊢ A ≈ C : Type@i }} by mauto 2 using soundness_ty'.
    assert (nbe Γ N C M1) by mauto 2.
    replace M1 with N in * by mauto 2.
    reflexivity.
  - assert {{ Γ ⊢ A : ^n{{{ Type@i }}} }} by mauto 3 using alg_type_infer_sound.
    assert {{ Γ ⊢ M1 : A }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ ⊢ M2 : A }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ ⊢ N : Eq A M1 M2 }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, A ⊢ A[Wk] : Type@i }} by mauto 3.
    assert {{ ⊢ Γ, A, A[Wk] }} by mauto 3.
    assert {{ Γ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }} by mauto 3.
    assert {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : ^n{{{ Type@j }}} }} by mauto 3 using alg_type_infer_sound.
    assert {{ Γ ⊢s Id,,M1,,M2,,N : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 2.
    assert {{ Γ ⊢ B[Id,,M1,,M2,,N] : Type@j }} by mauto 2.
    mauto 3.
  - assert (exists i, {{ Γ ⊢ A : Type@i }}) as [i] by mauto 2...
Qed.

#[export]
Hint Resolve alg_type_infer_normal : mcpts.


Lemma subtyp_sort_is_sort_helper {P} : forall {Γ : ctx P} {A B},
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
    assert (s2 = s) by admit. (* (eapply typ_eq_sort_implies_eq_level; mauto 2) *)
    subst.
    exists s1; split; mauto 3.
  - (* This also need the consequences *)
    assert ({{{ Π r A' B' }}} = {{{ Sort@s }}}) by admit.
    inversion H5.
Admitted.

Lemma subtyp_sort_is_sort {P} : forall {Γ : ctx P} {A s},
    {{ Γ ⊢ A ⊆ Sort@s }} ->
    exists s', {{ Γ ⊢ A ≈ Sort@s' }} /\ st_subtyp s' s.
Proof.
  intros.
  gen_presup H.
  eapply subtyp_sort_is_sort_helper; mauto 2.
Qed.

  
Lemma alg_type_check_typ_implies_alg_type_infer_typ {P} (pred_P : PredicativeSig P) : forall {Γ A s},
    {{ ⊢ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊢a A ⟸ Sort@s }} ->
    exists A' s', {{ ⟪ pred_P ⟫ Γ ⊢a A ⟹ A' }} /\ {{ Γ ⊢ A' ≈ Sort@s' }} /\ st_subtyp s' s.
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  assert {{ Γ ⊢ A' ⊆ Sort@s }} by (eapply CorrectConv; mauto 2).
  pose proof (subtyp_sort_is_sort H0) as [s' []].
  repeat eexists; mauto 3.
Qed.

#[export]
Hint Resolve alg_type_check_typ_implies_alg_type_infer_typ : mcpts.

Lemma alg_type_check_pi_implies_alg_type_infer_pi {P} (pred_P : PredicativeSig P) : forall {Γ M A B s1 s2 s3 s} {r : Ru_pi P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ Π r A B : Sort@s }} ->
    {{ ⟪ pred_P ⟫ Γ ⊢a M ⟸ Π r A B }} ->
    exists A' A0 B0, {{ ⟪ pred_P ⟫ Γ ⊢a M ⟹ A' }} /\ {{ Γ ⊢ A' ≈ Π r A0 B0 }} /\ {{ Γ ⊢ A0 ≈ A : Sort@s1 }} /\ (Convert pred_P {{{ Γ, A@s1 }}} B0 B).
Proof.
  intros * ? ? Hcheck.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ⊆ Sort@s }}) as [? []] by mauto 3.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  assert {{ Γ ⊢ A' ⊆ Π r A B }} by (eapply CorrectConv; mauto 3).
  (* This should follow by consequences of normalization *)
  assert (exists A0 B0, {{ Γ ⊢ A' ≈ Π r A0 B0 }} /\ {{ Γ ⊢ A0 ≈ A : Sort@s1 }} /\ {{ Γ, A0@s1 ⊢ B0 ⊆ B }}) as [A0 [B0 [? []]]] by admit.
  repeat eexists; mauto 3.
  assert {{ ⊢ Γ, A0@s1 ≈ Γ, A@s1 }} by mauto 3.
  assert {{ Γ, A@s1 ⊢ B0 ⊆ B }} by mauto 3.
  eapply CorrectConv; mauto 3.
Admitted.


#[export]
Hint Resolve alg_type_check_pi_implies_alg_type_infer_pi : mcpts.

Lemma alg_type_check_subtyp {P} (pred_P : PredicativeSig P) : forall {Γ A A' M},
    {{ ⟪ pred_P ⟫ Γ ⊢a M ⟸ A }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊢a M ⟸ A' }}.
Proof.
  intros * [] **.
  assert {{ Γ0 ⊢ A0 ⊆ B }} by (eapply CorrectConv; mauto 2).
  assert {{ Γ0 ⊢ A0 ⊆ A' }} by mauto 2.
  assert (Convert pred_P Γ0 A0 A') by (eapply CorrectConv; mauto 2).
  mauto 2.
Qed.

#[export]
Hint Resolve alg_type_check_subtyp : mcpts.

Corollary alg_type_check_conv {P} (pred_P : PredicativeSig P) : forall {Γ A A' M},
    {{ ⟪ pred_P ⟫ Γ ⊢a M ⟸ A }} ->
    {{ Γ ⊢ A ≈ A' }} ->
    {{ ⟪ pred_P ⟫ Γ ⊢a M ⟸ A' }}.
Proof.
  mauto 3.
Qed.

#[export]
Hint Resolve alg_type_check_conv : mcpts.

Lemma alg_type_check_complete {P} (pred_P : PredicativeSig P) : forall {Γ A M},
    user_exp P M ->
    {{ Γ ⊢ M : A }} ->
    {{ ⟪ pred_P ⟫ Γ ⊢a M ⟸ A }}.
Proof.
  intros * Hue.
  induction 1; gen_presups; inversion Hue; subst; clear Hue; mauto 4 using alg_type_check_subtyp.
  - econstructor; mauto 3.
    eapply CorrectConv; mauto 2.

  - assert (Convert pred_P Γ {{{ Sort@s3 }}} {{{ Sort@s3 }}}) by (eapply CorrectConv; mauto 3).
    econstructor; mauto 3.
    econstructor; mauto 3.

  - assert {{ ⟪ pred_P ⟫ Γ ⊢a A ⟸ Sort@s1 }} by mauto 2.
    assert {{ ⟪ pred_P ⟫ Γ, A@s1 ⊢a M ⟸ B }} by mauto 2.
    inversion_clear H3.
    assert {{ Γ, A@s1 ⊢ A0 ⊆ B }} by (eapply CorrectConv; mauto 3).
    assert {{ Γ ⊢ Π r A A0 ⊆ Π r A B }} by admit.
    assert (Convert pred_P Γ {{{ Π r A A0 }}} {{{ Π r A B }}}) by (eapply CorrectConv; mauto 3).
    econstructor; mauto 3.
    econstructor; mauto 3.
    admit.


  - assert {{ ⟪ pred_P ⟫ Γ ⊢a M ⟸ Π r A B }} by mauto 2.
    assert {{ ⟪ pred_P ⟫ Γ ⊢a N ⟸ A }} by mauto 2.
    econstructor; mauto 3.
    
    
  - econstructor; mauto 3.
    mauto using alg_subtyping_complete.
  - assert (exists j, {{ Γ, ℕ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    assert {{ Γ ⊢ A[Id,,M] : Type@i }} by mauto 3.
    assert {{ Γ ⊢ A[Id,,M] ≈ A[Id,,M] : Type@i }} as [? [? _]]%completeness_ty by mauto 3.
    econstructor; mauto using alg_subtyping_complete, soundness_ty'.
  - assert (exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    assert {{ ⊢ Γ, A }} by mauto 3.
    assert (exists j, {{ Γ, A ⊢a B ⟹ Type@j }} /\ j <= i) as [j' []] by mauto 3.
    assert (max j j' <= i) by lia.
    econstructor; mauto 3 using alg_subtyping_complete.
  - assert (exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    assert {{ Γ, A ⊢a M ⟸ B }} by mauto 3.
    assert (exists B', {{ Γ, A ⊢a M ⟹ B' }} /\ {{ Γ, A ⊢a B' ⊆ B }}) as [B' []] by (inversion_clear_by_head alg_type_check; firstorder).
    assert (exists W, nbe_ty Γ A W /\ {{ Γ ⊢ A ≈ W : Type@i }}) as [W []] by mauto 3 using soundness_ty.
    assert {{ ⊢ Γ, A }} by mauto 3.
    assert {{ Γ, A ⊢ M : B' }} by mauto 3 using alg_type_infer_sound.
    assert (exists j, {{ Γ, A ⊢ B' : Type@j }}) as [] by (gen_presups; eauto 2).
    econstructor; mauto 3.
    eapply alg_subtyping_complete.
    eapply wf_subtyp_pi'; mauto 2.
    mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
  - assert {{ Γ ⊢a M ⟸ Π A B }} by mauto 2.
    assert {{ Γ ⊢a N ⟸ A }} by mauto 2.
    assert (exists A' B', {{ Γ ⊢a M ⟹ Π A' B' }} /\ {{ Γ ⊢ A' ≈ A : Type@i }} /\ {{ Γ, A ⊢a B' ⊆ B }}) as [A' [B' [? []]]] by mauto 3.
    assert {{ Γ ⊢ M : ^n{{{ Π A' B' }}} }} by mauto 3 using alg_type_infer_sound.
    assert (exists j, {{ Γ ⊢ Π A' B' : Type@j }}) as [j] by (gen_presups; eauto 2).
    assert ({{ Γ ⊢ A' : Type@j }} /\ {{ Γ, ^(A' : exp) ⊢ B' : Type@j }}) as [] by mauto 3.
    assert {{ Γ ⊢ N : A' }} by mauto 3.
    assert {{ Γ ⊢ B'[Id,,N] : Type@j }} by mauto 3.
    assert (exists W, nbe_ty Γ {{{ B'[Id,,N] }}} W /\ {{ Γ ⊢ B'[Id,,N] ≈ W : Type@j }}) as [W []] by (eapply soundness_ty; mauto 3).
    assert {{ Γ, A ⊢ B' : Type@j }} by mauto 4.
    assert {{ Γ, A ⊢ B' ⊆ B }} by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
    assert {{ Γ ⊢ B'[Id,,N] ⊆ B[Id,,N] }} by mauto 3.
    assert {{ Γ ⊢ W ⊆ B[Id,,N] }} by (transitivity {{{ B'[Id,,N] }}}; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  - assert (exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    assert {{ ⊢ Γ, A }} by mauto 3.
    assert (exists j, {{ Γ, A ⊢a B ⟹ Type@j }} /\ j <= i) as [j' []] by mauto 3.
    assert (max j j' <= i) by lia.
    econstructor; mauto 3 using alg_subtyping_complete.
  - assert (exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    assert {{ ⊢ Γ, A }} by mauto 3.
    assert (exists j, {{ Γ, A ⊢a B ⟹ Type@j }} /\ j <= i) as [j' []] by mauto 3.
    assert {{ Γ ⊢ A : Type@j }}.
    {
      eapply alg_type_infer_sound in H3; mauto 3.
    }
    assert {{ Γ, A ⊢ B : Type@j' }}. {
      eapply alg_type_infer_sound in H6; mauto 3.
    }
    assert (exists WA, nbe_ty Γ A WA /\ {{ Γ ⊢ A ≈ WA : Type@j }}) as [WA []] by mauto 3 using soundness_ty.
    assert (exists WB, nbe_ty {{{ Γ , A }}} B WB /\ {{ Γ , A ⊢ B ≈ WB : Type@j' }}) as [WB []] by mauto 3 using soundness_ty.
    assert {{ Γ ⊢ WA : Type@j }} by (gen_presups; mauto 3).
    assert {{ Γ , ^(WA :exp) ⊢ WB : Type@j' }}.
    {
      gen_presups.
      eapply @ctxeq_exp with (Γ:={{{Γ,A}}}); mauto 3.
    }
    assert {{ Γ ⊢ ^ n{{{ Σ WA WB }}} ⊆ Σ A B }}.
    { eapply wf_subtyp_sigma with (i:=max j j'); mauto 3
      using lift_exp_eq_max_left, lift_exp_eq_max_right, lift_exp_max_left, lift_exp_max_right.
    }
    assert {{ Γ ⊢a ⟨ M : A; N : B ⟩ ⟹ Σ WA WB }} by (econstructor; mauto 3).
    mauto 3 using alg_subtyping_complete.
  - assert {{ Γ ⊢a M ⟸ Σ A B }} by mauto 3.
    assert (exists A' B', {{ Γ ⊢a M ⟹ Σ A' B' }} /\ {{ Γ ⊢ A' ≈ A : Type@i }} /\ {{ Γ, A ⊢a B' ⊆ B }}) as [A' [B' [? []]]] by mauto 3.
    assert {{ Γ ⊢a A' ⊆ A }} by mauto 3 using alg_subtyping_complete.
    mauto 3.
  - assert {{ Γ ⊢a M ⟸ Σ A B }} by mauto 3.
    assert (exists A' B', {{ Γ ⊢a M ⟹ Σ A' B' }} /\ {{ Γ ⊢ A' ≈ A : Type@i }} /\ {{ Γ, A ⊢a B' ⊆ B }}) as [A' [B' [? []]]] by mauto 3.
    assert {{ Γ ⊢ M : Σ A' B' }} by (eapply alg_type_sound in H4; mauto 3).
    assert (exists j, {{ Γ ⊢ Σ A' B' : Type@j }}) as [j] by (gen_presups; eauto 2).
    apply wf_sigma_inversion' in HA.
    apply wf_sigma_inversion' in H8. destruct_all.
    assert {{ Γ, ^(A:exp) ⊢ B' : Type@j }} by mauto 4.
    assert {{ Γ, A ⊢ B' ⊆ B }}. {
      eapply alg_subtyping_sound with (i:=max i0 j); mauto 3 using lift_exp_max_left, lift_exp_max_right.
    }
    assert (exists W, nbe_ty Γ {{{ B'[Id,,fst M] }}} W /\ {{ Γ ⊢ B'[Id,,fst M] ≈ W : Type@j }}) as [W []].  {
      eapply soundness_ty; mauto 3.
      eapply wf_conv'; [eapply wf_exp_sub |]; mauto 3.
      econstructor; mauto 3.
    }
    assert {{ Γ ⊢ B'[Id,,fst M] ⊆ B[Id,,fst M] }} by (eapply wf_subtyp_subst; mauto 3).
    assert {{ Γ ⊢ W ⊆ B[Id,,fst M] }} by (transitivity {{{ B'[Id,,fst M] }}}; mauto 3).
    mauto using alg_subtyping_complete.
  - assert (exists W, nbe_ty Γ A W /\ {{ Γ ⊢ A ≈ W : Type@i }}) as [W []] by (eapply soundness_ty; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  - assert (exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    econstructor; [econstructor |]; mauto 3 using alg_subtyping_complete.
  - assert (exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i) as [j []] by mauto 3.
    assert {{ Γ ⊢a M ⟸ A }} by eauto 2.
    assert (exists C, nbe_ty Γ A C /\ {{ Γ ⊢ A ≈ C : Type@i }}) as [C []] by mauto 3 using soundness_ty.
    assert (exists W, nbe Γ M A W /\ {{ Γ ⊢ M ≈ W : A }}) as [W []] by mauto 3 using soundness.
    econstructor; mauto 3.
    assert {{ Γ ⊢ ^n{{{ Eq C W W }}} ≈ Eq A M M : Type@i }} by mauto 3.
    mauto 3 using alg_subtyping_complete.
  - assert (exists k, {{ Γ ⊢a A ⟹ Type@k }} /\ k <= i) as [k []] by mauto 3.
    assert (exists l, {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢a B ⟹ Type@l }} /\ l <= j) as [l []] by mauto 3.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, A ⊢ A[Wk] : Type@i }} by mauto 3.
    assert {{ ⊢ Γ, A, A[Wk] }} by mauto 3.
    assert {{ Γ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }} by mauto 3.
    assert {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : ^n{{{ Type@j }}} }} by mauto 3 using alg_type_infer_sound.
    assert {{ Γ ⊢s Id,,M1,,M2,,N : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 2.
    assert {{ Γ ⊢ B[Id,,M1,,M2,,N] : Type@j }} by mauto 2.
    assert (exists C, nbe_ty Γ {{{ B[Id,,M1,,M2,,N] }}} C /\ {{ Γ ⊢ B[Id,,M1,,M2,,N] ≈ C : Type@j }}) as [C []] by mauto 3 using soundness_ty.
    econstructor; [econstructor |]; mauto 4 using alg_subtyping_complete.
Qed.

#[export]
Hint Resolve alg_type_check_complete : mcpts.

Corollary alg_type_infer_complete : forall {Γ A M},
    user_exp M ->
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

Corollary alg_type_infer_typ_complete : forall {Γ i A},
    user_exp A ->
    {{ Γ ⊢ A : Type@i }} ->
    exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i.
Proof.
  mauto 4 using alg_type_check_complete.
Qed.

#[export]
Hint Resolve alg_type_infer_typ_complete : mcpts.

Corollary alg_type_infer_pi_complete : forall {Γ i A},
    user_exp A ->
    {{ Γ ⊢ A : Type@i }} ->
    exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i.
Proof.
  mauto 4 using alg_type_check_complete.
Qed.

#[export]
Hint Resolve alg_type_infer_pi_complete : mcpts.
