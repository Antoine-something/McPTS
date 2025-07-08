From Coq Require Import Setoid.
From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import System CtxEq CoreInversions Presup.


Add Parametric Morphism {P : PtsSig} (s : St P) Γ : (wf_exp Γ)
    with signature eq_exp Γ {{{ Sort@s }}} ==> eq ==> iff as wf_exp_morphism_iff3.
Proof with mautosolve.
  split; intros; gen_presups;
    eapply wf_exp_conv; mauto 2.
  econstructor; mauto 2.
  symmetry; econstructor; mauto 2.
Qed.

Add Parametric Morphism {P : PtsSig} (s : St P) Γ : (eq_exp Γ)
    with signature eq_exp Γ {{{ Sort@s }}} ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff3.
Proof with mautosolve.
  split; intros; gen_presups;
    eapply eq_exp_conv; mauto 2.
  econstructor; mauto 2.
  symmetry; econstructor; mauto 2.
Qed.

#[local]
Ltac impl_opt_constructor :=
  intros;
  gen_presups;
  mautosolve 4.

Corollary wf_conv' {P : PtsSig} : forall (Γ : Ctx P) M A s A',
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
  (* impl_opt_constructor. *)
Admitted.

#[export]
Hint Resolve wf_conv' : mcpts.
#[export]
Remove Hints wf_conv : mcpts.

Corollary wf_exp_eq_conv' {P : PtsSig} : forall (Γ : Ctx P) M M' A A' s,
   {{ Γ ⊢ M ≈ M' : A }} ->
   {{ Γ ⊢ A ≈ A' : Sort@s }} ->
   {{ Γ ⊢ M ≈ M' : A' }}.
Proof.
  (* impl_opt_constructor. *)
Admitted.

#[export]
Hint Resolve wf_exp_eq_conv' : mcpts.
#[export]
Remove Hints wf_exp_eq_conv : mcpts.

Corollary wf_ctx_eq_extend' {P : PtsSig} : forall {Γ : Ctx P} {Δ A A' s},
    {{ ⊢ Γ ≈ Δ }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }} ->
    {{ ⊢ Γ, A::Sort@s ≈ Δ, A'::Sort@s }}.
Proof.
  intros.
  assert {{ Δ ⊢ A ≈ A' : Sort@s }} by (eapply ctxeq_exp_eq; mauto).
  gen_presups.
  (* mautosolve 4. *)
Admitted.

#[export]
Hint Resolve wf_ctx_eq_extend' : mcpts.
#[export]
Remove Hints eq_ctx_cons : mcpts.


Corollary wf_pi_max {P : PtsSig} : forall {Γ : Ctx P} {A B s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ Π r A B : Sort@s3 }}.
Proof.
  intros.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_pi_max : mcpts.

Corollary wf_fn' {P : PtsSig} : forall {Γ : Ctx P} {A M B s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ, A::Sort@s1 ⊢ M : B }} ->
    {{ Γ ⊢ λ r A M : Π r A B }}.
Proof.
  (* impl_opt_constructor. *)
Admitted.

#[export]
Hint Resolve wf_fn' : mcpts.
#[export]
Remove Hints wf_exp_lam : mcpts.

Corollary wf_app' {P : PtsSig} : forall {Γ : Ctx P} {M N A B s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ M : Π r A B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ M N : [Id,,N]B }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }}) as [].
  {
    split.
    eauto using wf_pi_inversion'.
  }
  
  exvar nat ltac:(fun i => assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }}) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_app' : mcpts.
#[export]
Remove Hints wf_app : mcpts.

Lemma wf_exp_eq_typ_sub' : forall Γ σ Δ i j,
    {{ Γ ⊢s σ : Δ }} ->
    i < j ->
    {{ Γ ⊢ Type@i[σ] ≈ Type@i : Type@j }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_exp_eq_typ_sub' : mcpts.

#[export]
Hint Rewrite -> wf_exp_eq_typ_sub' using solve [lia | mauto 3] : mcpts.


Corollary wf_exp_eq_pi_sub_max : forall {Γ σ Δ A i B j},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ, A ⊢ B : Type@j }} ->
    {{ Γ ⊢ (Π A B)[σ] ≈ Π (A[σ]) (B[q σ]) : Type@(max i j) }}.
Proof.
  intros.
  assert {{ Δ ⊢ A : Type@(max i j) }} by mauto using lift_exp_max_left.
  assert {{ Δ, A ⊢ B : Type@(max i j) }} by mauto using lift_exp_max_right.
  mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_sub_max : mcpts.

Corollary wf_exp_eq_pi_cong' : forall {Γ A A' B B' i},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ, A ⊢ B ≈ B' : Type@i }} ->
    {{ Γ ⊢ Π A B ≈ Π A' B' : Type@i }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong' : mcpts.
#[export]
Remove Hints wf_exp_eq_pi_cong : mcpts.

Corollary wf_exp_eq_pi_cong_max : forall {Γ A A' i B B' j},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ, A ⊢ B ≈ B' : Type@j }} ->
    {{ Γ ⊢ Π A B ≈ Π A' B' : Type@(max i j) }}.
Proof.
  intros.
  assert {{ Γ ⊢ A ≈ A' : Type@(max i j) }} by eauto using lift_exp_eq_max_left.
  assert {{ Γ, A ⊢ B ≈ B' : Type@(max i j) }} by eauto using lift_exp_eq_max_right.
  mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong_max : mcpts.

Corollary wf_exp_eq_fn_cong' : forall {Γ A A' i B M M'},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ, A ⊢ M ≈ M' : B }} ->
    {{ Γ ⊢ λ A M ≈ λ A' M' : Π A B }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_cong' : mcpts.
#[export]
Remove Hints wf_exp_eq_fn_cong : mcpts.

Corollary wf_exp_eq_fn_sub' : forall {Γ σ Δ A M B},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, A ⊢ M : B }} ->
    {{ Γ ⊢ (λ A M)[σ] ≈ λ A[σ] M[q σ] : (Π A B)[σ] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_sub' : mcpts.
#[export]
Remove Hints wf_exp_eq_fn_sub : mcpts.

Corollary wf_exp_eq_app_cong' : forall {Γ A B M M' N N'},
    {{ Γ ⊢ M ≈ M' : Π A B }} ->
    {{ Γ ⊢ N ≈ N' : A }} ->
    {{ Γ ⊢ M N ≈ M' N' : B[Id,,N] }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_cong' : mcpts.
#[export]
Remove Hints wf_exp_eq_app_cong : mcpts.

Corollary wf_exp_eq_app_sub' : forall {Γ σ Δ A B M N},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : Π A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert ({{ Δ ⊢ A : Type@i }} /\ {{ Δ, A ⊢ B : Type@i }}) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_sub' : mcpts.
#[export]
Remove Hints wf_exp_eq_app_sub : mcpts.

Corollary wf_exp_eq_pi_beta' : forall {Γ A B M N},
    {{ Γ, A ⊢ M : B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ (λ A M) N ≈ M[Id,,N] : B[Id,,N] }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert {{ Γ ⊢ A : Type@i }} by (eapply lift_exp_max_left; mauto 3)).
  exvar nat ltac:(fun i => assert {{ Γ, A ⊢ B : Type@i }} by (eapply lift_exp_max_right; mauto 3)).
  mautosolve 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_beta' : mcpts.
#[export]
Remove Hints wf_exp_eq_pi_beta : mcpts.

Corollary wf_exp_eq_pi_eta' : forall {Γ A B M},
    {{ Γ ⊢ M : Π A B }} ->
    {{ Γ ⊢ M ≈ λ A (M[Wk] #0) : Π A B }}.
Proof.
  intros.
  gen_presups.
  exvar nat ltac:(fun i => assert ({{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}) as [] by eauto using wf_pi_inversion').
  mautosolve 3.
Qed.
