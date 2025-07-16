From Coq Require Import Setoid.
From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export CoreInversions Presup.
Import Syntax_Notations.


Add Parametric Morphism {P : PtsSig} (s : St P) Γ : (wf_exp Γ)
    with signature eq_exp Γ {{{ Sort@s }}} ==> eq ==> iff as wf_exp_morphism_iff3.
Proof with mautosolve.
  split; intros; gen_presups;
    eapply wf_exp_conv; mauto 2.
  econstructor; mauto 2.
Qed.

Add Parametric Morphism {P : PtsSig} (s : St P) Γ : (eq_exp Γ)
    with signature eq_exp Γ {{{ Sort@s }}} ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff3.
Proof with mautosolve.
  split; intros; gen_presups;
    eapply eq_exp_conv; mauto 2.
  econstructor; mauto 2.
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
  intros;
  gen_presups;
  eapply wf_exp_conv; mauto 2.
Qed.

#[export]
Hint Resolve wf_conv' : mcpts.
#[export]
Remove Hints wf_conv : mcpts.

Corollary wf_exp_eq_conv' {P : PtsSig} : forall (Γ : Ctx P) M M' A A' s,
   {{ Γ ⊢ M ≈ M' : A }} ->
   {{ Γ ⊢ A ≈ A' : Sort@s }} ->
   {{ Γ ⊢ M ≈ M' : A' }}.
Proof.
  intros.
  eapply eq_exp_conv; mauto 2.
Qed.

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
  gen_presups.
  destruct_conjs.
  econstructor; mauto 2.
Qed.

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
    {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ λ r A M : Π r A B }}.
Proof.
  intros.
  gen_presups.
  econstructor; mauto 2.
Qed.

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
  inversion_clear HAwf0.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ≈ Sort@s }}) as [].
  {
    eapply wf_pi_inversion; mauto 2.
  }
  destruct_conjs.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_app' : mcpts.
#[export]
Remove Hints wf_exp_app : mcpts.

Lemma wf_exp_eq_typ_sub' {P : PtsSig} : forall (Γ : Ctx P) σ Δ s1 s2,
    {{ Γ ⊢s σ : Δ }} ->
    Ax P s1 s2 ->
    {{ Γ ⊢ [σ]Sort@s1 ≈ Sort@s1 : Sort@s2 }}.
Proof.
  intros.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_typ_sub' : mcpts.

#[export]
Hint Rewrite -> @wf_exp_eq_typ_sub' using solve [lia | mauto 3] : mcpts.


(* These results don't really make sense in our setting *)

(* Corollary wf_exp_eq_pi_sub_max : forall {Γ σ Δ A i B j}, *)
(*     {{ Γ ⊢s σ : Δ }} -> *)
(*     {{ Δ ⊢ A : Type@i }} -> *)
(*     {{ Δ, A ⊢ B : Type@j }} -> *)
(*     {{ Γ ⊢ (Π A B)[σ] ≈ Π (A[σ]) (B[q σ]) : Type@(max i j) }}. *)
(* Proof. *)
(*   intros. *)
(*   assert {{ Δ ⊢ A : Type@(max i j) }} by mauto using lift_exp_max_left. *)
(*   assert {{ Δ, A ⊢ B : Type@(max i j) }} by mauto using lift_exp_max_right. *)
(*   mauto. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve wf_exp_eq_pi_sub_max : mcpts. *)

(* Corollary wf_exp_eq_pi_cong' : forall {Γ A A' B B' i}, *)
(*     {{ Γ ⊢ A ≈ A' : Type@i }} -> *)
(*     {{ Γ, A ⊢ B ≈ B' : Type@i }} -> *)
(*     {{ Γ ⊢ Π A B ≈ Π A' B' : Type@i }}. *)
(* Proof. *)
(*   impl_opt_constructor. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve wf_exp_eq_pi_cong' : mcpts. *)
(* #[export] *)
(* Remove Hints wf_exp_eq_pi_cong : mcpts. *)

(* Corollary wf_exp_eq_pi_cong_max : forall {Γ A A' i B B' j}, *)
(*     {{ Γ ⊢ A ≈ A' : Type@i }} -> *)
(*     {{ Γ, A ⊢ B ≈ B' : Type@j }} -> *)
(*     {{ Γ ⊢ Π A B ≈ Π A' B' : Type@(max i j) }}. *)
(* Proof. *)
(*   intros. *)
(*   assert {{ Γ ⊢ A ≈ A' : Type@(max i j) }} by eauto using lift_exp_eq_max_left. *)
(*   assert {{ Γ, A ⊢ B ≈ B' : Type@(max i j) }} by eauto using lift_exp_eq_max_right. *)
(*   mauto. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve wf_exp_eq_pi_cong_max : mcpts. *)

Corollary wf_exp_eq_fn_cong' {P : PtsSig} : forall {Γ : Ctx P} {A A' s1 s2 s3 B M M'} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
    {{ Γ, A::Sort@s1 ⊢ M ≈ M' : B }} ->
    {{ Γ, A::Sort@s1 ⊢ B :Sort@s2 }} ->
    {{ Γ ⊢ λ r A M ≈ λ r A' M' : Π r A B }}.
Proof.
  intros.
  econstructor; mauto 2.
  assert ({{ ⊢ Γ }} /\ {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ ⊢ A' : Sort@s1 }} /\ {{ Γ ⊢ Sort@s1 }}) by (eapply presup_exp_eq; mauto 2).
  destruct_conjs.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_cong' : mcpts.
#[export]
Remove Hints eq_exp_cong_lam : mcpts.

Corollary wf_exp_eq_fn_sub' {P : PtsSig} : forall {Γ : Ctx P} {σ Δ A M B s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, A::Sort@s1 ⊢ M : B }} ->
    {{ Δ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ [σ](λ r A M) ≈ λ r [σ]A [(Wk∘σ),,#0]M : [σ](Π r A B) }}.
Proof.
  intros.
  gen_presups.
  econstructor; mauto 2.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_sub' : mcpts.
#[export]
Remove Hints eq_exp_prop_lam : mcpts.

Corollary wf_exp_eq_app_cong' {P : PtsSig} : forall {Γ : Ctx P} {A B M M' N N' s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ M ≈ M' : Π r A B }} ->
    {{ Γ ⊢ N ≈ N' : A }} ->
    {{ Γ ⊢ M N ≈ M' N' : [Id,,N]B }}.
Proof.
  intros.
  econstructor; mauto 2.
  assert {{ Γ ⊢ Π r A B }} by (eapply presup_exp_eq; mauto 2).
  eapply wf_typ_pi_inversion; mauto 2.
Qed.  

#[export]
Hint Resolve wf_exp_eq_app_cong' : mcpts.
#[export]
Remove Hints eq_exp_cong_app : mcpts.

Corollary wf_exp_eq_app_sub' {P : PtsSig} : forall {Γ : Ctx P} {σ Δ A B M N s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : Π r A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ [σ](M N) ≈ [σ]M [σ]N : [σ,,[σ]N]B }}.
Proof.
  intros.
  gen_presups.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_sub' : mcpts.
#[export]
Remove Hints eq_exp_prop_app : mcpts.

Corollary wf_exp_eq_pi_beta' {P : PtsSig} : forall {Γ : Ctx P} {A B M N s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ, A::Sort@s1 ⊢ M : B }} ->
    {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ (λ r A M) N ≈ [Id,,N]M : [Id,,N]B }}.
Proof.
  intros.
  gen_presups.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_beta' : mcpts.
#[export]
Remove Hints eq_exp_beta : mcpts.

Corollary wf_exp_eq_pi_eta' {P : PtsSig} : forall {Γ : Ctx P} {A B M s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ M : Π r A B }} ->
    {{ Γ ⊢ M ≈ λ r A ([Wk]M #0) : Π r A B }}.
Proof.
  intros.
  gen_presups.
  econstructor; mauto 2.
Qed.
