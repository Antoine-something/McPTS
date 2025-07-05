From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export CtxEq.
From McPTS.Core.Syntactic.System Require Export Definitions Lemmas Tactics.


Lemma presup_exp_eq_fn_cong_right {P : PtsSig} : forall {Γ : Ctx P} {s1 A A' s2 B M' s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ Γ ⊢ A' : Sort@s1 }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
    {{ ⊢ Γ, A :: Sort@s1 }} ->
    {{ Γ, A :: Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ, A :: Sort@s1  ⊢ M' : B }} ->
    {{ Γ ⊢ λ r A' M' : Π r A B }}.
Proof.
  intros.
  assert {{ Γ ⊢ Π r A B ≈ Π r A' B : Sort@s3 }}.
  {
    econstructor; mauto 3.
    eapply eq_exp_refl; mauto.
  }
  enough {{ Γ ⊢ λ r A' M' : Π r A' B }}.
  {
    eapply wf_exp_conv; mauto 2.
    eapply eq_typ_sym.
    econstructor; mauto 2.
  }
  econstructor; mauto 2.
  econstructor; mauto 2.
  eapply ctxeq_exp; mauto 2.
  econstructor; mauto 2.
  eapply ctxeq_exp; mauto 2.
  econstructor; mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_fn_cong_right : mcpts.

Lemma presup_exp_eq_fn_sub_right {P : PtsSig} : forall {Γ : Ctx P} {σ Δ s1 A s2 B M s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Δ, A :: Sort@s1 }} ->
    {{ Δ, A :: Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Δ, A :: Sort@s1 ⊢ M : B }} ->
    {{ Γ ⊢ λ r [σ]A [(Wk∘σ),,#0]M : [σ](Π r A B) }}.
Proof.
  intros.
  assert {{ Γ ⊢ [σ]A : Sort@s1 }} by mauto 2.
  assert {{ Γ, [σ]A::Sort@s1 ⊢ [(Wk∘σ),,#0]B : Sort@s2 }} by mauto 3.
  assert {{ Γ ⊢ Π r [σ]A [(Wk∘σ),,#0]B : Sort@s3 }} by (econstructor; mauto 2).
  assert {{ Γ ⊢ Π r [σ]A [(Wk∘σ),,#0]B ≈ Π r [σ]A [(Wk∘σ),,#0]B : Sort@s3 }} by (econstructor; mauto 2).
  assert {{ Γ, [σ]A::Sort@s1 ⊢ [(Wk∘σ),,#0]M : [(Wk∘σ),,#0]B }} by (econstructor; mauto 3).
  assert {{ Γ ⊢ λ r [σ]A [(Wk∘σ),,#0]M : Π r [σ]A [(Wk∘σ),,#0]B }} by (econstructor; mauto 3).
  eapply wf_conv; mauto 3.
  eapply wf_exp_conv; mauto 2.
  eapply wf_exp_clo; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2.
  eapply eq_exp_sym.
  eapply eq_exp_conv; mauto 2; econstructor; mauto 2.
  econstructor; mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_fn_sub_right : mcpts.

Lemma presup_exp_eq_app_cong_right {P : PtsSig} : forall {Γ : Ctx P} {s1 s2 s3 A B M' N N'} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Γ, A::Sort@s1 }} ->   (* this is redundant *)
    {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ M' : Π r A B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ N' : A }} ->
    {{ Γ ⊢ N ≈ N' : A }} ->
    {{ Γ ⊢ M' N' : [Id,,N]B }}.
Proof.
  intros.
  assert {{ Γ ⊢s Id ≈ Id : Γ }} by (eapply eq_sub_refl; econstructor; mauto 2).
  assert {{ Γ ⊢ A ≈ [Id]A : Sort@s1 }} by (eapply eq_exp_sym; econstructor; mauto 2).
  assert {{ Γ ⊢ N ≈ N' : [Id]A }} by mauto 2.
  assert {{ Γ ⊢s Id,,N ≈ Id,,N' : Γ, A::Sort@s1 }} by mauto 2.
  assert {{ Γ ⊢ [Id,,N]B ≈ [Id,,N']B : Sort@s2 }} by mauto 3.
  eapply wf_conv; mauto 3.
  econstructor; mauto 2.
  econstructor; mauto 2.
  eapply eq_exp_conv; mauto 2.
  eapply eq_exp_cong_clo; mauto 2.
  econstructor; mauto 2.
  eapply eq_exp_sym; mauto.
  eapply eq_exp_refl; mauto 2.
  econstructor; mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_cong_right : mcpts.

Lemma presup_exp_eq_app_sub_left : forall {Γ σ Δ i A B M N},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ ⊢ Δ, A }} ->
    {{ Δ, A ⊢ B : Type@i }} ->
    {{ Δ ⊢ M : Π A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ (M N)[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  assert {{ Γ, A[σ] ⊢s q σ : Δ, A }} by mauto 2.
  assert {{ Γ ⊢ M[σ] : (Π A B)[σ] }} by mauto 3.
  assert {{ Γ ⊢ Π A[σ] B[q σ] : Type@i }} by mauto 4.
  assert {{ Γ ⊢ M[σ] : Π A[σ] B[q σ] }} by mauto 3.
  assert {{ Δ ⊢ N : A[Id] }} by mauto 2.
  assert {{ Γ ⊢s (Id,,N)∘σ ≈ Id∘σ,,N[σ] : Δ, A }} by mauto 3.
  assert {{ Γ ⊢s (Id,,N)∘σ ≈ σ,,N[σ] : Δ, A }} by mauto 3.
  assert {{ Δ ⊢s Id,,N : Δ, A }} by mauto 3.
  assert {{ Γ ⊢s (Id,,N)∘σ : Δ, A }} by mauto 3.
  assert {{ Γ ⊢ B[(Id,,N)∘σ] ≈ B[σ,,N[σ]] : Type@i }} by mauto 2.
  assert {{ Γ ⊢s σ,,N[σ] : Δ, A }} by mauto 3.
  assert {{ Γ ⊢ B[σ,,N[σ]] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ B[Id,,N][σ] ≈ B[σ,,N[σ]] : Type@i }} by mauto 3.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_sub_left : mcpts.

Lemma presup_exp_eq_app_sub_right : forall {Γ σ Δ i A B M N},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ ⊢ Δ, A }} ->
    {{ Δ, A ⊢ B : Type@i }} ->
    {{ Δ ⊢ M : Π A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  assert {{ Γ ⊢ A[σ] : Type@i }} by mauto 2.
  assert {{ Γ, A[σ] ⊢s q σ : Δ, A }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ B[q σ] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ M[σ] : Π A[σ] B[q σ] }} by (eapply wf_conv; mauto 2).
  assert {{ Γ ⊢ N[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢s q σ∘(Id,,N[σ]) ≈ σ,,N[σ] : Δ, A }} by mauto 2.
  assert {{ Γ ⊢s Id,,N[σ] : Γ, A[σ] }} by mauto 2.
  assert {{ Γ ⊢s q σ∘(Id,,N[σ]) : Δ, A }} by mauto 2.
  assert {{ Γ ⊢ B[q σ∘(Id,,N[σ])] ≈ B[σ,,N[σ]] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ B[q σ][Id,,N[σ]] : Type@i }} by mauto 2.
  assert {{ Γ ⊢ B[q σ][Id,,N[σ]] ≈ B[σ,,N[σ]] : Type@i }} by mauto 3.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_sub_right : mcpts.

Lemma presup_exp_eq_pi_eta_right : forall {Γ i A B M},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢ B : Type@i }} ->
    {{ Γ ⊢ M : Π A B }} ->
    {{ Γ ⊢ λ A (M[Wk] #0) : Π A B }}.
Proof.
  intros.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, A, A[Wk] ⊢s q Wk : Γ, A }} by mauto 2.
  assert {{ Γ, A ⊢ A[Wk] : Type@i }} by mauto 2.
  assert {{ Γ, A, A[Wk] ⊢ B[q Wk] : Type@i }} by mauto 2.
  assert {{ Γ, A ⊢ M[Wk] : Π A[Wk] B[q Wk] }} by (eapply wf_conv; mauto 2).
  assert {{ Γ, A ⊢ #0 : A[Wk] }} by mauto 2.
  assert {{ Γ, A ⊢s q Wk∘(Id,,#0) ≈ Id : Γ, A }} by (etransitivity; mauto 2).
  assert {{ Γ, A ⊢s Id,,#0 : Γ, A, A[Wk] }} by mauto 2.
  assert {{ Γ, A ⊢ B[q Wk][Id,,#0] ≈ B[Id] : Type@i }} by (transitivity {{{ B[q Wk∘(Id,,#0)] }}}; mauto 3).
  econstructor; eauto.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_pi_eta_right : mcpts.

Lemma presup_exp_eq_prop_eq_var0 : forall {Γ i A},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ, A, A[Wk] ⊢ #0 : A[Wk∘Wk] }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ ⊢ Γ, A, A[Wk] }} by mauto 3.
  mauto 3.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_var0 : mcpts.

Lemma presup_exp_eq_prop_eq_var1 : forall {Γ i A},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ, A, A[Wk] ⊢ #1 : A[Wk∘Wk] }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ ⊢ Γ, A, A[Wk] }} by mauto 3.
  eapply var_compose_subs; mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_var1 : mcpts.

Lemma presup_exp_eq_prop_eq_wf : forall {Γ i A},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ ⊢ Γ, A, A[Wk] }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊢s Wk∘Wk : Γ }} by mauto 3.
  assert {{ Γ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }} by mauto 3.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_wf : mcpts.

Lemma presup_exp_eq_prop_eq_sub_helper2 : forall {Γ σ Δ i A M1 M2},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ M1 : A }} ->
    {{ Δ ⊢ M2 : A }} ->
    {{ Γ ⊢s σ,,M1[σ],,M2[σ] : Δ, A, A[Wk] }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A }} by mauto 3.
  assert {{ Δ, A ⊢s Wk : Δ }} by mauto 2.
  assert {{ Γ ⊢s σ,,M1[σ] : Δ, A }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] ≈ A[σ] : Type@i }} by mauto 3.
  assert {{ Γ ⊢ M2[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] : Type@i }} by mauto 3.
  assert {{ Γ ⊢ M2[σ] : A[Wk][σ,,M1[σ]] }} by mauto 3.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_sub_helper2 : mcpts.



Lemma presup_exp_eq_var_0_sub_left : forall {Γ σ Δ i A M},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ #0[σ,,M] : A[σ] }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A }} by mauto 2.
  assert {{ Δ, A ⊢ #0 : A[Wk] }} by mauto 2.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_var_0_sub_left : mcpts.

Lemma presup_exp_eq_var_S_sub_left : forall {Γ σ Δ i A M B x},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ #x : B ∈ Δ }} ->
    {{ Γ ⊢ #(S x)[σ,,M] : B[σ] }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A }} by mauto 2.
  assert (exists j, {{ Δ ⊢ B : Type@j }}) as [j] by mauto 2.
  assert {{ Δ, A ⊢ #(S x) : B[Wk] }} by mauto 3.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_var_S_sub_left : mcpts.

Lemma presup_exp_eq_sub_cong_right : forall {Γ σ σ' Δ i A M M'},
    {{ ⊢ Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Δ ⊢ M' : A }} ->
    {{ Δ ⊢ M ≈ M' : A }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ' : Δ }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢ M'[σ'] : A[σ] }}.
Proof.
  intros.
  eapply wf_conv; mauto 2.
  eapply exp_eq_sub_cong_typ2'; mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_sub_cong_right : mcpts.

Lemma presup_exp_eq_sub_compose_right : forall {Γ τ Γ' σ Γ'' i A M},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ' }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ ⊢ Γ'' }} ->
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ'' ⊢ A : Type@i }} ->
    {{ Γ'' ⊢ M : A }} ->
    {{ Γ ⊢ M[σ][τ] : A[σ∘τ] }}.
Proof.
  intros.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_sub_compose_right : mcpts.

#[local]
Ltac gen_presup_IH presup_exp_eq presup_sub_eq presup_subtyp H :=
  match type of H with
  | {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} =>
      let HΓ := fresh "HΓ" in
      let i := fresh "i" in
      let HM := fresh "HM" in
      let HN := fresh "HN" in
      let HAi := fresh "HAi" in
      pose proof presup_exp_eq _ _ _ _ H as [HΓ [HM [HN [i HAi]]]]
  | {{ ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Δ }} =>
      let HΓ := fresh "HΓ" in
      let Hσ := fresh "Hσ" in
      let Hτ := fresh "Hτ" in
      let HΔ := fresh "HΔ" in
      pose proof presup_sub_eq _ _ _ _ H as [HΓ [Hσ [Hτ HΔ]]]
  | {{ ^?Γ ⊢ ^?M ⊆ ^?N }} =>
      let HΓ := fresh "HΓ" in
      let i := fresh "i" in
      let HM := fresh "HM" in
      let HN := fresh "HN" in
      pose proof presup_subtyp _ _ _ H as [HΓ [i [HM HN]]]
  end.

Lemma presup_exp_eq : forall {Γ M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ M : A }} /\ {{ Γ ⊢ M' : A }} /\ exists i, {{ Γ ⊢ A : Type@i }}
with presup_sub_eq : forall {Γ Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢s σ : Δ }} /\ {{ Γ ⊢s σ' : Δ }} /\ {{ ⊢ Δ }}
with presup_subtyp : forall {Γ M M'}, {{ Γ ⊢ M ⊆ M' }} -> {{ ⊢ Γ }} /\ exists i, {{ Γ ⊢ M : Type@i }} /\ {{ Γ ⊢ M' : Type@i }}.
Proof with mautosolve 4.
  1: set (WkWksucc := {{{ Wk∘Wk ,, succ #1 }}}).
  all: inversion_clear 1;
    (on_all_hyp: gen_presup_IH presup_exp_eq presup_sub_eq presup_subtyp);
    gen_core_presups;
    clear presup_exp_eq presup_sub_eq presup_subtyp;
    repeat split; try mautosolve 3;
    try (eexists; unshelve solve [mauto 4 using lift_exp_max_left, lift_exp_max_right]; constructor).

  all: try (econstructor; mautosolve 4).

  (** presup_exp_eq cases *)
  - eexists; eapply exp_sub_typ; mauto 4 using lift_exp_max_left, lift_exp_max_right.

  (** presup_sub_eq cases *)

  - econstructor; mauto 3.
    eapply wf_conv...

  - enough {{ Γ ⊢ #0[σ] : A[Wk∘σ] }} by mauto 4.
    eapply wf_conv...

  (** presup_subtyp cases *)
  - exists (max (S i) (S j)); split; mauto 3 using lift_exp_max_left, lift_exp_max_right.
Qed.

Ltac gen_presup H := gen_presup_IH @presup_exp_eq @presup_sub_eq @presup_subtyp H + gen_core_presup H.

Ltac gen_presups := (on_all_hyp: fun H => gen_presup H); invert_wf_ctx; (on_all_hyp: fun H => gen_lookup_presup H); clear_dups.
