From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export CtxEq.
Import Syntax_Notations.


Lemma presup_exp_eq_fn_cong_right {P : PtsSig} : forall {Γ : ctx P} {s1 A A' s2 B M' s3} (r : Ru P s1 s2 s3),
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ Γ ⊢ A' : Sort@s1 }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
    {{ ⊢ Γ, A::Sort@s1 }} ->
    {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ, A::Sort@s1 ⊢ M' : B }} ->
    {{ Γ ⊢ λ r A' M' : Π r A B }}.
Proof.
  intros.
  assert {{ Γ ⊢ Π r A B ≈ Π r A' B : Sort@s3 }} by mauto 3.
  assert {{ Γ, A'::Sort@s1 ⊢ M' : B }} by mauto 4.
  assert {{ Γ ⊢ Π r A B : Sort@s3 }} by mauto 2.
  enough {{ Γ ⊢ λ r A' M' : Π r A' B }}; mauto.
Qed.

#[local]
Hint Resolve presup_exp_eq_fn_cong_right : mcpts.

Lemma presup_exp_eq_fn_sub_right {P : PtsSig} : forall {Γ : ctx P} {σ Δ s1 A s2 B M s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Δ, A::Sort@s1 }} ->
    {{ Δ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Δ, A::Sort@s1 ⊢ M : B }} ->
    {{ Γ ⊢ λ r A[σ] M[q σ] : (Π r A B)[σ] }}.
Proof.
  intros.
  assert {{ Γ ⊢ A[σ] : Sort@s1 }} by mauto 2.
  assert {{ Γ, A[σ]::Sort@s1 ⊢ B[q σ] : Sort@s2 }} by mauto 3.
  assert {{ Γ ⊢ Π r A[σ] B[q σ] : Sort@s3 }} by mauto 2.
  assert {{ Γ ⊢ Π r A[σ] B[q σ] ≈ Π r A[σ] B[q σ] : Sort@s3 }} by mauto 2.
  assert {{ Γ, A[σ]::Sort@s1 ⊢ M[q σ] : B[q σ] }} by mauto 3.
  assert {{ Γ ⊢ λ r A[σ] M[q σ] : Π r A[σ] B[q σ] }} by mauto 3.
  eapply wf_conv; mauto.
Qed.

#[local]
Hint Resolve presup_exp_eq_fn_sub_right : mcpts.

Lemma presup_exp_eq_app_cong_right {P : PtsSig} : forall {Γ : ctx P} {s1 A B M' N N' s2 s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Γ, A::Sort@s1 }} ->
    {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ M' : Π r A B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ N' : A }} ->
    {{ Γ ⊢ N ≈ N' : A }} ->
    {{ Γ ⊢ M' N' : B[Id,,N] }}.
Proof.
  intros.
  assert {{ Γ ⊢s Id ≈ Id : Γ }} by mauto 2.
  assert {{ Γ ⊢ A ≈ A[Id] : Sort@s1 }} by mauto 3.
  assert {{ Γ ⊢ N ≈ N' : A[Id] }} by mauto 2.
  assert {{ Γ ⊢s Id,,N ≈ Id,,N' : Γ, A::Sort@s1 }} by mauto 2.
  assert {{ Γ ⊢ B[Id,,N] ≈ B[Id,,N'] : Sort@s2 }} by (eapply wf_exp_eq_conv; mauto 3).
  eapply wf_conv; mauto 4.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_cong_right : mcpts.

Lemma presup_exp_eq_app_sub_left {P : PtsSig} : forall {Γ : ctx P} {σ Δ s1 A B M N s2 s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Δ, A::Sort@s1 }} ->
    {{ Δ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Δ ⊢ M : Π r A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ (M N)[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  assert {{ Γ, A[σ]::Sort@s1 ⊢s q σ : Δ, A::Sort@s1 }} by mauto 2.
  assert {{ Γ ⊢ M[σ] : (Π r A B)[σ] }} by mauto 3.
  assert {{ Γ ⊢ Π r A[σ] B[q σ] : Sort@s3 }} by mauto 4.
  assert {{ Γ ⊢ M[σ] : Π r A[σ] B[q σ] }} by mauto.
  assert {{ Δ ⊢ N : A[Id] }} by mauto 2.
  assert {{ Γ ⊢s (Id,,N)∘σ ≈ Id∘σ,,N[σ] : Δ, A::Sort@s1 }} by mauto 3.
  assert {{ Γ ⊢s (Id,,N)∘σ ≈ σ,,N[σ] : Δ, A::Sort@s1 }} by mauto 3.
  assert {{ Δ ⊢s Id,,N : Δ, A::Sort@s1 }} by mauto 3.
  assert {{ Γ ⊢s (Id,,N)∘σ : Δ, A::Sort@s1 }} by mauto 3.
  assert {{ Γ ⊢ B[(Id,,N)∘σ] ≈ B[σ,,N[σ]] : Sort@s2 }} by (eapply wf_exp_eq_conv; mauto 3).
  assert {{ Γ ⊢s σ,,N[σ] : Δ, A::Sort@s1 }} by mauto 3.
  assert {{ Γ ⊢ B[σ,,N[σ]] : Sort@s2 }} by mauto 2.
  assert {{ Γ ⊢ B[(Id,,N)∘σ] ≈ B[Id,,N][σ] : Sort@s2 }} by mauto.
  assert {{ Γ ⊢ B[Id,,N][σ] ≈ B[σ,,N[σ]] : Sort@s2 }} by mauto.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_sub_left : mcpts.

Lemma presup_exp_eq_app_sub_right {P : PtsSig} : forall {Γ : ctx P} {σ Δ s1 A B M N s2 s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Δ, A::Sort@s1 }} ->
    {{ Δ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Δ ⊢ M : Π r A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  assert {{ Γ ⊢ A[σ] : Sort@s1 }} by mauto 2.
  assert {{ Γ, A[σ]::Sort@s1 ⊢s q σ : Δ, A::Sort@s1 }} by mauto 2.
  assert {{ Γ, A[σ]::Sort@s1 ⊢ B[q σ] : Sort@s2 }} by mauto 2.
  assert {{ Γ ⊢ M[σ] : Π r A[σ] B[q σ] }} by (eapply wf_conv; mauto 3).
  assert {{ Γ ⊢ N[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢s q σ∘(Id,,N[σ]) ≈ σ,,N[σ] : Δ, A::Sort@s1 }} by mauto 2.
  assert {{ Γ ⊢s Id,,N[σ] : Γ, A[σ]::Sort@s1 }} by mauto 2.
  assert {{ Γ ⊢s q σ∘(Id,,N[σ]) : Δ, A::Sort@s1 }} by mauto 2.
  assert {{ Γ ⊢ B[q σ∘(Id,,N[σ])] ≈ B[σ,,N[σ]] : Sort@s2 }} by (eapply wf_exp_eq_conv; mauto).
  assert {{ Γ ⊢ B[q σ][Id,,N[σ]] : Sort@s2 }} by mauto 2.
  assert {{ Γ ⊢ B[q σ][Id,,N[σ]] ≈ B[q σ∘(Id,,N[σ])] : Sort@s2 }} by (symmetry; mauto).
  assert {{ Γ ⊢ B[q σ][Id,,N[σ]] ≈ B[σ,,N[σ]] : Sort@s2 }} by (eapply wf_exp_eq_conv; mauto).
  eapply wf_conv; mauto.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_sub_right : mcpts.

Lemma presup_exp_eq_pi_eta_right {P : PtsSig} : forall {Γ : ctx P} {s1 A B M s2 s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Γ, A::Sort@s1 }} ->
    {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ M : Π r A B }} ->
    {{ Γ ⊢ λ r A (M[Wk] #0) : Π r A B }}.
Proof.
  intros.
  assert {{ Γ, A::Sort@s1 ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, A::Sort@s1, A[Wk]::Sort@s1 ⊢s q Wk : Γ, A::Sort@s1 }} by mauto 2.
  assert {{ Γ, A::Sort@s1 ⊢ A[Wk] : Sort@s1 }} by mauto 2.
  assert {{ Γ, A::Sort@s1, A[Wk]::Sort@s1 ⊢ B[q Wk] : Sort@s2 }} by mauto 2.
  assert {{ Γ, A::Sort@s1 ⊢ M[Wk] : Π r A[Wk] B[q Wk] }} by (eapply wf_conv; mauto 3).
  assert {{ Γ, A::Sort@s1 ⊢ #0 : A[Wk] }} by mauto 2.
  assert {{ Γ, A::Sort@s1 ⊢s q Wk∘(Id,,#0) ≈ Id : Γ, A::Sort@s1 }} by (etransitivity; mauto 2).
  assert {{ Γ, A::Sort@s1 ⊢s Id,,#0 : Γ, A::Sort@s1, A[Wk]::Sort@s1 }} by mauto 2.
  assert {{ Γ, A::Sort@s1 ⊢ B[q Wk∘(Id,,#0)] ≈ B[Id] : Sort@s2 }} by (eapply wf_exp_eq_conv; mauto).
  assert {{ Γ, A::Sort@s1 ⊢ B[q Wk][Id,,#0] ≈ B[Id] : Sort@s2 }} by (transitivity {{{ B[q Wk∘(Id,,#0)] }}}; eapply wf_exp_eq_conv; mauto).
  econstructor; eauto.
  eapply wf_conv; mauto 4.
Qed.

#[local]
Hint Resolve presup_exp_eq_pi_eta_right : mcpts.

(* The next four lemmas provable, but probably only used for propositional equality, so we might want to remove them *)
Lemma presup_exp_eq_prop_eq_var0 {P : PtsSig} : forall {Γ : ctx P} {s A},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ, A::Sort@s, A[Wk]::Sort@s ⊢ #0 : A[Wk∘Wk] }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A::Sort@s }} by mauto 3.
  assert {{ Γ, A::Sort@s ⊢s Wk : Γ }} by mauto 2.
  assert {{ ⊢ Γ, A::Sort@s, A[Wk]::Sort@s }} by mauto 3.
  mauto 3.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_var0 : mcpts.

Lemma presup_exp_eq_prop_eq_var1 {P : PtsSig} : forall {Γ : ctx P} {s A},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ, A::Sort@s, A[Wk]::Sort@s ⊢ #1 : A[Wk∘Wk] }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A::Sort@s }} by mauto 3.
  assert {{ Γ, A::Sort@s ⊢s Wk : Γ }} by mauto 2.
  assert {{ ⊢ Γ, A::Sort@s, A[Wk]::Sort@s }} by mauto 3.
  eapply var_compose_subs; mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_var1 : mcpts.

Lemma presup_exp_eq_prop_eq_sub_helper2 {P : PtsSig} : forall {Γ : ctx P} {σ Δ s A M1 M2},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Δ ⊢ M1 : A }} ->
    {{ Δ ⊢ M2 : A }} ->
    {{ Γ ⊢s σ,,M1[σ],,M2[σ] : Δ, A::Sort@s, A[Wk]::Sort@s }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A::Sort@s }} by mauto 3.
  assert {{ Δ, A::Sort@s ⊢s Wk : Δ }} by mauto 2.
  assert {{ Γ ⊢s σ,,M1[σ] : Δ, A::Sort@s }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] ≈ A[Wk∘(σ,,M1[σ])] : Sort@s }} by (eapply wf_exp_eq_conv; mauto).
  assert {{ Γ ⊢ A[Wk∘(σ,,M1[σ])] ≈ A[σ] : Sort@s }} by (eapply wf_exp_eq_conv; mauto).
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] ≈ A[σ] : Sort@s }} by (transitivity {{{ A[Wk∘(σ,,M1[σ])] }}}; mauto 3).
  assert {{ Γ ⊢ M2[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ M2[σ] : A[Wk][σ,,M1[σ]] }} by (eapply wf_conv; mauto 3).
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_sub_helper2 : mcpts.

Lemma presup_exp_eq_prop_eq_id_sub_helper2 {P : PtsSig} : forall {Γ : ctx P} {s A M1 M2},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M1 : A }} ->
    {{ Γ ⊢ M2 : A }} ->
    {{ Γ ⊢s Id,,M1,,M2 : Γ, A::Sort@s, A[Wk]::Sort@s }}.
Proof.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢s Id : Γ }} by mauto 2.
  assert {{ Γ ⊢s Id,,M1 : Γ, A::Sort@s }} by mauto 2.
  assert {{ ⊢ Γ, A::Sort@s }} by mauto 3.
  assert {{ Γ, A::Sort@s ⊢ A[Wk] : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][Id,,M1] : Sort@s }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][Id,,M1] ≈ A[Wk∘(Id,,M1)] : Sort@s }} by (eapply wf_exp_eq_conv; mauto 4).
  assert {{ Γ ⊢ A[Wk∘(Id,,M1)] ≈ A[Id] : Sort@s }} by  (eapply wf_exp_eq_conv; mauto 4).
  assert {{ Γ ⊢ A[Wk][Id,,M1] ≈ A : Sort@s }} by (eapply wf_exp_eq_conv; mauto 4).
  assert {{ Γ ⊢ M2 : A[Wk][Id,,M1] }} by (eapply wf_conv; mauto 3).
  mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_id_sub_helper2 : mcpts.


Lemma presup_exp_eq_var_0_sub_left {P : PtsSig} : forall {Γ : ctx P} {σ Δ s A M},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ #0[σ,,M] : A[σ] }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A::Sort@s }} by mauto 2.
  assert {{ Δ, A::Sort@s ⊢ #0 : A[Wk] }} by mauto 2.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_var_0_sub_left : mcpts.

Lemma presup_exp_eq_var_S_sub_left {P : PtsSig} : forall {Γ : ctx P} {σ Δ s1 A M B x s2},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ #x : B :: Sort@s2 ∈ Δ }} ->
    {{ Γ ⊢ #(S x)[σ,,M] : B[σ] }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A::Sort@s1 }} by mauto 2.
  assert ({{ Δ ⊢ B : Sort@s2 }}) by (eapply presup_ctx_lookup_typ; mauto).
  assert {{ Δ, A::Sort@s1 ⊢ #(S x) : B[Wk] }} by mauto 3.
  eapply wf_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_var_S_sub_left : mcpts.

Lemma presup_exp_eq_sub_cong_right {P : PtsSig} : forall {Γ : ctx P} {σ σ' Δ s A M M'},
    {{ ⊢ Δ }} ->
    {{ Δ ⊢ A : Sort@s }} ->
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
  eapply wf_conv; mauto 3.
  eapply exp_eq_sub_cong_typ2'; mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_sub_cong_right : mcpts.

Lemma presup_exp_eq_sub_compose_right {P : PtsSig} : forall {Γ : ctx P} {τ Γ' σ Γ'' s A M},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ' }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ ⊢ Γ'' }} ->
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ'' ⊢ A : Sort@s }} ->
    {{ Γ'' ⊢ M : A }} ->
    {{ Γ ⊢ M[σ][τ] : A[σ∘τ] }}.
Proof.
  intros.
  eapply wf_conv; mauto 4.
Qed.

#[local]
Hint Resolve presup_exp_eq_sub_compose_right : mcpts.

#[local]
Ltac gen_presup_IH presup_exp_eq presup_sub_eq presup_typ_eq H :=
  match type of H with
  | {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} =>
      let HΓ := fresh "HΓ" in
      let HM := fresh "HM" in
      let HN := fresh "HN" in
      let HA := fresh "HA" in
      pose proof presup_exp_eq _ _ _ _ _ H as [HΓ [HM [HN HA]]]
  | {{ ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Δ }} =>
      let HΓ := fresh "HΓ" in
      let Hσ := fresh "Hσ" in
      let Hτ := fresh "Hτ" in
      let HΔ := fresh "HΔ" in
      pose proof presup_sub_eq _ _ _ _ _ H as [HΓ [Hσ [Hτ HΔ]]]
  | {{ ^?Γ ⊢ ^?A ≈ ^?B }} =>
      let HΓ := fresh "HΓ" in
      let HA := fresh "HA" in
      let HB := fresh "HB" in
      pose proof presup_typ_eq _ _ _ _ H as [HΓ [HA HB]]
  end.

Lemma presup_exp_eq {P : PtsSig} : forall {Γ : ctx P} {M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ M : A }} /\ {{ Γ ⊢ M' : A }} /\ {{ Γ ⊢ A  }}
with presup_sub_eq {P : PtsSig} : forall {Γ : ctx P} {Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢s σ : Δ }} /\ {{ Γ ⊢s σ' : Δ }} /\ {{ ⊢ Δ }}
with presup_typ_eq {P : PtsSig} : forall {Γ : ctx P} {A A'}, {{ Γ ⊢ A ≈ A' }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ A }} /\ {{ Γ ⊢ A' }}.
Proof with mautosolve 4.
  all: inversion_clear 1;
    (on_all_hyp: gen_presup_IH presup_exp_eq presup_sub_eq presup_typ_eq);
    gen_core_presups;
    clear presup_exp_eq presup_sub_eq presup_typ_eq;
    repeat split; try mautosolve 3;
    try (eexists; unshelve solve [mauto 4]; constructor).

  all: try (econstructor; mautosolve 4).
  - econstructor; mauto 3. 
    eapply wf_conv; mauto 5.
  - econstructor; mauto 3.
    eapply wf_conv; mauto 5.
  - econstructor; mauto 3.
    eapply wf_conv; mauto 5.
    dependent destruction HΔ.
    econstructor; mauto 3.
    eapply wf_conv; mauto 5.
Qed.

Ltac gen_presup H := gen_presup_IH @presup_exp_eq @presup_sub_eq @presup_typ_eq H + gen_core_presup H.

Ltac gen_presups := (on_all_hyp: fun H => gen_presup H); invert_wf_ctx; (on_all_hyp: fun H => gen_lookup_presup H); clear_dups.
