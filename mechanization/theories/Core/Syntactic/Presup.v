From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export CtxEq.
Import Syntax_Notations.


Lemma presup_exp_eq_fn_cong_right {P : PtsSig} : forall {Γ : ctx P} {s1 A A' s2 B M' s3} (r : Ru P s1 s2 s3),
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ Γ ⊢ A' : Sort@s1 }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
    {{ ⊢ Γ, A@s1 }} ->
    {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ, A@s1 ⊢ M' : B }} ->
    {{ Γ ⊢ λ r A' M' : Π r A B }}.
Proof.
  intros.
  assert {{ Γ ⊢ Π r A B ≈ Π r A' B : Sort@s3 }} by mauto 3.
  assert {{ Γ ⊢ A ≈ A' }} by mauto 2.
  assert {{ ⊢ Γ, A@s1 ≈ Γ, A'@s1 }} by (econstructor; mauto 3).
  assert {{ Γ, A'@s1 ⊢ M' : B }} by mauto 4.
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
    {{ ⊢ Δ, A@s1 }} ->
    {{ Δ, A@s1 ⊢ B : Sort@s2 }} ->
    {{ Δ, A@s1 ⊢ M : B }} ->
    {{ Γ ⊢ λ r A[σ] M[q σ] : (Π r A B)[σ] }}.
Proof.
  intros.
  assert {{ Γ ⊢ A[σ] : Sort@s1 }} by mauto 2.  
  assert {{ Γ, A[σ]@s1 ⊢ B[q σ] : Sort@s2 }} by mauto 4.
  assert {{ Γ ⊢ Π r A[σ] B[q σ] : Sort@s3 }} by mauto 2.
  assert {{ Γ ⊢ Π r A[σ] B[q σ] ≈ Π r A[σ] B[q σ] : Sort@s3 }} by mauto 2.
  assert {{ Γ, A[σ]@s1 ⊢ M[q σ] : B[q σ] }} by mauto 4.
  assert {{ Γ ⊢ λ r A[σ] M[q σ] : Π r A[σ] B[q σ] }} by mauto 3.
  eapply wf_exp_conv; mauto 4.
Qed.

#[local]
Hint Resolve presup_exp_eq_fn_sub_right : mcpts.

Lemma presup_exp_eq_app_cong_right {P : PtsSig} : forall {Γ : ctx P} {s1 A B M' N N' s2 s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Γ, A@s1 }} ->
    {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ M' : Π r A B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ N' : A }} ->
    {{ Γ ⊢ N ≈ N' : A }} ->
    {{ Γ ⊢ M' N' : B[Id,,N] }}.
Proof.
  intros.
  assert {{ Γ ⊢s Id ≈ Id : Γ }} by mauto 2.
  assert {{ Γ ⊢ A ≈ A[Id] : Sort@s1 }} by mauto 3.
  assert {{ Γ ⊢ N ≈ N' : A[Id] }} by mauto 3.
  assert {{ Γ ⊢s Id,,N ≈ Id,,N' : Γ, A@s1 }} by mauto 3.
  assert {{ Γ ⊢ B[Id,,N] ≈ B[Id,,N'] : Sort@s2 }} by mauto 3.
  assert {{ Γ ⊢ B[Id,,N] : Sort@s2 }} by mauto 4.
  eapply wf_exp_conv; mauto 4.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_cong_right : mcpts.

Lemma presup_exp_eq_app_sub_left {P : PtsSig} : forall {Γ : ctx P} {σ Δ s1 A B M N s2 s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Δ, A@s1 }} ->
    {{ Δ, A@s1 ⊢ B : Sort@s2 }} ->
    {{ Δ ⊢ M : Π r A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ (M N)[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  assert {{ Γ, A[σ]@s1 ⊢s q σ : Δ, A@s1 }} by mauto 3.
  assert {{ Γ ⊢ M[σ] : (Π r A B)[σ] }} by mauto 3.
  assert {{ Γ ⊢ Π r A[σ] B[q σ] : Sort@s3 }} by mauto 4.
  assert {{ Γ ⊢ M[σ] : Π r A[σ] B[q σ] }} by mauto.
  assert {{ Δ ⊢ N : A[Id] }} by mauto 3.
  assert {{ Γ ⊢s (Id,,N)∘σ ≈ Id∘σ,,N[σ] : Δ, A@s1 }} by mauto 4.
  assert {{ Γ ⊢s (Id,,N)∘σ ≈ σ,,N[σ] : Δ, A@s1 }} by mauto 3.
  assert {{ Δ ⊢s Id,,N : Δ, A@s1 }} by mauto 3.
  assert {{ Γ ⊢s (Id,,N)∘σ : Δ, A@s1 }} by mauto 3.
  assert {{ Γ ⊢ B[(Id,,N)∘σ] ≈ B[σ,,N[σ]] : Sort@s2 }} by mauto 3.
  assert {{ Γ ⊢s σ,,N[σ] : Δ, A@s1 }} by mauto 4.
  assert {{ Γ ⊢ B[σ,,N[σ]] : Sort@s2 }} by mauto 2.
  assert {{ Γ ⊢ B[(Id,,N)∘σ] ≈ B[Id,,N][σ] : Sort@s2 }} by mauto.
  assert {{ Γ ⊢ B[Id,,N][σ] ≈ B[σ,,N[σ]] : Sort@s2 }} by mauto 3.
  eapply wf_exp_conv; mauto 4.  
Qed.

#[local]
Hint Resolve presup_exp_eq_app_sub_left : mcpts.

Lemma presup_exp_eq_app_sub_right {P : PtsSig} : forall {Γ : ctx P} {σ Δ s1 A B M N s2 s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Δ, A@s1 }} ->
    {{ Δ, A@s1 ⊢ B : Sort@s2 }} ->
    {{ Δ ⊢ M : Π r A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  assert {{ Γ ⊢ A[σ] : Sort@s1 }} by mauto 2.
  assert {{ Γ, A[σ]@s1 ⊢s q σ : Δ, A@s1 }} by mauto 3.
  assert {{ Γ, A[σ]@s1 ⊢ B[q σ] : Sort@s2 }} by mauto 2.
  assert {{ Γ ⊢ M[σ] : Π r A[σ] B[q σ] }} by (eapply wf_exp_conv; mauto 3).
  assert {{ Γ ⊢ N[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢s q σ∘(Id,,N[σ]) ≈ σ,,N[σ] : Δ, A@s1 }} by mauto 3.
  assert {{ Γ ⊢s Id,,N[σ] : Γ, A[σ]@s1 }} by mauto 3.
  assert {{ Γ ⊢s q σ∘(Id,,N[σ]) : Δ, A@s1 }} by mauto 2.
  assert {{ Γ ⊢ B[q σ∘(Id,,N[σ])] ≈ B[σ,,N[σ]] : Sort@s2 }} by mauto 3. 
  assert {{ Γ ⊢ B[q σ][Id,,N[σ]] : Sort@s2 }} by mauto 2.
  assert {{ Γ ⊢ B[q σ][Id,,N[σ]] ≈ B[q σ∘(Id,,N[σ])] : Sort@s2 }} by (symmetry; mauto).
  assert {{ Γ ⊢ B[q σ][Id,,N[σ]] ≈ B[σ,,N[σ]] : Sort@s2 }} by mauto 3. 
  eapply wf_exp_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_sub_right : mcpts.

Lemma presup_exp_eq_pi_eta_right {P : PtsSig} : forall {Γ : ctx P} {s1 A B M s2 s3} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Γ, A@s1 }} ->
    {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ M : Π r A B }} ->
    {{ Γ ⊢ λ r A (M[Wk] #0) : Π r A B }}.
Proof.
  intros.
  assert {{ Γ, A@s1 ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, A@s1, A[Wk]@s1 ⊢s q Wk : Γ, A@s1 }} by mauto 3.
  assert {{ Γ, A@s1 ⊢ A[Wk] : Sort@s1 }} by mauto 2.
  assert {{ Γ, A@s1, A[Wk]@s1 ⊢ B[q Wk] : Sort@s2 }} by mauto 2.
  assert {{ Γ, A@s1 ⊢ M[Wk] : Π r A[Wk] B[q Wk] }} by (eapply wf_exp_conv; mauto 3).
  assert {{ Γ, A@s1 ⊢ A[Wk] : Sort@s1 }} by mauto 3.
  assert {{ Γ, A@s1 ⊢ #0 : A[Wk] }} by mauto 2.
  assert {{ Γ, A@s1 ⊢s q Wk∘(Id,,#0) ≈ Id : Γ, A@s1 }} by (etransitivity; mauto 3).
  assert {{ Γ, A@s1 ⊢s Id,,#0 : Γ, A@s1, A[Wk]@s1 }} by mauto 3.
  assert {{ Γ, A@s1 ⊢ B[q Wk∘(Id,,#0)] ≈ B[Id] : Sort@s2 }} by mauto 3. 
  assert {{ Γ, A@s1 ⊢ B[q Wk][Id,,#0] ≈ B[Id] : Sort@s2 }} by (transitivity {{{ B[q Wk∘(Id,,#0)] }}}; mauto 3). 
  econstructor; eauto.
  eapply wf_exp_conv; mauto 4.
Qed.

#[local]
Hint Resolve presup_exp_eq_pi_eta_right : mcpts.

(* The next four lemmas are provable, but probably only used for propositional equality, so we might want to remove them *)
Lemma presup_exp_eq_prop_eq_var0 {P : PtsSig} : forall {Γ : ctx P} {A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ, A@s, A[Wk]@s ⊢ #0 : A[Wk∘Wk] }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A@s }} by mauto 3.
  assert {{ Γ, A@s ⊢s Wk : Γ }} by mauto 2.
  assert {{ ⊢ Γ, A@s, A[Wk]@s }} by mauto 3.
  assert {{ Γ, A@s ⊢ A[Wk] : Sort@s }} by mauto 3.
  assert {{ Γ, A@s, A[Wk]@s ⊢ A[Wk][Wk] : Sort@s }} by mauto 4.
  assert {{ Γ, A@s, A[Wk]@s ⊢ A[Wk∘Wk] : Sort@s }} by mauto 4.
  eapply wf_exp_conv with (A := {{{ A[Wk][Wk] }}}); mauto 4.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_var0 : mcpts.

Lemma presup_exp_eq_prop_eq_var1 {P : PtsSig} : forall {Γ : ctx P} {A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ, A@s, A[Wk]@s ⊢ #1 : A[Wk∘Wk] }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A@s }} by mauto 3.
  assert {{ Γ, A@s ⊢s Wk : Γ }} by mauto 2.
  assert {{ ⊢ Γ, A@s, A[Wk]@s }} by mauto 3.
  eapply var_compose_subs; mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_var1 : mcpts.

Lemma presup_exp_eq_prop_eq_sub_helper2 {P : PtsSig} : forall {Γ : ctx P} {σ Δ A M1 M2 s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Δ ⊢ M1 : A }} ->
    {{ Δ ⊢ M2 : A }} ->
    {{ Γ ⊢s σ,,M1[σ],,M2[σ] : Δ, A@s, A[Wk]@s }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A@s }} by mauto 3.
  assert {{ Δ, A@s ⊢s Wk : Δ }} by mauto 2.
  assert {{ Γ ⊢s σ,,M1[σ] : Δ, A@s }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] ≈ A[Wk∘(σ,,M1[σ])] : Sort@s }} by mauto.
  assert {{ Γ ⊢s Wk∘(σ,,M1[σ]) ≈ σ : Δ }} by mauto.
  assert {{ Γ ⊢ A[Wk∘(σ,,M1[σ])] ≈ A[σ] : Sort@s }} by mauto.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] ≈ A[σ] : Sort@s }} by (transitivity {{{ A[Wk∘(σ,,M1[σ])] }}}; mauto 3).
  assert {{ Γ ⊢ M2[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][σ,,M1[σ]] : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ M2[σ] : A[Wk][σ,,M1[σ]] }} by (eapply wf_exp_conv; mauto 3).
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_sub_helper2 : mcpts.

Lemma presup_exp_eq_prop_eq_id_sub_helper2 {P : PtsSig} : forall {Γ : ctx P} {A M1 M2 s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M1 : A }} ->
    {{ Γ ⊢ M2 : A }} ->
    {{ Γ ⊢s Id,,M1,,M2 : Γ, A@s, A[Wk]@s }}.
Proof.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢s Id : Γ }} by mauto 2.
  assert {{ Γ ⊢s Id,,M1 : Γ, A@s }} by mauto 2.
  assert {{ ⊢ Γ, A@s }} by mauto 3.
  assert {{ Γ, A@s ⊢ A[Wk] : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][Id,,M1] : Sort@s }} by mauto 2.
  assert {{ Γ ⊢ A[Wk][Id,,M1] ≈ A[Wk∘(Id,,M1)] : Sort@s }} by mauto.
  assert {{ Γ ⊢s Wk∘(Id,,M1) ≈ Id : Γ }} by mauto 2.
  assert {{ Γ ⊢ A[Wk∘(Id,,M1)] ≈ A[Id] : Sort@s }} by mauto.
  assert {{ Γ ⊢ A[Wk][Id,,M1] ≈ A : Sort@s }} by mauto.
  assert {{ Γ ⊢ M2 : A[Wk][Id,,M1] }} by (eapply wf_exp_conv; mauto 3).
  mauto 2.
Qed.

#[export]
Hint Resolve presup_exp_eq_prop_eq_id_sub_helper2 : mcpts.


Lemma presup_exp_eq_var_0_sub_left {P : PtsSig} : forall {Γ : ctx P} {σ Δ A M s},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ #0[σ,,M] : A[σ] }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A@s }} by mauto 2.
  assert {{ Δ ⊢ A : Sort@s }} by mauto 2.
  assert {{ Δ, A@s ⊢ A[Wk] : Sort@s }} by mauto 3.
  assert {{ Δ, A@s ⊢ #0 : A[Wk] }} by mauto 2.
  eapply wf_exp_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_var_0_sub_left : mcpts.

Lemma presup_exp_eq_var_S_sub_left {P : PtsSig} : forall {Γ : ctx P} {σ Δ A M B x s s'},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ #x : B@s' ∈ Δ }} ->
    {{ Γ ⊢ #(S x)[σ,,M] : B[σ] }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A@s }} by mauto 2.
  assert {{ Δ ⊢ B : Sort@s' }} by (eapply presup_ctx_lookup_typ; mauto).
  destruct_conjs.
  assert {{ Δ, A@s ⊢ B[Wk] : Sort@s' }} by mauto 4.
  assert {{ Δ, A@s ⊢ #(S x) : B[Wk] }} by mauto 3.
  eapply wf_exp_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_var_S_sub_left : mcpts.

Lemma presup_exp_eq_sub_cong_right {P : PtsSig} : forall {Γ : ctx P} {σ σ' Δ A M M' s},
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
  eapply wf_exp_conv; mauto 3.
Qed.

#[local]
Hint Resolve presup_exp_eq_sub_cong_right : mcpts.

Lemma presup_exp_eq_sub_compose_right {P : PtsSig} : forall {Γ : ctx P} {τ Γ' σ Γ'' A M s},
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
  eapply wf_exp_conv; mauto 4.
Qed.

#[local]
Hint Resolve presup_exp_eq_sub_compose_right : mcpts.

Lemma wf_exp_sub_id_wf_typ {P} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M[Id] : A }}.
Proof.
  induction 1; intros; try solve [econstructor; mauto 3].
  - eapply wf_exp_conv with (A := {{{ (Π r A B)[Id] }}}); mauto 3;
      econstructor; mauto 3.
  - eapply wf_exp_conv with (A := {{{ B[Id,,N][Id] }}}); mauto 4;
      econstructor; mauto 3.
  - eapply wf_exp_conv with (A := {{{ A[Id] }}}); mauto 3;
      econstructor; mauto 3.
  - eapply wf_exp_conv with (A := {{{ A[σ][Id] }}}); mauto 3;
      econstructor; mauto 3.
Qed.

#[local]
Hint Resolve wf_exp_sub_id_wf_typ : mcpts.
    
#[local]
Ltac gen_presup_IH presup_exp_eq presup_sub_eq (* presup_typ_eq *) H :=
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
  (* | {{ ^?Γ ⊢ ^?A ≈ ^?B }} => *)
  (*     let HΓ := fresh "HΓ" in *)
  (*     let HA := fresh "HA" in *)
  (*     let HB := fresh "HB" in *)
  (*     pose proof presup_typ_eq _ _ _ _ H as [HΓ [HA HB]] *)
  end.

Lemma presup_exp_eq {P : PtsSig} : forall {Γ : ctx P} {M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ M : A }} /\ {{ Γ ⊢ M' : A }} /\ {{ Γ ⊢ A  }}
with presup_sub_eq {P : PtsSig} : forall {Γ : ctx P} {Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢s σ : Δ }} /\ {{ Γ ⊢s σ' : Δ }} /\ {{ ⊢ Δ }}.
(* with presup_typ_eq {P : PtsSig} : forall {Γ : ctx P} {A A'}, {{ Γ ⊢ A ≈ A' }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ A }} /\ {{ Γ ⊢ A' }}. *)
Proof with mautosolve 5.
  all: inversion_clear 1;
    (on_all_hyp: gen_presup_IH presup_exp_eq presup_sub_eq (* presup_typ_eq *));
    gen_core_presups;
    clear presup_exp_eq presup_sub_eq (* presup_typ_eq *);
    repeat split; try mautosolve 3;
    try (eexists; unshelve solve [mauto 4]; constructor).

  all: try (econstructor; mautosolve 4).
  - econstructor; mauto 3.
    eapply wf_exp_conv; mauto 3.
  - econstructor; mauto 3.
    assert {{ Γ ⊢ A[σ0∘τ] : Sort@s }} by mauto 3.
    assert {{ Γ ⊢ A[σ0][τ] : Sort@s }} by mauto 3.
    assert {{ Γ ⊢ A[σ0∘τ] ≈ A[σ0][τ] : Sort@s }} by mauto 3.
    assert {{ Γ ⊢ M[τ] : A[σ0][τ] }} by mauto 3.
    mauto 3.
  - econstructor; mauto 3.
    assert {{ Γ0 ⊢ A : Sort@s }} by mauto 2.
    assert {{ Γ ⊢s Wk∘σ : Γ0 }} by mauto 3.
    assert {{ Γ ⊢ A[Wk∘σ] : Sort@s }} by mauto 3.
    eapply wf_exp_conv with (A := {{{ A[Wk][σ] }}}); mauto 4.
Qed.

Corollary presup_typ_eq {P} : forall {Γ : ctx P} {A B}, {{ Γ ⊢ A ≈ B }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ A }} /\ {{ Γ ⊢ B }}.
Proof.
  intros * H.
  induction H.
  - repeat split; mauto 2.
  - assert ({{ ⊢ Γ }} /\ {{ Γ ⊢ A : Sort@s }} /\ {{ Γ ⊢ B : Sort@s }} /\ {{ Γ ⊢ Sort@s }}) by (eapply presup_exp_eq; mauto 2).
    destruct_conjs.
    repeat split; mauto 2.
  - assert ({{ ⊢ Γ }} /\ {{ Γ ⊢ B : Sort@s }} /\ {{ Γ ⊢ C : Sort@s }} /\ {{ Γ ⊢ Sort@s }}) by (eapply presup_exp_eq; mauto 2).
    destruct_conjs.
    repeat split; mauto 2.
Qed.

Ltac gen_presup_IH' presup_exp_eq presup_sub_eq presup_typ_eq H :=
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


Ltac gen_presup H := gen_presup_IH' @presup_exp_eq @presup_sub_eq @presup_typ_eq H + gen_core_presup H.

Ltac gen_presups := (on_all_hyp: fun H => gen_presup H); invert_wf_ctx; (on_all_hyp: fun H => gen_lookup_presup H); clear_dups.
