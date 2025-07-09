From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import CtxEq.
From McPTS.Core.Syntactic Require Import System.


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

Lemma presup_exp_eq_app_sub_left {P : PtsSig} : forall {Γ : Ctx P} {σ Δ s1 s2 s3 A B M N} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Δ, A::Sort@s1 }} ->
    {{ Δ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Δ ⊢ M : Π r A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ [σ](M N) : [σ,,[σ]N]B }}.
Proof.
  intros.
  assert {{ Γ, [σ]A::Sort@s1 ⊢s (Wk∘σ),,#0 : Δ, A::Sort@s1 }} by mauto 2.
  assert {{ Γ ⊢ [σ]M : [σ](Π r A B) }} by (econstructor; mauto 2).
  assert {{ Γ ⊢ Π r [σ]A [(Wk∘σ),,#0]B : Sort@s3 }} by (econstructor; mauto 2).
  assert {{ Γ ⊢ [σ]M : Π r [σ]A [(Wk∘σ),,#0]B }}.
  {
    eapply wf_exp_conv; mauto 2.
    econstructor; mauto 2.
    econstructor; mauto 2.
    econstructor; mauto 2.
  }
  assert {{ Δ ⊢ N : [Id]A }} by mauto 2.
  assert {{ Γ ⊢s σ∘(Id,,N) ≈ σ∘Id,,[σ]N : Δ, A::Sort@s1 }}.
  {
    econstructor; mauto 2.
    econstructor; mauto 2.
  }
  assert {{ Γ ⊢s σ∘(Id,,N) ≈ σ,,[σ]N : Δ, A::Sort@s1 }} by mauto 3.
  assert {{ Δ ⊢s Id,,N : Δ, A::Sort@s1 }} by mauto 3.
  assert {{ Γ ⊢s σ∘(Id,,N) : Δ, A::Sort@s1 }} by (econstructor; mauto 3).
  assert {{ Γ ⊢ [σ∘(Id,,N)]B ≈ [σ,,[σ]N]B : Sort@s2 }} by mauto 2.
  assert {{ Γ ⊢s σ,,[σ]N : Δ, A::Sort@s1 }}.
  {
    econstructor; mauto 2.
    econstructor; mauto 2.
  }
  assert {{ Γ ⊢ [σ,,[σ]N]B : Sort@s2 }} by mauto 2.
  assert {{ Γ ⊢ [σ][Id,,N]B ≈ [σ,,[σ]N]B : Sort@s2 }} by (econstructor; mauto 2).
  eapply wf_conv; mauto 3.
  econstructor; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_sub_left : mcpts.

Lemma presup_exp_eq_app_sub_right {P : PtsSig} : forall {Γ : Ctx P} {σ Δ s1 s2 s3 A B M N} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Δ, A::Sort@s1 }} ->
    {{ Δ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Δ ⊢ M : Π r A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ [σ]M [σ]N : [σ,,[σ]N]B }}.
Proof.
  intros.
  assert {{ Γ ⊢ [σ]A : Sort@s1 }} by mauto 2.
  assert {{ Γ, [σ]A::Sort@s1 ⊢s (Wk∘σ),,#0 : Δ, A::Sort@s1 }} by mauto 2.
  assert {{ Γ, [σ]A::Sort@s1 ⊢ [(Wk∘σ),,#0]B : Sort@s2 }} by mauto 2.
  assert {{ Γ ⊢ [σ]M : Π r [σ]A [(Wk∘σ),,#0]B }}.
  {
    eapply wf_conv; mauto 2; econstructor; mauto 2.
    econstructor; mauto 2.    
  }
  assert {{ Γ ⊢ [σ]N : [σ]A }} by (econstructor; mauto 2).
  assert {{ Γ ⊢s (Id,,[σ]N)∘((Wk∘σ),,#0) ≈ σ,,[σ]N : Δ, A::Sort@s1 }} by mauto 2.
  assert {{ Γ ⊢s Id,,[σ]N : Γ, [σ]A::Sort@s1 }} by mauto 2.
  assert {{ Γ ⊢s (Id,,[σ]N)∘((Wk∘σ),,#0) : Δ, A::Sort@s1 }} by (econstructor; mauto 2).
  assert {{ Γ ⊢ [(Id,,[σ]N)∘((Wk∘σ),,#0)]B ≈ [σ,,[σ]N]B : Sort@s2 }} by mauto 2.
  assert {{ Γ ⊢ [Id,,[σ]N][(Wk∘σ),,#0]B : Sort@s2 }} by mauto 2.
  assert {{ Γ ⊢ [Id,,[σ]N][(Wk∘σ),,#0]B ≈ [σ,,[σ]N]B : Sort@s2 }} by (econstructor; mauto 3).
  eapply wf_conv; mauto 3; econstructor; mauto 2; econstructor; mauto 2; econstructor; mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_app_sub_right : mcpts.

Lemma presup_exp_eq_pi_eta_right {P : PtsSig} : forall {Γ : Ctx P} {s1 s2 s3 A B M} {r : Ru P s1 s2 s3},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ ⊢ Γ, A::Sort@s1 }} ->
    {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ M : Π r A B }} ->
    {{ Γ ⊢ λ r A ([Wk]M #0) : Π r A B }}.
Proof.
  intros.
  assert {{ Γ, A::Sort@s1 ⊢s Wk : Γ }} by (econstructor; mauto 2).
  assert {{ Γ, A::Sort@s1, [Wk]A::Sort@s1 ⊢s (Wk∘Wk),,#0 : Γ, A::Sort@s1 }} by mauto 2.
  assert {{ Γ, A::Sort@s1 ⊢ [Wk]A : Sort@s1 }} by mauto 2.
  assert {{ Γ, A::Sort@s1, [Wk]A::Sort@s1 ⊢ [(Wk∘Wk),,#0]B : Sort@s2 }} by mauto 2.
  assert {{ Γ, A::Sort@s1 ⊢ [Wk]M : Π r [Wk]A [(Wk∘Wk),,#0]B }} by (eapply wf_conv; mauto 2; econstructor; mauto 2; econstructor; mauto 2).
  assert {{ Γ, A::Sort@s1 ⊢ #0 : [Wk]A }} by (econstructor; mauto 2; econstructor; mauto 2).
  assert {{ Γ, A::Sort@s1 ⊢s (Id,,#0)∘((Wk∘Wk),,#0) ≈ Id : Γ, A::Sort@s1 }} by (etransitivity; mauto 2).
  assert {{ Γ, A::Sort@s1 ⊢s Id,,#0 : Γ, A::Sort@s1, [Wk]A::Sort@s1 }} by mauto 2.
  assert {{ Γ, A::Sort@s1 ⊢ [Id,,#0][(Wk∘Wk),,#0]B ≈ [Id]B : Sort@s2 }}.
  {
    transitivity {{{ [(Id,,#0)∘((Wk∘Wk),,#0)]B }}}; mauto 3.
    eapply eq_exp_conv; mauto 2.
    eapply eq_exp_cong_clo; mauto 2.
    eapply eq_exp_refl; mauto 2.
    econstructor; mauto 2.
    econstructor; mauto 2.
  }
  econstructor; eauto.
  eapply wf_exp_pi; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2; econstructor; mauto 2.
  econstructor; mauto 2.
  eapply eq_exp_conv; mauto 2.
  transitivity {{{ [Id]B }}}; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2.
Qed.


#[local]
Hint Resolve presup_exp_eq_pi_eta_right : mcpts.

Lemma presup_exp_eq_var_0_sub_left {P : PtsSig} : forall {Γ : Ctx P} {σ Δ s A M},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : [σ]A }} ->
    {{ Γ ⊢ [σ,,M]#0 : [σ]A }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A::Sort@s }} by (econstructor; mauto 2).
  assert {{ Δ, A::Sort@s ⊢ #0 : [Wk]A }} by (econstructor; mauto 2; econstructor; mauto 2).
  eapply wf_conv; mauto 3; econstructor; mauto 2.
  econstructor; mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_var_0_sub_left : mcpts.

Lemma presup_exp_eq_var_S_sub_left {P : PtsSig} : forall {Γ : Ctx P} {σ Δ s A M B x s'},
    {{ ⊢ Γ }} ->
    {{ ⊢ Δ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : [σ]A }} ->
    {{ #x : B :: Sort@s' ∈ Δ }} ->
    {{ Γ ⊢ [σ,,M]#(S x) : [σ]B }}.
Proof.
  intros.
  assert {{ ⊢ Δ, A::Sort@s }} by (econstructor; mauto 2).
  assert {{ Δ ⊢ B : Sort@s' }} by mauto 2.
  assert {{ Δ, A::Sort@s ⊢ #(S x) : [Wk]B }} by (econstructor; mauto 2; econstructor; mauto 2).
  eapply wf_conv; mauto 2; econstructor; mauto 2.
  econstructor; mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_var_S_sub_left : mcpts.

Lemma presup_exp_eq_sub_cong_right {P : PtsSig} : forall {Γ : Ctx P} {σ σ' Δ s A M M'},
    {{ ⊢ Δ }} ->
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Δ ⊢ M' : A }} ->
    {{ Δ ⊢ M ≈ M' : A }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ' : Δ }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢ [σ']M' : [σ]A }}.
Proof.
  intros.
  eapply wf_conv; mauto 2.
  eapply wf_exp_clo; mauto 2.
  eapply eq_exp_conv; mauto 2.
  eapply eq_exp_cong_clo; mauto 2.
  eapply eq_sub_sym; mauto 2.
  eapply eq_exp_refl; mauto 2.
  econstructor; mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_sub_cong_right : mcpts.

Lemma presup_exp_eq_sub_compose_right {P : PtsSig} : forall {Γ : Ctx P} {τ Γ' σ Γ'' s A M},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ' }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ ⊢ Γ'' }} ->
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ'' ⊢ A : Sort@s }} ->
    {{ Γ'' ⊢ M : A }} ->
    {{ Γ ⊢ [τ][σ]M : [τ∘σ]A }}.
Proof.
  intros.
  eapply wf_conv; mauto 3; econstructor; mauto 2.
  eapply wf_exp_clo; mauto 2.
  eapply wf_exp_clo; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2.
Qed.

#[local]
Hint Resolve presup_exp_eq_sub_compose_right : mcpts.

#[local]
Ltac gen_presup_IH presup_exp_eq presup_sub_eq presup_subtyp H :=
  match type of H with
  | {{ ^?Γ ⊢ ^?M : ^?A }} =>
      let HΓ := fresh "HΓ" in
      let HA := fresh "HA" in
      pose proof presup_exp _ _ _ _ H as [HΓ HA]
  | {{ ^?Γ ⊢s ^?σ : ^?Δ }} =>
      let HΓ := fresh "HΓ" in
      let HΔ := fresh "HΔ" in
      pose proof presup_sub _ _ _ _ H as [HΓ HΔ]
  | {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} =>
      let HΓ := fresh "HΓ" in
      let HM := fresh "HM" in
      let HM' := fresh "HM'" in
      let HA := fresh "HA" in
      pose proof presup_exp_eq _ _ _ _ _ H as [HΓ [HM [HM' HA]]]
  | {{ ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Δ }} =>
      let HΓ := fresh "HΓ" in
      let Hσ := fresh "Hσ" in
      let Hσ' := fresh "Hσ'" in
      let HΔ := fresh "HΔ" in
      pose proof presup_sub_eq _ _ _ _ _ H as [HΓ [Hσ [Hσ' HΔ]]]
  end.


Lemma presup_exp_eq {P : PtsSig} : forall {Γ : Ctx P} {M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ M : A }} /\ {{ Γ ⊢ M' : A }} /\ {{ Γ ⊢ A }}
with presup_sub_eq {P : PtsSig} : forall {Γ : Ctx P} {Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢s σ : Δ }} /\ {{ Γ ⊢s σ' : Δ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve 4.    
(*   all: inversion_clear 1; *)
(*     (on_all_hyp: gen_presup_IH presup_exp_eq presup_sub_eq presup_subtyp); *)
(*     gen_core_presups; *)
(*     clear presup_exp_eq presup_sub_eq; *)
(*     repeat split; try mautosolve 3; *)
(*     try (eexists; unshelve solve [mauto 4 using lift_exp_max_left, lift_exp_max_right]; constructor). *)

  
(*   all: try (econstructor; mautosolve 4). *)
  
(*   (** presup_exp_eq cases *) *)
(*   - eapply exp_sub_typ; mauto 4 using lift_exp_max_left, lift_exp_max_right. *)

(*   (** presup_sub_eq cases *) *)

(*   - econstructor; mauto 3. *)
(*     eapply wf_conv... *)

(*   - enough {{ Γ ⊢ #0[σ] : A[Wk∘σ] }} by mauto 4. *)
(*     eapply wf_conv... *)
(* Qed. *)
Admitted.

           
Ltac gen_presup H := gen_presup_IH @presup_exp_eq @presup_sub_eq H + gen_core_presup H.

Ltac gen_presups := (on_all_hyp: fun H => gen_presup H); invert_wf_ctx; (on_all_hyp: fun H => gen_lookup_presup H); clear_dups.
