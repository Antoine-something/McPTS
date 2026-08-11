From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export System.
Import Syntax_Notations.

Lemma ctx_sub_refl {P} : forall {Γ : ctx P},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ ⊆ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve ctx_sub_refl : mcpts.

Module ctxsub_judg.
  #[local]
  Ltac gen_ctxsub_helper_IH ctxsub_exp_helper ctxsub_exp_eq_helper ctxsub_sub_helper ctxsub_sub_eq_helper ctxsub_subtyp_helper ctxsub_typ_helper ctxsub_typ_eq_helper H :=
  match type of H with
  | {{ ^?Γ ⊢ ^?M : ^?A }} => pose proof ctxsub_exp_helper _ _ _ _ H
  | {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} => pose proof ctxsub_exp_eq_helper _ _ _ _ _ H
  | {{ ^?Γ ⊢s ^?σ : ^?Δ }} => pose proof ctxsub_sub_helper _ _ _ _ H
  | {{ ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Δ }} => pose proof ctxsub_sub_eq_helper _ _ _ _ _ H
  | {{ ^?Γ ⊢ ^?M ⊆ ^?M' }} => pose proof ctxsub_subtyp_helper _ _ _ _ H
  | {{ ^?Γ ⊢ ^?A }} => pose proof ctxsub_typ_helper _ _ _ H
  | {{ ^?Γ ⊢ ^?A ≈ ^?A' }} => pose proof ctxsub_typ_eq_helper _ _ _ _ H
  end.

  #[local]
  Lemma ctxsub_exp_helper {P} : forall {Γ : ctx P} {M A}, {{ Γ ⊢ M : A }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M : A }}
  with
  ctxsub_exp_eq_helper {P} : forall {Γ : ctx P} {M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M ≈ M' : A }}
  with
  ctxsub_sub_helper {P} : forall {Γ Γ' : ctx P} {σ}, {{ Γ ⊢s σ : Γ' }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢s σ : Γ' }}
  with
  ctxsub_sub_eq_helper {P} : forall {Γ Γ' : ctx P} {σ σ'}, {{ Γ ⊢s σ ≈ σ' : Γ' }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}
  with
  ctxsub_subtyp_helper {P} : forall {Γ : ctx P} {M M'}, {{ Γ ⊢ M ⊆ M' }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M ⊆ M' }}
  with
  ctxsub_typ_helper {P} : forall {Γ : ctx P} {A}, {{ Γ ⊢ A }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ A }}
  with
  ctxsub_typ_eq_helper {P} : forall {Γ : ctx P} {A A'}, {{ Γ ⊢ A ≈ A' }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ A ≈ A' }}.
  Proof with mautosolve.
    all: inversion_clear 1;
      (on_all_hyp: gen_ctxsub_helper_IH ctxsub_exp_helper ctxsub_exp_eq_helper ctxsub_sub_helper ctxsub_sub_eq_helper ctxsub_subtyp_helper ctxsub_typ_helper ctxsub_typ_eq_helper);
      clear ctxsub_exp_helper ctxsub_exp_eq_helper ctxsub_sub_helper ctxsub_sub_eq_helper ctxsub_subtyp_helper ctxsub_typ_helper ctxsub_typ_eq_helper;
      intros * HΓΔ; destruct (presup_ctx_sub HΓΔ); mauto 4;
      try (rename B into C); try (rename B' into C'); try (rename A0 into B); try (rename A' into B').
    
    (** Function and Sigma cases *)
    6,18,20: rename A into B.
    1-9,13-22: assert {{ Δ ⊢ B : Sort@s1 }} by eauto; assert {{ ⊢ Δ, B ⊆ Γ, B }} by mauto;
    econstructor...
    
    (** Recursor cases *)
    2,4-6: assert {{ ⊢ Δ, ℕ ⊆ Γ, ℕ }} by (econstructor; mauto 3); assert {{ ⊢ Δ, ℕ, B ⊆ Γ, ℕ, B }} by (econstructor; mauto 5); econstructor...

    (** Variable cases *)
    1,3: assert (exists B, {{ #x : B ∈ Δ }} /\ {{ Δ ⊢ B ⊆ A }}) as [B []] by mauto 2; assert {{ Δ ⊢ #x : B }} by mauto 2; econstructor...

    (** Conversion cases *)
    1,3: econstructor...

    - (* wf_exp_eq, variable shift case *)
      inversion_clear HΓΔ.
      assert (exists B1, {{ #x : B1 ∈ Γ1 }} /\ {{ Γ1 ⊢ B1 ⊆ B }}) as [B1 []] by mauto 2.
      assert {{ ⊢ Γ1, A0 }} by mauto 3.
      econstructor...

    - inversion_clear HΓΔ.
      assert {{ ⊢ Γ0, A0 }} by mauto 3.
      eapply wf_sub_conv; mauto 3.
      
    - inversion_clear HΓΔ.
      assert {{ ⊢ Γ0, A0 }} by mauto 3.
      eapply wf_sub_eq_conv; mauto 3.

    - assert {{ Δ ⊢ B' }} by mauto 3.
      assert {{ ⊢ Δ, B' ⊆ Γ, B' }} by mauto 5.
      assert {{ Δ ⊢ A }} by mauto 3.
      assert {{ ⊢ Δ, A ⊆ Γ, A }} by mauto 5.
      assert {{ Δ, B' ⊢ C ⊆ C' }} by mauto 2.
      assert {{ Δ, B' ⊢ C' }} by mauto 2.
      assert {{ Δ, A ⊢ C }} by mauto 3.
      assert {{ Δ ⊢ A ≈ B' }} by mauto 3.
      econstructor...
    - assert {{ Δ ⊢ B' }} by mauto 3.
      assert {{ ⊢ Δ, B' ⊆ Γ, B' }} by mauto 5.
      assert {{ Δ ⊢ A }} by mauto 3.
      assert {{ ⊢ Δ, A ⊆ Γ, A }} by mauto 5.
      assert {{ Δ, B' ⊢ C ⊆ C' }} by mauto 2.
      assert {{ Δ, B' ⊢ C' }} by mauto 2.
      assert {{ Δ, A ⊢ C }} by mauto 3.
      assert {{ Δ ⊢ A ≈ B' }} by mauto 3.
      econstructor...    
  Qed.

  
  Corollary ctxsub_exp {P} : forall {Γ : ctx P} {Δ M A}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢ M : A }} -> {{ Δ ⊢ M : A }}.
  Proof.
    eauto using ctxsub_exp_helper.
  Qed.

  Corollary ctxsub_exp_eq {P} : forall {Γ : ctx P} {Δ M M' A}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢ M ≈ M' : A }} -> {{ Δ ⊢ M ≈ M' : A }}.
  Proof.
    eauto using ctxsub_exp_eq_helper.
  Qed.

  Corollary ctxsub_sub {P} : forall {Γ : ctx P} {Δ σ Γ'}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢s σ : Γ' }} -> {{ Δ ⊢s σ : Γ' }}.
  Proof.
    eauto using ctxsub_sub_helper.
  Qed.

  Corollary ctxsub_sub_eq {P} : forall {Γ : ctx P} {Δ σ σ' Γ'}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
  Proof.
    eauto using ctxsub_sub_eq_helper.
  Qed.

  Corollary ctxsub_subtyp {P} : forall {Γ : ctx P} {Δ A B}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢ A ⊆ B }} -> {{ Δ ⊢ A ⊆ B }}.
  Proof.
    eauto using ctxsub_subtyp_helper.
  Qed.

  Corollary ctxsub_typ {P} : forall {Γ : ctx P} {Δ A}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢ A }} -> {{ Δ ⊢ A }}.
  Proof.
    eauto using ctxsub_typ_helper.
  Qed.
  
  Corollary ctxsub_typ_eq {P} : forall {Γ : ctx P} {Δ A A'}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢ A ≈ A' }} -> {{ Δ ⊢ A ≈ A' }}.
  Proof.
    eauto using ctxsub_typ_eq_helper.
  Qed.
  
  #[export]
  Hint Resolve ctxsub_exp ctxsub_exp_eq ctxsub_sub ctxsub_sub_eq ctxsub_subtyp ctxsub_typ ctxsub_typ_eq : mcpts.
End ctxsub_judg.

Export ctxsub_judg.

Lemma wf_ctx_sub_trans {P} : forall (Γ0 : ctx P) Γ1,
    {{ ⊢ Γ0 ⊆ Γ1 }} ->
    forall  Γ2,
    {{ ⊢ Γ1 ⊆ Γ2 }} ->
    {{ ⊢ Γ0 ⊆ Γ2 }}.
Proof.
  induction 1; intros; progressive_inversion; [constructor |].
  eapply wf_ctx_sub_extend; mauto 3.
Qed.

#[export]
Hint Resolve wf_ctx_sub_trans : mcpts.

#[export]
Instance wf_ctx_sub_trans_ins {P} : Transitive (@wf_ctx_sub P).
Proof. eauto using wf_ctx_sub_trans. Qed.

Add Parametric Morphism {P} : (@wf_exp P)
  with signature wf_ctx_sub --> eq ==> eq ==> Basics.impl as ctxsub_exp_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_exp_eq P)
  with signature wf_ctx_sub --> eq ==> eq ==> eq ==> Basics.impl as ctxsub_exp_eq_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_sub P)
  with signature wf_ctx_sub --> eq ==> eq ==> Basics.impl as ctxsub_sub_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_sub_eq P)
  with signature wf_ctx_sub --> eq ==> eq ==> eq ==> Basics.impl as ctxsub_sub_eq_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_subtyp P)
  with signature wf_ctx_sub --> eq ==> eq ==> Basics.impl as ctxsub_subtyp_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.
