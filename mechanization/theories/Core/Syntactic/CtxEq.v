From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export System.
Import Syntax_Notations.


Lemma ctx_eq_refl {P : PtsSig} : forall {Γ : ctx P}, {{ ⊢ Γ }} -> {{ ⊢ Γ ≈ Γ }}.
Proof with mautosolve.
  induction 1; mauto 2.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve ctx_eq_refl : mcpts.

Lemma ctx_eq_sym {P : PtsSig} : forall {Γ Δ : ctx P}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ ≈ Γ }}.
Proof.
  intros.
  symmetry.
  eassumption.
Qed.

#[export]
Hint Resolve ctx_eq_sym : mcpts.

#[local]
Ltac gen_ctxeq_helper_IH ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper H :=
match type of H with
| {{ ^?Γ ⊢ ^?M : ^?A }} => pose proof ctxeq_exp_helper _ _ _ H
| {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} => pose proof ctxeq_exp_eq_helper _ _ _ _ H
| {{ ^?Γ ⊢s ^?σ : ^?Δ }} => pose proof ctxeq_sub_helper _ _ _ H
| {{ ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Δ }} => pose proof ctxeq_sub_eq_helper _ _ _ _ H
end.


#[local]
Lemma ctxeq_lookup_helper {P} : forall {Γ : ctx P} {x A s}, {{ #x : A : Sort@s ∈ Γ }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> exists A', {{ #x : A' : Sort@s ∈ Δ }} /\ {{ Γ ⊢ A ≈ A' : Sort@s }} /\ {{ Δ ⊢ A ≈ A' : Sort@s }}.
Proof.
  induction 1; intros.
  - inversion_clear H.
    assert {{ ⊢ Γ }} by mauto 2.
    assert {{ Γ, A:Sort@s0 ⊢s Wk : Γ }} by mauto 3.
    assert {{ ⊢ Γ0 }} by mauto 2.
    assert {{ Γ0, A0:Sort@s0 ⊢s Wk : Γ0 }} by mauto 3.
    eexists; repeat split; mauto 4.
  - inversion_clear H0.
    assert (exists A' : exp P, {{ # n : A' : Sort@s0 ∈ Γ0 }} /\ {{ Γ ⊢ A ≈ A' : Sort@s0 }} /\ {{ Γ0 ⊢ A ≈ A' : Sort@s0 }}) by mauto 2.
    destruct_conjs.
    assert {{ ⊢ Γ }} by mauto 2.
    assert {{ Γ, B:Sort@s1 ⊢s Wk : Γ }} by mauto 3.
    assert {{ ⊢ Γ0 }} by mauto 2.
    assert {{ Γ0, A0:Sort@s1 ⊢s Wk : Γ0 }} by mauto 3.
    eexists; repeat split; mauto 3.
Qed.


#[local]
Lemma ctxeq_exp_helper {P : PtsSig} : forall {Γ : ctx P} {M A}, {{ Γ ⊢ M : A }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢ M : A }}
with
ctxeq_exp_eq_helper {P : PtsSig} : forall {Γ : ctx P} {M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢ M ≈ M' : A }}
with
ctxeq_sub_helper {P : PtsSig} : forall {Γ : ctx P} {Γ' σ}, {{ Γ ⊢s σ : Γ' }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢s σ : Γ' }}
with
ctxeq_sub_eq_helper {P : PtsSig} : forall {Γ : ctx P} {Γ' σ σ'}, {{ Γ ⊢s σ ≈ σ' : Γ' }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
Proof with mautosolve.
  all: inversion_clear 1;
    (on_all_hyp: gen_ctxeq_helper_IH (@ctxeq_exp_helper P) (@ctxeq_exp_eq_helper P) (@ctxeq_sub_helper P) (@ctxeq_sub_eq_helper P));
    clear ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper;
    intros * HΓΔ; destruct (presup_ctx_eq HΓΔ); mauto 4;
    try (rename B into C); try (rename B' into C'); try (rename A0 into B); try (rename A' into B').
  
  (** Exp well-formedness cases *)
  (** Π and λ cases *)
  1,2,3:
    assert {{ Δ ⊢ B : Sort@s1 }} by mauto;
    assert {{ ⊢ Δ, B:Sort@s1 ≈ Γ, B:Sort@s1 }} by (econstructor; mauto 3);
    assert {{ Δ, B:Sort@s1 ⊢ C : Sort@s2 }} by mauto;
    econstructor; mauto.
    
  
  (** Variable case *)
  - assert (exists B, {{ #x : B : Sort@s ∈ Δ }} /\ {{ Γ ⊢ A ≈ B : Sort@s }} /\ {{ Δ ⊢ A ≈ B : Sort@s }}) by (eapply ctxeq_lookup_helper; mauto 2).
    destruct_conjs.
    
    eapply wf_exp_conv with (A := H5); mauto 2.
    
  (** Conversion case *)
  - assert {{ Δ ⊢ B ≈ A : Sort@s }} by mauto.
    eapply wf_exp_conv; mauto 2.
    
  (** Exp equality cases *)
  (** Π congruence case *)
  - assert {{ Δ ⊢ B : Sort@s1 }} by mauto.
    assert {{ Δ ⊢ B ≈ B' : Sort@s1 }} by mauto.
    assert {{ ⊢ Δ, B:Sort@s1 ≈ Γ, B:Sort@s1 }} by (econstructor; mauto 3).
    assert {{ Δ, B:Sort@s1 ⊢ C ≈ C' : Sort@s2 }} by mauto.
    mauto 2.

  (** λ congruence case *)
  - assert {{ Δ ⊢ B : Sort@s1 }} by mauto.
    assert {{ Δ ⊢ B ≈ B' : Sort@s1 }} by mauto.
    assert {{ ⊢ Δ, B:Sort@s1 ≈ Γ, B:Sort@s1 }} by (econstructor; mauto 3).
    assert {{ Δ, B:Sort@s1 ⊢ C : Sort@s2 }} by mauto.
    assert {{ Δ, B:Sort@s1 ⊢ M0 ≈ M'0 : C }} by mauto.
    mauto 2.
    
  (** Function application congruence case *)
  - assert {{ Δ ⊢ N ≈ N' : B }} by mauto.
    assert {{ Δ ⊢ M0 ≈ M'0 : Π r B C }} by mauto.
    assert {{ Δ ⊢ B : Sort@s1 }} by mauto.
    assert {{ ⊢ Δ, B:Sort@s1 ≈ Γ, B:Sort@s1 }} by (econstructor; mauto 3).
    assert {{ Δ, B:Sort@s1 ⊢ C : Sort@s2 }} by mauto.
    mauto 2.
    
  (** β case *)
  - assert {{ Δ ⊢ B : Sort@s1 }} by mauto.
    assert {{ ⊢ Δ, B:Sort@s1 ≈ Γ, B:Sort@s1 }} by (econstructor; mauto 3).
    assert {{ Δ, B:Sort@s1 ⊢ C : Sort@s2 }} by mauto.
    assert {{ Δ, B:Sort@s1 ⊢ M0 : C }} by mauto.
    assert {{ Δ ⊢ N : B }} by mauto.
    mauto 2.

  (** η case *)
  - assert {{ Δ ⊢ B : Sort@s1 }} by mauto.
    assert {{ ⊢ Δ, B:Sort@s1 ≈ Γ, B:Sort@s1 }} by (econstructor; mauto 3).
    assert {{ Δ, B:Sort@s1 ⊢ C : Sort@s2 }} by mauto.
    assert {{ Δ ⊢ M : Π r B C }} by mauto.
    mauto 2.

  (** Variable reflexivity case *)
  - assert (exists B, {{ #x : B : Sort@s ∈ Δ }} /\ {{ Γ ⊢ A ≈ B : Sort@s }} /\ {{ Δ ⊢ A ≈ B : Sort@s }} /\ {{ Δ ⊢ A : Sort@s }}) by mauto.
    destruct_conjs.
    eapply wf_exp_eq_conv; mauto.

  (** Variable weakening case *)
  - inversion_clear HΓΔ.
    assert {{ ⊢ Γ0, A0:Sort@s' }} by (econstructor; mauto 3).
    assert (exists B', {{ #x : B' : Sort@s ∈ Γ1 }} /\ {{ Γ0 ⊢ B ≈ B' : Sort@s }} /\ {{ Γ1 ⊢ B ≈ B' : Sort@s }} /\ {{ Γ1 ⊢ B : Sort@s }}) as [B'] by mauto.
    assert {{ ⊢ Γ1, A0:Sort@s' }} by mauto 3.
    assert {{ Γ1, A0:Sort@s' ⊢s Wk : Γ1 }} by mauto 3.
    destruct_conjs.
    eapply wf_exp_eq_conv; mauto 4.

  (** Conversion case *)
  - assert {{ Δ ⊢ M ≈ M' : A }} by mauto.
    assert {{ Δ ⊢ A : Sort@s }} by mauto.
    assert {{ Δ ⊢ B ≈ A : Sort@s }} by mauto.
    eapply wf_exp_eq_conv; mauto 2.
    
  (** sub_wf cases (only weakening *)
  - inversion_clear HΓΔ.
    eapply wf_sub_conv; mauto.

  (** Id expansion cases (only weakening reflexivity) *)
  - inversion_clear HΓΔ.
    mauto.
Qed.  (* I don't know why this Qed takes so long to check (faster than before) *)


Corollary ctxeq_exp {P : PtsSig} : forall {Γ : ctx P} {Δ M A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ M : A }} -> {{ Δ ⊢ M : A }}.
Proof.
  intros; eapply ctxeq_exp_helper; mauto.
Qed.

Corollary ctxeq_exp_eq {P : PtsSig} : forall {Γ : ctx P} {Δ M M' A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ M ≈ M' : A }} -> {{ Δ ⊢ M ≈ M' : A }}.
Proof.
  intros; eapply ctxeq_exp_eq_helper; mauto.
Qed.

Corollary ctxeq_typ {P : PtsSig} : forall {Γ : ctx P} {Δ A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ A }} -> {{ Δ ⊢ A }}.
Proof.
  intros.
  induction H0; mauto 3.
  assert {{ Δ ⊢ A : Sort@s }} by (eapply ctxeq_exp_helper; mauto 3).
  mauto 2.
Qed.

Corollary ctxeq_typ_eq {P : PtsSig} : forall {Γ : ctx P} {Δ A B}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ A ≈ B }} -> {{ Δ ⊢ A ≈ B }}.
Proof.
  induction 2.
  - assert {{ Δ ⊢ A }} by (eapply ctxeq_typ; mauto 2).
    mauto 2.
  - assert {{ Δ ⊢ A ≈ B : Sort@s }} by (eapply ctxeq_exp_eq_helper; mauto 2).
    mauto 2.
  - assert {{ Δ ⊢ B ≈ C : Sort@s }} by (eapply ctxeq_exp_eq_helper; mauto 2).
    assert {{ Δ ⊢ A ≈ B }} by mauto 2.
    mauto 2.    
Qed.

Corollary ctxeq_sub {P : PtsSig} : forall {Γ : ctx P} {Δ σ Γ'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ : Γ' }} -> {{ Δ ⊢s σ : Γ' }}.
Proof. intros; eapply ctxeq_sub_helper; mauto. Qed.

Corollary ctxeq_sub_eq {P : PtsSig} : forall {Γ : ctx P} {Δ σ σ' Γ'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
Proof. intros; eapply ctxeq_sub_eq_helper; mauto. Qed.

#[export]
Hint Resolve ctxeq_exp ctxeq_exp_eq ctxeq_typ ctxeq_typ_eq ctxeq_sub ctxeq_sub_eq : mcpts.


Lemma ctx_eq_trans {P : PtsSig} : forall {Γ0 Γ1 Γ2 : ctx P}, {{ ⊢ Γ0 ≈ Γ1 }} -> {{ ⊢ Γ1 ≈ Γ2 }} -> {{ ⊢ Γ0 ≈ Γ2 }}.
Proof with mautosolve.
  intros * HΓ01.
  gen Γ2.
  induction HΓ01; mauto.
  intros.
  inversion_clear H5.
  assert {{ ⊢ Γ ≈ Δ0 }} by mauto 2.
  econstructor; mauto 3.
  etransitivity; mauto 2.
  eapply ctxeq_exp_eq; mauto 2.
Qed.

#[export]
Hint Resolve ctx_eq_trans : mcpts.

#[export]
Instance wf_ctx_PER {P : PtsSig} : PER (@wf_ctx_eq P).
Proof.
  split.
  - eauto using ctx_eq_sym.
  - eauto using ctx_eq_trans.
Qed.



Add Parametric Morphism {P : PtsSig} : (@wf_exp P)
  with signature wf_ctx_eq ==> eq ==> eq ==> iff as ctxeq_exp_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P : PtsSig} : (@wf_exp_eq P)
  with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as ctxeq_exp_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P} : (@wf_typ P)
  with signature wf_ctx_eq ==> eq ==> iff as ctxeq_typ_morphism.
Proof.
  intros. split; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} : (@wf_typ_eq P)
  with signature wf_ctx_eq ==> eq ==> eq ==> iff as ctxeq_typ_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P : PtsSig} : (@wf_sub P)
  with signature wf_ctx_eq ==> eq ==> eq ==> iff as ctxeq_sub_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P : PtsSig} : (@wf_sub_eq P)
  with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as ctxeq_sub_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.
