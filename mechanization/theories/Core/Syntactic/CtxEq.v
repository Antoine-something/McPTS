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
Ltac gen_ctxeq_helper_IH ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_typ_helper ctxeq_typ_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper H :=
match type of H with
| {{ ^?Γ ⊢ ^?M : ^?A }} => pose proof ctxeq_exp_helper _ _ _ H
| {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} => pose proof ctxeq_exp_eq_helper _ _ _ _ H
| {{ ^?Γ ⊢ ^?A }} => pose proof ctxeq_typ_helper _ _ H
| {{ ^?Γ ⊢ ^?A ≈ ^?B }} => pose proof ctxeq_typ_eq_helper _ _ _ H
| {{ ^?Γ ⊢s ^?σ : ^?Δ }} => pose proof ctxeq_sub_helper _ _ _ H
| {{ ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Δ }} => pose proof ctxeq_sub_eq_helper _ _ _ _ H
end.

#[local]
  Lemma ctxeq_lookup_helper {P} : forall {Γ : ctx P} {x A}, {{ #x : A ∈ Γ }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> exists A', {{ #x : A' ∈ Δ }} /\ {{ Γ ⊢ A ≈ A' }} /\ {{ Δ ⊢ A ≈ A' }}.
Proof.
  induction 1; intros.
  - inversion_clear H.
    assert {{ ⊢ Γ }} by mauto 2.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ ⊢ Γ0 }} by mauto 2.
    assert {{ Γ0, A0 ⊢s Wk : Γ0 }} by mauto 3.
    eexists; repeat split; mauto 4.
  - inversion_clear H0.
    assert (exists A' : exp P, {{ # n : A' ∈ Γ0 }} /\ {{ Γ ⊢ A ≈ A' }} /\ {{ Γ0 ⊢ A ≈ A' }}) by mauto 2.
    destruct_conjs.
    assert {{ ⊢ Γ }} by mauto 2.
    assert {{ Γ, B ⊢s Wk : Γ }} by mauto 3.
    assert {{ ⊢ Γ0 }} by mauto 2.
    assert {{ Γ0, A0 ⊢s Wk : Γ0 }} by mauto 3.
    eexists; repeat split; mauto 3.

Qed.

#[local]
Lemma ctxeq_exp_helper {P : PtsSig} : forall {Γ : ctx P} {M A}, {{ Γ ⊢ M : A }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢ M : A }}
with
ctxeq_exp_eq_helper {P : PtsSig} : forall {Γ : ctx P} {M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢ M ≈ M' : A }}
with
ctxeq_typ_helper {P : PtsSig} : forall {Γ : ctx P} {A}, {{ Γ ⊢ A }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢ A }}
with
ctxeq_typ_eq_helper {P : PtsSig} : forall {Γ : ctx P} {A B}, {{ Γ ⊢ A ≈ B }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢ A ≈ B }}
with
ctxeq_sub_helper {P : PtsSig} : forall {Γ : ctx P} {Γ' σ}, {{ Γ ⊢s σ : Γ' }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢s σ : Γ' }}
with
ctxeq_sub_eq_helper {P : PtsSig} : forall {Γ : ctx P} {Γ' σ σ'}, {{ Γ ⊢s σ ≈ σ' : Γ' }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
Proof with mautosolve.
  all: inversion_clear 1;
    (on_all_hyp: gen_ctxeq_helper_IH (@ctxeq_exp_helper P) (@ctxeq_exp_eq_helper P) (@ctxeq_typ_helper P) (@ctxeq_typ_eq_helper P) (@ctxeq_sub_helper P) (@ctxeq_sub_eq_helper P));
    clear ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_typ_helper ctxeq_typ_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper;
    intros * HΓΔ; destruct (presup_ctx_eq HΓΔ); mauto 4;
    try (rename B into C); try (rename B' into C'); try (rename A0 into B); try (rename A' into B').

  (** Exp well-formedness cases *)
  (** Π and λ cases *)
  1,2,3:
    assert {{ Δ ⊢ B : Sort@s1 }} by mauto;
    assert {{ ⊢ Δ, B ≈ Γ, B }} by (econstructor; mauto 3);
    assert {{ Δ, B ⊢ C : Sort@s2 }} by mauto;
    econstructor; mauto.
    
  
  (** Variable case *)
  - assert (exists B, {{ #x : B ∈ Δ }} /\ {{ Γ ⊢ A ≈ B }} /\ {{ Δ ⊢ A ≈ B }}) by (eapply ctxeq_lookup_helper; mauto 2).
    destruct_conjs.
    
    eapply wf_exp_conv with (A := H5); mauto 2.
    assert (exists s, {{ Δ ⊢ H5 : Sort@s }}) as [] by mauto 3.
    econstructor; mauto 2.
    
  (** Natural recursion case **)
  - assert {{ Δ ⊢ MZ : B[Id,,zero] }} by mauto.
    assert {{ Δ ⊢ M0 : ℕ }} by mauto.
    assert {{ ⊢ Δ, ℕ ≈ Γ, ℕ }} by (econstructor; mauto 4).
    assert {{ ⊢ Δ, ℕ, B ≈ Γ, ℕ, B }} by (econstructor; mauto 4).
    assert {{ Δ, ℕ, B ⊢ MS : B[Wk∘Wk,,succ #1] }} by mauto.
    mauto.

  (** Conversion case *)
  - assert {{ Δ ⊢ B ≈ A }} by mauto.
    assert {{ Δ ⊢ A }} by mauto.
    assert {{ Δ ⊢ M : B }} by mauto.
    mauto 2.
    
  (** Exp equality cases *)
  (** Π congruence case *)
  - assert {{ Δ ⊢ B : Sort@s1 }} by mauto.
    assert {{ Δ ⊢ B ≈ B' : Sort@s1 }} by mauto.
    assert {{ ⊢ Δ, B ≈ Γ, B }} by (econstructor; mauto 3).
    assert {{ Δ, B ⊢ C ≈ C' : Sort@s2 }} by mauto.
    mauto 2.

  (** λ congruence case *)
  - assert {{ Δ ⊢ B : Sort@s1 }} by mauto.
    assert {{ Δ ⊢ B ≈ B' : Sort@s1 }} by mauto.
    assert {{ ⊢ Δ, B ≈ Γ, B }} by (econstructor; mauto 3).
    assert {{ Δ, B ⊢ C : Sort@s2 }} by mauto.
    assert {{ Δ, B ⊢ M0 ≈ M'0 : C }} by mauto.
    mauto 2.
    
  (** Function application congruence case *)
  - assert {{ Δ ⊢ N ≈ N' : B }} by mauto.
    assert {{ Δ ⊢ M0 ≈ M'0 : Π r B C }} by mauto.
    assert {{ Δ ⊢ B : Sort@s1 }} by mauto.
    assert {{ ⊢ Δ, B ≈ Γ, B }} by (econstructor; mauto 3).
    assert {{ Δ, B ⊢ C : Sort@s2 }} by mauto.
    mauto 2.
    
  (** β case *)
  - assert {{ Δ ⊢ B : Sort@s1 }} by mauto.
    assert {{ ⊢ Δ, B ≈ Γ, B }} by (econstructor; mauto 3).
    assert {{ Δ, B ⊢ C : Sort@s2 }} by mauto.
    assert {{ Δ, B ⊢ M0 : C }} by mauto.
    assert {{ Δ ⊢ N : B }} by mauto.
    mauto 2.

  (** η case *)
  - assert {{ Δ ⊢ B : Sort@s1 }} by mauto.
    assert {{ ⊢ Δ, B ≈ Γ, B }} by (econstructor; mauto 3).
    assert {{ Δ, B ⊢ C : Sort@s2 }} by mauto.
    assert {{ Δ ⊢ M : Π r B C }} by mauto.
    mauto 2.

  (** Natural recursion congruence case **)
  - assert {{ Δ ⊢ MZ ≈ MZ' : B[Id,,zero] }} by mauto.
    assert {{ Δ ⊢ M0 ≈ M'0 : ℕ }} by mauto.
    assert {{ ⊢ Δ, ℕ ≈ Γ, ℕ }} by (econstructor; mauto 4).
    assert {{ ⊢ Δ, ℕ, B ≈ Γ, ℕ, B }} by (econstructor; mauto 4).
    assert {{ Δ, ℕ, B ⊢ MS ≈ MS' : B[Wk∘Wk,,succ #1] }} by mauto.
    mauto.

  (** Natural recursion base case **)
  - assert {{ ⊢ Δ, ℕ ≈ Γ, ℕ }} by (econstructor; mauto 4).
    assert {{ ⊢ Δ, ℕ, B ≈ Γ, ℕ, B }} by (econstructor; mauto 4).
    assert {{ Δ, ℕ ⊢ B : Sort@s' }} by mauto.
    assert {{ Δ ⊢ M' : B[Id,,zero] }} by mauto.
    assert {{ Δ, ℕ, B ⊢ MS : B[Wk∘Wk,,succ #1] }} by mauto.
    mauto.

  (** Natural recursion succ case **)
  - assert {{ ⊢ Δ, ℕ ≈ Γ, ℕ }} by (econstructor; mauto 4).
    assert {{ ⊢ Δ, ℕ, B ≈ Γ, ℕ, B }} by (econstructor; mauto 4).
    assert {{ Δ ⊢ M0 : ℕ }} by mauto.
    assert {{ Δ, ℕ, B ⊢ MS : B[Wk∘Wk,,succ #1] }} by mauto.
    mauto.

  (** Variable reflexivity case *)
  - assert (exists B s, {{ #x : B ∈ Δ }} /\ {{ Γ ⊢ A ≈ B }} /\ {{ Δ ⊢ A ≈ B }} /\ {{ Δ ⊢ A : Sort@s }}) by mauto.
    destruct_conjs.
    eapply wf_exp_eq_conv; mauto.

  (** Variable weakening case *)
  - inversion_clear HΓΔ.
    assert {{ ⊢ Γ1, A0 }} by (econstructor; mauto 3).
    assert (exists B1 s', {{ #x : B1 ∈ Γ1 }} /\ {{ Γ0 ⊢ B ≈ B1 }} /\ {{ Γ1 ⊢ B ≈ B1 }} /\ {{ Γ1 ⊢ B : Sort@s' }}) by mauto.
    destruct_conjs.
    eapply wf_exp_eq_conv; mauto 4.

  (** Conversion case *)
  - assert {{ Δ ⊢ M ≈ M' : B }} by mauto.
    assert {{ Δ ⊢ A }} by mauto.
    assert {{ Δ ⊢ B ≈ A }} by mauto.
    mauto 2.
    
  (** sub_wf cases (only weakening *)
  - inversion_clear HΓΔ.
    eapply wf_sub_conv; mauto.

  (** Id expansion cases (only weakening reflexivity) *)
  - inversion_clear HΓΔ.
    mauto.
Qed.  (* I don't know why this Qed takes so long to check *)


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
  intros; eapply ctxeq_typ_helper; mauto.
Qed.

Corollary ctxeq_typ_eq {P : PtsSig} : forall {Γ : ctx P} {Δ A B}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ A ≈ B }} -> {{ Δ ⊢ A ≈ B }}.
Proof.
  intros; eapply ctxeq_typ_eq_helper; mauto.
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
  induction HΓ01 as [|Γ0 ? s01 T0 s01' T1]; mauto.
  inversion_clear 1 as [|? Γ2' s12 ? s12' T2].
  clear Γ2; rename Γ2' into Γ2.
  assert {{ ⊢ Γ0 ≈ Γ2 }} by mauto.
  assert {{ Γ0 ⊢ T2 : Sort@s12' }} by mauto 3.
  assert {{ Γ2 ⊢ T0 : Sort@s01 }} by mauto 3.
  assert {{ Γ0 ⊢ T0 ≈ T2 }} by (transitivity T1; mauto 4).
  assert {{ Γ2 ⊢ T0 ≈ T2 }} by (transitivity T1; mauto 4).
  econstructor; mauto 3.
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
