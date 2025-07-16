From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export System.
Import Syntax_Notations.

Lemma ctx_eq_refl {P : PtsSig} : forall {Γ : Ctx P}, {{ ⊢ Γ }} -> {{ ⊢ Γ ≈ Γ }}.
Proof with mautosolve.
  intros *.
  induction 1; econstructor; mauto 2; econstructor; mauto 2.
Qed.

#[export]
Hint Resolve ctx_eq_refl : mcpts.

Lemma ctx_eq_sym {P : PtsSig} : forall {Γ Δ : Ctx P}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ ≈ Γ }}.
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
Lemma ctxeq_exp_helper {P : PtsSig} : forall {Γ : Ctx P} {M A}, {{ Γ ⊢ M : A }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢ M : A }}
with
ctxeq_exp_eq_helper {P : PtsSig} : forall {Γ : Ctx P} {M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢ M ≈ M' : A }}
with
ctxeq_typ_helper {P : PtsSig} : forall {Γ : Ctx P} {A}, {{ Γ ⊢ A }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢ A }}
with
ctxeq_typ_eq_helper {P : PtsSig} : forall {Γ : Ctx P} {A B}, {{ Γ ⊢ A ≈ B }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢ A ≈ B }}
with
ctxeq_sub_helper {P : PtsSig} : forall {Γ : Ctx P} {Γ' σ}, {{ Γ ⊢s σ : Γ' }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢s σ : Γ' }}
with
ctxeq_sub_eq_helper {P : PtsSig} : forall {Γ : Ctx P} {Γ' σ σ'}, {{ Γ ⊢s σ ≈ σ' : Γ' }} -> forall {Δ}, {{ ⊢ Δ ≈ Γ }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
Proof with mautosolve.
  all: inversion_clear 1;
    (on_all_hyp: gen_ctxeq_helper_IH (@ctxeq_exp_helper P) (@ctxeq_exp_eq_helper P) (@ctxeq_typ_helper P) (@ctxeq_typ_eq_helper P) (@ctxeq_sub_helper P) (@ctxeq_sub_eq_helper P));
    clear ctxeq_exp_helper ctxeq_exp_eq_helper ctxeq_typ_helper ctxeq_typ_eq_helper ctxeq_sub_helper ctxeq_sub_eq_helper;
    intros * HΓΔ; destruct (presup_ctx_eq HΓΔ); mauto 4;
    try (rename B into C); try (rename B' into C'); try (rename A0 into B); try (rename A' into B').

  (** Exp well-formedness cases *)
  (** Π and λ cases *)
  2,3: assert {{ Δ ⊢ B : Sort@s1 }} by mauto; econstructor; mauto.
  
  (** Variable case *)
  - assert (exists B, {{ #i : B :: Sort@s ∈ Δ }} /\ {{ Δ ⊢ B ≈ A : Sort@s }} /\ {{ Δ ⊢ A : Sort@s }}) by mauto.
    destruct_conjs.
    eapply wf_exp_conv; mauto 2.    

  (** Function application case *)  
  - assert {{ Δ ⊢ N : B }} by mauto.
    assert {{ Δ ⊢ M0 : Π r B C }} by mauto.
    assert {{ Δ ⊢ B : Sort@s1 }} by mauto.
    assert {{ Δ, B::Sort@s1 ⊢ C : Sort@s2 }} by mauto.    
    assert {{ Δ ⊢ Π r B C : Sort@s3 }} by mauto.
    mauto 2.

  (** Conversion case *)
  - assert {{ Δ ⊢ B ≈ A }} by mauto.
    assert {{ Δ ⊢ A }} by mauto.
    assert {{ Δ ⊢ M : B }} by mauto.
    mauto 2.
    
  (** Exp equality cases *)
  (** β case *)
  - assert {{ Δ ⊢ N : B }} by mauto.
    assert {{ Δ ⊢ B : Sort@s1 }} by mauto.
    assert {{ Δ, B::Sort@s1 ⊢ M0 : C }} by mauto.
    mauto 2.

  (** Π congruence case *)
  - assert {{ Δ ⊢ A1 : Sort@s1 }} by mauto.
    assert {{ Δ ⊢ A1 ≈ A2 : Sort@s1 }} by mauto.
    assert {{ Δ, A1::Sort@s1 ⊢ B1 ≈ B2 : Sort@s2 }} by mauto.
    mauto 2.

  (** λ congruence case *)
  - assert {{ Δ ⊢ A1 : Sort@s1 }} by mauto.
    assert {{ Δ ⊢ A1 ≈ A2 : Sort@s1 }} by mauto.
    assert {{ Δ, A1::Sort@s1 ⊢ M1 ≈ M2 : C }} by mauto.
    mauto 2.

  (** Function application congruence case *)
  - assert {{ Δ ⊢ N1 ≈ N2 : B }} by mauto.
    assert {{ Δ ⊢ M1 ≈ M2 : Π r B C }} by mauto.
    assert {{ Δ ⊢ Π r B C : Sort@s3 }} by mauto.
    mauto 2.

  (** sub_wf cases *)
  - inversion_clear HΓΔ.
    eapply wf_sub_conv; mauto.

  (** Id expansion cases *)
  - inversion_clear HΓΔ.
    mauto.

  - inversion_clear HΓΔ.
    eapply eq_sub_conv; mauto.    
Qed.  (* I don't know why this Qed takes so long to check *)


Corollary ctxeq_exp {P : PtsSig} : forall {Γ : Ctx P} {Δ M A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ M : A }} -> {{ Δ ⊢ M : A }}.
Proof.
  intros; eapply ctxeq_exp_helper; mauto.
Qed.

Corollary ctxeq_exp_eq {P : PtsSig} : forall {Γ : Ctx P} {Δ M M' A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ M ≈ M' : A }} -> {{ Δ ⊢ M ≈ M' : A }}.
Proof.
  intros; eapply ctxeq_exp_eq_helper; mauto.
Qed.

Corollary ctxeq_typ {P : PtsSig} : forall {Γ : Ctx P} {Δ A}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ A }} -> {{ Δ ⊢ A }}.
Proof.
  intros; eapply ctxeq_typ_helper; mauto.
Qed.

Corollary ctxeq_typ_eq {P : PtsSig} : forall {Γ : Ctx P} {Δ A B}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ A ≈ B }} -> {{ Δ ⊢ A ≈ B }}.
Proof.
  intros; eapply ctxeq_typ_eq_helper; mauto.
Qed.

Corollary ctxeq_sub {P : PtsSig} : forall {Γ : Ctx P} {Δ σ Γ'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ : Γ' }} -> {{ Δ ⊢s σ : Γ' }}.
Proof. intros; eapply ctxeq_sub_helper; mauto. Qed.

Corollary ctxeq_sub_eq {P : PtsSig} : forall {Γ : Ctx P} {Δ σ σ' Γ'}, {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
Proof. intros; eapply ctxeq_sub_eq_helper; mauto. Qed.

#[export]
Hint Resolve ctxeq_exp ctxeq_exp_eq ctxeq_sub ctxeq_sub_eq : mcpts.


Lemma ctx_eq_trans {P : PtsSig} : forall {Γ0 Γ1 Γ2 : Ctx P}, {{ ⊢ Γ0 ≈ Γ1 }} -> {{ ⊢ Γ1 ≈ Γ2 }} -> {{ ⊢ Γ0 ≈ Γ2 }}.
Proof with mautosolve.
  intros * HΓ01.
  gen Γ2.
  induction HΓ01 as [|Γ0 ? s01 T0 T1]; mauto.
  inversion_clear 1 as [|? Γ2' s12 ? T2].
  clear Γ2; rename Γ2' into Γ2.
  assert {{ ⊢ Γ0 ≈ Γ2 }} by mauto.
  assert {{ Γ0 ⊢ T0 ≈ T2 : Sort@s01 }}.
  {
    transitivity {{{ T1 }}}; mauto.
  }
  econstructor...
Qed.

#[export]
Hint Resolve ctx_eq_trans : mcpts.

#[export]
Instance wf_ctx_PER {P : PtsSig} : PER (@eq_ctx P).
Proof.
  split.
  - eauto using ctx_eq_sym.
  - eauto using ctx_eq_trans.
Qed.



Add Parametric Morphism {P : PtsSig} : (@wf_exp P)
  with signature eq_ctx ==> eq ==> eq ==> iff as ctxeq_exp_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P : PtsSig} : (@eq_exp P)
  with signature eq_ctx ==> eq ==> eq ==> eq ==> iff as ctxeq_exp_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P : PtsSig} : (@wf_sub P)
  with signature eq_ctx ==> eq ==> eq ==> iff as ctxeq_sub_morphism.
Proof.
  intros. split; mauto 3.
Qed.


Add Parametric Morphism {P : PtsSig} : (@eq_sub P)
  with signature eq_ctx ==> eq ==> eq ==> eq ==> iff as ctxeq_sub_eq_morphism.
Proof.
  intros. split; mauto 3.
Qed.
