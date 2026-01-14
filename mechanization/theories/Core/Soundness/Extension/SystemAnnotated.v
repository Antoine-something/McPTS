From Coq Require Import List Classes.RelationClasses Setoid Morphisms.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export Syntax System Corollaries.
Import Syntax_Notations.


Reserved Notation "⊫ Γ > sts " (in custom judg at level 80, Γ custom exp, sts constr).
Reserved Notation "Γ : sts ⊫ M : A > s" (in custom judg at level 80, Γ custom exp, sts constr, M custom exp, A custom exp, s constr).
Reserved Notation "Γ : sts ⊫ A > s" (in custom judg at level 80, Γ custom exp, sts constr, A custom exp, s constr).
Reserved Notation "Γ : sts ⊫s σ : Δ > sts'" (in custom judg at level 80, Γ custom exp, sts constr, σ custom exp, Δ custom exp, sts' constr).

Generalizable All Variables.

Inductive wf_ctx_ann {P} : ctx P -> list P -> Prop :=
| wfa_ctx_empty : {{ ⊫ ⋅ > nil }}
| wfa_ctx_extend :
  `( {{ ⊫ Γ > sts }} ->
     {{ Γ ⊢ A : Sort@s }} ->
     {{ ⊫ Γ, A > (s :: sts) }} )
where "⊫ Γ > sts" := (wf_ctx_ann Γ sts) (in custom judg) : type_scope.

#[export]
Hint Constructors wf_ctx_ann : mcpts.

Lemma wf_ctx_then_wf_ctx_ann {P} : forall {Γ : ctx P},
    {{ ⊢ Γ }} ->
    exists sts, {{ ⊫ Γ > sts }}.
Proof.
  induction 1; mauto 2.
  destruct_conjs.
  eexists; mauto 2.
Qed.

Lemma wf_ctx_ann_then_wf_ctx {P} : forall {Γ : ctx P} {sts},
    {{ ⊫ Γ > sts }} ->
    {{ ⊢ Γ }}.
Proof.
  induction 1; mauto 2.
Qed.


Inductive wf_exp_ann {P} : ctx P -> list P -> exp P -> exp P -> P -> Prop :=
| wf_st :
  `( Ax P s1 s2 -> Ax P s2 s3 ->
     {{ ⊫ Γ > sts }} ->
     {{ Γ : sts ⊫ Sort@s1 : Sort@s2 > s3 }} )
| wf_pi :
  `( forall (r : Ru P s1 s2 s3),
        Ax P s3 s3' ->
        {{ Γ : sts ⊫ A : Sort@s1 > s1' }} ->
        {{ Γ, A : (s1 :: sts) ⊫ B : Sort@s2 > s2' }} ->
        {{ Γ : sts ⊫ Π r A B : Sort@s3 > s3' }} )
where "Γ : sts ⊫ M : A > s" := (wf_exp_ann Γ sts M A s) (in custom judg) : type_scope.

Lemma wf_exp_ann_implies_wf_exp {P} : forall {Γ : ctx P} {sts M A s},
    {{ Γ : sts ⊫ M : A > s }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  induction 1;
    match goal with
    | H : {{ ⊫ ^?Γ > ?sts }} |- _ =>
        assert {{ ⊢ Γ }} by (eapply (wf_ctx_ann_then_wf_ctx H))
    | _ => idtac
    end;
    mauto 2.  
Qed.

Lemma wf_exp_implies_wf_exp_ann_helper {P} (full_P : FullSig P) : forall {Γ : ctx P} {sts M A},
    {{ Γ ⊢ M : A }} ->
    {{ ⊫ Γ > sts }} ->
    exists s,
      {{ Γ : sts ⊫ M : A > s }}.
Proof.
  intros * H.
  gen sts.
  induction H.
  - intros.
    assert (exists s3, Ax P s2 s3) as [s3] by (eapply full_P).
    eexists; econstructor; mauto 2.

  - intros.
    assert (exists s1', {{ Γ : sts ⊫ A : Sort@s1 > s1' }}) as [s1'] by mauto 2.
    assert {{ ⊫ Γ, A > (s1 :: sts) }} by mauto 2.
    assert (exists s2', {{ Γ, A : (s1 :: sts) ⊫ B : Sort@s2 > s2' }}) as [s2'] by mauto 2.
    assert (exists s3', Ax P s3 s3') as [s3'] by (eapply full_P).
    eexists; econstructor; mauto 2.
Admitted.

Lemma wf_exp_implies_wf_exp_ann {P} (full_P : FullSig P) : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    exists sts s,
      {{ Γ : sts ⊫ M : A > s }}.
Proof.
  intros * H.
  gen_presup H.
  assert (exists sts, {{ ⊫ Γ > sts }}) as [sts] by (eapply wf_ctx_then_wf_ctx_ann; mauto 2).
  eexists.
  eapply wf_exp_implies_wf_exp_ann_helper; mauto 2.
Qed.
