From Coq Require Import List Classes.RelationClasses Setoid Morphisms.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export Syntax System Corollaries.
Import Syntax_Notations.


Reserved Notation "⊫ Γ" (in custom judg at level 80, Γ custom exp).
Reserved Notation "Γ ⊫ M : A > s" (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp, s custom exp).
Reserved Notation "Γ ⊫ A > s" (in custom judg at level 80, Γ custom exp, A custom exp, s custom exp).
Reserved Notation "Γ ⊫s σ : Δ" (in custom judg at level 80, Γ custom exp, σ custom exp, Δ custom exp).

Generalizable All Variables.

Inductive wf_ctx_ann {P} : ctx P -> Prop :=
| wfa_ctx_empty : {{ ⊫ ⋅ }}
| wfa_ctx_enxtend :
  `( {{ ⊫ Γ }} ->
     {{ Γ ⊫ A : Sort@s > s' }} ->
     {{ ⊫ Γ, A@s }} )
where "⊫ Γ" := (wf_ctx_ann Γ) (in custom judg) : type_scope
with wf_exp_ann {P} : ctx P -> typ P -> P -> exp P -> Prop :=
(** Sorts *)
| wfa_st :
  `( Ax P s1 s2 -> Ax P s2 s3 ->
     {{ ⊫ Γ }} ->
     {{ Γ ⊫ Sort@s1 : Sort@s2 > s3 }} )

(** Functions *)
| wfa_pi :
  `( forall (r : Ru P s1 s2 s3),
        Ax P s3 s3' ->
        {{ Γ ⊫ A : Sort@s1 > s1' }} ->
        {{ Γ, A@s1 ⊫ B : Sort@s2 > s2' }} ->
        {{ Γ ⊫ Π r A B : Sort@s3 > s3' }} )
| wfa_fn :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊫ A : Sort@s1 > s1' }} ->
        {{ Γ, A@s1 ⊫ B : Sort@s2 > s2' }} ->
        {{ Γ, A@s1 ⊫ M : B > s2 }} ->
        {{ Γ ⊫ λ r A M : Π r A B > s3 }} )
| wfa_app :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ ⊫ A : Sort@s1 > s1' }} ->
        {{ Γ, A@s1 ⊫ B : Sort@s2 > s2' }} ->
        {{ Γ ⊫ M : Π r A B > s3 }} ->
        {{ Γ ⊫ N : A > s1 }} ->
        {{ Γ ⊫ M N : B[Id,,N] > s2 }} )

(** Variables *)
| wfa_vlookup :
  `( {{ ⊫ Γ }} ->
     (** This premise is redundant, but helpful for soundness *)
     {{ #x : A@s ∈ Γ }} ->
     {{ Γ ⊫ #x : A > s }} )

(** explicit substitutions *)
| wfa_exp_sub_typ :
  `( {{ Γ ⊫s σ : Δ }} ->
     {{ Δ ⊫ M : A > s }} ->
     {{ Δ ⊫ A : Sort@s > s' }} ->
     {{ Γ ⊫ M[σ] : A[σ] > s }} )
| wfa_exp_sub_sort :
  `( {{ Γ ⊫s σ : Δ }} ->
     {{ Δ ⊫ A : Sort@s > s' }} ->
     {{ Γ ⊫ A[σ] : Sort@s > s' }} )

(** Conversions *)
| wfa_exp_conv :
  `( {{ Γ ⊫ M : A > s }} ->
     {{ Γ ⊫ A' : Sort@s > s' }} ->
     {{ Γ ⊢ A ≈ A' : Sort@s }} ->
     {{ Γ ⊫ M : A' > s }} )
| wfa_exp_conv_ann :
  `( {{ Γ ⊫ M : A > s }} ->
     {{ Γ ⊫ A > s' }} ->
     {{ Γ ⊫ M : A > s' }} )
where "Γ ⊫ M : A > s" := (wf_exp_ann Γ A s M) (in custom judg) : type_scope

with wf_typ_ann {P} : ctx P -> typ P -> P -> Prop :=
| wfa_typ_st :
  `( Ax P s s' ->
     {{ ⊫ Γ }} ->
     {{ Γ ⊫ Sort@s > s' }} )
| wfa_typ_exp :
  `( {{ Γ ⊫ A : Sort@s > s' }} ->
     {{ Γ ⊫ A > s }} )
where "Γ ⊫ A > s" := (wf_typ_ann Γ A s) (in custom judg) : type_scope
with wf_sub_ann {P} : ctx P -> ctx P -> sub P -> Prop :=
| wfa_sub_id :
  `( {{ ⊫ Γ }} ->
     {{ Γ ⊫s Id : Γ }} )
| wfa_sub_weaken :
  `( {{ ⊫ Γ, A@s }} ->
     {{ Γ, A@s ⊫s Wk : Γ }} )
| wfa_sub_compose :
  `( {{ Γ1 ⊫s σ2 : Γ2 }} ->
     {{ Γ2 ⊫s σ1 : Γ3 }} ->
     {{ Γ1 ⊫s σ1∘σ2 : Γ3 }} )
| wfa_sub_extend :
  `( {{ Γ ⊫s σ : Δ }} ->
     {{ Δ ⊫ A : Sort@s > s' }} ->
     {{ Γ ⊫ M : A[σ] > s }} ->
     {{ Γ ⊫s σ,,M : Δ, A@s }} )
| wfa_sub_conv :
  `( {{ Γ ⊫s σ : Δ }} ->
     {{ ⊫ Δ' }} ->
     {{ ⊢ Δ ≈ Δ' }} ->
     {{ Γ ⊫s σ : Δ' }} )
where "Γ ⊫s σ : Δ" := (wf_sub_ann Γ Δ σ) (in custom judg) : type_scope.

#[export]
Hint Constructors wf_ctx_ann wf_exp_ann wf_typ_ann wf_sub_ann : mcpts.


Scheme wf_ctx_ann_mut_ind := Induction for wf_ctx_ann Sort Prop
with  wf_exp_ann_mut_ind := Induction for wf_exp_ann Sort Prop
with wf_typ_ann_mut_ind := Induction for wf_typ_ann Sort Prop
with wf_sub_ann_mut_ind := Induction for wf_sub_ann Sort Prop.
Combined Scheme syntactic_wf_ann_mut_ind from
  wf_ctx_ann_mut_ind,
  wf_exp_ann_mut_ind,
  wf_typ_ann_mut_ind,
  wf_sub_ann_mut_ind.

#[local]
Ltac apply_fullness_once P full_P H :=
  match type of H with
  | Ax P ?s1 ?s2 =>
      let s2' := fresh "s2'" in
      assert (exists s2', Ax P s2 s2') as [s2'] by (eapply full_P)
  | Ru P ?s1 ?s2 ?s3 =>
      let s3' := fresh "s3'" in
      assert (exists s3', Ax P s3 s3') as [s3'] by (eapply full_P)
  | _ => idtac
  end.

#[local]
Ltac apply_fullness_all P full_P :=
  on_all_hyp: (fun H => apply_fullness_once P full_P H).


#[local]
Ltac gen_annotated_judg_IH P full_P ann_ctx ann_exp ann_sub H :=
  match type of H with
  | {{ ⊢ ^?Γ }} =>
      let HΓ := fresh "HΓ" in
      pose proof ann_ctx P full_P Γ H as HΓ
  | {{ ^?Γ ⊢ ^?M : ^?A }} =>
      let HM := fresh "HM" in
      pose proof ann_exp P full_P Γ M A H as HM
  | {{ ^?Γ ⊢s ^?σ : ^?Δ }} =>
      let Hσ := fresh "Hσ" in
      pose proof ann_sub P full_P Γ σ Δ H as Hσ
  end.




Lemma wf_ctx_implies_wf_ctx_ann {P} (full_P : FullSig P) : forall {Γ : ctx P},
    {{ ⊢ Γ }} -> {{ ⊫ Γ }}
with wf_exp_implies_wf_exp_ann {P} (full_P : FullSig P) : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} -> exists s, {{ Γ ⊫ M : A > s }}
with wf_sub_implies_wf_sub_ann {P} (full_P : FullSig P) : forall {Γ : ctx P} {σ Δ},
    {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊫s σ : Δ }}.
Proof.
  all: inversion_clear 1;
    (on_all_hyp: gen_annotated_judg_IH P full_P wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_sub_implies_wf_sub_ann);
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_sub_implies_wf_sub_ann;
    destruct_conjs;
    apply_fullness_all P full_P;
    mauto 3.

  - eexists; econstructor; mauto 3.
  - assert {{ Γ ⊫ Π r A0 B : Sort@s3 > s3' }} by mauto 3.
    assert {{ Γ ⊫ Π r A0 B > s3 }} by mauto 3.
    assert {{ Γ ⊫ M0 : Π r A0 B > s3 }} by mauto 2.
    assert {{ Γ ⊫ A0 > s1 }} by mauto 2.
    assert {{ Γ ⊫ N : A0 > s1 }} by mauto 2.
    exists s2. mauto 3.
  - assert {{ Δ ⊫ A0 > s }} by mauto 2.
    assert {{ Δ ⊫ M0 : A0 > s }} by mauto 2.
    eexists; econstructor; mauto 3.
  - assert {{ Γ ⊫ M : A0 > s }} by mauto 3.
    eexists; mauto 3.
  - econstructor; mauto 3.
    assert {{ Γ ⊫ A[σ0] : Sort@s > HM0 }} by mauto 3.
    assert {{ Γ ⊫ A[σ0] > s }} by mauto 2.
    mauto 3.
Qed.


Lemma wf_typ_full_implies_wf_exp {P} (full_P : FullSig P) : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    exists s, {{ Γ ⊢ A : Sort@s }}.
Proof.
  inversion_clear 1; mauto 2.
  assert (exists s', Ax P s s') as [s'] by (eapply full_P).
  eexists; mauto 2.
Qed.


Lemma wf_typ_implies_wf_typ_ann {P} (full_P : FullSig P) : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} -> exists s, {{ Γ ⊫ A > s }}.
Proof.
  intros.
  assert (exists s, {{ Γ ⊢ A : Sort@s }}) as [s] by (eapply wf_typ_full_implies_wf_exp; mauto 2).
  eapply (wf_exp_implies_wf_exp_ann full_P) in H0.
  destruct_conjs.
  mauto 3.
Qed.



Lemma wf_judg_ann_implies_wf_judg {P} :
  (forall (Γ : ctx P), {{ ⊫ Γ }} -> {{ ⊢ Γ }}) /\
    (forall (Γ : ctx P) A s M, {{ Γ ⊫ M : A > s }} -> {{ Γ ⊢ M : A }}) /\
    (forall (Γ : ctx P) A s, {{ Γ ⊫ A > s }} -> {{ Γ ⊢ A }}) /\    
    (forall (Γ : ctx P) Δ σ, {{ Γ ⊫s σ : Δ }} -> {{ Γ ⊢s σ : Δ }}).
Proof.
  eapply syntactic_wf_ann_mut_ind; mauto 2.
Qed.

Corollary wf_ctx_ann_implies_wf_ctx {P} : forall {Γ : ctx P},
    {{ ⊫ Γ }} -> {{ ⊢ Γ }}.
Proof. intros; eapply wf_judg_ann_implies_wf_judg; mauto 2. Qed.

Corollary wf_exp_ann_implies_wf_exp {P} : forall {Γ : ctx P} {A s M},
    {{ Γ ⊫ M : A > s }} -> {{ Γ ⊢ M : A }}.
Proof. intros; eapply wf_judg_ann_implies_wf_judg; mauto 2. Qed.

Corollary wf_typ_ann_implies_wf_typ {P} : forall {Γ : ctx P} {A s},
    {{ Γ ⊫ A > s }} -> {{ Γ ⊢ A }}.
Proof. intros; eapply wf_judg_ann_implies_wf_judg; mauto 2. Qed.

Corollary wf_sub_ann_implies_wf_sub {P} : forall {Γ : ctx P} {Δ σ},
    {{ Γ ⊫s σ : Δ }} -> {{ Γ ⊢s σ : Δ }}.
Proof. intros; eapply wf_judg_ann_implies_wf_judg; mauto 2. Qed.
