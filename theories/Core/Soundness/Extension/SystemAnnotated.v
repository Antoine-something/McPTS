From Coq Require Import List Classes.RelationClasses Setoid Morphisms.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export Syntax System Corollaries.
From McPTS.Core.Soundness Require Import LogicalRelation.
Import Syntax_Notations.


Reserved Notation "⊫ Γ 'with' anns" (in custom judg at level 80, Γ custom exp, anns constr).
Reserved Notation "Γ 'with' anns ⊫ M : A @ s" (in custom judg at level 80, Γ custom exp, anns constr, M custom exp, A custom exp, s custom exp).
Reserved Notation "Γ 'with' anns ⊫ A @ s" (in custom judg at level 80, Γ custom exp, anns constr, A custom exp, s custom exp).
Reserved Notation "Γ 'with' anns ⊫s σ : Δ 'with' anns'" (in custom judg at level 80, Γ custom exp, anns constr, σ custom exp, Δ custom exp, anns' constr).

Generalizable All Variables.

Inductive wf_ctx_ann {P} : ctx_anns P -> ctx P -> Prop :=
| wfa_ctx_empty : {{ ⊫ ⋅ with nil}}
| wfa_ctx_enxtend :
  `( {{ ⊫ Γ with anns }} ->
     {{ Γ with anns ⊫ A @ so }} ->
     {{ ⊫ Γ, A with so::anns }} )
where "⊫ Γ 'with' anns" := (wf_ctx_ann anns Γ) (in custom judg) : type_scope
with wf_exp_ann {P} : ctx_anns P -> ctx P -> typ P -> SortOption P -> exp P -> Prop :=
(** Sorts *)
| wfa_st :
  `( Ax_typ P s1 s2 ->
     {{ ⊫ Γ with anns }} ->
     {{ Γ with anns ⊫ Sort@s1 : Sort@s2 @ ^None }} )

(** Functions *)
| wfa_pi :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ with anns ⊫ A : Sort@s1 @ so1 }} ->
        {{ Γ, A with (Some s1)::anns ⊫ B : Sort@s2 @ so2 }} ->
        {{ Γ with anns ⊫ Π r A B : Sort@s3 @ ^None }} )
| wfa_fn :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ with anns ⊫ A : Sort@s1 @ so1 }} ->
        {{ Γ, A with (Some s1)::anns ⊫ B : Sort@s2 @ so2 }} ->
        {{ Γ, A with (Some s1)::anns ⊫ M : B @ ^(Some s2) }} ->
        {{ Γ with anns ⊫ λ r A B M : Π r A B @ ^(Some s3) }} )
| wfa_app :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ with anns ⊫ A : Sort@s1 @ so1 }} ->
        {{ Γ, A with (Some s1)::anns ⊫ B : Sort@s2 @ so2 }} ->
        {{ Γ with anns ⊫ M : Π r A B @ ^(Some s3) }} ->
        {{ Γ with anns ⊫ N : A @ ^(Some s1) }} ->
        {{ Γ with anns ⊫ M N : B[Id,,N] @ ^(Some s2) }} )

(** Variables *)
| wfa_vlookup :
  `( {{ ⊫ Γ with anns }} ->
     {{ #x : A@so ∈ Γ with anns }} ->
     {{ Γ with anns ⊫ #x : A @ so }} )

(** Naturals *)
| wfa_nat :
  `( forall (r : Ru_nat P sn),
        {{ ⊫ Γ with anns}} ->
        {{ Γ with anns ⊫ ℕ : Sort@sn @ ^None }} )
| wfa_zero :
  `( forall (r : Ru_nat P sn),
        {{ ⊫ Γ with anns }} ->
        {{ Γ with anns ⊫ zero : ℕ @ ^(Some sn) }} )
| wfa_succ :
  `( forall (r : Ru_nat P sn),
        {{ Γ with anns ⊫ M : ℕ @ ^(Some sn) }} ->
        {{ Γ with anns ⊫ succ M : ℕ @ ^(Some sn) }} )
| wfa_rec :
  `( forall (r : Ru_nat P sn),
        {{ Γ, ℕ with (Some sn)::anns ⊫ A @ so }} ->
        {{ Γ with anns ⊫ MZ : A[Id,,zero] @ so }} ->
        {{ Γ, ℕ, A with so ::(Some sn)::anns ⊫ MS : A[Wk∘Wk,,succ #1] @ so  }} ->
        {{ Γ with anns ⊫ M : ℕ @ ^(Some sn) }} ->
        {{ Γ with anns ⊫ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] @ so }} )

(** explicit substitutions *)
| wfa_exp_sub:
  `( {{ Γ with anns ⊫s σ : Δ with anns' }} ->
     {{ Δ with anns' ⊫ M : A @ so }} ->
     {{ Δ with anns' ⊫ A @ so }} ->
     {{ Γ with anns ⊫ M[σ] : A[σ] @ so }} )

(** Conversions *)
| wfa_exp_conv :
  `( {{ Γ with anns ⊫ M : A @ so }} ->
     {{ Γ with anns ⊫ A' @ so' }} ->
     {{ Γ ⊢ A ⊆ A' }} ->
     {{ Γ with anns ⊫ M : A' @ so' }} )
| wfa_exp_conv_ann :
  `( {{ Γ with anns ⊫ M : A @ so }} ->
     {{ Γ with anns ⊫ A @ so' }} ->
     {{ Γ with anns ⊫ M : A @ so' }} )
where "Γ 'with' anns ⊫ M : A @ s" := (wf_exp_ann anns Γ A s M) (in custom judg) : type_scope

with wf_typ_ann {P} : ctx_anns P -> ctx P -> typ P -> SortOption P -> Prop :=
| wfa_typ_st :
  `( {{ ⊫ Γ with anns }} ->
     {{ Γ with anns ⊫ Sort@s @ ^None }} )
| wfa_typ_exp :
  `( {{ Γ with anns ⊫ A : Sort@s @ so }} ->
     {{ Γ with anns ⊫ A @ ^(Some s) }} )
| wfa_typ_sub :
  `( {{ Γ with anns ⊫s σ : Δ with anns' }} ->
     {{ Δ with anns' ⊫ A @ so}} ->
     {{ Γ with anns ⊫ A[σ] @ so }} )
where "Γ 'with' anns ⊫ A @ s" := (wf_typ_ann anns Γ A s) (in custom judg) : type_scope
with wf_sub_ann {P} : ctx_anns P -> ctx_anns P -> ctx P -> ctx P -> sub P -> Prop :=
| wfa_sub_id :
  `( {{ ⊫ Γ with anns }} ->
     {{ Γ with anns ⊫s Id : Γ with anns }} )
| wfa_sub_weaken :
  `( {{ ⊫ Γ, A with (Some s)::anns }} ->
     {{ Γ, A with (Some s)::anns ⊫s Wk : Γ with anns}} )
| wfa_sub_compose :
  `( {{ Γ1 with anns1 ⊫s σ2 : Γ2 with anns2 }} ->
     {{ Γ2 with anns2 ⊫s σ1 : Γ3 with anns3 }} ->
     {{ Γ1 with anns1 ⊫s σ1∘σ2 : Γ3 with anns3 }} )
| wfa_sub_extend :
  `( {{ Γ with anns ⊫s σ : Δ with anns' }} ->
     {{ Δ with anns' ⊫ A : Sort@s @ so }} ->
     {{ Γ with anns ⊫ M : A[σ] @ ^(Some s) }} ->
     {{ Γ with anns ⊫s σ,,M : Δ, A with (Some s)::anns'  }} )
| wfa_sub_conv :
  `( {{ Γ with anns ⊫s σ : Δ with anns' }} ->
     {{ ⊫ Δ' with anns'' }} ->
     {{ ⊢ Δ ⊆ Δ' }} ->
     {{ Γ with anns ⊫s σ : Δ' with anns'' }} )
where "Γ 'with' anns ⊫s σ : Δ 'with' anns'" := (wf_sub_ann anns anns' Γ Δ σ) (in custom judg) : type_scope.


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
  | Ax_typ P ?s1 ?s2 =>
      let s2' := fresh "s2'" in
      assert (exists s2', Ax_typ P s2 s2') as [s2'] by (eapply full_P)
  | Ru_pi P ?s1 ?s2 ?s3 =>
      let s3' := fresh "s3'" in
      assert (exists s3', Ax_typ P s3 s3') as [s3'] by (eapply full_P)
  | _ => idtac
  end.

#[local]
Ltac apply_fullness_all P full_P :=
  on_all_hyp: (fun H => apply_fullness_once P full_P H).


#[local]
Ltac gen_annotated_judg_IH P ann_ctx ann_exp ann_typ ann_sub H :=
  match type of H with
  | {{ ⊢ ^?Γ }} =>
      let HΓ := fresh "HΓ" in
      pose proof ann_ctx P Γ H as HΓ
  | {{ ^?Γ ⊢ ^?M : ^?A }} =>
      let HM := fresh "HM" in
      pose proof ann_exp P Γ M A H as HM
  | {{ ^?Γ ⊢ ^?A }} =>
      let HA := fresh "HA" in
      pose proof ann_typ P Γ A H as HA
  | {{ ^?Γ ⊢s ^?σ : ^?Δ }} =>
      let Hσ := fresh "Hσ" in
      pose proof ann_sub P Γ σ Δ H as Hσ
  end.

#[local]
Ltac gen_sort_none P :=
  repeat
    match goal with
    | s : P |- _ =>
        let Hs := fresh "Hs" in
        eassert {{ ^?Γ ⊫ Sort@s @ ^None }} by mauto 3;
        mark s
    end;
  unmark_all.

Lemma ctx_ann_decomp {P : PtsSig} : forall {Γ : ctx P} {A s}, {{ ⊫ Γ, A@s }} -> {{ ⊫ Γ }} /\ exists so, {{ Γ ⊫ A : Sort@s @ so }}.
Proof with now eauto.
  inversion 1...
Qed.

#[local]
Hint Resolve ctx_ann_decomp : mcpts.

Corollary ctx_ann_decomp_left {P : PtsSig} : forall {Γ : ctx P} {A s}, {{ ⊫ Γ, A@s }} -> {{ ⊫ Γ }}.
Proof with easy.
  intros * ?%ctx_ann_decomp...
Qed.

Corollary ctx_ann_decomp_right {P : PtsSig} : forall {Γ : ctx P} {A s}, {{ ⊫ Γ, A@s }} -> exists so, {{ Γ ⊫ A : Sort@s @ so }}.
Proof with easy.
  intros * ?%ctx_ann_decomp...
Qed.

#[local]
Hint Resolve ctx_ann_decomp_left ctx_ann_decomp_right : mcpts.

Lemma presup_sub_ann_ctx_ann {P} : forall {Γ : ctx P} {σ Δ},
    {{ Γ ⊫s σ : Δ }} -> {{ ⊫ Γ }} /\ {{ ⊫ Δ }}.
Proof.
  induction 1; destruct_conjs; split; mauto 3.
Qed.

#[local]
Hint Resolve presup_sub_ann_ctx_ann : mcpts.

Lemma presup_sub_ann_ctx_ann_left {P} : forall {Γ : ctx P} {σ Δ},
    {{ Γ ⊫s σ : Δ }} -> {{ ⊫ Γ }}.
Proof with easy.
  intros * ?%presup_sub_ann_ctx_ann...
Qed.

Lemma presup_sub_ann_ctx_ann_right {P} : forall {Γ : ctx P} {σ Δ},
    {{ Γ ⊫s σ : Δ }} -> {{ ⊫ Δ }}.
Proof with easy.
  intros * ?%presup_sub_ann_ctx_ann...
Qed.

#[local]
Hint Resolve presup_sub_ann_ctx_ann_left presup_sub_ann_ctx_ann_right : mcpts.

Lemma presup_exp_ann_ctx_ann {P} : forall {Γ : ctx P} {M A so},
    {{ Γ ⊫ M : A @ so }} -> {{ ⊫ Γ }}.
Proof.
  induction 1; mauto 3.
Qed.

#[local]
  Hint Resolve presup_exp_ann_ctx_ann : mcpts.
  
Lemma wf_ctx_implies_wf_ctx_ann {P} : forall {Γ : ctx P},
    {{ ⊢ Γ }} -> {{ ⊫ Γ }}
with wf_exp_implies_wf_exp_ann {P} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} -> exists so, {{ Γ ⊫ M : A @ so }}
with wf_typ_implies_wf_typ_ann {P} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} -> exists so, {{ Γ ⊫ A @ so }}
with wf_sub_implies_wf_sub_ann {P} : forall {Γ : ctx P} {σ Δ},
    {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊫s σ : Δ }}.
Proof.
  all: inversion_clear 1;
    (on_all_hyp: gen_annotated_judg_IH P wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann);
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann;
    destruct_conjs;
    mauto 3.

  - eexists; econstructor; mauto 3.
  - assert {{ Γ ⊫ Π r A0 B : Sort@s3 @ ^None }} by mauto 3.
    assert {{ Γ ⊫ Π r A0 B @ ^(Some s3) }} by mauto 3.
    assert {{ Γ ⊫ M0 : Π r A0 B @ ^(Some s3) }} by mauto 2.
    assert {{ Γ ⊫ A0 @ ^(Some s1) }} by mauto 2.
    assert {{ Γ ⊫ N : A0 @ ^(Some s1) }} by mauto 2.
    eexists; mauto 2.
  - eexists; econstructor; mauto 3.
    eapply wfa_exp_conv_ann; mauto 3.
    do 2 (econstructor; mauto 3).
  - assert {{ Γ ⊫s Id : Γ }} by mauto 4.
    assert {{ Γ ⊢ ℕ : Sort@s }} by mauto 3.
    assert {{ Γ ⊢ ℕ[Id] : Sort@s }} by mauto 4.
    assert {{ Γ ⊢ ℕ ≈ ℕ[Id] : Sort@s }} by mauto 3.
    assert {{ Γ ⊢ ℕ ⊆ ℕ[Id] }} by mauto 3.
    assert {{ Γ ⊫ zero : ℕ[Id] @ ^(Some s) }} by (eapply wfa_exp_conv; mauto).
    assert {{ Γ ⊫s Id,,zero : Γ, ℕ@s }} by (econstructor; mauto 3).
    assert {{ Γ ⊫ A0[Id,,zero] @ ^(Some s') }} by mauto 3.
    assert {{ Γ ⊫ MZ : A0[Id,,zero] @ ^(Some s') }} by mauto 3.
    assert {{ Γ ⊢ ℕ : Sort@s }} by mauto 3.
    assert {{ Γ ⊫ ℕ @ ^(Some s) }} by mauto 4.
    assert {{ Γ, ℕ@s ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, ℕ@s ⊫s Wk : Γ }} by mauto 3.
    assert {{ Γ, ℕ@s, A0@s' ⊢s Wk : Γ, ℕ@s }} by mauto 3.
    assert {{ Γ, ℕ@s, A0@s' ⊫s Wk : Γ, ℕ@s }} by mauto 3.
    assert {{ Γ, ℕ@s, A0@s' ⊫s Wk∘Wk : Γ }} by mauto 3.
    assert {{ Γ, ℕ@s, A0@s' ⊢ ℕ[Wk][Wk] ≈ ℕ : Sort@s }} by mauto 3.
    assert {{ Γ, ℕ@s, A0@s' ⊢ ℕ[Wk][Wk] ≈ ℕ[Wk∘Wk] : Sort@s }} by mauto 3.
    assert {{ Γ, ℕ@s, A0@s' ⊫ #1 : ℕ[Wk][Wk] @ ^(Some s) }} by mauto 4.
    assert {{ Γ, ℕ@s, A0@s' ⊫ #1 : ℕ @ ^(Some s) }} by (eapply wfa_exp_conv; mauto 4).
    assert {{ Γ, ℕ@s, A0@s' ⊫ succ #1 : ℕ @ ^(Some s) }} by mauto 3.
    assert {{ Γ, ℕ@s, A0@s' ⊢ ℕ ⊆ ℕ[Wk∘Wk] }} by (econstructor; mauto 4).
    assert {{ Γ, ℕ@s, A0@s' ⊫ succ #1 : ℕ[Wk∘Wk] @ ^(Some s) }} by (eapply wfa_exp_conv; mauto 4).
    assert {{ Γ, ℕ@s, A0@s' ⊫s Wk∘Wk,,succ #1 : Γ, ℕ@s }} by (econstructor; mauto 3).
    assert {{ Γ, ℕ@s, A0@s' ⊫ A0[Wk∘Wk,,succ #1] @ ^(Some s') }} by mauto 3.
    assert {{ Γ, ℕ@s, A0@s' ⊫ MS : A0[Wk∘Wk,,succ #1] @ ^(Some s') }} by mauto 3.
    eexists; econstructor; mauto 3.
  - assert (exists so, {{ Δ ⊫ A0 @ so }}) as [so] by mauto 3.
    assert {{ Δ ⊫ M0 : A0 @ so }} by mauto 2.
    assert {{ Γ ⊢ M0[σ] : A0[σ] }} by mauto 2.
    destruct so.
    + assert {{ Γ ⊫ M0[σ] : A0[σ] @ ^None }}.
      econstructor; mauto.
      eexists; mauto 3.
    + mauto 3.
  - assert {{ Γ ⊫ M : A[σ0] @ ^ (Some s) }} by mauto 4.
    mauto 3.
Qed.

#[export]
Hint Resolve wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann : mcpts.

Lemma wf_judg_ann_implies_wf_judg {P} :
  (forall (Γ : ctx P), {{ ⊫ Γ }} -> {{ ⊢ Γ }}) /\
    (forall (Γ : ctx P) A so M, {{ Γ ⊫ M : A @ so }} -> {{ Γ ⊢ M : A }}) /\
    (forall (Γ : ctx P) A so, {{ Γ ⊫ A @ so }} -> {{ Γ ⊢ A }}) /\
    (forall (Γ : ctx P) Δ σ, {{ Γ ⊫s σ : Δ }} -> {{ Γ ⊢s σ : Δ }}).
Proof.
  eapply syntactic_wf_ann_mut_ind; mauto 2.
Qed.

Corollary wf_ctx_ann_implies_wf_ctx {P} : forall {Γ : ctx P},
    {{ ⊫ Γ }} -> {{ ⊢ Γ }}.
Proof. intros; eapply wf_judg_ann_implies_wf_judg; mauto 2. Qed.

Corollary wf_exp_ann_implies_wf_exp {P} : forall {Γ : ctx P} {A s M},
    {{ Γ ⊫ M : A @ s }} -> {{ Γ ⊢ M : A }}.
Proof. intros; eapply wf_judg_ann_implies_wf_judg; mauto 2. Qed.

Corollary wf_typ_ann_implies_wf_typ {P} : forall {Γ : ctx P} {A s},
    {{ Γ ⊫ A @ s }} -> {{ Γ ⊢ A }}.
Proof. intros; eapply wf_judg_ann_implies_wf_judg; mauto 2. Qed.

Corollary wf_sub_ann_implies_wf_sub {P} : forall {Γ : ctx P} {Δ σ},
    {{ Γ ⊫s σ : Δ }} -> {{ Γ ⊢s σ : Δ }}.
Proof. intros; eapply wf_judg_ann_implies_wf_judg; mauto 2. Qed.
